-- Algorithms/Horner.lean
--
-- Source-facing Horner-rule infrastructure for Higham Chapter 5.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.ForwardError
import NumStability.Algorithms.MatMul

namespace NumStability

open scoped BigOperators

/-!
Horner data in this file is stored in descending coefficient order:
`[a_n, a_{n-1}, ..., a_0]`.  This matches the loop form in Higham's
Algorithm 5.1, where the computation starts from the leading coefficient and
then walks downward through the remaining coefficients.
-/

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

/-- Formal derivative of `polyDesc`, evaluated at `x`.  For descending
coefficients `[a_n, ..., a_0]`, this is
`n*a_n*x^(n-1) + ... + a_1`. -/
noncomputable def polyDescDeriv (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: rest =>
      (rest.length : ℝ) * a * x ^ (rest.length - 1) +
        polyDescDeriv x rest

/-- Absolute-coefficient majorant for the formal derivative of `polyDesc`.
For descending coefficients this is
`n*|a_n|*|x|^(n-1) + ... + |a_1|`. -/
noncomputable def polyDescDerivAbs (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: rest =>
      (rest.length : ℝ) * |a| * |x| ^ (rest.length - 1) +
        polyDescDerivAbs x rest

/-- The derivative absolute majorant is nonnegative. -/
theorem polyDescDerivAbs_nonneg (x : ℝ) :
    ∀ coeffsDesc : List ℝ, 0 ≤ polyDescDerivAbs x coeffsDesc := by
  intro coeffsDesc
  induction coeffsDesc with
  | nil =>
      simp [polyDescDerivAbs]
  | cons a rest ih =>
      have hterm :
          0 ≤ (rest.length : ℝ) * |a| * |x| ^ (rest.length - 1) := by
        exact mul_nonneg
          (mul_nonneg (by exact_mod_cast rest.length.zero_le)
            (abs_nonneg a))
          (pow_nonneg (abs_nonneg x) _)
      simp [polyDescDerivAbs]
      exact add_nonneg hterm ih

/-- The formal derivative is bounded by its absolute-coefficient majorant. -/
theorem abs_polyDescDeriv_le_polyDescDerivAbs (x : ℝ) :
    ∀ coeffsDesc : List ℝ,
      |polyDescDeriv x coeffsDesc| ≤ polyDescDerivAbs x coeffsDesc := by
  intro coeffsDesc
  induction coeffsDesc with
  | nil =>
      simp [polyDescDeriv, polyDescDerivAbs]
  | cons a rest ih =>
      have hterm :
          |(rest.length : ℝ) * a * x ^ (rest.length - 1)| ≤
            (rest.length : ℝ) * |a| * |x| ^ (rest.length - 1) := by
        rw [abs_mul, abs_mul, abs_pow,
          abs_of_nonneg (by exact_mod_cast rest.length.zero_le)]
      have htri :
          |(rest.length : ℝ) * a * x ^ (rest.length - 1) +
              polyDescDeriv x rest| ≤
            |(rest.length : ℝ) * a * x ^ (rest.length - 1)| +
              |polyDescDeriv x rest| :=
        abs_add_le _ _
      have hsum :
          |(rest.length : ℝ) * a * x ^ (rest.length - 1)| +
              |polyDescDeriv x rest| ≤
            (rest.length : ℝ) * |a| * |x| ^ (rest.length - 1) +
              polyDescDerivAbs x rest :=
        add_le_add hterm ih
      simpa [polyDescDeriv, polyDescDerivAbs] using le_trans htri hsum

/-- Higham, 2nd ed., Chapter 5, Algorithm 5.2, first-derivative core:
one exact coupled Horner update for `(p, p')`. -/
def hornerDerivativeStep (x : ℝ) (state : ℝ × ℝ) (a : ℝ) : ℝ × ℝ :=
  let y := hornerStep x state.1 a
  (y, x * state.2 + state.1)

/-- Algorithm 5.2 specialized to the value and first derivative.  The first
component is `p(x)` and the second component is `p'(x)`. -/
def hornerDerivativeDesc (x : ℝ) : List ℝ → ℝ × ℝ
  | [] => (0, 0)
  | a :: rest => rest.foldl (hornerDerivativeStep x) (a, 0)

lemma hornerDerivativeFold_eq_acc_mul_pow_add_polyDesc_and_deriv
    (x : ℝ) :
    ∀ (rest : List ℝ) (y d : ℝ),
      (rest.foldl (hornerDerivativeStep x) (y, d)).1 =
        y * x ^ rest.length + polyDesc x rest ∧
      (rest.foldl (hornerDerivativeStep x) (y, d)).2 =
        d * x ^ rest.length +
          (rest.length : ℝ) * y * x ^ (rest.length - 1) +
          polyDescDeriv x rest := by
  intro rest
  induction rest with
  | nil =>
      intro y d
      simp [polyDesc, polyDescDeriv]
  | cons a rest ih =>
      intro y d
      have hfirst :=
        (ih (hornerStep x y a) (x * d + y)).1
      have hsecond :=
        (ih (hornerStep x y a) (x * d + y)).2
      constructor
      · rw [List.foldl]
        change (rest.foldl (hornerDerivativeStep x)
            (hornerStep x y a, x * d + y)).1 =
          y * x ^ (a :: rest).length + polyDesc x (a :: rest)
        rw [hfirst]
        simp [polyDesc, hornerStep, pow_succ]
        ring
      · rw [List.foldl]
        change (rest.foldl (hornerDerivativeStep x)
            (hornerStep x y a, x * d + y)).2 =
          d * x ^ (a :: rest).length +
            ((a :: rest).length : ℝ) * y *
              x ^ ((a :: rest).length - 1) +
            polyDescDeriv x (a :: rest)
        rw [hsecond]
        cases rest with
        | nil =>
            simp [polyDescDeriv, hornerStep]
            ring
        | cons b tail =>
            simp [polyDescDeriv, hornerStep, pow_succ]
            ring

/-- The value component of Algorithm 5.2's first-derivative core is ordinary
Horner evaluation. -/
theorem hornerDerivativeDesc_fst_eq_polyDesc
    (x : ℝ) (coeffsDesc : List ℝ) :
    (hornerDerivativeDesc x coeffsDesc).1 = polyDesc x coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [hornerDerivativeDesc, polyDesc]
  | cons a rest =>
      have h :=
        (hornerDerivativeFold_eq_acc_mul_pow_add_polyDesc_and_deriv x
          rest a 0).1
      simpa [hornerDerivativeDesc, polyDesc] using h

/-- Algorithm 5.2's first-derivative core computes the formal derivative of the
descending-list polynomial. -/
theorem hornerDerivativeDesc_snd_eq_polyDescDeriv
    (x : ℝ) (coeffsDesc : List ℝ) :
    (hornerDerivativeDesc x coeffsDesc).2 = polyDescDeriv x coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [hornerDerivativeDesc, polyDescDeriv]
  | cons a rest =>
      have h :=
        (hornerDerivativeFold_eq_acc_mul_pow_add_polyDesc_and_deriv x
          rest a 0).2
      simpa [hornerDerivativeDesc, polyDescDeriv] using h

/-! ## Problem 5.1: differentiating the Horner recurrence -/

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

/-- Source-facing higher derivative value generated by Algorithm 5.2 after the
final factorial scaling. -/
noncomputable def polyDescHigherDeriv
    (alpha : ℝ) (i : ℕ) (coeffsDesc : List ℝ) : ℝ :=
  (Nat.factorial i : ℝ) * hornerTaylorFunctionDesc alpha coeffsDesc i

/-- Algorithm 5.2 output surface for derivative order `i`. -/
noncomputable def hornerHigherDerivativeOutput
    (alpha : ℝ) (coeffsDesc : List ℝ) (i : ℕ) : ℝ :=
  polyDescHigherDeriv alpha i coeffsDesc

/-- Finite `i = 0:k` output surface for Algorithm 5.2. -/
noncomputable def hornerHigherDerivativeOutputs
    (alpha : ℝ) (k : ℕ) (coeffsDesc : List ℝ) : Fin (k + 1) → ℝ :=
  fun i => hornerHigherDerivativeOutput alpha coeffsDesc i.val

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

lemma hornerTaylorFunctionFold_one_eq_derivativeFold
    (alpha : ℝ) :
    ∀ (rest : List ℝ) (coeff : ℕ → ℝ),
      (rest.foldl
          (fun c b => hornerTaylorFunctionStep alpha b c) coeff) 1 =
        (rest.foldl (hornerDerivativeStep alpha)
          (coeff 0, coeff 1)).2 := by
  intro rest
  induction rest with
  | nil =>
      intro coeff
      simp
  | cons a rest ih =>
      intro coeff
      simpa [List.foldl, hornerTaylorFunctionStep,
        hornerDerivativeStep, hornerStep] using
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

/-- The first differentiated-Horner Taylor coefficient is the first derivative. -/
theorem hornerTaylorFunctionDesc_one_eq_polyDescDeriv
    (alpha : ℝ) (coeffsDesc : List ℝ) :
    hornerTaylorFunctionDesc alpha coeffsDesc 1 =
      polyDescDeriv alpha coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [hornerTaylorFunctionDesc, polyDescDeriv]
  | cons a rest =>
      have hfold :=
        hornerTaylorFunctionFold_one_eq_derivativeFold alpha rest
          (fun
            | 0 => a
            | _ + 1 => 0)
      have hderiv :=
        hornerDerivativeDesc_snd_eq_polyDescDeriv alpha (a :: rest)
      simpa [hornerTaylorFunctionDesc, hornerDerivativeDesc] using
        Eq.trans hfold hderiv

theorem polyDescHigherDeriv_zero_eq_polyDesc
    (alpha : ℝ) (coeffsDesc : List ℝ) :
    polyDescHigherDeriv alpha 0 coeffsDesc =
      polyDesc alpha coeffsDesc := by
  simp [polyDescHigherDeriv, hornerTaylorFunctionDesc_zero_eq_polyDesc]

theorem polyDescHigherDeriv_one_eq_polyDescDeriv
    (alpha : ℝ) (coeffsDesc : List ℝ) :
    polyDescHigherDeriv alpha 1 coeffsDesc =
      polyDescDeriv alpha coeffsDesc := by
  simp [polyDescHigherDeriv, hornerTaylorFunctionDesc_one_eq_polyDescDeriv]

theorem hornerHigherDerivativeOutput_eq_factorial_taylor
    (alpha : ℝ) (coeffsDesc : List ℝ) (i : ℕ) :
    hornerHigherDerivativeOutput alpha coeffsDesc i =
      (Nat.factorial i : ℝ) *
        hornerTaylorFunctionDesc alpha coeffsDesc i := by
  rfl

theorem hornerHigherDerivativeOutputs_apply
    (alpha : ℝ) (k : ℕ) (coeffsDesc : List ℝ) (i : Fin (k + 1)) :
    hornerHigherDerivativeOutputs alpha k coeffsDesc i =
      polyDescHigherDeriv alpha i.val coeffsDesc := by
  rfl

/-! ### All-order identification and rounded Algorithm 5.2

The function-valued state above stores Taylor coefficients, rather than the
derivatives themselves.  The next recurrence is independent: it is obtained
by differentiating `x * q(x) + a` and therefore carries the factor `i + 1`
in derivative order `i + 1`.  Relating the two recurrences identifies every
order, including the orders `i ≥ 2` that are not covered by the earlier
value/first-derivative specialization. -/

/-- One differentiated Horner update on the *scaled* formal derivatives.
If `deriv i` is `q^(i)(alpha)`, the successor branch is the product-rule
identity `(x*q)^(i+1) = x*q^(i+1) + (i+1)*q^i`. -/
noncomputable def hornerFormalDerivativeFunctionStep
    (alpha a : ℝ) (deriv : ℕ → ℝ) : ℕ → ℝ
  | 0 => alpha * deriv 0 + a
  | i + 1 => alpha * deriv (i + 1) + (i + 1 : ℝ) * deriv i

/-- All formal derivatives produced by repeatedly differentiating the Horner
recurrence.  This is the scaled, source-level interpretation of Algorithm 5.2. -/
noncomputable def hornerFormalDerivativeFunctionDesc
    (alpha : ℝ) : List ℝ → ℕ → ℝ
  | [] => fun _ => 0
  | a :: rest =>
      rest.foldl
        (fun deriv b => hornerFormalDerivativeFunctionStep alpha b deriv)
        (fun
          | 0 => a
          | _ + 1 => 0)

lemma hornerFormalDerivativeFunctionStep_factorial_taylor
    (alpha a : ℝ) (coeff : ℕ → ℝ) (i : ℕ) :
    hornerFormalDerivativeFunctionStep alpha a
        (fun j => (Nat.factorial j : ℝ) * coeff j) i =
      (Nat.factorial i : ℝ) *
        hornerTaylorFunctionStep alpha a coeff i := by
  cases i with
  | zero =>
      simp [hornerFormalDerivativeFunctionStep, hornerTaylorFunctionStep]
  | succ i =>
      simp only [hornerFormalDerivativeFunctionStep,
        hornerTaylorFunctionStep, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]
      ring

lemma hornerFormalDerivativeFunctionFold_factorial_taylor
    (alpha : ℝ) :
    ∀ (rest : List ℝ) (coeff : ℕ → ℝ) (i : ℕ),
      rest.foldl
          (fun deriv b => hornerFormalDerivativeFunctionStep alpha b deriv)
          (fun j => (Nat.factorial j : ℝ) * coeff j) i =
        (Nat.factorial i : ℝ) *
          (rest.foldl
            (fun c b => hornerTaylorFunctionStep alpha b c) coeff) i := by
  intro rest
  induction rest with
  | nil =>
      intro coeff i
      rfl
  | cons a rest ih =>
      intro coeff i
      simp only [List.foldl]
      rw [show
        hornerFormalDerivativeFunctionStep alpha a
            (fun j => (Nat.factorial j : ℝ) * coeff j) =
          fun j => (Nat.factorial j : ℝ) *
            hornerTaylorFunctionStep alpha a coeff j by
              funext j
              exact hornerFormalDerivativeFunctionStep_factorial_taylor
                alpha a coeff j]
      exact ih (hornerTaylorFunctionStep alpha a coeff) i

/-- End-to-end all-order identification for Algorithm 5.2: after the final
factorial scaling, its Taylor-state output is exactly the formal derivative
obtained by differentiating every Horner update.  There are no order-specific
premises. -/
theorem polyDescHigherDeriv_eq_hornerFormalDerivativeFunctionDesc
    (alpha : ℝ) (i : ℕ) (coeffsDesc : List ℝ) :
    polyDescHigherDeriv alpha i coeffsDesc =
      hornerFormalDerivativeFunctionDesc alpha coeffsDesc i := by
  cases coeffsDesc with
  | nil =>
      simp [polyDescHigherDeriv, hornerTaylorFunctionDesc,
        hornerFormalDerivativeFunctionDesc]
  | cons a rest =>
      let coeff : ℕ → ℝ := fun
        | 0 => a
        | _ + 1 => 0
      have h :=
        hornerFormalDerivativeFunctionFold_factorial_taylor
          alpha rest coeff i
      have hinit :
          (fun j => (Nat.factorial j : ℝ) * coeff j) = coeff := by
        funext j
        cases j <;> simp [coeff]
      rw [hinit] at h
      simpa [polyDescHigherDeriv, hornerTaylorFunctionDesc,
        hornerFormalDerivativeFunctionDesc, coeff] using h.symm

/-- The independent all-order formal recurrence agrees with the existing
displayed polynomial at order zero. -/
theorem hornerFormalDerivativeFunctionDesc_zero_eq_polyDesc
    (alpha : ℝ) (coeffsDesc : List ℝ) :
    hornerFormalDerivativeFunctionDesc alpha coeffsDesc 0 =
      polyDesc alpha coeffsDesc := by
  rw [← polyDescHigherDeriv_eq_hornerFormalDerivativeFunctionDesc]
  exact polyDescHigherDeriv_zero_eq_polyDesc alpha coeffsDesc

/-- The independent all-order formal recurrence agrees with the existing
displayed formal derivative at order one. -/
theorem hornerFormalDerivativeFunctionDesc_one_eq_polyDescDeriv
    (alpha : ℝ) (coeffsDesc : List ℝ) :
    hornerFormalDerivativeFunctionDesc alpha coeffsDesc 1 =
      polyDescDeriv alpha coeffsDesc := by
  rw [← polyDescHigherDeriv_eq_hornerFormalDerivativeFunctionDesc]
  exact polyDescHigherDeriv_one_eq_polyDescDeriv alpha coeffsDesc

/-- Coefficients of the synthetic-division quotient generated while Horner's
method evaluates the current accumulator `y` against the remaining descending
coefficient list. -/
def hornerSyntheticQuotientFold (alpha y : ℝ) : List ℝ → List ℝ
  | [] => []
  | [ _a0 ] => [y]
  | a :: b :: rest =>
      y :: hornerSyntheticQuotientFold alpha (hornerStep alpha y a)
        (b :: rest)

/-- Synthetic-division quotient coefficients for `coeffsDesc`, in descending
order.  If `coeffsDesc` represents `p`, the result represents the quotient
`q` in `p(x) = (x - alpha) q(x) + p(alpha)`. -/
def hornerSyntheticQuotientDesc (alpha : ℝ) : List ℝ → List ℝ
  | [] => []
  | [_a] => []
  | a :: b :: rest => hornerSyntheticQuotientFold alpha a (b :: rest)

lemma hornerSyntheticQuotientFold_length (alpha : ℝ) :
    ∀ (rest : List ℝ) (y : ℝ),
      (hornerSyntheticQuotientFold alpha y rest).length = rest.length := by
  intro rest
  induction rest with
  | nil =>
      intro y
      simp [hornerSyntheticQuotientFold]
  | cons a rest ih =>
      intro y
      cases rest with
      | nil =>
          simp [hornerSyntheticQuotientFold]
      | cons b tail =>
          simpa [hornerSyntheticQuotientFold] using
            ih (hornerStep alpha y a)

lemma hornerSyntheticQuotientFold_spec (alpha x : ℝ) :
    ∀ (rest : List ℝ) (y : ℝ),
      y * x ^ rest.length + polyDesc x rest =
        (x - alpha) *
            polyDesc x (hornerSyntheticQuotientFold alpha y rest) +
          rest.foldl (hornerStep alpha) y := by
  intro rest
  induction rest with
  | nil =>
      intro y
      simp [hornerSyntheticQuotientFold, polyDesc]
  | cons a rest ih =>
      intro y
      cases rest with
      | nil =>
          simp [hornerSyntheticQuotientFold, polyDesc, hornerStep]
          ring
      | cons b tail =>
          have hih := ih (hornerStep alpha y a)
          have hlen :
              (hornerSyntheticQuotientFold alpha (hornerStep alpha y a)
                  (b :: tail)).length = (b :: tail).length :=
            hornerSyntheticQuotientFold_length alpha (b :: tail)
              (hornerStep alpha y a)
          have hlen' :
              (hornerSyntheticQuotientFold alpha (alpha * y + a)
                  (b :: tail)).length = (b :: tail).length := by
            simpa [hornerStep] using hlen
          simp [hornerSyntheticQuotientFold, polyDesc, hornerStep,
            pow_succ] at hih ⊢
          calc
            y * (x ^ tail.length * x * x) +
                (a * (x ^ tail.length * x) +
                  (b * x ^ tail.length + polyDesc x tail)) =
              (x - alpha) * (y * (x ^ tail.length * x)) +
                ((alpha * y + a) * (x ^ tail.length * x) +
                  (b * x ^ tail.length + polyDesc x tail)) := by
                ring
            _ =
              (x - alpha) * (y * (x ^ tail.length * x)) +
                ((x - alpha) *
                    polyDesc x
                      (hornerSyntheticQuotientFold alpha
                        (alpha * y + a) (b :: tail)) +
                  List.foldl (hornerStep alpha)
                    (alpha * (alpha * y + a) + b) tail) := by
                rw [hih]
            _ =
              (x - alpha) *
                  (y * (x ^ tail.length * x) +
                    polyDesc x
                      (hornerSyntheticQuotientFold alpha
                        (alpha * y + a) (b :: tail))) +
                List.foldl (hornerStep alpha)
                  (alpha * (alpha * y + a) + b) tail := by
                ring
            _ =
              (x - alpha) *
                  (y * x ^
                      (hornerSyntheticQuotientFold alpha
                        (alpha * y + a) (b :: tail)).length +
                    polyDesc x
                      (hornerSyntheticQuotientFold alpha
                        (alpha * y + a) (b :: tail))) +
                List.foldl (hornerStep alpha)
                  (alpha * (alpha * y + a) + b) tail := by
                rw [hlen']
                simp [pow_succ]

/-- Horner's method implements synthetic division:
`p(x) = (x - alpha) q(x) + p(alpha)`. -/
theorem hornerSyntheticDivisionDesc_spec
    (alpha x : ℝ) (coeffsDesc : List ℝ) :
    polyDesc x coeffsDesc =
      (x - alpha) * polyDesc x
          (hornerSyntheticQuotientDesc alpha coeffsDesc) +
        hornerDesc alpha coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [polyDesc, hornerSyntheticQuotientDesc, hornerDesc]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [polyDesc, hornerSyntheticQuotientDesc, hornerDesc]
      | cons b tail =>
          simpa [polyDesc, hornerSyntheticQuotientDesc, hornerDesc]
            using hornerSyntheticQuotientFold_spec alpha x (b :: tail) a

lemma hornerSyntheticQuotientFold_eval_eq_derivativeFold
    (alpha : ℝ) :
    ∀ (rest : List ℝ) (y d : ℝ),
      polyDesc alpha (hornerSyntheticQuotientFold alpha y rest) +
          d * alpha ^ rest.length =
        (rest.foldl (hornerDerivativeStep alpha) (y, d)).2 := by
  intro rest
  induction rest with
  | nil =>
      intro y d
      simp [hornerSyntheticQuotientFold, polyDesc]
  | cons a rest ih =>
      intro y d
      cases rest with
      | nil =>
          simp [hornerSyntheticQuotientFold, polyDesc,
            hornerDerivativeStep, hornerStep]
          ring
      | cons b tail =>
          have hih := ih (hornerStep alpha y a) (alpha * d + y)
          have hlen :
              (hornerSyntheticQuotientFold alpha (hornerStep alpha y a)
                  (b :: tail)).length = (b :: tail).length :=
            hornerSyntheticQuotientFold_length alpha (b :: tail)
              (hornerStep alpha y a)
          have hlen' :
              (hornerSyntheticQuotientFold alpha (alpha * y + a)
                  (b :: tail)).length = (b :: tail).length := by
            simpa [hornerStep] using hlen
          simp [hornerSyntheticQuotientFold, polyDesc,
            hornerDerivativeStep, hornerStep, pow_succ] at hih ⊢
          rw [hlen']
          simp [pow_succ]
          calc
            y * (alpha ^ tail.length * alpha) +
                polyDesc alpha
                  (hornerSyntheticQuotientFold alpha
                    (alpha * y + a) (b :: tail)) +
                d * (alpha ^ tail.length * alpha * alpha) =
              polyDesc alpha
                  (hornerSyntheticQuotientFold alpha
                    (alpha * y + a) (b :: tail)) +
                (alpha * d + y) *
                  (alpha ^ tail.length * alpha) := by
                ring
            _ =
              (List.foldl (hornerDerivativeStep alpha)
                (alpha * (alpha * y + a) + b,
                  alpha * (alpha * d + y) + (alpha * y + a)) tail).2 := hih

/-- Evaluating the synthetic-division quotient at `alpha` gives `p'(alpha)`. -/
theorem hornerSyntheticQuotientDesc_eval_eq_polyDescDeriv
    (alpha : ℝ) (coeffsDesc : List ℝ) :
    polyDesc alpha (hornerSyntheticQuotientDesc alpha coeffsDesc) =
      polyDescDeriv alpha coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [hornerSyntheticQuotientDesc, polyDesc, polyDescDeriv]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [hornerSyntheticQuotientDesc, polyDesc, polyDescDeriv]
      | cons b tail =>
          have hfold :=
            hornerSyntheticQuotientFold_eval_eq_derivativeFold alpha
              (b :: tail) a 0
          have hderiv :=
            hornerDerivativeDesc_snd_eq_polyDescDeriv alpha (a :: b :: tail)
          simpa [hornerSyntheticQuotientDesc, hornerDerivativeDesc] using
            Eq.trans hfold hderiv

lemma polyDescAbs_hornerSyntheticQuotientFold_le_derivMajorant
    (x : ℝ) :
    ∀ (rest : List ℝ) (y : ℝ),
      polyDescAbs x (hornerSyntheticQuotientFold x y rest) ≤
        (rest.length : ℝ) * |y| * |x| ^ (rest.length - 1) +
          polyDescDerivAbs x rest := by
  intro rest
  induction rest with
  | nil =>
      intro y
      simp [hornerSyntheticQuotientFold, polyDescAbs, polyDescDerivAbs]
  | cons a rest ih =>
      intro y
      cases rest with
      | nil =>
          simp [hornerSyntheticQuotientFold, polyDescAbs, polyDescDerivAbs]
      | cons b tail =>
          have htail :=
            ih (hornerStep x y a)
          have hy :
              |hornerStep x y a| ≤ |x| * |y| + |a| := by
            unfold hornerStep
            calc
              |x * y + a| ≤ |x * y| + |a| := abs_add_le _ _
              _ = |x| * |y| + |a| := by rw [abs_mul]
          have hfactor_nonneg :
              0 ≤ ((b :: tail).length : ℝ) *
                  |x| ^ ((b :: tail).length - 1) := by
            exact mul_nonneg
              (by exact_mod_cast (b :: tail).length.zero_le)
              (pow_nonneg (abs_nonneg x) _)
          have hscaled :
              ((b :: tail).length : ℝ) *
                  |hornerStep x y a| *
                  |x| ^ ((b :: tail).length - 1) ≤
                ((b :: tail).length : ℝ) *
                  (|x| * |y| + |a|) *
                  |x| ^ ((b :: tail).length - 1) := by
            nlinarith [mul_le_mul_of_nonneg_left hy hfactor_nonneg]
          have htail' :
              polyDescAbs x
                  (hornerSyntheticQuotientFold x (hornerStep x y a)
                    (b :: tail)) ≤
                ((b :: tail).length : ℝ) *
                  (|x| * |y| + |a|) *
                  |x| ^ ((b :: tail).length - 1) +
                  polyDescDerivAbs x (b :: tail) := by
            exact le_trans htail (add_le_add hscaled (le_refl _))
          have hqtailLen :
              (hornerSyntheticQuotientFold x (hornerStep x y a)
                (b :: tail)).length = (b :: tail).length :=
            hornerSyntheticQuotientFold_length x (b :: tail)
              (hornerStep x y a)
          simp [hornerSyntheticQuotientFold, polyDescAbs,
            polyDescDerivAbs, pow_succ, hqtailLen] at htail' ⊢
          nlinarith [htail',
            mul_nonneg (abs_nonneg y)
              (pow_nonneg (abs_nonneg x) tail.length),
            mul_nonneg (abs_nonneg a)
              (pow_nonneg (abs_nonneg x) tail.length),
            polyDescDerivAbs_nonneg x tail]

/-- The absolute majorant of the exact synthetic-division quotient is bounded
by the derivative absolute majorant `ptilde'` used in Higham (5.7). -/
theorem polyDescAbs_hornerSyntheticQuotientDesc_le_polyDescDerivAbs
    (x : ℝ) (coeffsDesc : List ℝ) :
    polyDescAbs x (hornerSyntheticQuotientDesc x coeffsDesc) ≤
      polyDescDerivAbs x coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [hornerSyntheticQuotientDesc, polyDescAbs, polyDescDerivAbs]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [hornerSyntheticQuotientDesc, polyDescAbs, polyDescDerivAbs]
      | cons b tail =>
          simpa [hornerSyntheticQuotientDesc, polyDescDerivAbs] using
            polyDescAbs_hornerSyntheticQuotientFold_le_derivMajorant
              x (b :: tail) a

/-- Higham, 2nd ed., Chapter 5, Section 5.3, equation (5.8):
auxiliary accumulator for the Newton form
`sum_i c_i * prod_{j<i} (x - alpha_j)`.  The argument `basis` carries the
current prefix product. -/
noncomputable def newtonFormAux (x : ℝ) :
    List ℝ → List ℝ → ℝ → ℝ
  | [], _nodes, _basis => 0
  | c :: _cs, [], basis => c * basis
  | c :: cs, alpha :: nodes, basis =>
      c * basis + newtonFormAux x cs nodes (basis * (x - alpha))

/-- Higham, 2nd ed., Chapter 5, Section 5.3, equation (5.8):
the Newton-form polynomial
`p(x) = sum_i c_i * prod_{j<i} (x - alpha_j)`.

The coefficient list is `[c_0, ..., c_n]`; the node list starts with
`[alpha_0, ...]`.  Extra nodes are ignored, as in the source formula where
`alpha_n` is interpolation data but not used in the product for `c_n`. -/
noncomputable def newtonForm (x : ℝ) (coeffs nodes : List ℝ) : ℝ :=
  newtonFormAux x coeffs nodes 1

/-- Nested Horner-like evaluation of the Newton-form polynomial:
`q_i = c_i + (x - alpha_i) q_{i+1}`. -/
noncomputable def newtonFormNested (x : ℝ) :
    List ℝ → List ℝ → ℝ
  | [], _nodes => 0
  | c :: _cs, [] => c
  | c :: cs, alpha :: nodes =>
      c + (x - alpha) * newtonFormNested x cs nodes

lemma newtonFormAux_eq_basis_mul_nested (x : ℝ) :
    ∀ (coeffs nodes : List ℝ) (basis : ℝ),
      newtonFormAux x coeffs nodes basis =
        basis * newtonFormNested x coeffs nodes := by
  intro coeffs
  induction coeffs with
  | nil =>
      intro nodes basis
      simp [newtonFormAux, newtonFormNested]
  | cons c cs ih =>
      intro nodes basis
      cases nodes with
      | nil =>
          simp [newtonFormAux, newtonFormNested]
          ring
      | cons alpha nodes =>
          simp [newtonFormAux, newtonFormNested, ih]
          ring

/-- Equation (5.8)'s displayed sum/product Newton form is equal to the
standard nested evaluation recurrence immediately following the displayed
formula. -/
theorem newtonForm_eq_newtonFormNested
    (x : ℝ) (coeffs nodes : List ℝ) :
    newtonForm x coeffs nodes = newtonFormNested x coeffs nodes := by
  simpa [newtonForm] using
    newtonFormAux_eq_basis_mul_nested x coeffs nodes 1

/-- Higham, 2nd ed., Chapter 5, Section 5.3:
one exact divided-difference sweep at level `k`.

For entries `j <= k`, the source recurrence leaves the entry fixed.  For
`j > k`, it applies
`(c_j^(k) - c_{j-1}^(k)) / (alpha_j - alpha_{j-k-1})`.  The functions are
indexed by natural numbers so later finite-vector and matrix adapters can
restrict them to `0:n`. -/
noncomputable def dividedDifferenceStep
    (nodes coeffs : ℕ → ℝ) (k : ℕ) : ℕ → ℝ :=
  fun j =>
    if j ≤ k then
      coeffs j
    else
      (coeffs j - coeffs (j - 1)) /
        (nodes j - nodes (j - k - 1))

theorem dividedDifferenceStep_of_le
    (nodes coeffs : ℕ → ℝ) {k j : ℕ} (hj : j ≤ k) :
    dividedDifferenceStep nodes coeffs k j = coeffs j := by
  simp [dividedDifferenceStep, hj]

theorem dividedDifferenceStep_of_gt
    (nodes coeffs : ℕ → ℝ) {k j : ℕ} (hj : k < j) :
    dividedDifferenceStep nodes coeffs k j =
      (coeffs j - coeffs (j - 1)) /
        (nodes j - nodes (j - k - 1)) := by
  have hnot : ¬j ≤ k := Nat.not_le_of_gt hj
  simp [dividedDifferenceStep, hnot]

/-- Embed a finite vector on `0:n` into a natural-number-indexed vector,
padding with zero outside the source range. -/
noncomputable def dividedDifferenceFinToNat {n : ℕ}
    (v : Fin (n + 1) → ℝ) : ℕ → ℝ :=
  fun j => if h : j < n + 1 then v ⟨j, h⟩ else 0

/-- The predecessor index used by the finite divided-difference row. -/
def dividedDifferenceFinPred {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- Higham (5.9): the finite lower-bidiagonal `L_k` action for divided
differences on the vector indexed by `0:n`.

Rows `0:k` are copied.  Later rows contain the two nonzero coefficients
`1/(alpha_j-alpha_{j-k-1})` and `-1/(alpha_j-alpha_{j-k-1})`, multiplying
entries `j` and `j-1` respectively. -/
noncomputable def dividedDifferenceLMatrix
    (nodes : ℕ → ℝ) (n k : ℕ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun i j =>
    if _hi : i.val ≤ k then
      if j = i then 1 else 0
    else
      let den := nodes i.val - nodes (i.val - k - 1)
      (if j = i then 1 / den else 0) +
        (if j = dividedDifferenceFinPred i then -(1 / den) else 0)

/-- Matrix-vector action of Higham's finite `L_k`. -/
noncomputable def dividedDifferenceLMatrixAction
    (nodes : ℕ → ℝ) (n k : ℕ) (v : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => ∑ j : Fin (n + 1), dividedDifferenceLMatrix nodes n k i j * v j

theorem dividedDifferenceLMatrixAction_of_le
    (nodes : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : i.val ≤ k) :
    dividedDifferenceLMatrixAction nodes n k v i = v i := by
  simp [dividedDifferenceLMatrixAction, dividedDifferenceLMatrix, hi,
    Finset.mem_univ]

theorem dividedDifferenceLMatrixAction_of_gt
    (nodes : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : k < i.val) :
    dividedDifferenceLMatrixAction nodes n k v i =
      (v i - v (dividedDifferenceFinPred i)) /
        (nodes i.val - nodes (i.val - k - 1)) := by
  have hnot : ¬i.val ≤ k := Nat.not_le_of_gt hi
  simp [dividedDifferenceLMatrixAction, dividedDifferenceLMatrix, hnot,
    Finset.sum_add_distrib, Finset.mem_univ, add_mul]
  ring

/-- The finite `L_k` matrix action is exactly the scalar divided-difference
recurrence on indices `0:n`. -/
theorem dividedDifferenceLMatrixAction_eq_step
    (nodes : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    dividedDifferenceLMatrixAction nodes n k v i =
      dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k i.val := by
  by_cases hi : i.val ≤ k
  · rw [dividedDifferenceLMatrixAction_of_le nodes v hi,
      dividedDifferenceStep_of_le nodes (dividedDifferenceFinToNat v) hi]
    simp [dividedDifferenceFinToNat, i.isLt]
  · have hgt : k < i.val := Nat.lt_of_not_ge hi
    rw [dividedDifferenceLMatrixAction_of_gt nodes v hgt,
      dividedDifferenceStep_of_gt nodes (dividedDifferenceFinToNat v) hgt]
    have hpred : i.val - 1 < n + 1 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
    simp [dividedDifferenceFinToNat, dividedDifferenceFinPred, i.isLt, hpred]

/-- Absolute-value action `|L_k| v` for the finite divided-difference matrix. -/
noncomputable def dividedDifferenceAbsLMatrixAction
    (nodes : ℕ → ℝ) (n k : ℕ) (v : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => ∑ j : Fin (n + 1),
    |dividedDifferenceLMatrix nodes n k i j| * v j

theorem dividedDifferenceAbsLMatrixAction_nonneg
    (nodes : ℕ → ℝ) (n k : ℕ) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    ∀ i, 0 ≤ dividedDifferenceAbsLMatrixAction nodes n k v i := by
  intro i
  unfold dividedDifferenceAbsLMatrixAction
  exact Finset.sum_nonneg (fun j _ =>
    mul_nonneg (abs_nonneg _) (hv j))

/-- Componentwise absolute-value domination for one exact `L_k` action:
`|L_k v| <= |L_k| |v|`. -/
theorem abs_dividedDifferenceLMatrixAction_le_absLMatrixAction
    (nodes : ℕ → ℝ) (n k : ℕ) (v : Fin (n + 1) → ℝ) :
    ∀ i : Fin (n + 1),
      |dividedDifferenceLMatrixAction nodes n k v i| ≤
        dividedDifferenceAbsLMatrixAction nodes n k
          (fun j => |v j|) i := by
  intro i
  unfold dividedDifferenceLMatrixAction dividedDifferenceAbsLMatrixAction
  calc
    |∑ j : Fin (n + 1), dividedDifferenceLMatrix nodes n k i j * v j|
        ≤ ∑ j : Fin (n + 1),
            |dividedDifferenceLMatrix nodes n k i j * v j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin (n + 1),
          |dividedDifferenceLMatrix nodes n k i j| * |v j| := by
          apply Finset.sum_congr rfl
          intro j _
          exact abs_mul (dividedDifferenceLMatrix nodes n k i j) (v j)

/-- Monotonicity of the absolute `|L_k|` action. -/
theorem dividedDifferenceAbsLMatrixAction_mono
    (nodes : ℕ → ℝ) (n k : ℕ)
    (v w : Fin (n + 1) → ℝ)
    (hvw : ∀ i, v i ≤ w i) :
    ∀ i, dividedDifferenceAbsLMatrixAction nodes n k v i ≤
      dividedDifferenceAbsLMatrixAction nodes n k w i := by
  intro i
  unfold dividedDifferenceAbsLMatrixAction
  exact Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_left (hvw j) (abs_nonneg _))

/-- Linearity of the absolute `|L_k|` action with respect to subtraction in
the vector argument. -/
theorem dividedDifferenceAbsLMatrixAction_sub
    (nodes : ℕ → ℝ) (n k : ℕ)
    (v w : Fin (n + 1) → ℝ) :
    ∀ i, dividedDifferenceAbsLMatrixAction nodes n k
        (fun j => v j - w j) i =
      dividedDifferenceAbsLMatrixAction nodes n k v i -
        dividedDifferenceAbsLMatrixAction nodes n k w i := by
  intro i
  unfold dividedDifferenceAbsLMatrixAction
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Linearity of the absolute `|L_k|` action with respect to scalar
multiplication in the vector argument. -/
theorem dividedDifferenceAbsLMatrixAction_smul
    (nodes : ℕ → ℝ) (n k : ℕ) (a : ℝ)
    (v : Fin (n + 1) → ℝ) :
    ∀ i, dividedDifferenceAbsLMatrixAction nodes n k
        (fun j => a * v j) i =
      a * dividedDifferenceAbsLMatrixAction nodes n k v i := by
  intro i
  unfold dividedDifferenceAbsLMatrixAction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Componentwise absolute-value domination for the difference of two exact
`L_k` actions. -/
theorem abs_dividedDifferenceLMatrixAction_sub_le_absLMatrixAction
    (nodes : ℕ → ℝ) (n k : ℕ)
    (v w : Fin (n + 1) → ℝ) :
    ∀ i : Fin (n + 1),
      |dividedDifferenceLMatrixAction nodes n k v i -
          dividedDifferenceLMatrixAction nodes n k w i| ≤
        dividedDifferenceAbsLMatrixAction nodes n k
          (fun j => |v j - w j|) i := by
  intro i
  unfold dividedDifferenceLMatrixAction dividedDifferenceAbsLMatrixAction
  have hsum :
      (∑ j : Fin (n + 1),
          dividedDifferenceLMatrix nodes n k i j * v j) -
        (∑ j : Fin (n + 1),
          dividedDifferenceLMatrix nodes n k i j * w j) =
        ∑ j : Fin (n + 1),
          dividedDifferenceLMatrix nodes n k i j * (v j - w j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    |(∑ j : Fin (n + 1),
        dividedDifferenceLMatrix nodes n k i j * v j) -
      (∑ j : Fin (n + 1),
        dividedDifferenceLMatrix nodes n k i j * w j)|
        = |∑ j : Fin (n + 1),
            dividedDifferenceLMatrix nodes n k i j * (v j - w j)| := by
          rw [hsum]
    _ ≤ ∑ j : Fin (n + 1),
          |dividedDifferenceLMatrix nodes n k i j * (v j - w j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin (n + 1),
          |dividedDifferenceLMatrix nodes n k i j| * |v j - w j| := by
        apply Finset.sum_congr rfl
        intro j _
        exact abs_mul (dividedDifferenceLMatrix nodes n k i j) (v j - w j)

/-- Recursive absolute product majorant
`(1+gamma)|L_{m-1}| ... (1+gamma)|L_0| v` for divided differences. -/
noncomputable def dividedDifferenceAbsLProductAction
    (nodes : ℕ → ℝ) (gamma : ℝ) (n : ℕ) :
    ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, v => v
  | k + 1, v => fun i =>
      (1 + gamma) *
        dividedDifferenceAbsLMatrixAction nodes n k
          (dividedDifferenceAbsLProductAction nodes gamma n k v) i

theorem dividedDifferenceAbsLProductAction_nonneg
    (nodes : ℕ → ℝ) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (n m : ℕ) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    ∀ i, 0 ≤ dividedDifferenceAbsLProductAction nodes gamma n m v i := by
  induction m with
  | zero =>
      intro i
      exact hv i
  | succ m ih =>
      intro i
      unfold dividedDifferenceAbsLProductAction
      exact mul_nonneg (by linarith)
        (dividedDifferenceAbsLMatrixAction_nonneg nodes n m
          (dividedDifferenceAbsLProductAction nodes gamma n m v) ih i)

/-- Pull the repeated scalar factor in
`(1+gamma)|L_{m-1}| ... (1+gamma)|L_0| v` to the front. -/
theorem dividedDifferenceAbsLProductAction_const_gamma
    (nodes : ℕ → ℝ) (gamma : ℝ) (n m : ℕ)
    (v : Fin (n + 1) → ℝ) :
    ∀ i, dividedDifferenceAbsLProductAction nodes gamma n m v i =
      (1 + gamma) ^ m *
        dividedDifferenceAbsLProductAction nodes 0 n m v i := by
  induction m with
  | zero =>
      intro i
      simp [dividedDifferenceAbsLProductAction]
  | succ m ih =>
      intro i
      have hih :
          dividedDifferenceAbsLProductAction nodes gamma n m v =
            fun i => (1 + gamma) ^ m *
              dividedDifferenceAbsLProductAction nodes 0 n m v i := by
        funext j
        exact ih j
      calc
        dividedDifferenceAbsLProductAction nodes gamma n (m + 1) v i =
            (1 + gamma) *
              dividedDifferenceAbsLMatrixAction nodes n m
                (dividedDifferenceAbsLProductAction nodes gamma n m v) i := rfl
        _ = (1 + gamma) *
              dividedDifferenceAbsLMatrixAction nodes n m
                (fun j => (1 + gamma) ^ m *
                  dividedDifferenceAbsLProductAction nodes 0 n m v j) i := by
              rw [hih]
        _ = (1 + gamma) *
              ((1 + gamma) ^ m *
                dividedDifferenceAbsLMatrixAction nodes n m
                  (dividedDifferenceAbsLProductAction nodes 0 n m v) i) := by
              rw [dividedDifferenceAbsLMatrixAction_smul]
        _ = (1 + gamma) ^ (m + 1) *
              dividedDifferenceAbsLProductAction nodes 0 n (m + 1) v i := by
              simp [dividedDifferenceAbsLProductAction, pow_succ]
              ring

/-- Exact divided-difference columns `c^(k)` generated by the standard source
recurrence, with `c^(0) = f`. -/
noncomputable def dividedDifferenceCoeffs
    (nodes f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => f
  | k + 1 => dividedDifferenceStep nodes (dividedDifferenceCoeffs nodes f k) k

theorem dividedDifferenceCoeffs_zero
    (nodes f : ℕ → ℝ) :
    dividedDifferenceCoeffs nodes f 0 = f := rfl

theorem dividedDifferenceCoeffs_succ_entry_of_le
    (nodes f : ℕ → ℝ) {k j : ℕ} (hj : j ≤ k) :
    dividedDifferenceCoeffs nodes f (k + 1) j =
      dividedDifferenceCoeffs nodes f k j := by
  simp [dividedDifferenceCoeffs, dividedDifferenceStep_of_le nodes
    (dividedDifferenceCoeffs nodes f k) hj]

theorem dividedDifferenceCoeffs_succ_entry_of_gt
    (nodes f : ℕ → ℝ) {k j : ℕ} (hj : k < j) :
    dividedDifferenceCoeffs nodes f (k + 1) j =
      (dividedDifferenceCoeffs nodes f k j -
          dividedDifferenceCoeffs nodes f k (j - 1)) /
        (nodes j - nodes (j - k - 1)) := by
  simp [dividedDifferenceCoeffs, dividedDifferenceStep_of_gt nodes
    (dividedDifferenceCoeffs nodes f k) hj]

/-- Finite divided-difference coefficient columns `c^(k)` over the source
index set `0:n`.  The successor column is the finite `L_k` action from
Higham (5.9). -/
noncomputable def dividedDifferenceFiniteCoeffs
    (nodes f : ℕ → ℝ) (n : ℕ) : ℕ → Fin (n + 1) → ℝ
  | 0 => fun i => f i.val
  | k + 1 =>
      dividedDifferenceLMatrixAction nodes n k
        (dividedDifferenceFiniteCoeffs nodes f n k)

theorem dividedDifferenceFiniteCoeffs_zero
    (nodes f : ℕ → ℝ) (n : ℕ) :
    dividedDifferenceFiniteCoeffs nodes f n 0 =
      fun i : Fin (n + 1) => f i.val := rfl

theorem dividedDifferenceFiniteCoeffs_succ
    (nodes f : ℕ → ℝ) (n k : ℕ) :
    dividedDifferenceFiniteCoeffs nodes f n (k + 1) =
      dividedDifferenceLMatrixAction nodes n k
        (dividedDifferenceFiniteCoeffs nodes f n k) := rfl

/-- Exact finite product action `L_{m-1} ... L_0 v` for divided differences. -/
noncomputable def dividedDifferenceLProductAction
    (nodes : ℕ → ℝ) (n : ℕ) :
    ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, v => v
  | k + 1, v =>
      dividedDifferenceLMatrixAction nodes n k
        (dividedDifferenceLProductAction nodes n k v)

theorem dividedDifferenceLProductAction_zero
    (nodes : ℕ → ℝ) (n : ℕ) :
    dividedDifferenceLProductAction nodes n 0 =
      fun v : Fin (n + 1) → ℝ => v := rfl

theorem dividedDifferenceLProductAction_succ
    (nodes : ℕ → ℝ) (n k : ℕ) :
    dividedDifferenceLProductAction nodes n (k + 1) =
      fun v : Fin (n + 1) → ℝ =>
        dividedDifferenceLMatrixAction nodes n k
          (dividedDifferenceLProductAction nodes n k v) := rfl

/-- The exact finite divided-difference columns are the product
`L_{m-1} ... L_0 f`. -/
theorem dividedDifferenceFiniteCoeffs_eq_LProductAction
    (nodes f : ℕ → ℝ) (n m : ℕ) :
    ∀ i : Fin (n + 1),
      dividedDifferenceFiniteCoeffs nodes f n m i =
        dividedDifferenceLProductAction nodes n m
          (fun i : Fin (n + 1) => f i.val) i := by
  induction m with
  | zero =>
      intro i
      rfl
  | succ m ih =>
      intro i
      have hprev :
          dividedDifferenceFiniteCoeffs nodes f n m =
            dividedDifferenceLProductAction nodes n m
              (fun i : Fin (n + 1) => f i.val) := by
        funext j
        exact ih j
      rw [dividedDifferenceFiniteCoeffs_succ,
        dividedDifferenceLProductAction_succ, hprev]

/-- Absolute-product majorant for the exact finite divided-difference
columns. -/
theorem dividedDifferenceFiniteCoeffs_abs_le_absLProduct_zero
    (nodes f : ℕ → ℝ) (n m : ℕ) :
    ∀ i : Fin (n + 1),
      |dividedDifferenceFiniteCoeffs nodes f n m i| ≤
        dividedDifferenceAbsLProductAction nodes 0 n m
          (fun i : Fin (n + 1) => |f i.val|) i := by
  induction m with
  | zero =>
      intro i
      rfl
  | succ m ih =>
      intro i
      have habs :=
        abs_dividedDifferenceLMatrixAction_le_absLMatrixAction nodes n m
          (dividedDifferenceFiniteCoeffs nodes f n m) i
      have hmono :=
        dividedDifferenceAbsLMatrixAction_mono nodes n m
          (fun j => |dividedDifferenceFiniteCoeffs nodes f n m j|)
          (dividedDifferenceAbsLProductAction nodes 0 n m
            (fun i : Fin (n + 1) => |f i.val|))
          ih i
      calc
        |dividedDifferenceFiniteCoeffs nodes f n (m + 1) i|
            = |dividedDifferenceLMatrixAction nodes n m
                (dividedDifferenceFiniteCoeffs nodes f n m) i| := rfl
        _ ≤ dividedDifferenceAbsLMatrixAction nodes n m
              (fun j => |dividedDifferenceFiniteCoeffs nodes f n m j|) i := habs
        _ ≤ dividedDifferenceAbsLMatrixAction nodes n m
              (dividedDifferenceAbsLProductAction nodes 0 n m
                (fun i : Fin (n + 1) => |f i.val|)) i := hmono
        _ = dividedDifferenceAbsLProductAction nodes 0 n (m + 1)
              (fun i : Fin (n + 1) => |f i.val|) i := by
              simp [dividedDifferenceAbsLProductAction]

/-- The finite `L_k` coefficient columns agree entrywise with the
natural-number recurrence used for the source scalar divided differences. -/
theorem dividedDifferenceFiniteCoeffs_eq_nat
    (nodes f : ℕ → ℝ) (n k : ℕ) (i : Fin (n + 1)) :
    dividedDifferenceFiniteCoeffs nodes f n k i =
      dividedDifferenceCoeffs nodes f k i.val := by
  induction k generalizing i with
  | zero =>
      rfl
  | succ k ih =>
      by_cases hi : i.val ≤ k
      · rw [dividedDifferenceFiniteCoeffs_succ,
          dividedDifferenceLMatrixAction_of_le nodes
            (dividedDifferenceFiniteCoeffs nodes f n k) hi,
          dividedDifferenceCoeffs_succ_entry_of_le nodes f hi]
        exact ih i
      · have hgt : k < i.val := Nat.lt_of_not_ge hi
        rw [dividedDifferenceFiniteCoeffs_succ,
          dividedDifferenceLMatrixAction_of_gt nodes
            (dividedDifferenceFiniteCoeffs nodes f n k) hgt,
          dividedDifferenceCoeffs_succ_entry_of_gt nodes f hgt,
          ih i, ih (dividedDifferenceFinPred i)]
        simp [dividedDifferenceFinPred]

/-- Diagonal row-scaling action `G_k` from Higham (5.9): rows `0:k` are
unchanged, while later rows are multiplied by a supplied local factor. -/
noncomputable def dividedDifferenceGAction
    (eta : ℕ → ℝ) (k : ℕ) (v : ℕ → ℝ) : ℕ → ℝ :=
  fun j => if j ≤ k then v j else eta j * v j

theorem dividedDifferenceGAction_of_le
    (eta : ℕ → ℝ) (v : ℕ → ℝ) {k j : ℕ} (hj : j ≤ k) :
    dividedDifferenceGAction eta k v j = v j := by
  simp [dividedDifferenceGAction, hj]

theorem dividedDifferenceGAction_of_gt
    (eta : ℕ → ℝ) (v : ℕ → ℝ) {k j : ℕ} (hj : k < j) :
    dividedDifferenceGAction eta k v j = eta j * v j := by
  have hnot : ¬j ≤ k := Nat.not_le_of_gt hj
  simp [dividedDifferenceGAction, hnot]

theorem dividedDifferenceGAction_step_of_gt
    (nodes coeffs eta : ℕ → ℝ) {k j : ℕ} (hj : k < j) :
    dividedDifferenceGAction eta k (dividedDifferenceStep nodes coeffs k) j =
      eta j *
        ((coeffs j - coeffs (j - 1)) /
          (nodes j - nodes (j - k - 1))) := by
  simp [dividedDifferenceGAction_of_gt eta
    (dividedDifferenceStep nodes coeffs k) hj,
    dividedDifferenceStep_of_gt nodes coeffs hj]

/-- Higham (5.9): the finite diagonal `G_k` scaling matrix. -/
noncomputable def dividedDifferenceGMatrix
    (eta : ℕ → ℝ) (n k : ℕ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun i j => if j = i then if i.val ≤ k then 1 else eta i.val else 0

/-- Matrix-vector action of Higham's finite diagonal `G_k`. -/
noncomputable def dividedDifferenceGMatrixAction
    (eta : ℕ → ℝ) (n k : ℕ) (v : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => ∑ j : Fin (n + 1), dividedDifferenceGMatrix eta n k i j * v j

theorem dividedDifferenceGMatrixAction_of_le
    (eta : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : i.val ≤ k) :
    dividedDifferenceGMatrixAction eta n k v i = v i := by
  simp [dividedDifferenceGMatrixAction, dividedDifferenceGMatrix, hi,
    Finset.mem_univ]

theorem dividedDifferenceGMatrixAction_of_gt
    (eta : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : k < i.val) :
    dividedDifferenceGMatrixAction eta n k v i = eta i.val * v i := by
  have hnot : ¬i.val ≤ k := Nat.not_le_of_gt hi
  simp [dividedDifferenceGMatrixAction, dividedDifferenceGMatrix, hnot,
    Finset.mem_univ]

/-- The finite diagonal `G_k` action agrees with the natural-number-indexed
row-scaling action on indices `0:n`. -/
theorem dividedDifferenceGMatrixAction_eq_GAction
    (eta : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    dividedDifferenceGMatrixAction eta n k v i =
      dividedDifferenceGAction eta k (dividedDifferenceFinToNat v) i.val := by
  by_cases hi : i.val ≤ k
  · rw [dividedDifferenceGMatrixAction_of_le eta v hi,
      dividedDifferenceGAction_of_le eta (dividedDifferenceFinToNat v) hi]
    simp [dividedDifferenceFinToNat, i.isLt]
  · have hgt : k < i.val := Nat.lt_of_not_ge hi
    rw [dividedDifferenceGMatrixAction_of_gt eta v hgt,
      dividedDifferenceGAction_of_gt eta (dividedDifferenceFinToNat v) hgt]
    simp [dividedDifferenceFinToNat, i.isLt]

/-- Finite-matrix form of Higham (5.9): applying `G_k L_k` to a finite vector
agrees rowwise with the scalar `G_k` action applied to the exact
divided-difference step. -/
theorem dividedDifferenceGMatrixAction_LMatrixAction_eq
    (eta nodes : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    dividedDifferenceGMatrixAction eta n k
        (dividedDifferenceLMatrixAction nodes n k v) i =
      dividedDifferenceGAction eta k
        (dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k)
        i.val := by
  by_cases hi : i.val ≤ k
  · rw [dividedDifferenceGMatrixAction_of_le eta
      (dividedDifferenceLMatrixAction nodes n k v) hi,
      dividedDifferenceGAction_of_le eta
        (dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k) hi,
      dividedDifferenceLMatrixAction_eq_step nodes v i]
  · have hgt : k < i.val := Nat.lt_of_not_ge hi
    rw [dividedDifferenceGMatrixAction_of_gt eta
      (dividedDifferenceLMatrixAction nodes n k v) hgt,
      dividedDifferenceGAction_of_gt eta
        (dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k) hgt,
      dividedDifferenceLMatrixAction_eq_step nodes v i]

/-- Iterated finite product action
`G_{m-1} L_{m-1} ... G_0 L_0 v` for the divided-difference matrix factors in
Higham (5.10).  The function `eta k` supplies the diagonal entries for `G_k`. -/
noncomputable def dividedDifferenceGLProductAction
    (nodes : ℕ → ℝ) (eta : ℕ → ℕ → ℝ) (n : ℕ) :
    ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, v => v
  | k + 1, v =>
      dividedDifferenceGMatrixAction (eta k) n k
        (dividedDifferenceLMatrixAction nodes n k
          (dividedDifferenceGLProductAction nodes eta n k v))

/-- Rounded primitive divided-difference sweep.  Entries `j <= k` are copied,
and entries `j > k` are computed with one rounded subtraction for the numerator,
one rounded subtraction for the node gap, and one rounded division. -/
noncomputable def fl_dividedDifferenceStep
    (fp : FPModel) (nodes coeffs : ℕ → ℝ) (k : ℕ) : ℕ → ℝ :=
  fun j =>
    if j ≤ k then
      coeffs j
    else
      fp.fl_div
        (fp.fl_sub (coeffs j) (coeffs (j - 1)))
        (fp.fl_sub (nodes j) (nodes (j - k - 1)))

theorem fl_dividedDifferenceStep_of_le
    (fp : FPModel) (nodes coeffs : ℕ → ℝ) {k j : ℕ} (hj : j ≤ k) :
    fl_dividedDifferenceStep fp nodes coeffs k j = coeffs j := by
  simp [fl_dividedDifferenceStep, hj]

/-- Finite rounded divided-difference coefficient columns over `0:n`.  The
successor column applies the rounded primitive sweep to the previous finite
column. -/
noncomputable def fl_dividedDifferenceFiniteCoeffs
    (fp : FPModel) (nodes f : ℕ → ℝ) (n : ℕ) :
    ℕ → Fin (n + 1) → ℝ
  | 0 => fun i => f i.val
  | k + 1 => fun i =>
      fl_dividedDifferenceStep fp nodes
        (dividedDifferenceFinToNat
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)) k i.val

theorem fl_dividedDifferenceFiniteCoeffs_zero
    (fp : FPModel) (nodes f : ℕ → ℝ) (n : ℕ) :
    fl_dividedDifferenceFiniteCoeffs fp nodes f n 0 =
      fun i : Fin (n + 1) => f i.val := rfl

theorem fl_dividedDifferenceFiniteCoeffs_succ
    (fp : FPModel) (nodes f : ℕ → ℝ) (n k : ℕ) :
    fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) =
      fun i : Fin (n + 1) =>
        fl_dividedDifferenceStep fp nodes
          (dividedDifferenceFinToNat
            (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)) k i.val := rfl

/-- Finite rounded matrix adapter for Higham (5.9): if the active rows of the
rounded divided-difference sweep are supplied as multiplicative perturbations
of the exact scalar row update, then the finite rounded sweep is the rowwise
`G_k L_k` matrix action. -/
theorem fl_dividedDifferenceStep_eq_GMatrixAction_of_row_factors
    (fp : FPModel) (nodes : ℕ → ℝ) {n k : ℕ}
    (v : Fin (n + 1) → ℝ) (eta : ℕ → ℝ)
    (hrow : ∀ i : Fin (n + 1), k < i.val →
      fl_dividedDifferenceStep fp nodes (dividedDifferenceFinToNat v) k i.val =
        eta i.val *
          dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k i.val) :
    ∀ i : Fin (n + 1),
      fl_dividedDifferenceStep fp nodes (dividedDifferenceFinToNat v) k i.val =
        dividedDifferenceGMatrixAction eta n k
          (dividedDifferenceLMatrixAction nodes n k v) i := by
  intro i
  by_cases hi : i.val ≤ k
  · rw [fl_dividedDifferenceStep_of_le fp nodes
      (dividedDifferenceFinToNat v) hi,
      dividedDifferenceGMatrixAction_of_le eta
        (dividedDifferenceLMatrixAction nodes n k v) hi,
      dividedDifferenceLMatrixAction_eq_step nodes v i,
      dividedDifferenceStep_of_le nodes (dividedDifferenceFinToNat v) hi]
  · have hgt : k < i.val := Nat.lt_of_not_ge hi
    rw [hrow i hgt,
      dividedDifferenceGMatrixAction_of_gt eta
        (dividedDifferenceLMatrixAction nodes n k v) hgt,
      dividedDifferenceLMatrixAction_eq_step nodes v i]

/-- Scalar row version of Higham (5.9): one rounded divided-difference entry
is the exact `L_k` row update multiplied by the local error factors from the
two subtractions and the division.  The denominator of the rounded division is
kept as an explicit nonzero hypothesis, matching `FPModel.model_div`. -/
theorem fl_dividedDifferenceStep_entry_error_factors
    (fp : FPModel) (nodes coeffs : ℕ → ℝ) {k j : ℕ}
    (hj : k < j)
    (hden : nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat :
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0) :
    ∃ δnum δden δdiv : ℝ,
      |δnum| ≤ fp.u ∧ |δden| ≤ fp.u ∧ |δdiv| ≤ fp.u ∧
        fl_dividedDifferenceStep fp nodes coeffs k j =
          dividedDifferenceStep nodes coeffs k j *
            ((1 + δnum) / (1 + δden)) * (1 + δdiv) := by
  obtain ⟨δnum, hδnum, hnum⟩ :=
    fp.model_sub (coeffs j) (coeffs (j - 1))
  obtain ⟨δden, hδden, hdenEq⟩ :=
    fp.model_sub (nodes j) (nodes (j - k - 1))
  obtain ⟨δdiv, hδdiv, hdiv⟩ :=
    fp.model_div
      (fp.fl_sub (coeffs j) (coeffs (j - 1)))
      (fp.fl_sub (nodes j) (nodes (j - k - 1))) hdenHat
  refine ⟨δnum, δden, δdiv, hδnum, hδden, hδdiv, ?_⟩
  set num := coeffs j - coeffs (j - 1)
  set den := nodes j - nodes (j - k - 1)
  have hden' : den ≠ 0 := by
    simpa [den] using hden
  have hdenProduct : den * (1 + δden) ≠ 0 := by
    intro hzero
    apply hdenHat
    rw [hdenEq]
    simpa [den] using hzero
  have hdenFactor : 1 + δden ≠ 0 :=
    (mul_ne_zero_iff.mp hdenProduct).2
  have halg :
      ((num * (1 + δnum)) / (den * (1 + δden))) *
          (1 + δdiv) =
        (num / den) * ((1 + δnum) / (1 + δden)) *
          (1 + δdiv) := by
    field_simp [hden', hdenFactor]
  calc
    fl_dividedDifferenceStep fp nodes coeffs k j
        = fp.fl_div
            (fp.fl_sub (coeffs j) (coeffs (j - 1)))
            (fp.fl_sub (nodes j) (nodes (j - k - 1))) := by
          simp [fl_dividedDifferenceStep, Nat.not_le_of_gt hj]
    _ = ((num * (1 + δnum)) / (den * (1 + δden))) *
          (1 + δdiv) := by
          rw [hdiv, hnum, hdenEq]
    _ = (num / den) * ((1 + δnum) / (1 + δden)) *
          (1 + δdiv) := halg
    _ = dividedDifferenceStep nodes coeffs k j *
          ((1 + δnum) / (1 + δden)) * (1 + δdiv) := by
          rw [dividedDifferenceStep_of_gt nodes coeffs hj]

/-- Gamma-three version of the scalar row bridge for Higham (5.9).  The
denominator subtraction appears inverted in the exact algebra; the existing
signed product-error lemma packages the two subtraction errors and final
division error into one `theta_3`. -/
theorem fl_dividedDifferenceStep_entry_gamma3
    (fp : FPModel) (nodes coeffs : ℕ → ℝ) {k j : ℕ}
    (hj : k < j)
    (hden : nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat :
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp 3 ∧
        fl_dividedDifferenceStep fp nodes coeffs k j =
          dividedDifferenceStep nodes coeffs k j * (1 + θ) := by
  rcases fl_dividedDifferenceStep_entry_error_factors
      fp nodes coeffs hj hden hdenHat with
    ⟨δnum, δden, δdiv, hδnum, hδden, hδdiv, hstep⟩
  let δ : Fin 3 → ℝ := fun i =>
    if i = 0 then δnum else if i = 1 then δden else δdiv
  let neg : Fin 3 → Bool := fun i => if i = 1 then true else false
  have hδ : ∀ i : Fin 3, |δ i| ≤ fp.u := by
    intro i
    fin_cases i <;> simp [δ, hδnum, hδden, hδdiv]
  rcases prod_signed_error_bound fp 3 δ neg hδ hγ with
    ⟨θ, hθ, hprod⟩
  refine ⟨θ, hθ, ?_⟩
  have hprodEval :
      (∏ i : Fin 3,
          if neg i = true then 1 / (1 + δ i) else 1 + δ i) =
        (1 + δnum) * (1 / (1 + δden)) * (1 + δdiv) := by
    rw [Fin.prod_univ_three]
    simp [δ, neg]
  have hfactor :
      ((1 + δnum) / (1 + δden)) * (1 + δdiv) = 1 + θ := by
    calc
      ((1 + δnum) / (1 + δden)) * (1 + δdiv)
          = (1 + δnum) * (1 / (1 + δden)) * (1 + δdiv) := by
            simp [div_eq_mul_inv]
      _ = 1 + θ := by
            rw [← hprod, hprodEval]
  calc
    fl_dividedDifferenceStep fp nodes coeffs k j
        = dividedDifferenceStep nodes coeffs k j *
            (((1 + δnum) / (1 + δden)) * (1 + δdiv)) := by
          rw [hstep]
          ring
    _ = dividedDifferenceStep nodes coeffs k j * (1 + θ) := by
          rw [hfactor]

/-- Finite `gamma_3` adapter for Higham (5.9): under the active-row
nonzero-denominator hypotheses, the rounded finite divided-difference sweep is
represented rowwise by a finite `G_k L_k` action whose active diagonal factors
are all within `gamma fp 3` of one. -/
theorem fl_dividedDifferenceStep_exists_GMatrixAction_gamma3
    (fp : FPModel) (nodes : ℕ → ℝ) {n k : ℕ}
    (v : Fin (n + 1) → ℝ)
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ eta : ℕ → ℝ,
      (∀ i : Fin (n + 1), k < i.val →
        |eta i.val - 1| ≤ gamma fp 3) ∧
      ∀ i : Fin (n + 1),
        fl_dividedDifferenceStep fp nodes
            (dividedDifferenceFinToNat v) k i.val =
          dividedDifferenceGMatrixAction eta n k
            (dividedDifferenceLMatrixAction nodes n k v) i := by
  classical
  let theta : ℕ → ℝ := fun j =>
    if hjk : k < j then
      if hjn : j < n + 1 then
        Classical.choose
          (fl_dividedDifferenceStep_entry_gamma3 fp nodes
            (dividedDifferenceFinToNat v) hjk
            (hden j hjk hjn) (hdenHat j hjk hjn) hγ)
      else
        0
    else
      0
  let eta : ℕ → ℝ := fun j => 1 + theta j
  refine ⟨eta, ?_, ?_⟩
  · intro i hi
    have hspec := Classical.choose_spec
      (fl_dividedDifferenceStep_entry_gamma3 fp nodes
        (dividedDifferenceFinToNat v) hi
        (hden i.val hi i.isLt) (hdenHat i.val hi i.isLt) hγ)
    have htheta :
        theta i.val =
          Classical.choose
            (fl_dividedDifferenceStep_entry_gamma3 fp nodes
              (dividedDifferenceFinToNat v) hi
              (hden i.val hi i.isLt) (hdenHat i.val hi i.isLt) hγ) := by
      have hile : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
      simp [theta, hi, hile]
    have hetaDiff : eta i.val - 1 = theta i.val := by
      simp [eta]
    rw [hetaDiff, htheta]
    exact hspec.1
  · apply fl_dividedDifferenceStep_eq_GMatrixAction_of_row_factors
    intro i hi
    have hspec := Classical.choose_spec
      (fl_dividedDifferenceStep_entry_gamma3 fp nodes
        (dividedDifferenceFinToNat v) hi
        (hden i.val hi i.isLt) (hdenHat i.val hi i.isLt) hγ)
    have htheta :
        theta i.val =
          Classical.choose
            (fl_dividedDifferenceStep_entry_gamma3 fp nodes
              (dividedDifferenceFinToNat v) hi
              (hden i.val hi i.isLt) (hdenHat i.val hi i.isLt) hγ) := by
      have hile : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
      simp [theta, hi, hile]
    have heta :
        eta i.val =
          1 +
            Classical.choose
              (fl_dividedDifferenceStep_entry_gamma3 fp nodes
                (dividedDifferenceFinToNat v) hi
                (hden i.val hi i.isLt) (hdenHat i.val hi i.isLt) hγ) := by
      simp [eta, htheta]
    calc
      fl_dividedDifferenceStep fp nodes
          (dividedDifferenceFinToNat v) k i.val =
        dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k i.val *
          (1 +
            Classical.choose
              (fl_dividedDifferenceStep_entry_gamma3 fp nodes
                (dividedDifferenceFinToNat v) hi
                (hden i.val hi i.isLt) (hdenHat i.val hi i.isLt) hγ)) := hspec.2
      _ = eta i.val *
          dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k i.val := by
            rw [heta]
            ring

/-- Componentwise finite-row error consequence of the `gamma_3` divided
difference model.  This is the rowwise absolute-error bridge used before
assembling the product/residual bounds (5.10)-(5.12). -/
theorem fl_dividedDifferenceStep_finite_abs_error_gamma3
    (fp : FPModel) (nodes : ℕ → ℝ) {n k : ℕ}
    (v : Fin (n + 1) → ℝ)
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceStep fp nodes
          (dividedDifferenceFinToNat v) k i.val -
        dividedDifferenceLMatrixAction nodes n k v i| ≤
        gamma fp 3 *
          |dividedDifferenceLMatrixAction nodes n k v i| := by
  intro i
  by_cases hi : i.val ≤ k
  · rw [fl_dividedDifferenceStep_of_le fp nodes
      (dividedDifferenceFinToNat v) hi,
      dividedDifferenceLMatrixAction_of_le nodes v hi]
    simp [dividedDifferenceFinToNat, i.isLt,
      mul_nonneg (gamma_nonneg fp hγ) (abs_nonneg (v i))]
  · have hgt : k < i.val := Nat.lt_of_not_ge hi
    rcases fl_dividedDifferenceStep_entry_gamma3 fp nodes
        (dividedDifferenceFinToNat v) hgt
        (hden i.val hgt i.isLt) (hdenHat i.val hgt i.isLt) hγ with
      ⟨θ, hθ, hfl⟩
    rw [dividedDifferenceLMatrixAction_eq_step nodes v i, hfl]
    set exactRow :=
      dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k i.val
    have hdiff : exactRow * (1 + θ) - exactRow = exactRow * θ := by
      ring
    calc
      |exactRow * (1 + θ) - exactRow|
          = |exactRow * θ| := by rw [hdiff]
      _ = |exactRow| * |θ| := abs_mul exactRow θ
      _ ≤ |exactRow| * gamma fp 3 :=
            mul_le_mul_of_nonneg_left hθ (abs_nonneg exactRow)
      _ = gamma fp 3 * |exactRow| := by ring

/-- One-sweep magnitude consequence of the finite `gamma_3` divided-difference
model.  This packages the local row factors in the `|computed| <=
(1+gamma_3)|exact L_k row|` form used by product-style bounds. -/
theorem fl_dividedDifferenceStep_finite_abs_le_one_plus_gamma3
    (fp : FPModel) (nodes : ℕ → ℝ) {n k : ℕ}
    (v : Fin (n + 1) → ℝ)
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceStep fp nodes
          (dividedDifferenceFinToNat v) k i.val| ≤
        (1 + gamma fp 3) *
          |dividedDifferenceLMatrixAction nodes n k v i| := by
  intro i
  by_cases hi : i.val ≤ k
  · rw [fl_dividedDifferenceStep_of_le fp nodes
      (dividedDifferenceFinToNat v) hi,
      dividedDifferenceLMatrixAction_of_le nodes v hi]
    simp [dividedDifferenceFinToNat, i.isLt]
    have hcoef : (1 : ℝ) ≤ 1 + gamma fp 3 := by
      linarith [gamma_nonneg fp hγ]
    calc
      |v i| = (1 : ℝ) * |v i| := by ring
      _ ≤ (1 + gamma fp 3) * |v i| :=
            mul_le_mul_of_nonneg_right hcoef (abs_nonneg (v i))
  · have hgt : k < i.val := Nat.lt_of_not_ge hi
    rcases fl_dividedDifferenceStep_entry_gamma3 fp nodes
        (dividedDifferenceFinToNat v) hgt
        (hden i.val hgt i.isLt) (hdenHat i.val hgt i.isLt) hγ with
      ⟨θ, hθ, hfl⟩
    rw [dividedDifferenceLMatrixAction_eq_step nodes v i, hfl]
    set exactRow :=
      dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k i.val
    have htheta :
        |1 + θ| ≤ 1 + gamma fp 3 := by
      calc
        |1 + θ| ≤ |(1 : ℝ)| + |θ| := abs_add_le 1 θ
        _ ≤ 1 + gamma fp 3 := by
              simpa using add_le_add_left hθ (1 : ℝ)
    calc
      |exactRow * (1 + θ)| = |exactRow| * |1 + θ| :=
        abs_mul exactRow (1 + θ)
      _ ≤ |exactRow| * (1 + gamma fp 3) :=
            mul_le_mul_of_nonneg_left htheta (abs_nonneg exactRow)
      _ = (1 + gamma fp 3) * |exactRow| := by ring

/-- Rounded finite-column form of Higham (5.9): the computed successor column
is a finite `G_k L_k` action on the previous computed column, with active
diagonal factors within `gamma fp 3` of one. -/
theorem fl_dividedDifferenceFiniteCoeffs_succ_exists_GMatrixAction_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n k : ℕ}
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ eta : ℕ → ℝ,
      (∀ i : Fin (n + 1), k < i.val →
        |eta i.val - 1| ≤ gamma fp 3) ∧
      ∀ i : Fin (n + 1),
        fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i =
          dividedDifferenceGMatrixAction eta n k
            (dividedDifferenceLMatrixAction nodes n k
              (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)) i := by
  simpa [fl_dividedDifferenceFiniteCoeffs] using
    (fl_dividedDifferenceStep_exists_GMatrixAction_gamma3 fp nodes
      (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)
      hden hdenHat hγ)

/-- Componentwise one-step error for the rounded finite divided-difference
coefficient columns. -/
theorem fl_dividedDifferenceFiniteCoeffs_succ_abs_error_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n k : ℕ}
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i -
        dividedDifferenceLMatrixAction nodes n k
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n k) i| ≤
        gamma fp 3 *
          |dividedDifferenceLMatrixAction nodes n k
            (fl_dividedDifferenceFiniteCoeffs fp nodes f n k) i| := by
  simpa [fl_dividedDifferenceFiniteCoeffs] using
    (fl_dividedDifferenceStep_finite_abs_error_gamma3 fp nodes
      (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)
      hden hdenHat hγ)

/-- One-step magnitude bound for the rounded finite divided-difference
coefficient columns. -/
theorem fl_dividedDifferenceFiniteCoeffs_succ_abs_le_one_plus_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n k : ℕ}
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i| ≤
        (1 + gamma fp 3) *
          |dividedDifferenceLMatrixAction nodes n k
            (fl_dividedDifferenceFiniteCoeffs fp nodes f n k) i| := by
  simpa [fl_dividedDifferenceFiniteCoeffs] using
    (fl_dividedDifferenceStep_finite_abs_le_one_plus_gamma3 fp nodes
      (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)
      hden hdenHat hγ)

/-- Absolute-matrix one-step majorant for the rounded finite divided-difference
coefficient columns: `|computed c^(k+1)| <= (1+gamma_3)|L_k| |computed c^k|`. -/
theorem fl_dividedDifferenceFiniteCoeffs_succ_abs_le_absL_one_plus_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n k : ℕ}
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i| ≤
        (1 + gamma fp 3) *
          dividedDifferenceAbsLMatrixAction nodes n k
            (fun j => |fl_dividedDifferenceFiniteCoeffs fp nodes f n k j|) i := by
  intro i
  have hstep :=
    fl_dividedDifferenceFiniteCoeffs_succ_abs_le_one_plus_gamma3
      fp nodes f hden hdenHat hγ i
  have habs :=
    abs_dividedDifferenceLMatrixAction_le_absLMatrixAction nodes n k
      (fl_dividedDifferenceFiniteCoeffs fp nodes f n k) i
  have hscale_nonneg : 0 ≤ 1 + gamma fp 3 := by
    linarith [gamma_nonneg fp hγ]
  calc
    |fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i|
        ≤ (1 + gamma fp 3) *
          |dividedDifferenceLMatrixAction nodes n k
            (fl_dividedDifferenceFiniteCoeffs fp nodes f n k) i| := hstep
    _ ≤ (1 + gamma fp 3) *
          dividedDifferenceAbsLMatrixAction nodes n k
            (fun j => |fl_dividedDifferenceFiniteCoeffs fp nodes f n k j|) i :=
          mul_le_mul_of_nonneg_left habs hscale_nonneg

/-- Multi-step absolute product majorant for the rounded finite
divided-difference coefficient columns. -/
theorem fl_dividedDifferenceFiniteCoeffs_abs_le_absLProduct_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n : ℕ} (m : ℕ)
    (hden : ∀ k j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ k j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n m i| ≤
        dividedDifferenceAbsLProductAction nodes (gamma fp 3) n m
          (fun i : Fin (n + 1) => |f i.val|) i := by
  induction m with
  | zero =>
      intro i
      rfl
  | succ m ih =>
      intro i
      have hstep :=
        fl_dividedDifferenceFiniteCoeffs_succ_abs_le_absL_one_plus_gamma3
          fp nodes f
          (fun j hjk hjn => hden m j hjk hjn)
          (fun j hjk hjn => hdenHat m j hjk hjn)
          hγ i
      have hmono :=
        dividedDifferenceAbsLMatrixAction_mono nodes n m
          (fun j => |fl_dividedDifferenceFiniteCoeffs fp nodes f n m j|)
          (dividedDifferenceAbsLProductAction nodes (gamma fp 3) n m
            (fun i : Fin (n + 1) => |f i.val|))
          ih i
      have hscale_nonneg : 0 ≤ 1 + gamma fp 3 := by
        linarith [gamma_nonneg fp hγ]
      calc
        |fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i|
            ≤ (1 + gamma fp 3) *
              dividedDifferenceAbsLMatrixAction nodes n m
                (fun j => |fl_dividedDifferenceFiniteCoeffs fp nodes f n m j|)
                i := hstep
        _ ≤ (1 + gamma fp 3) *
              dividedDifferenceAbsLMatrixAction nodes n m
                (dividedDifferenceAbsLProductAction nodes (gamma fp 3) n m
                  (fun i : Fin (n + 1) => |f i.val|)) i :=
              mul_le_mul_of_nonneg_left hmono hscale_nonneg
        _ = dividedDifferenceAbsLProductAction nodes (gamma fp 3) n (m + 1)
              (fun i : Fin (n + 1) => |f i.val|) i := rfl

/-- Componentwise product perturbation bound for computed divided-difference
columns.  This is the finite-vector form of Higham (5.10)-(5.11): the
computed column differs from the exact `L_{m-1} ... L_0 f` column by the gap
between the rounded absolute product majorant and the exact absolute product
majorant. -/
theorem fl_dividedDifferenceFiniteCoeffs_abs_sub_exact_le_absLProduct_gap_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n : ℕ} (m : ℕ)
    (hden : ∀ k j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ k j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n m i -
        dividedDifferenceFiniteCoeffs nodes f n m i| ≤
        dividedDifferenceAbsLProductAction nodes (gamma fp 3) n m
          (fun i : Fin (n + 1) => |f i.val|) i -
          dividedDifferenceAbsLProductAction nodes 0 n m
            (fun i : Fin (n + 1) => |f i.val|) i := by
  induction m with
  | zero =>
      intro i
      simp [fl_dividedDifferenceFiniteCoeffs, dividedDifferenceFiniteCoeffs,
        dividedDifferenceAbsLProductAction]
  | succ m ih =>
      intro i
      let γ := gamma fp 3
      let flm : Fin (n + 1) → ℝ :=
        fl_dividedDifferenceFiniteCoeffs fp nodes f n m
      let exactm : Fin (n + 1) → ℝ :=
        dividedDifferenceFiniteCoeffs nodes f n m
      let pg : Fin (n + 1) → ℝ :=
        dividedDifferenceAbsLProductAction nodes γ n m
          (fun i : Fin (n + 1) => |f i.val|)
      let p0 : Fin (n + 1) → ℝ :=
        dividedDifferenceAbsLProductAction nodes 0 n m
          (fun i : Fin (n + 1) => |f i.val|)
      have hγ_nonneg : 0 ≤ γ := by
        exact gamma_nonneg fp hγ
      have hlocal :=
        fl_dividedDifferenceFiniteCoeffs_succ_abs_error_gamma3
          fp nodes f
          (fun j hjk hjn => hden m j hjk hjn)
          (fun j hjk hjn => hdenHat m j hjk hjn)
          hγ i
      have hrowabs :=
        abs_dividedDifferenceLMatrixAction_le_absLMatrixAction nodes n m
          flm i
      have hflabs :
          ∀ j : Fin (n + 1), |flm j| ≤ pg j := by
        intro j
        exact
          fl_dividedDifferenceFiniteCoeffs_abs_le_absLProduct_gamma3
            fp nodes f m hden hdenHat hγ j
      have hflmono :=
        dividedDifferenceAbsLMatrixAction_mono nodes n m
          (fun j => |flm j|) pg hflabs i
      have hlocal_pg :
          |fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
            dividedDifferenceLMatrixAction nodes n m flm i| ≤
            γ * dividedDifferenceAbsLMatrixAction nodes n m pg i := by
        calc
          |fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
            dividedDifferenceLMatrixAction nodes n m flm i|
              ≤ γ * |dividedDifferenceLMatrixAction nodes n m flm i| := by
                simpa [γ, flm] using hlocal
          _ ≤ γ *
              dividedDifferenceAbsLMatrixAction nodes n m
                (fun j => |flm j|) i :=
                mul_le_mul_of_nonneg_left hrowabs hγ_nonneg
          _ ≤ γ * dividedDifferenceAbsLMatrixAction nodes n m pg i :=
                mul_le_mul_of_nonneg_left hflmono hγ_nonneg
      have hprop0 :=
        abs_dividedDifferenceLMatrixAction_sub_le_absLMatrixAction nodes n m
          flm exactm i
      have hgap_prev :
          ∀ j : Fin (n + 1), |flm j - exactm j| ≤ pg j - p0 j := by
        intro j
        simpa [flm, exactm, pg, p0, γ] using ih j
      have hpropmono :=
        dividedDifferenceAbsLMatrixAction_mono nodes n m
          (fun j => |flm j - exactm j|)
          (fun j => pg j - p0 j) hgap_prev i
      have hprop_gap :
          |dividedDifferenceLMatrixAction nodes n m flm i -
            dividedDifferenceLMatrixAction nodes n m exactm i| ≤
            dividedDifferenceAbsLMatrixAction nodes n m
              (fun j => pg j - p0 j) i := by
        exact le_trans hprop0 hpropmono
      have htri :
          |fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
            dividedDifferenceFiniteCoeffs nodes f n (m + 1) i| ≤
            |fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
              dividedDifferenceLMatrixAction nodes n m flm i| +
            |dividedDifferenceLMatrixAction nodes n m flm i -
              dividedDifferenceLMatrixAction nodes n m exactm i| := by
        have hsplit :
            fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
              dividedDifferenceFiniteCoeffs nodes f n (m + 1) i =
            (fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
              dividedDifferenceLMatrixAction nodes n m flm i) +
            (dividedDifferenceLMatrixAction nodes n m flm i -
              dividedDifferenceLMatrixAction nodes n m exactm i) := by
          simp [exactm, dividedDifferenceFiniteCoeffs_succ]
        rw [hsplit]
        exact abs_add_le _ _
      have hAbsSub :
          dividedDifferenceAbsLMatrixAction nodes n m
            (fun j => pg j - p0 j) i =
          dividedDifferenceAbsLMatrixAction nodes n m pg i -
            dividedDifferenceAbsLMatrixAction nodes n m p0 i :=
        dividedDifferenceAbsLMatrixAction_sub nodes n m pg p0 i
      calc
        |fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
          dividedDifferenceFiniteCoeffs nodes f n (m + 1) i|
            ≤
            |fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
              dividedDifferenceLMatrixAction nodes n m flm i| +
            |dividedDifferenceLMatrixAction nodes n m flm i -
              dividedDifferenceLMatrixAction nodes n m exactm i| := htri
        _ ≤ γ * dividedDifferenceAbsLMatrixAction nodes n m pg i +
            dividedDifferenceAbsLMatrixAction nodes n m
              (fun j => pg j - p0 j) i :=
              add_le_add hlocal_pg hprop_gap
        _ = dividedDifferenceAbsLProductAction nodes (gamma fp 3) n (m + 1)
              (fun i : Fin (n + 1) => |f i.val|) i -
            dividedDifferenceAbsLProductAction nodes 0 n (m + 1)
              (fun i : Fin (n + 1) => |f i.val|) i := by
              simp [dividedDifferenceAbsLProductAction, pg, p0, γ, hAbsSub]
              ring

/-- Source-shaped scalar form of the divided-difference product perturbation
bound.  Since the same `gamma_3` factor is used at every step, the absolute
product gap equals `((1+gamma_3)^m - 1) |L_{m-1}| ... |L_0| |f|`. -/
theorem fl_dividedDifferenceFiniteCoeffs_abs_sub_exact_le_scalar_absLProduct_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n : ℕ} (m : ℕ)
    (hden : ∀ k j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ k j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n m i -
        dividedDifferenceFiniteCoeffs nodes f n m i| ≤
        ((1 + gamma fp 3) ^ m - 1) *
          dividedDifferenceAbsLProductAction nodes 0 n m
            (fun i : Fin (n + 1) => |f i.val|) i := by
  intro i
  have hgap :=
    fl_dividedDifferenceFiniteCoeffs_abs_sub_exact_le_absLProduct_gap_gamma3
      fp nodes f m hden hdenHat hγ i
  have hconst :=
    dividedDifferenceAbsLProductAction_const_gamma nodes (gamma fp 3) n m
      (fun i : Fin (n + 1) => |f i.val|) i
  calc
    |fl_dividedDifferenceFiniteCoeffs fp nodes f n m i -
      dividedDifferenceFiniteCoeffs nodes f n m i|
        ≤ dividedDifferenceAbsLProductAction nodes (gamma fp 3) n m
            (fun i : Fin (n + 1) => |f i.val|) i -
          dividedDifferenceAbsLProductAction nodes 0 n m
            (fun i : Fin (n + 1) => |f i.val|) i := hgap
    _ = ((1 + gamma fp 3) ^ m - 1) *
          dividedDifferenceAbsLProductAction nodes 0 n m
            (fun i : Fin (n + 1) => |f i.val|) i := by
          rw [hconst]
          ring

/-- Natural-index helper for the inverse of Higham's divided-difference
matrix `L_k`. Rows `0:k` are copied; later rows reconstruct by the recurrence
`z_j = z_{j-1} + (alpha_j - alpha_{j-k-1}) w_j`. -/
noncomputable def dividedDifferenceLInvActionNat
    (nodes : ℕ → ℝ) (k : ℕ) (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => w 0
  | j + 1 =>
      if j + 1 ≤ k then
        w (j + 1)
      else
        dividedDifferenceLInvActionNat nodes k w j +
          (nodes (j + 1) - nodes (j + 1 - k - 1)) * w (j + 1)

/-- Finite inverse action `L_k^{-1}` for the divided-difference matrix. -/
noncomputable def dividedDifferenceLInvAction
    (nodes : ℕ → ℝ) (n k : ℕ) (w : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i =>
    dividedDifferenceLInvActionNat nodes k (dividedDifferenceFinToNat w) i.val

/-- Natural-index helper for the absolute inverse action `|L_k^{-1}|`. -/
noncomputable def dividedDifferenceAbsLInvActionNat
    (nodes : ℕ → ℝ) (k : ℕ) (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => w 0
  | j + 1 =>
      if j + 1 ≤ k then
        w (j + 1)
      else
        dividedDifferenceAbsLInvActionNat nodes k w j +
          |nodes (j + 1) - nodes (j + 1 - k - 1)| * w (j + 1)

/-- Absolute majorant action `|L_k^{-1}| v`. -/
noncomputable def dividedDifferenceAbsLInvAction
    (nodes : ℕ → ℝ) (n k : ℕ) (w : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i =>
    dividedDifferenceAbsLInvActionNat nodes k (dividedDifferenceFinToNat w) i.val

theorem dividedDifferenceLInvAction_of_le
    (nodes : ℕ → ℝ) {n k : ℕ} (w : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : i.val ≤ k) :
    dividedDifferenceLInvAction nodes n k w i = w i := by
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simp [dividedDifferenceLInvAction, dividedDifferenceLInvActionNat,
        dividedDifferenceFinToNat, hi_lt]
  | succ i _ =>
      simp [dividedDifferenceLInvAction, dividedDifferenceLInvActionNat, hi,
        dividedDifferenceFinToNat, hi_lt]

theorem dividedDifferenceLInvAction_of_gt
    (nodes : ℕ → ℝ) {n k : ℕ} (w : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : k < i.val) :
    dividedDifferenceLInvAction nodes n k w i =
      dividedDifferenceLInvAction nodes n k w (dividedDifferenceFinPred i) +
        (nodes i.val - nodes (i.val - k - 1)) * w i := by
  rcases i with ⟨i, hi_lt⟩
  cases i with
  | zero =>
      exact (Nat.not_lt_zero k hi).elim
  | succ i =>
      have hnot : ¬ i + 1 ≤ k := Nat.not_le_of_gt hi
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      have hi_lt_n : i < n := Nat.succ_lt_succ_iff.mp hi_lt
      simp [dividedDifferenceLInvAction, dividedDifferenceLInvActionNat, hnot,
        dividedDifferenceFinToNat, dividedDifferenceFinPred, hi_lt_n]

theorem dividedDifferenceAbsLInvAction_of_le
    (nodes : ℕ → ℝ) {n k : ℕ} (w : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : i.val ≤ k) :
    dividedDifferenceAbsLInvAction nodes n k w i = w i := by
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
        dividedDifferenceFinToNat, hi_lt]
  | succ i _ =>
      simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
        hi, dividedDifferenceFinToNat, hi_lt]

theorem dividedDifferenceAbsLInvAction_of_gt
    (nodes : ℕ → ℝ) {n k : ℕ} (w : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : k < i.val) :
    dividedDifferenceAbsLInvAction nodes n k w i =
      dividedDifferenceAbsLInvAction nodes n k w (dividedDifferenceFinPred i) +
        |nodes i.val - nodes (i.val - k - 1)| * w i := by
  rcases i with ⟨i, hi_lt⟩
  cases i with
  | zero =>
      exact (Nat.not_lt_zero k hi).elim
  | succ i =>
      have hnot : ¬ i + 1 ≤ k := Nat.not_le_of_gt hi
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      have hi_lt_n : i < n := Nat.succ_lt_succ_iff.mp hi_lt
      simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
        hnot, dividedDifferenceFinToNat, dividedDifferenceFinPred, hi_lt_n]

/-- Componentwise absolute-value domination for one exact inverse action:
`|L_k^{-1} v| <= |L_k^{-1}| |v|`. -/
theorem abs_dividedDifferenceLInvAction_le_absLInvAction
    (nodes : ℕ → ℝ) (n k : ℕ) (v : Fin (n + 1) → ℝ) :
    ∀ i : Fin (n + 1),
      |dividedDifferenceLInvAction nodes n k v i| ≤
        dividedDifferenceAbsLInvAction nodes n k
          (fun j => |v j|) i := by
  intro i
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simp [dividedDifferenceLInvAction, dividedDifferenceAbsLInvAction,
        dividedDifferenceLInvActionNat, dividedDifferenceAbsLInvActionNat,
        dividedDifferenceFinToNat, hi_lt]
  | succ i ih =>
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      by_cases hle : i + 1 ≤ k
      · simp [dividedDifferenceLInvAction, dividedDifferenceAbsLInvAction,
          dividedDifferenceLInvActionNat, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt]
      · have hstep :
            |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i| ≤
              dividedDifferenceAbsLInvActionNat nodes k
                (dividedDifferenceFinToNat
                  (fun j : Fin (n + 1) => |v j|)) i := by
          simpa [dividedDifferenceLInvAction, dividedDifferenceAbsLInvAction]
            using ih hpred_lt
        have hmul :
            |(nodes (i + 1) - nodes (i + 1 - k - 1)) *
                dividedDifferenceFinToNat v (i + 1)| =
              |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                |dividedDifferenceFinToNat v (i + 1)| := by
          rw [abs_mul]
        calc
          |dividedDifferenceLInvAction nodes n k v ⟨i + 1, hi_lt⟩|
              =
              |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i +
                (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                  dividedDifferenceFinToNat v (i + 1)| := by
                simp [dividedDifferenceLInvAction, dividedDifferenceLInvActionNat,
                  hle]
          _ ≤
              |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i| +
              |(nodes (i + 1) - nodes (i + 1 - k - 1)) *
                dividedDifferenceFinToNat v (i + 1)| :=
                abs_add_le _ _
          _ =
              |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i| +
              |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                |dividedDifferenceFinToNat v (i + 1)| := by rw [hmul]
          _ ≤
              dividedDifferenceAbsLInvActionNat nodes k
                (dividedDifferenceFinToNat
                  (fun j : Fin (n + 1) => |v j|)) i +
              |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                |dividedDifferenceFinToNat v (i + 1)| :=
                add_le_add hstep (le_refl _)
          _ =
              dividedDifferenceAbsLInvAction nodes n k
                (fun j : Fin (n + 1) => |v j|) ⟨i + 1, hi_lt⟩ := by
                simp [dividedDifferenceAbsLInvAction,
                  dividedDifferenceAbsLInvActionNat, hle,
                  dividedDifferenceFinToNat, hi_lt]

theorem dividedDifferenceAbsLInvAction_nonneg
    (nodes : ℕ → ℝ) (n k : ℕ) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    ∀ i, 0 ≤ dividedDifferenceAbsLInvAction nodes n k v i := by
  intro i
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simpa [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
        dividedDifferenceFinToNat, hi_lt] using hv ⟨0, hi_lt⟩
  | succ i ih =>
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      by_cases hle : i + 1 ≤ k
      · simpa [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt] using hv ⟨i + 1, hi_lt⟩
      · have hprev :
            0 ≤ dividedDifferenceAbsLInvActionNat nodes k
              (dividedDifferenceFinToNat v) i := by
          simpa [dividedDifferenceAbsLInvAction] using ih hpred_lt
        have hterm :
            0 ≤ |nodes (i + 1) - nodes (i + 1 - k - 1)| *
              dividedDifferenceFinToNat v (i + 1) := by
          exact mul_nonneg (abs_nonneg _)
            (by simpa [dividedDifferenceFinToNat, hi_lt] using
              hv ⟨i + 1, hi_lt⟩)
        simpa [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle] using add_nonneg hprev hterm

/-- Monotonicity of the absolute inverse action. -/
theorem dividedDifferenceAbsLInvAction_mono
    (nodes : ℕ → ℝ) (n k : ℕ)
    (v w : Fin (n + 1) → ℝ)
    (hvw : ∀ i, v i ≤ w i) :
    ∀ i, dividedDifferenceAbsLInvAction nodes n k v i ≤
      dividedDifferenceAbsLInvAction nodes n k w i := by
  intro i
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simpa [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
        dividedDifferenceFinToNat, hi_lt] using hvw ⟨0, hi_lt⟩
  | succ i ih =>
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      by_cases hle : i + 1 ≤ k
      · simpa [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt] using hvw ⟨i + 1, hi_lt⟩
      · have hprev :
            dividedDifferenceAbsLInvActionNat nodes k
              (dividedDifferenceFinToNat v) i ≤
            dividedDifferenceAbsLInvActionNat nodes k
              (dividedDifferenceFinToNat w) i := by
          simpa [dividedDifferenceAbsLInvAction] using ih hpred_lt
        have hterm :
            |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                dividedDifferenceFinToNat v (i + 1) ≤
              |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                dividedDifferenceFinToNat w (i + 1) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa [dividedDifferenceFinToNat, hi_lt] using
              hvw ⟨i + 1, hi_lt⟩)
            (abs_nonneg _)
        simpa [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle] using add_le_add hprev hterm

/-- Linearity of `|L_k^{-1}|` with respect to subtraction in the vector
argument. -/
theorem dividedDifferenceAbsLInvAction_sub
    (nodes : ℕ → ℝ) (n k : ℕ)
    (v w : Fin (n + 1) → ℝ) :
    ∀ i, dividedDifferenceAbsLInvAction nodes n k
        (fun j => v j - w j) i =
      dividedDifferenceAbsLInvAction nodes n k v i -
        dividedDifferenceAbsLInvAction nodes n k w i := by
  intro i
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
        dividedDifferenceFinToNat, hi_lt]
  | succ i ih =>
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      by_cases hle : i + 1 ≤ k
      · simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt]
      · have hih :
            dividedDifferenceAbsLInvActionNat nodes k
                (dividedDifferenceFinToNat
                  (fun j : Fin (n + 1) => v j - w j)) i =
              dividedDifferenceAbsLInvActionNat nodes k
                  (dividedDifferenceFinToNat v) i -
                dividedDifferenceAbsLInvActionNat nodes k
                  (dividedDifferenceFinToNat w) i := by
          simpa [dividedDifferenceAbsLInvAction] using ih hpred_lt
        simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt, hih]
        ring

/-- Linearity of `|L_k^{-1}|` with respect to scalar multiplication in the
vector argument. -/
theorem dividedDifferenceAbsLInvAction_smul
    (nodes : ℕ → ℝ) (n k : ℕ) (a : ℝ)
    (v : Fin (n + 1) → ℝ) :
    ∀ i, dividedDifferenceAbsLInvAction nodes n k
        (fun j => a * v j) i =
      a * dividedDifferenceAbsLInvAction nodes n k v i := by
  intro i
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
        dividedDifferenceFinToNat, hi_lt]
  | succ i ih =>
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      by_cases hle : i + 1 ≤ k
      · simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt]
      · have hih :
            dividedDifferenceAbsLInvActionNat nodes k
                (dividedDifferenceFinToNat
                  (fun j : Fin (n + 1) => a * v j)) i =
              a * dividedDifferenceAbsLInvActionNat nodes k
                  (dividedDifferenceFinToNat v) i := by
          simpa [dividedDifferenceAbsLInvAction] using ih hpred_lt
        simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt, hih]
        ring

theorem abs_dividedDifferenceLInvAction_sub_le_absLInvAction
    (nodes : ℕ → ℝ) (n k : ℕ)
    (v w : Fin (n + 1) → ℝ) :
    ∀ i : Fin (n + 1),
      |dividedDifferenceLInvAction nodes n k v i -
          dividedDifferenceLInvAction nodes n k w i| ≤
        dividedDifferenceAbsLInvAction nodes n k
          (fun j => |v j - w j|) i := by
  intro i
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simp [dividedDifferenceLInvAction, dividedDifferenceAbsLInvAction,
        dividedDifferenceLInvActionNat, dividedDifferenceAbsLInvActionNat,
        dividedDifferenceFinToNat, hi_lt]
  | succ i ih =>
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      by_cases hle : i + 1 ≤ k
      · simp [dividedDifferenceLInvAction, dividedDifferenceAbsLInvAction,
          dividedDifferenceLInvActionNat, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt]
      · have hih :
            |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i -
              dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat w) i| ≤
              dividedDifferenceAbsLInvActionNat nodes k
                (dividedDifferenceFinToNat
                  (fun j : Fin (n + 1) => |v j - w j|)) i := by
          simpa [dividedDifferenceLInvAction, dividedDifferenceAbsLInvAction]
            using ih hpred_lt
        have hmul :
            |(nodes (i + 1) - nodes (i + 1 - k - 1)) *
                (dividedDifferenceFinToNat v (i + 1) -
                  dividedDifferenceFinToNat w (i + 1))| =
              |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                |dividedDifferenceFinToNat v (i + 1) -
                  dividedDifferenceFinToNat w (i + 1)| := by
          rw [abs_mul]
        have htri :
            |(dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i +
              (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                dividedDifferenceFinToNat v (i + 1)) -
              (dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat w) i +
              (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                dividedDifferenceFinToNat w (i + 1))| ≤
              |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i -
                dividedDifferenceLInvActionNat nodes k
                  (dividedDifferenceFinToNat w) i| +
              |(nodes (i + 1) - nodes (i + 1 - k - 1)) *
                (dividedDifferenceFinToNat v (i + 1) -
                  dividedDifferenceFinToNat w (i + 1))| := by
          have hsplit :
              (dividedDifferenceLInvActionNat nodes k
                  (dividedDifferenceFinToNat v) i +
                (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                  dividedDifferenceFinToNat v (i + 1)) -
                (dividedDifferenceLInvActionNat nodes k
                  (dividedDifferenceFinToNat w) i +
                (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                  dividedDifferenceFinToNat w (i + 1)) =
                (dividedDifferenceLInvActionNat nodes k
                  (dividedDifferenceFinToNat v) i -
                  dividedDifferenceLInvActionNat nodes k
                    (dividedDifferenceFinToNat w) i) +
                (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                  (dividedDifferenceFinToNat v (i + 1) -
                    dividedDifferenceFinToNat w (i + 1)) := by
            ring
          rw [hsplit]
          exact abs_add_le _ _
        calc
          |dividedDifferenceLInvAction nodes n k v ⟨i + 1, hi_lt⟩ -
            dividedDifferenceLInvAction nodes n k w ⟨i + 1, hi_lt⟩|
              ≤
              |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i -
                dividedDifferenceLInvActionNat nodes k
                  (dividedDifferenceFinToNat w) i| +
              |(nodes (i + 1) - nodes (i + 1 - k - 1)) *
                (dividedDifferenceFinToNat v (i + 1) -
                  dividedDifferenceFinToNat w (i + 1))| := by
                simpa [dividedDifferenceLInvAction,
                  dividedDifferenceLInvActionNat, hle] using htri
          _ =
              |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i -
                dividedDifferenceLInvActionNat nodes k
                  (dividedDifferenceFinToNat w) i| +
              |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                |dividedDifferenceFinToNat v (i + 1) -
                  dividedDifferenceFinToNat w (i + 1)| := by rw [hmul]
          _ ≤
              dividedDifferenceAbsLInvActionNat nodes k
                (dividedDifferenceFinToNat
                  (fun j : Fin (n + 1) => |v j - w j|)) i +
              |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                |dividedDifferenceFinToNat v (i + 1) -
                  dividedDifferenceFinToNat w (i + 1)| :=
                add_le_add hih (le_refl _)
          _ =
              dividedDifferenceAbsLInvAction nodes n k
                (fun j : Fin (n + 1) => |v j - w j|)
                ⟨i + 1, hi_lt⟩ := by
                simp [dividedDifferenceAbsLInvAction,
                  dividedDifferenceAbsLInvActionNat, hle,
                  dividedDifferenceFinToNat, hi_lt]

/-- The recursive inverse action is a left inverse of the finite
divided-difference action. -/
theorem dividedDifferenceLInvAction_LMatrixAction_eq
    (nodes : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    (hden : ∀ i : Fin (n + 1), k < i.val →
      nodes i.val - nodes (i.val - k - 1) ≠ 0) :
    ∀ i : Fin (n + 1),
      dividedDifferenceLInvAction nodes n k
        (dividedDifferenceLMatrixAction nodes n k v) i = v i := by
  intro i
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      have hle : (0 : ℕ) ≤ k := Nat.zero_le k
      rw [dividedDifferenceLInvAction_of_le
        (i := ⟨0, hi_lt⟩) nodes
        (dividedDifferenceLMatrixAction nodes n k v) hle,
        dividedDifferenceLMatrixAction_of_le
          (i := ⟨0, hi_lt⟩) nodes v hle]
  | succ i ih =>
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      by_cases hle : i + 1 ≤ k
      · have hrow : (⟨i + 1, hi_lt⟩ : Fin (n + 1)).val ≤ k := hle
        rw [dividedDifferenceLInvAction_of_le
          (i := ⟨i + 1, hi_lt⟩) nodes
          (dividedDifferenceLMatrixAction nodes n k v) hrow,
          dividedDifferenceLMatrixAction_of_le
            (i := ⟨i + 1, hi_lt⟩) nodes v hrow]
      · have hgt : k < i + 1 := Nat.lt_of_not_ge hle
        have hrow :
            dividedDifferenceLMatrixAction nodes n k v ⟨i + 1, hi_lt⟩ =
              (v ⟨i + 1, hi_lt⟩ - v (dividedDifferenceFinPred ⟨i + 1, hi_lt⟩)) /
                (nodes (i + 1) - nodes (i + 1 - k - 1)) :=
          dividedDifferenceLMatrixAction_of_gt nodes v hgt
        have hpred :
            dividedDifferenceFinPred (⟨i + 1, hi_lt⟩ : Fin (n + 1)) =
              ⟨i, hpred_lt⟩ := by
          simp [dividedDifferenceFinPred]
        have hprev :
            dividedDifferenceLInvAction nodes n k
              (dividedDifferenceLMatrixAction nodes n k v)
              (dividedDifferenceFinPred ⟨i + 1, hi_lt⟩) =
              v ⟨i, hpred_lt⟩ := by
          rw [hpred]
          exact ih hpred_lt
        have hprev' :
            dividedDifferenceLInvAction nodes n k
              (dividedDifferenceLMatrixAction nodes n k v)
              ⟨i, hpred_lt⟩ =
              v ⟨i, hpred_lt⟩ :=
          ih hpred_lt
        have hden' :
            nodes (i + 1) - nodes (i + 1 - k - 1) ≠ 0 :=
          hden ⟨i + 1, hi_lt⟩ hgt
        calc
          dividedDifferenceLInvAction nodes n k
              (dividedDifferenceLMatrixAction nodes n k v)
              ⟨i + 1, hi_lt⟩ =
            dividedDifferenceLInvAction nodes n k
              (dividedDifferenceLMatrixAction nodes n k v)
              (dividedDifferenceFinPred ⟨i + 1, hi_lt⟩) +
              (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                dividedDifferenceLMatrixAction nodes n k v ⟨i + 1, hi_lt⟩ := by
              rw [dividedDifferenceLInvAction_of_gt
                (i := ⟨i + 1, hi_lt⟩) nodes
                (dividedDifferenceLMatrixAction nodes n k v) hgt]
          _ =
            v ⟨i, hpred_lt⟩ +
              (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                ((v ⟨i + 1, hi_lt⟩ - v ⟨i, hpred_lt⟩) /
                  (nodes (i + 1) - nodes (i + 1 - k - 1))) := by
              simp [hprev', hrow, hpred]
          _ = v ⟨i + 1, hi_lt⟩ := by
              field_simp [hden']
              ring

/-- Exact inverse product `L_0^{-1} ... L_{m-1}^{-1}`. -/
noncomputable def dividedDifferenceLInvProductAction
    (nodes : ℕ → ℝ) (n : ℕ) :
    ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, v => v
  | k + 1, v =>
      dividedDifferenceLInvProductAction nodes n k
        (dividedDifferenceLInvAction nodes n k v)

/-- Absolute inverse product `|L_0^{-1}| ... |L_{m-1}^{-1}|`. -/
noncomputable def dividedDifferenceAbsLInvProductAction
    (nodes : ℕ → ℝ) (n : ℕ) :
    ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, v => v
  | k + 1, v =>
      dividedDifferenceAbsLInvProductAction nodes n k
        (dividedDifferenceAbsLInvAction nodes n k v)

theorem dividedDifferenceAbsLInvProductAction_nonneg
    (nodes : ℕ → ℝ) (n m : ℕ) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    ∀ i, 0 ≤ dividedDifferenceAbsLInvProductAction nodes n m v i := by
  induction m generalizing v with
  | zero =>
      intro i
      exact hv i
  | succ m ih =>
      exact ih
        (dividedDifferenceAbsLInvAction nodes n m v)
        (dividedDifferenceAbsLInvAction_nonneg nodes n m v hv)

theorem dividedDifferenceAbsLInvProductAction_mono
    (nodes : ℕ → ℝ) (n m : ℕ)
    (v w : Fin (n + 1) → ℝ)
    (hvw : ∀ i, v i ≤ w i) :
    ∀ i, dividedDifferenceAbsLInvProductAction nodes n m v i ≤
      dividedDifferenceAbsLInvProductAction nodes n m w i := by
  induction m generalizing v w with
  | zero =>
      intro i
      exact hvw i
  | succ m ih =>
      exact ih
        (dividedDifferenceAbsLInvAction nodes n m v)
        (dividedDifferenceAbsLInvAction nodes n m w)
        (dividedDifferenceAbsLInvAction_mono nodes n m v w hvw)

theorem dividedDifferenceAbsLInvProductAction_smul
    (nodes : ℕ → ℝ) (n m : ℕ) (a : ℝ)
    (v : Fin (n + 1) → ℝ) :
    ∀ i, dividedDifferenceAbsLInvProductAction nodes n m
        (fun j => a * v j) i =
      a * dividedDifferenceAbsLInvProductAction nodes n m v i := by
  induction m generalizing v with
  | zero =>
      intro i
      rfl
  | succ m ih =>
      intro i
      have hstep :=
        dividedDifferenceAbsLInvAction_smul nodes n m a v
      have hfun :
          dividedDifferenceAbsLInvAction nodes n m
              (fun j : Fin (n + 1) => a * v j) =
            fun j =>
              a * dividedDifferenceAbsLInvAction nodes n m v j := by
        funext j
        exact hstep j
      simp [dividedDifferenceAbsLInvProductAction, hfun, ih]

theorem abs_dividedDifferenceLInvProductAction_sub_le_absLInvProductAction
    (nodes : ℕ → ℝ) (n m : ℕ)
    (v w : Fin (n + 1) → ℝ) :
    ∀ i : Fin (n + 1),
      |dividedDifferenceLInvProductAction nodes n m v i -
          dividedDifferenceLInvProductAction nodes n m w i| ≤
        dividedDifferenceAbsLInvProductAction nodes n m
          (fun j => |v j - w j|) i := by
  induction m generalizing v w with
  | zero =>
      intro i
      simp [dividedDifferenceLInvProductAction,
        dividedDifferenceAbsLInvProductAction]
  | succ m ih =>
      intro i
      have hlocal :=
        abs_dividedDifferenceLInvAction_sub_le_absLInvAction nodes n m v w
      have hmono :=
        dividedDifferenceAbsLInvProductAction_mono nodes n m
          (fun j =>
            |dividedDifferenceLInvAction nodes n m v j -
              dividedDifferenceLInvAction nodes n m w j|)
          (dividedDifferenceAbsLInvAction nodes n m
            (fun j => |v j - w j|)) hlocal
      calc
        |dividedDifferenceLInvProductAction nodes n (m + 1) v i -
          dividedDifferenceLInvProductAction nodes n (m + 1) w i|
            ≤ dividedDifferenceAbsLInvProductAction nodes n m
                (fun j =>
                  |dividedDifferenceLInvAction nodes n m v j -
                    dividedDifferenceLInvAction nodes n m w j|) i :=
              ih
                (dividedDifferenceLInvAction nodes n m v)
                (dividedDifferenceLInvAction nodes n m w) i
        _ ≤ dividedDifferenceAbsLInvProductAction nodes n m
                (dividedDifferenceAbsLInvAction nodes n m
                  (fun j => |v j - w j|)) i :=
              hmono i
        _ = dividedDifferenceAbsLInvProductAction nodes n (m + 1)
                (fun j => |v j - w j|) i := rfl

/-- The inverse product reconstructs the original data from exact
divided-difference columns. -/
theorem dividedDifferenceLInvProductAction_finiteCoeffs_eq_data
    (nodes f : ℕ → ℝ) {n : ℕ} (m : ℕ)
    (hden : ∀ k j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0) :
    ∀ i : Fin (n + 1),
      dividedDifferenceLInvProductAction nodes n m
        (dividedDifferenceFiniteCoeffs nodes f n m) i = f i.val := by
  induction m with
  | zero =>
      intro i
      rfl
  | succ m ih =>
      intro i
      have hleft :
          dividedDifferenceLInvAction nodes n m
            (dividedDifferenceFiniteCoeffs nodes f n (m + 1)) =
          dividedDifferenceFiniteCoeffs nodes f n m := by
        funext j
        have hden_m :
            ∀ i : Fin (n + 1), m < i.val →
              nodes i.val - nodes (i.val - m - 1) ≠ 0 := by
          intro i hi
          exact hden m i.val hi i.isLt
        simpa [dividedDifferenceFiniteCoeffs_succ] using
          dividedDifferenceLInvAction_LMatrixAction_eq
            nodes (dividedDifferenceFiniteCoeffs nodes f n m) hden_m j
      simpa [dividedDifferenceLInvProductAction, hleft] using ih i

/-- A generic perturbed inverse product used for the residual unwind in
Higham (5.12). The step argument represents
`L_k^{-1} + Delta L_k^{-1}`. -/
noncomputable def dividedDifferencePerturbedLInvProductAction
    {n : ℕ}
    (step : ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) :
    ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, v => v
  | k + 1, v =>
      dividedDifferencePerturbedLInvProductAction step k (step k v)

theorem dividedDifferencePerturbedLInvProduct_abs_le
    (nodes : ℕ → ℝ) {n : ℕ} (m : ℕ) {gamma : ℝ}
    (hgamma : 0 ≤ gamma)
    (step : ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hstep : ∀ k v i,
      |step k v i - dividedDifferenceLInvAction nodes n k v i| ≤
        gamma * dividedDifferenceAbsLInvAction nodes n k
          (fun j => |v j|) i) :
    ∀ (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)),
      |dividedDifferencePerturbedLInvProductAction step m v i -
          dividedDifferenceLInvProductAction nodes n m v i| ≤
        ((1 + gamma) ^ m - 1) *
          dividedDifferenceAbsLInvProductAction nodes n m
            (fun j => |v j|) i := by
  induction m with
  | zero =>
      intro v i
      simp [dividedDifferencePerturbedLInvProductAction,
        dividedDifferenceLInvProductAction]
  | succ m ih =>
      intro v i
      let pstep := step m v
      let estep := dividedDifferenceLInvAction nodes n m v
      let avec : Fin (n + 1) → ℝ :=
        dividedDifferenceAbsLInvAction nodes n m (fun j => |v j|)
      have habs_estep :
          ∀ j, |estep j| ≤ avec j := by
        intro j
        simpa [estep, avec] using
          abs_dividedDifferenceLInvAction_le_absLInvAction nodes n m v j
      have hprop_local :
          ∀ j, |pstep j - estep j| ≤ gamma * avec j := by
        intro j
        simpa [pstep, estep, avec] using hstep m v j
      have hlocal_abs :
          ∀ j, |pstep j| ≤ (1 + gamma) * avec j := by
        intro j
        have htri :
            |pstep j| ≤ |pstep j - estep j| + |estep j| := by
          have hsplit : pstep j = (pstep j - estep j) + estep j := by ring
          calc
            |pstep j| = |(pstep j - estep j) + estep j| := by
              exact congrArg abs hsplit
            _ ≤ |pstep j - estep j| + |estep j| :=
              abs_add_le (pstep j - estep j) (estep j)
        calc
          |pstep j| ≤ |pstep j - estep j| + |estep j| := htri
          _ ≤ gamma * avec j + avec j :=
                add_le_add (hprop_local j) (habs_estep j)
          _ = (1 + gamma) * avec j := by ring
      have hscale_nonneg : 0 ≤ 1 + gamma := by linarith
      have hcoef_nonneg : 0 ≤ (1 + gamma) ^ m - 1 := by
        have hpow : 1 ≤ (1 + gamma) ^ m :=
          one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + gamma)
        linarith
      have hpart_pert_bound :
          |dividedDifferencePerturbedLInvProductAction step m pstep i -
              dividedDifferenceLInvProductAction nodes n m pstep i| ≤
            ((1 + gamma) ^ m - 1) *
              ((1 + gamma) *
                dividedDifferenceAbsLInvProductAction nodes n m avec i) := by
        have hpert_mono :
            ∀ j,
              dividedDifferenceAbsLInvProductAction nodes n m
                (fun r => |pstep r|) j ≤
              dividedDifferenceAbsLInvProductAction nodes n m
                (fun r => (1 + gamma) * avec r) j :=
          dividedDifferenceAbsLInvProductAction_mono nodes n m
            (fun r => |pstep r|) (fun r => (1 + gamma) * avec r)
            hlocal_abs
        have hpert_smul :
            dividedDifferenceAbsLInvProductAction nodes n m
                (fun r => (1 + gamma) * avec r) i =
              (1 + gamma) *
                dividedDifferenceAbsLInvProductAction nodes n m avec i :=
          dividedDifferenceAbsLInvProductAction_smul nodes n m
            (1 + gamma) avec i
        calc
          |dividedDifferencePerturbedLInvProductAction step m pstep i -
              dividedDifferenceLInvProductAction nodes n m pstep i|
              ≤ ((1 + gamma) ^ m - 1) *
                  dividedDifferenceAbsLInvProductAction nodes n m
                    (fun j => |pstep j|) i := ih pstep i
          _ ≤ ((1 + gamma) ^ m - 1) *
                  dividedDifferenceAbsLInvProductAction nodes n m
                    (fun r => (1 + gamma) * avec r) i :=
                mul_le_mul_of_nonneg_left (hpert_mono i) hcoef_nonneg
          _ = ((1 + gamma) ^ m - 1) *
                  ((1 + gamma) *
                    dividedDifferenceAbsLInvProductAction nodes n m avec i) := by
                rw [hpert_smul]
      have hpart_exact_bound :
          |dividedDifferenceLInvProductAction nodes n m pstep i -
              dividedDifferenceLInvProductAction nodes n m estep i| ≤
            gamma * dividedDifferenceAbsLInvProductAction nodes n m avec i := by
        have hprop_mono :
            ∀ j,
              dividedDifferenceAbsLInvProductAction nodes n m
                (fun r => |pstep r - estep r|) j ≤
              dividedDifferenceAbsLInvProductAction nodes n m
                (fun r => gamma * avec r) j :=
          dividedDifferenceAbsLInvProductAction_mono nodes n m
            (fun r => |pstep r - estep r|)
            (fun r => gamma * avec r) hprop_local
        have hprop_smul :
            dividedDifferenceAbsLInvProductAction nodes n m
                (fun r => gamma * avec r) i =
              gamma *
                dividedDifferenceAbsLInvProductAction nodes n m avec i :=
          dividedDifferenceAbsLInvProductAction_smul nodes n m gamma avec i
        calc
          |dividedDifferenceLInvProductAction nodes n m pstep i -
              dividedDifferenceLInvProductAction nodes n m estep i|
              ≤ dividedDifferenceAbsLInvProductAction nodes n m
                  (fun j => |pstep j - estep j|) i :=
                abs_dividedDifferenceLInvProductAction_sub_le_absLInvProductAction
                  nodes n m pstep estep i
          _ ≤ dividedDifferenceAbsLInvProductAction nodes n m
                  (fun r => gamma * avec r) i := hprop_mono i
          _ = gamma * dividedDifferenceAbsLInvProductAction nodes n m avec i :=
                hprop_smul
      have htri :
          |dividedDifferencePerturbedLInvProductAction step (m + 1) v i -
              dividedDifferenceLInvProductAction nodes n (m + 1) v i| ≤
            |dividedDifferencePerturbedLInvProductAction step m pstep i -
              dividedDifferenceLInvProductAction nodes n m pstep i| +
            |dividedDifferenceLInvProductAction nodes n m pstep i -
              dividedDifferenceLInvProductAction nodes n m estep i| := by
        have hsplit :
            dividedDifferencePerturbedLInvProductAction step (m + 1) v i -
              dividedDifferenceLInvProductAction nodes n (m + 1) v i =
            (dividedDifferencePerturbedLInvProductAction step m pstep i -
              dividedDifferenceLInvProductAction nodes n m pstep i) +
            (dividedDifferenceLInvProductAction nodes n m pstep i -
              dividedDifferenceLInvProductAction nodes n m estep i) := by
          simp [dividedDifferencePerturbedLInvProductAction,
            dividedDifferenceLInvProductAction, pstep, estep]
        rw [hsplit]
        exact abs_add_le _ _
      calc
        |dividedDifferencePerturbedLInvProductAction step (m + 1) v i -
          dividedDifferenceLInvProductAction nodes n (m + 1) v i|
            ≤
            |dividedDifferencePerturbedLInvProductAction step m pstep i -
              dividedDifferenceLInvProductAction nodes n m pstep i| +
            |dividedDifferenceLInvProductAction nodes n m pstep i -
              dividedDifferenceLInvProductAction nodes n m estep i| := htri
        _ ≤ ((1 + gamma) ^ m - 1) *
              ((1 + gamma) *
                dividedDifferenceAbsLInvProductAction nodes n m avec i) +
            gamma * dividedDifferenceAbsLInvProductAction nodes n m avec i :=
              add_le_add hpart_pert_bound hpart_exact_bound
        _ = ((1 + gamma) ^ (m + 1) - 1) *
              dividedDifferenceAbsLInvProductAction nodes n (m + 1)
                (fun j => |v j|) i := by
              simp [dividedDifferenceAbsLInvProductAction, avec, pow_succ]
              ring

/-- Higham (5.12), finite residual form. If the original data vector is
obtained by unwinding the computed divided differences with inverse steps
`L_k^{-1} + Delta L_k^{-1}`, and each such step has componentwise relative
majorant `gamma`, then exact Newton reconstruction with
`L_0^{-1}...L_{m-1}^{-1}` has the source residual bound. -/
theorem dividedDifferenceResidual_error_bound
    (nodes : ℕ → ℝ) {n : ℕ} (m : ℕ) {gamma : ℝ}
    (hgamma : 0 ≤ gamma)
    (step : ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hstep : ∀ k v i,
      |step k v i - dividedDifferenceLInvAction nodes n k v i| ≤
        gamma * dividedDifferenceAbsLInvAction nodes n k
          (fun j => |v j|) i)
    (f chat : Fin (n + 1) → ℝ)
    (hf : f = dividedDifferencePerturbedLInvProductAction step m chat) :
    ∀ i : Fin (n + 1),
      |f i - dividedDifferenceLInvProductAction nodes n m chat i| ≤
        ((1 + gamma) ^ m - 1) *
          dividedDifferenceAbsLInvProductAction nodes n m
            (fun j => |chat j|) i := by
  intro i
  subst f
  exact dividedDifferencePerturbedLInvProduct_abs_le
    nodes m hgamma step hstep chat i

/-- Product-form adapter for Higham (5.10): if every active rounded row update
has the supplied multiplicative factor `eta k j`, then the `m`th computed
finite divided-difference column is the iterated product
`G_{m-1} L_{m-1} ... G_0 L_0` applied to the initial data. -/
theorem fl_dividedDifferenceFiniteCoeffs_eq_GLProductAction_of_row_factors
    (fp : FPModel) (nodes f : ℕ → ℝ) (eta : ℕ → ℕ → ℝ) (n m : ℕ)
    (hrow : ∀ k, k < m → ∀ i : Fin (n + 1), k < i.val →
      fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i =
        eta k i.val *
          dividedDifferenceStep nodes
            (dividedDifferenceFinToNat
              (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)) k i.val) :
    ∀ i : Fin (n + 1),
      fl_dividedDifferenceFiniteCoeffs fp nodes f n m i =
        dividedDifferenceGLProductAction nodes eta n m
          (fun i : Fin (n + 1) => f i.val) i := by
  induction m with
  | zero =>
      intro i
      rfl
  | succ m ih =>
      intro i
      have hrowPrev :
          ∀ k, k < m → ∀ i : Fin (n + 1), k < i.val →
            fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i =
              eta k i.val *
                dividedDifferenceStep nodes
                  (dividedDifferenceFinToNat
                    (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
                  k i.val := by
        intro k hk
        exact hrow k (Nat.lt_trans hk (Nat.lt_succ_self m))
      have hprev :
          fl_dividedDifferenceFiniteCoeffs fp nodes f n m =
            dividedDifferenceGLProductAction nodes eta n m
              (fun i : Fin (n + 1) => f i.val) := by
        funext i
        exact ih hrowPrev i
      have hstep :
          fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i =
            dividedDifferenceGMatrixAction (eta m) n m
              (dividedDifferenceLMatrixAction nodes n m
                (fl_dividedDifferenceFiniteCoeffs fp nodes f n m)) i := by
        have hrowStep :
            ∀ i : Fin (n + 1), m < i.val →
              fl_dividedDifferenceStep fp nodes
                  (dividedDifferenceFinToNat
                    (fl_dividedDifferenceFiniteCoeffs fp nodes f n m))
                  m i.val =
                eta m i.val *
                  dividedDifferenceStep nodes
                    (dividedDifferenceFinToNat
                      (fl_dividedDifferenceFiniteCoeffs fp nodes f n m))
                    m i.val := by
          intro i hi
          simpa [fl_dividedDifferenceFiniteCoeffs] using
            hrow m (Nat.lt_succ_self m) i hi
        simpa [fl_dividedDifferenceFiniteCoeffs] using
          (fl_dividedDifferenceStep_eq_GMatrixAction_of_row_factors
            fp nodes
            (fl_dividedDifferenceFiniteCoeffs fp nodes f n m)
            (eta m) hrowStep i)
      calc
        fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i =
            dividedDifferenceGMatrixAction (eta m) n m
              (dividedDifferenceLMatrixAction nodes n m
                (fl_dividedDifferenceFiniteCoeffs fp nodes f n m)) i := hstep
        _ = dividedDifferenceGMatrixAction (eta m) n m
              (dividedDifferenceLMatrixAction nodes n m
                (dividedDifferenceGLProductAction nodes eta n m
                  (fun i : Fin (n + 1) => f i.val))) i := by
              rw [hprev]
        _ = dividedDifferenceGLProductAction nodes eta n (m + 1)
              (fun i : Fin (n + 1) => f i.val) i := rfl

/-- Gamma-three product representation for the rounded finite
divided-difference columns.  This is the finite product-form foundation for
Higham (5.10); turning it into the printed normwise/product perturbation bound
is a separate matrix-product estimate. -/
theorem fl_dividedDifferenceFiniteCoeffs_exists_GLProductAction_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n : ℕ} (m : ℕ)
    (hden : ∀ k j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ k j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ eta : ℕ → ℕ → ℝ,
      (∀ k, k < m → ∀ i : Fin (n + 1), k < i.val →
        |eta k i.val - 1| ≤ gamma fp 3) ∧
      ∀ i : Fin (n + 1),
        fl_dividedDifferenceFiniteCoeffs fp nodes f n m i =
          dividedDifferenceGLProductAction nodes eta n m
            (fun i : Fin (n + 1) => f i.val) i := by
  classical
  let theta : ℕ → ℕ → ℝ := fun k j =>
    if hjk : k < j then
      if hjn : j < n + 1 then
        Classical.choose
          (fl_dividedDifferenceStep_entry_gamma3 fp nodes
            (dividedDifferenceFinToNat
              (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
            hjk (hden k j hjk hjn) (hdenHat k j hjk hjn) hγ)
      else
        0
    else
      0
  let eta : ℕ → ℕ → ℝ := fun k j => 1 + theta k j
  refine ⟨eta, ?_, ?_⟩
  · intro k hk i hi
    have hspec := Classical.choose_spec
      (fl_dividedDifferenceStep_entry_gamma3 fp nodes
        (dividedDifferenceFinToNat
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
        hi (hden k i.val hi i.isLt) (hdenHat k i.val hi i.isLt) hγ)
    have htheta :
        theta k i.val =
          Classical.choose
            (fl_dividedDifferenceStep_entry_gamma3 fp nodes
              (dividedDifferenceFinToNat
                (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
              hi (hden k i.val hi i.isLt)
              (hdenHat k i.val hi i.isLt) hγ) := by
      have hile : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
      simp [theta, hi, hile]
    have hetaDiff : eta k i.val - 1 = theta k i.val := by
      simp [eta]
    rw [hetaDiff, htheta]
    exact hspec.1
  · apply fl_dividedDifferenceFiniteCoeffs_eq_GLProductAction_of_row_factors
    intro k hk i hi
    have hspec := Classical.choose_spec
      (fl_dividedDifferenceStep_entry_gamma3 fp nodes
        (dividedDifferenceFinToNat
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
        hi (hden k i.val hi i.isLt) (hdenHat k i.val hi i.isLt) hγ)
    have htheta :
        theta k i.val =
          Classical.choose
            (fl_dividedDifferenceStep_entry_gamma3 fp nodes
              (dividedDifferenceFinToNat
                (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
              hi (hden k i.val hi i.isLt)
              (hdenHat k i.val hi i.isLt) hγ) := by
      have hile : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
      simp [theta, hi, hile]
    have heta :
        eta k i.val =
          1 +
            Classical.choose
              (fl_dividedDifferenceStep_entry_gamma3 fp nodes
                (dividedDifferenceFinToNat
                  (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
                hi (hden k i.val hi i.isLt)
                (hdenHat k i.val hi i.isLt) hγ) := by
      simp [eta, htheta]
    calc
      fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i =
          fl_dividedDifferenceStep fp nodes
            (dividedDifferenceFinToNat
              (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)) k i.val := by
            rfl
      _ = dividedDifferenceStep nodes
            (dividedDifferenceFinToNat
              (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)) k i.val *
          (1 +
            Classical.choose
              (fl_dividedDifferenceStep_entry_gamma3 fp nodes
                (dividedDifferenceFinToNat
                  (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
                hi (hden k i.val hi i.isLt)
                (hdenHat k i.val hi i.isLt) hγ)) := hspec.2
      _ = eta k i.val *
          dividedDifferenceStep nodes
            (dividedDifferenceFinToNat
              (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)) k i.val := by
            rw [heta]
            ring

/-- Higham, 2nd ed., Chapter 5, Section 5.3, equation (5.13b):
the Leja prefix product `prod_{k=0}^{j-1} |alpha_i - alpha_k|`. -/
noncomputable def lejaPrefixProduct
    (nodes : ℕ → ℝ) (j i : ℕ) : ℝ :=
  (Finset.range j).prod (fun k => |nodes i - nodes k|)

theorem lejaPrefixProduct_zero
    (nodes : ℕ → ℝ) (i : ℕ) :
    lejaPrefixProduct nodes 0 i = 1 := by
  simp [lejaPrefixProduct]

theorem lejaPrefixProduct_nonneg
    (nodes : ℕ → ℝ) (j i : ℕ) :
    0 ≤ lejaPrefixProduct nodes j i := by
  unfold lejaPrefixProduct
  exact Finset.prod_nonneg (fun k _ => abs_nonneg (nodes i - nodes k))

theorem lejaPrefixProduct_succ
    (nodes : ℕ → ℝ) (j i : ℕ) :
    lejaPrefixProduct nodes (j + 1) i =
      lejaPrefixProduct nodes j i * |nodes i - nodes j| := by
  simp [lejaPrefixProduct, Finset.prod_range_succ]

/-- Higham (5.13a,b): a Leja ordering of `alpha_0, ..., alpha_n`.

The first node maximizes absolute value over the finite source set, and each
subsequent node maximizes the prefix product against the nodes already chosen.
Ties are allowed, as in the usual mathematical definition. -/
def IsLejaOrdering (nodes : ℕ → ℝ) (n : ℕ) : Prop :=
  (∀ i, i ≤ n → |nodes i| ≤ |nodes 0|) ∧
    ∀ j, 1 ≤ j → j < n →
      ∀ i, j ≤ i → i ≤ n →
        lejaPrefixProduct nodes j i ≤ lejaPrefixProduct nodes j j

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

/-- First greedy choice in the Leja ordering algorithm: position `0` contains
an index whose node has maximal absolute value among `0:n`. -/
def LejaGreedyFirstChoice (nodes : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i, i ≤ n → |nodes i| ≤ |nodes 0|

/-- Greedy choice at Leja step `j`: after positions `< j` are fixed, position
`j` maximizes the current prefix product over the remaining positions `j:n`. -/
def LejaGreedyStepChoice (nodes : ℕ → ℝ) (n j : ℕ) : Prop :=
  ∀ i, j ≤ i → i ≤ n →
    lejaPrefixProduct nodes j i ≤ lejaPrefixProduct nodes j j

/-- Certificate surface for the standard greedy Leja-ordering algorithm.  The
algorithm repeatedly swaps a maximizer into the next position; this predicate
records the choices made by such a trace after the swaps have been applied. -/
def IsLejaGreedyTrace (nodes : ℕ → ℝ) (n : ℕ) : Prop :=
  LejaGreedyFirstChoice nodes n ∧
    ∀ j, 1 ≤ j → j < n → LejaGreedyStepChoice nodes n j

/-- A greedy Leja trace satisfies Higham's defining Leja-ordering conditions
(5.13a,b). -/
theorem IsLejaGreedyTrace.isLejaOrdering
    {nodes : ℕ → ℝ} {n : ℕ}
    (htrace : IsLejaGreedyTrace nodes n) :
    IsLejaOrdering nodes n := by
  exact htrace

/-- Source-facing flop budget for the greedy Leja-ordering construction in
Problem 5.4.  The recurrence adds the next odd increment, so after `n` stages
the budget is exactly `n^2`. -/
def lejaGreedyFlopCount : ℕ → ℕ
  | 0 => 0
  | n + 1 => lejaGreedyFlopCount n + (2 * n + 1)

theorem lejaGreedyFlopCount_eq_square (n : ℕ) :
    lejaGreedyFlopCount n = n * n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [lejaGreedyFlopCount, ih]
      ring

/-! ## Root-product evaluation -/

/-- Exact evaluation of a polynomial from its leading coefficient and roots:
`a_n * prod_i (x - x_i)`, accumulated left to right. -/
noncomputable def rootProductEvalFrom (x : ℝ) :
    List ℝ → ℝ → ℝ
  | [], acc => acc
  | r :: roots, acc => rootProductEvalFrom x roots (acc * (x - r))

/-- Top-level exact root-product evaluation. -/
noncomputable def rootProductEval (aLeading x : ℝ) (roots : List ℝ) : ℝ :=
  rootProductEvalFrom x roots aLeading

/-- Rounded evaluation of the root-product form.  Each root contributes one
rounded subtraction and one rounded multiplication. -/
noncomputable def fl_rootProductEvalFrom (fp : FPModel) (x : ℝ) :
    List ℝ → ℝ → ℝ
  | [], acc => acc
  | r :: roots, acc =>
      fl_rootProductEvalFrom fp x roots
        (fp.fl_mul acc (fp.fl_sub x r))

/-- Top-level rounded root-product evaluation. -/
noncomputable def fl_rootProductEval
    (fp : FPModel) (aLeading x : ℝ) (roots : List ℝ) : ℝ :=
  fl_rootProductEvalFrom fp x roots aLeading

lemma rootProductEvalFrom_smul (x : ℝ) :
    ∀ (roots : List ℝ) (acc c : ℝ),
      rootProductEvalFrom x roots (acc * c) =
        rootProductEvalFrom x roots acc * c := by
  intro roots
  induction roots with
  | nil =>
      intro acc c
      simp [rootProductEvalFrom]
  | cons r roots ih =>
      intro acc c
      simp [rootProductEvalFrom, ih]
      ring

lemma relErrorCounter_one_add
    (fp : FPModel) {δ : ℝ} (hδ : |δ| ≤ fp.u) :
    relErrorCounter fp 1 (1 + δ) := by
  refine ⟨fun _ => δ, fun _ => false, ?_, ?_⟩
  · intro _i
    exact hδ
  · simp

lemma relErrorCounter_one (fp : FPModel) :
    relErrorCounter fp 0 (1 : ℝ) := by
  refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · simp

/-- Root-product evaluation has exactly two relative-error factors per root:
one for forming `x - x_i` and one for multiplying it into the accumulator. -/
theorem fl_rootProductEvalFrom_exists_relErrorCounter
    (fp : FPModel) (x : ℝ) :
    ∀ (roots : List ℝ) (acc : ℝ),
      ∃ c : ℝ,
        relErrorCounter fp (2 * roots.length) c ∧
          fl_rootProductEvalFrom fp x roots acc =
            rootProductEvalFrom x roots acc * c := by
  intro roots
  induction roots with
  | nil =>
      intro acc
      refine ⟨1, ?_, ?_⟩
      · simpa using relErrorCounter_one fp
      · simp [fl_rootProductEvalFrom, rootProductEvalFrom]
  | cons r roots ih =>
      intro acc
      obtain ⟨δsub, hδsub, hsub⟩ := fp.model_sub x r
      obtain ⟨δmul, hδmul, hmul⟩ :=
        fp.model_mul acc (fp.fl_sub x r)
      let cLocal : ℝ := (1 + δsub) * (1 + δmul)
      have hfirst :
          fp.fl_mul acc (fp.fl_sub x r) =
            acc * (x - r) * cLocal := by
        simp [cLocal]
        rw [hmul, hsub]
        ring
      obtain ⟨cRest, hcRest, hrest⟩ :=
        ih (fp.fl_mul acc (fp.fl_sub x r))
      have hcLocal : relErrorCounter fp 2 cLocal := by
        have hsubCounter := relErrorCounter_one_add fp hδsub
        have hmulCounter := relErrorCounter_one_add fp hδmul
        simpa [cLocal, Nat.add_comm] using
          relErrorCounter_mul fp 1 1 (1 + δsub) (1 + δmul)
            hsubCounter hmulCounter
      refine ⟨cLocal * cRest, ?_, ?_⟩
      · have hcounter :=
          relErrorCounter_mul fp 2 (2 * roots.length)
            cLocal cRest hcLocal hcRest
        simpa [List.length_cons, Nat.mul_add, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc] using hcounter
      · simp [fl_rootProductEvalFrom, rootProductEvalFrom]
        rw [hrest, hfirst]
        rw [rootProductEvalFrom_smul x roots (acc * (x - r)) cLocal]
        ring

theorem fl_rootProductEvalFrom_forward_error_bound
    (fp : FPModel) (x : ℝ) (roots : List ℝ) (acc : ℝ)
    (hγ : gammaValid fp (2 * roots.length)) :
    |fl_rootProductEvalFrom fp x roots acc -
        rootProductEvalFrom x roots acc| ≤
      gamma fp (2 * roots.length) *
        |rootProductEvalFrom x roots acc| := by
  obtain ⟨c, hc, hfl⟩ :=
    fl_rootProductEvalFrom_exists_relErrorCounter fp x roots acc
  have hcγ := relErrorCounter_abs_sub_one_le_gamma
    fp (2 * roots.length) c hc hγ
  rw [hfl]
  calc
    |rootProductEvalFrom x roots acc * c -
        rootProductEvalFrom x roots acc|
        = |rootProductEvalFrom x roots acc| * |c - 1| := by
          have h :
              rootProductEvalFrom x roots acc * c -
                  rootProductEvalFrom x roots acc =
                rootProductEvalFrom x roots acc * (c - 1) := by
            ring
          rw [h, abs_mul]
    _ ≤ |rootProductEvalFrom x roots acc| *
          gamma fp (2 * roots.length) :=
        mul_le_mul_of_nonneg_left hcγ (abs_nonneg _)
    _ = gamma fp (2 * roots.length) *
          |rootProductEvalFrom x roots acc| := by ring

theorem fl_rootProductEval_forward_error_bound
    (fp : FPModel) (aLeading x : ℝ) (roots : List ℝ)
    (hγ : gammaValid fp (2 * roots.length)) :
    |fl_rootProductEval fp aLeading x roots -
        rootProductEval aLeading x roots| ≤
      gamma fp (2 * roots.length) *
        |rootProductEval aLeading x roots| := by
  simpa [fl_rootProductEval, rootProductEval] using
    fl_rootProductEvalFrom_forward_error_bound fp x roots aLeading hγ

/-! ## Problem 5.2: beginner power-building evaluation -/

/-- Coefficients in ascending order `[a_0, a_1, ..., a_n]` denote
`a_0 + a_1*x + ... + a_n*x^n`. -/
noncomputable def polyAsc (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: rest => a + x * polyAsc x rest

/-- Tail contribution for the beginner power-building loop.  If the current
stored power is `y`, the next coefficient is multiplied by `x*y`. -/
noncomputable def beginnerPowerTail (x : ℝ) :
    List ℝ → ℝ → ℝ
  | [], _y => 0
  | a :: rest, y =>
      let y' := x * y
      a * y' + beginnerPowerTail x rest y'

/-- Higham, 2nd ed., Problem 5.2: one exact step of the beginner algorithm
`y <- x*y; q <- q + a_i*y`, with state `(q,y)`. -/
def beginnerPowerStep (x : ℝ) (state : ℝ × ℝ) (a : ℝ) : ℝ × ℝ :=
  let y' := x * state.2
  (state.1 + a * y', y')

/-- Exact beginner power-building evaluation from ascending coefficients. -/
noncomputable def beginnerPowerEvalAsc (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a0 :: rest => (rest.foldl (beginnerPowerStep x) (a0, 1)).1

lemma beginnerPowerFold_fst_eq_add_tail (x : ℝ) :
    ∀ (coeffsAscTail : List ℝ) (q y : ℝ),
      (coeffsAscTail.foldl (beginnerPowerStep x) (q, y)).1 =
        q + beginnerPowerTail x coeffsAscTail y := by
  intro coeffsAscTail
  induction coeffsAscTail with
  | nil =>
      intro q y
      simp [beginnerPowerTail]
  | cons a rest ih =>
      intro q y
      simp [List.foldl, beginnerPowerStep, beginnerPowerTail, ih]
      ring

lemma beginnerPowerTail_eq_mul_x_polyAsc (x : ℝ) :
    ∀ (coeffsAscTail : List ℝ) (y : ℝ),
      beginnerPowerTail x coeffsAscTail y =
        y * x * polyAsc x coeffsAscTail := by
  intro coeffsAscTail
  induction coeffsAscTail with
  | nil =>
      intro y
      simp [beginnerPowerTail, polyAsc]
  | cons a rest ih =>
      intro y
      simp [beginnerPowerTail, polyAsc, ih]
      ring

/-- The exact beginner power-building loop evaluates the same ascending
polynomial as the displayed monomial formula. -/
theorem beginnerPowerEvalAsc_eq_polyAsc
    (x : ℝ) (coeffsAsc : List ℝ) :
    beginnerPowerEvalAsc x coeffsAsc = polyAsc x coeffsAsc := by
  cases coeffsAsc with
  | nil =>
      rfl
  | cons a0 rest =>
      have hfold := beginnerPowerFold_fst_eq_add_tail x rest a0 1
      have htail := beginnerPowerTail_eq_mul_x_polyAsc x rest 1
      calc
        beginnerPowerEvalAsc x (a0 :: rest)
            = a0 + beginnerPowerTail x rest 1 := by
              simpa [beginnerPowerEvalAsc] using hfold
        _ = a0 + x * polyAsc x rest := by
              rw [htail]
              ring
        _ = polyAsc x (a0 :: rest) := by
              simp [polyAsc]

lemma fl_mul_abs_error_bound (fp : FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  have hdiff : fp.fl_mul x y - x * y = (x * y) * δ := by
    rw [hfl]
    ring
  calc
    |fp.fl_mul x y - x * y| = |x * y| * |δ| := by
      rw [hdiff, abs_mul]
    _ ≤ |x * y| * fp.u :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = fp.u * |x * y| := by ring

lemma fl_add_abs_error_bound (fp : FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * |x + y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
  have hdiff : fp.fl_add x y - (x + y) = (x + y) * δ := by
    rw [hfl]
    ring
  calc
    |fp.fl_add x y - (x + y)| = |x + y| * |δ| := by
      rw [hdiff, abs_mul]
    _ ≤ |x + y| * fp.u :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = fp.u * |x + y| := by ring

lemma fl_mul_error_of_operand_error
    (fp : FPModel) (a yhat y eps : ℝ)
    (hy : |yhat - y| ≤ eps) :
    |fp.fl_mul a yhat - a * y| ≤
      fp.u * |a * yhat| + |a| * eps := by
  have hlocal := fl_mul_abs_error_bound fp a yhat
  have hdecomp :
      fp.fl_mul a yhat - a * y =
        (fp.fl_mul a yhat - a * yhat) + a * (yhat - y) := by
    ring
  have hprop : |a * (yhat - y)| ≤ |a| * eps := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg a)
  calc
    |fp.fl_mul a yhat - a * y|
        = |(fp.fl_mul a yhat - a * yhat) + a * (yhat - y)| := by
          rw [hdecomp]
    _ ≤ |fp.fl_mul a yhat - a * yhat| + |a * (yhat - y)| :=
          abs_add_le _ _
    _ ≤ fp.u * |a * yhat| + |a| * eps :=
          add_le_add hlocal hprop

lemma fl_add_error_of_operand_errors
    (fp : FPModel) (qhat q that t epsQ epsT : ℝ)
    (hq : |qhat - q| ≤ epsQ) (ht : |that - t| ≤ epsT) :
    |fp.fl_add qhat that - (q + t)| ≤
      fp.u * |qhat + that| + epsQ + epsT := by
  have hlocal := fl_add_abs_error_bound fp qhat that
  have hdecomp :
      fp.fl_add qhat that - (q + t) =
        (fp.fl_add qhat that - (qhat + that)) +
          (qhat - q) + (that - t) := by
    ring
  have htri :
      |(fp.fl_add qhat that - (qhat + that)) +
          (qhat - q) + (that - t)| ≤
        |fp.fl_add qhat that - (qhat + that)| +
          |qhat - q| + |that - t| := by
    have h1 :
        |(fp.fl_add qhat that - (qhat + that)) +
            (qhat - q) + (that - t)| ≤
          |(fp.fl_add qhat that - (qhat + that)) +
            (qhat - q)| + |that - t| :=
      abs_add_le _ _
    have h2 :
        |(fp.fl_add qhat that - (qhat + that)) +
            (qhat - q)| ≤
          |fp.fl_add qhat that - (qhat + that)| + |qhat - q| :=
      abs_add_le _ _
    linarith
  calc
    |fp.fl_add qhat that - (q + t)|
        = |(fp.fl_add qhat that - (qhat + that)) +
            (qhat - q) + (that - t)| := by
          rw [hdecomp]
    _ ≤ |fp.fl_add qhat that - (qhat + that)| +
          |qhat - q| + |that - t| := htri
    _ ≤ fp.u * |qhat + that| + epsQ + epsT := by
          linarith

/-- Rounded beginner power-building step.  The modeled implementation rounds
the power update, the coefficient-times-power product, and the accumulation. -/
noncomputable def fl_beginnerPowerStep
    (fp : FPModel) (x : ℝ) (state : ℝ × ℝ) (a : ℝ) : ℝ × ℝ :=
  let y' := fp.fl_mul x state.2
  let t := fp.fl_mul a y'
  (fp.fl_add state.1 t, y')

/-- Rounded beginner power-building evaluation from ascending coefficients. -/
noncomputable def fl_beginnerPowerEvalAsc
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a0 :: rest => (rest.foldl (fl_beginnerPowerStep fp x) (a0, 1)).1

/-- Recursive forward-error budget for the beginner power-building loop,
starting from rounded/exact states `(qhat,yhat)` and `(q,y)` with current error
budgets `epsQ` and `epsY`. -/
noncomputable def beginnerPowerForwardBudgetFrom
    (fp : FPModel) (x : ℝ) :
    List ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  | [], _qhat, _q, _yhat, _y, epsQ, _epsY => epsQ
  | a :: rest, qhat, q, yhat, y, epsQ, epsY =>
      let yhat' := fp.fl_mul x yhat
      let y' := x * y
      let epsY' := fp.u * |x * yhat| + |x| * epsY
      let termhat := fp.fl_mul a yhat'
      let term := a * y'
      let epsTerm := fp.u * |a * yhat'| + |a| * epsY'
      let qhat' := fp.fl_add qhat termhat
      let q' := q + term
      let epsQ' := fp.u * |qhat + termhat| + epsQ + epsTerm
      beginnerPowerForwardBudgetFrom fp x rest qhat' q' yhat' y' epsQ' epsY'

/-- Top-level recursive forward-error budget for Problem 5.2. -/
noncomputable def beginnerPowerForwardBudget
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a0 :: rest =>
      beginnerPowerForwardBudgetFrom fp x rest a0 a0 1 1 0 0

theorem fl_beginnerPowerFold_forward_error_bound_from
    (fp : FPModel) (x : ℝ) :
    ∀ (coeffsAscTail : List ℝ)
      (qhat q yhat y epsQ epsY : ℝ),
      |qhat - q| ≤ epsQ →
      |yhat - y| ≤ epsY →
      |(coeffsAscTail.foldl (fl_beginnerPowerStep fp x)
          (qhat, yhat)).1 -
        (coeffsAscTail.foldl (beginnerPowerStep x) (q, y)).1| ≤
        beginnerPowerForwardBudgetFrom fp x coeffsAscTail
          qhat q yhat y epsQ epsY := by
  intro coeffsAscTail
  induction coeffsAscTail with
  | nil =>
      intro qhat q yhat y epsQ epsY hq _hy
      simpa [beginnerPowerForwardBudgetFrom] using hq
  | cons a rest ih =>
      intro qhat q yhat y epsQ epsY hq hy
      let yhat' : ℝ := fp.fl_mul x yhat
      let y' : ℝ := x * y
      let epsY' : ℝ := fp.u * |x * yhat| + |x| * epsY
      let termhat : ℝ := fp.fl_mul a yhat'
      let term : ℝ := a * y'
      let epsTerm : ℝ := fp.u * |a * yhat'| + |a| * epsY'
      let qhat' : ℝ := fp.fl_add qhat termhat
      let q' : ℝ := q + term
      let epsQ' : ℝ := fp.u * |qhat + termhat| + epsQ + epsTerm
      have hy' : |yhat' - y'| ≤ epsY' := by
        simpa [yhat', y', epsY'] using
          fl_mul_error_of_operand_error fp x yhat y epsY hy
      have hterm : |termhat - term| ≤ epsTerm := by
        simpa [termhat, term, epsTerm] using
          fl_mul_error_of_operand_error fp a yhat' y' epsY' hy'
      have hq' : |qhat' - q'| ≤ epsQ' := by
        simpa [qhat', q', termhat, term, epsQ'] using
          fl_add_error_of_operand_errors fp qhat q termhat term epsQ epsTerm
            hq hterm
      simpa [List.foldl, fl_beginnerPowerStep, beginnerPowerStep,
        beginnerPowerForwardBudgetFrom, yhat', y', epsY',
        termhat, term, epsTerm, qhat', q', epsQ'] using
          ih qhat' q' yhat' y' epsQ' epsY' hq' hy'

/-- Higham, 2nd ed., Problem 5.2: finite forward-error analysis of the beginner
power-building evaluator.  The budget exposes all modeled rounded operations:
one multiplication for the next power, one multiplication by the coefficient,
and one addition into the accumulated sum for each nonconstant coefficient. -/
theorem fl_beginnerPowerEvalAsc_forward_error_bound
    (fp : FPModel) (x : ℝ) (coeffsAsc : List ℝ) :
    |fl_beginnerPowerEvalAsc fp x coeffsAsc -
        beginnerPowerEvalAsc x coeffsAsc| ≤
      beginnerPowerForwardBudget fp x coeffsAsc := by
  cases coeffsAsc with
  | nil =>
      simp [fl_beginnerPowerEvalAsc, beginnerPowerEvalAsc,
        beginnerPowerForwardBudget]
  | cons a0 rest =>
      have h :=
        fl_beginnerPowerFold_forward_error_bound_from fp x
          rest a0 a0 1 1 0 0 (by simp) (by simp)
      simpa [fl_beginnerPowerEvalAsc, beginnerPowerEvalAsc,
        beginnerPowerForwardBudget] using h

theorem fl_beginnerPowerEvalAsc_forward_error_bound_poly
    (fp : FPModel) (x : ℝ) (coeffsAsc : List ℝ) :
    |fl_beginnerPowerEvalAsc fp x coeffsAsc -
        polyAsc x coeffsAsc| ≤
      beginnerPowerForwardBudget fp x coeffsAsc := by
  simpa [beginnerPowerEvalAsc_eq_polyAsc x coeffsAsc] using
    fl_beginnerPowerEvalAsc_forward_error_bound fp x coeffsAsc

/-! ## Problem 5.3: even/odd splitting -/

mutual
  /-- Even-indexed coefficients from an ascending coefficient list. -/
  def evenCoeffsAsc : List ℝ → List ℝ
    | [] => []
    | a :: rest => a :: oddCoeffsAsc rest

  /-- Odd-indexed coefficients from an ascending coefficient list. -/
  def oddCoeffsAsc : List ℝ → List ℝ
    | [] => []
    | _a :: rest => evenCoeffsAsc rest
end

/-- Higham, 2nd ed., Problem 5.3: exact even/odd decomposition
`p(x) = p_even(x^2) + x*p_odd(x^2)`, for ascending coefficients. -/
theorem polyAsc_evenOdd_split (x : ℝ) :
    ∀ coeffsAsc : List ℝ,
      polyAsc x coeffsAsc =
        polyAsc (x * x) (evenCoeffsAsc coeffsAsc) +
          x * polyAsc (x * x) (oddCoeffsAsc coeffsAsc) := by
  intro coeffsAsc
  induction coeffsAsc with
  | nil =>
      simp [polyAsc, evenCoeffsAsc, oddCoeffsAsc]
  | cons a rest ih =>
      simp only [polyAsc, evenCoeffsAsc, oddCoeffsAsc]
      rw [ih]
      ring

/-- Exact even/odd split evaluator. -/
noncomputable def evenOddSplitEvalAsc (x : ℝ) (coeffsAsc : List ℝ) : ℝ :=
  polyAsc (x * x) (evenCoeffsAsc coeffsAsc) +
    x * polyAsc (x * x) (oddCoeffsAsc coeffsAsc)

theorem evenOddSplitEvalAsc_eq_polyAsc
    (x : ℝ) (coeffsAsc : List ℝ) :
    evenOddSplitEvalAsc x coeffsAsc = polyAsc x coeffsAsc := by
  unfold evenOddSplitEvalAsc
  rw [← polyAsc_evenOdd_split x coeffsAsc]

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

/-- Rounded even/odd split evaluation: form `yhat = fl(x*x)`, evaluate the even
and odd coefficient lists by Horner at `yhat`, then compute
`fl(even + fl(x*odd))`. -/
noncomputable def fl_evenOddSplitHornerEvalAsc
    (fp : FPModel) (x : ℝ) (coeffsAsc : List ℝ) : ℝ :=
  let yhat := fp.fl_mul x x
  let evenHat := fl_hornerAsc fp yhat (evenCoeffsAsc coeffsAsc)
  let oddHat := fl_hornerAsc fp yhat (oddCoeffsAsc coeffsAsc)
  fp.fl_add evenHat (fp.fl_mul x oddHat)

/-- Finite forward-error budget for the rounded even/odd split evaluator. -/
noncomputable def evenOddSplitForwardBudget
    (fp : FPModel) (x : ℝ) (coeffsAsc : List ℝ) : ℝ :=
  let yhat := fp.fl_mul x x
  let y := x * x
  let epsY := fp.u * |x * x|
  let even := evenCoeffsAsc coeffsAsc
  let odd := oddCoeffsAsc coeffsAsc
  let evenHat := fl_hornerAsc fp yhat even
  let oddHat := fl_hornerAsc fp yhat odd
  let epsEven :=
    hornerAscForwardBudget fp yhat even +
      polyAscArgErrorBudget yhat y even epsY
  let epsOdd :=
    hornerAscForwardBudget fp yhat odd +
      polyAscArgErrorBudget yhat y odd epsY
  let prodHat := fp.fl_mul x oddHat
  let epsProd := fp.u * |x * oddHat| + |x| * epsOdd
  fp.u * |evenHat + prodHat| + epsEven + epsProd

/-- Higham, 2nd ed., Problem 5.3: finite forward-error analysis for the
even/odd split evaluator, with the computed `y = fl(x*x)` included in the
budget. -/
theorem fl_evenOddSplitHornerEvalAsc_forward_error_bound
    (fp : FPModel) (x : ℝ) (coeffsAsc : List ℝ) :
    |fl_evenOddSplitHornerEvalAsc fp x coeffsAsc -
        polyAsc x coeffsAsc| ≤
      evenOddSplitForwardBudget fp x coeffsAsc := by
  let yhat : ℝ := fp.fl_mul x x
  let y : ℝ := x * x
  let epsY : ℝ := fp.u * |x * x|
  let even : List ℝ := evenCoeffsAsc coeffsAsc
  let odd : List ℝ := oddCoeffsAsc coeffsAsc
  let evenHat : ℝ := fl_hornerAsc fp yhat even
  let oddHat : ℝ := fl_hornerAsc fp yhat odd
  let epsEvenRound : ℝ := hornerAscForwardBudget fp yhat even
  let epsOddRound : ℝ := hornerAscForwardBudget fp yhat odd
  let epsEvenArg : ℝ := polyAscArgErrorBudget yhat y even epsY
  let epsOddArg : ℝ := polyAscArgErrorBudget yhat y odd epsY
  let epsEven : ℝ := epsEvenRound + epsEvenArg
  let epsOdd : ℝ := epsOddRound + epsOddArg
  let prodHat : ℝ := fp.fl_mul x oddHat
  let prod : ℝ := x * polyAsc y odd
  let epsProd : ℝ := fp.u * |x * oddHat| + |x| * epsOdd
  have hy : |yhat - y| ≤ epsY := by
    simpa [yhat, y, epsY] using fl_mul_abs_error_bound fp x x
  have hevenRound :
      |evenHat - polyAsc yhat even| ≤ epsEvenRound := by
    simpa [evenHat, epsEvenRound] using
      fl_hornerAsc_forward_error_bound fp yhat even
  have hoddRound :
      |oddHat - polyAsc yhat odd| ≤ epsOddRound := by
    simpa [oddHat, epsOddRound] using
      fl_hornerAsc_forward_error_bound fp yhat odd
  have hevenArg :
      |polyAsc yhat even - polyAsc y even| ≤ epsEvenArg := by
    simpa [epsEvenArg] using
      polyAsc_arg_error_bound yhat y epsY even hy
  have hoddArg :
      |polyAsc yhat odd - polyAsc y odd| ≤ epsOddArg := by
    simpa [epsOddArg] using
      polyAsc_arg_error_bound yhat y epsY odd hy
  have heven : |evenHat - polyAsc y even| ≤ epsEven := by
    have hdecomp :
        evenHat - polyAsc y even =
          (evenHat - polyAsc yhat even) +
            (polyAsc yhat even - polyAsc y even) := by
      ring
    calc
      |evenHat - polyAsc y even|
          = |(evenHat - polyAsc yhat even) +
              (polyAsc yhat even - polyAsc y even)| := by
            rw [hdecomp]
      _ ≤ |evenHat - polyAsc yhat even| +
            |polyAsc yhat even - polyAsc y even| :=
          abs_add_le _ _
      _ ≤ epsEvenRound + epsEvenArg :=
          add_le_add hevenRound hevenArg
      _ = epsEven := rfl
  have hodd : |oddHat - polyAsc y odd| ≤ epsOdd := by
    have hdecomp :
        oddHat - polyAsc y odd =
          (oddHat - polyAsc yhat odd) +
            (polyAsc yhat odd - polyAsc y odd) := by
      ring
    calc
      |oddHat - polyAsc y odd|
          = |(oddHat - polyAsc yhat odd) +
              (polyAsc yhat odd - polyAsc y odd)| := by
            rw [hdecomp]
      _ ≤ |oddHat - polyAsc yhat odd| +
            |polyAsc yhat odd - polyAsc y odd| :=
          abs_add_le _ _
      _ ≤ epsOddRound + epsOddArg :=
          add_le_add hoddRound hoddArg
      _ = epsOdd := rfl
  have hprod : |prodHat - prod| ≤ epsProd := by
    simpa [prodHat, prod, epsProd] using
      fl_mul_error_of_operand_error fp x oddHat (polyAsc y odd) epsOdd hodd
  have hadd :
      |fp.fl_add evenHat prodHat -
          (polyAsc y even + prod)| ≤
        fp.u * |evenHat + prodHat| + epsEven + epsProd :=
    fl_add_error_of_operand_errors fp evenHat (polyAsc y even)
      prodHat prod epsEven epsProd heven hprod
  have htarget :
      fp.fl_add evenHat prodHat - polyAsc x coeffsAsc =
        fp.fl_add evenHat prodHat - (polyAsc y even + prod) := by
    rw [polyAsc_evenOdd_split x coeffsAsc]
  calc
    |fl_evenOddSplitHornerEvalAsc fp x coeffsAsc -
        polyAsc x coeffsAsc|
        = |fp.fl_add evenHat prodHat - polyAsc x coeffsAsc| := by
          simp [fl_evenOddSplitHornerEvalAsc, yhat, even, odd,
            evenHat, oddHat, prodHat]
    _ = |fp.fl_add evenHat prodHat - (polyAsc y even + prod)| := by
          rw [htarget]
    _ ≤ fp.u * |evenHat + prodHat| + epsEven + epsProd := hadd
    _ = evenOddSplitForwardBudget fp x coeffsAsc := by
          simp [evenOddSplitForwardBudget, yhat, y, epsY, even, odd,
            evenHat, oddHat, epsEvenRound, epsOddRound, epsEvenArg,
            epsOddArg, epsEven, epsOdd, prodHat, epsProd]

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

/-- Formal derivative of `polyDescPairs`, keeping the coefficient-error
payloads available for coefficientwise backward-error statements. -/
noncomputable def polyDescPairsDeriv (x : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | p :: rest =>
      (rest.length : ℝ) * p.1 * x ^ (rest.length - 1) +
        polyDescPairsDeriv x rest

/-- Formal derivative after applying each coefficient's multiplicative
perturbation. -/
noncomputable def polyDescPairsDerivPerturbed (x : ℝ) :
    List (ℝ × ℝ) → ℝ
  | [] => 0
  | p :: rest =>
      (rest.length : ℝ) * (p.1 * (1 + p.2)) *
          x ^ (rest.length - 1) +
        polyDescPairsDerivPerturbed x rest

/-- Absolute-coefficient majorant for `polyDescPairsDeriv`. -/
noncomputable def polyDescPairsDerivAbs (x : ℝ) :
    List (ℝ × ℝ) → ℝ
  | [] => 0
  | p :: rest =>
      (rest.length : ℝ) * |p.1| * |x| ^ (rest.length - 1) +
        polyDescPairsDerivAbs x rest

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

theorem polyDescPairsDeriv_eq_polyDescDeriv_map_fst (x : ℝ) :
    ∀ pairs : List (ℝ × ℝ),
      polyDescPairsDeriv x pairs =
        polyDescDeriv x (pairs.map Prod.fst) := by
  intro pairs
  induction pairs with
  | nil =>
      simp [polyDescPairsDeriv, polyDescDeriv]
  | cons p rest ih =>
      simp [polyDescPairsDeriv, polyDescDeriv, ih]

theorem polyDescPairsDerivAbs_eq_polyDescDerivAbs_map_fst (x : ℝ) :
    ∀ pairs : List (ℝ × ℝ),
      polyDescPairsDerivAbs x pairs =
        polyDescDerivAbs x (pairs.map Prod.fst) := by
  intro pairs
  induction pairs with
  | nil =>
      simp [polyDescPairsDerivAbs, polyDescDerivAbs]
  | cons p rest ih =>
      simp [polyDescPairsDerivAbs, polyDescDerivAbs, ih]

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

/-- Derivative analogue of
`abs_polyDescPairsPerturbed_sub_polyDescPairs_le`: componentwise coefficient
perturbations bounded by `eta` perturb the derivative by at most
`eta * polyDescPairsDerivAbs`. -/
theorem abs_polyDescPairsDerivPerturbed_sub_polyDescPairsDeriv_le
    (x eta : ℝ) (_heta : 0 ≤ eta) :
    ∀ pairs : List (ℝ × ℝ),
      (∀ p ∈ pairs, |p.2| ≤ eta) →
      |polyDescPairsDerivPerturbed x pairs -
        polyDescPairsDeriv x pairs| ≤
        eta * polyDescPairsDerivAbs x pairs := by
  intro pairs
  induction pairs with
  | nil =>
      intro _hbound
      simp [polyDescPairsDerivPerturbed, polyDescPairsDeriv,
        polyDescPairsDerivAbs]
  | cons p rest ih =>
      intro hbound
      have hp : |p.2| ≤ eta := hbound p (by simp)
      have hrest : ∀ q ∈ rest, |q.2| ≤ eta := by
        intro q hq
        exact hbound q (by simp [hq])
      have htail :=
        ih hrest
      have hhead :
          |(rest.length : ℝ) * (p.1 * (1 + p.2)) *
                x ^ (rest.length - 1) -
              (rest.length : ℝ) * p.1 *
                x ^ (rest.length - 1)| ≤
            eta *
              ((rest.length : ℝ) * |p.1| *
                |x| ^ (rest.length - 1)) := by
        have hdiff :
            (rest.length : ℝ) * (p.1 * (1 + p.2)) *
                x ^ (rest.length - 1) -
              (rest.length : ℝ) * p.1 *
                x ^ (rest.length - 1) =
              ((rest.length : ℝ) * p.1 *
                x ^ (rest.length - 1)) * p.2 := by
          ring
        rw [hdiff, abs_mul]
        have hcoef_nonneg :
            0 ≤ (rest.length : ℝ) * |p.1| *
                |x| ^ (rest.length - 1) := by
          exact mul_nonneg
            (mul_nonneg (by exact_mod_cast rest.length.zero_le)
              (abs_nonneg p.1))
            (pow_nonneg (abs_nonneg x) _)
        have hcoef :
            |(rest.length : ℝ) * p.1 *
                x ^ (rest.length - 1)| =
              (rest.length : ℝ) * |p.1| *
                |x| ^ (rest.length - 1) := by
          rw [abs_mul, abs_mul, abs_pow,
            abs_of_nonneg (by exact_mod_cast rest.length.zero_le)]
        rw [hcoef]
        calc
          (rest.length : ℝ) * |p.1| * |x| ^ (rest.length - 1) *
              |p.2| ≤
              (rest.length : ℝ) * |p.1| *
                |x| ^ (rest.length - 1) * eta :=
            mul_le_mul_of_nonneg_left hp hcoef_nonneg
          _ = eta *
              ((rest.length : ℝ) * |p.1| *
                |x| ^ (rest.length - 1)) := by
            ring
      have htri :
          |polyDescPairsDerivPerturbed x (p :: rest) -
              polyDescPairsDeriv x (p :: rest)| ≤
            |(rest.length : ℝ) * (p.1 * (1 + p.2)) *
                x ^ (rest.length - 1) -
              (rest.length : ℝ) * p.1 *
                x ^ (rest.length - 1)| +
            |polyDescPairsDerivPerturbed x rest -
              polyDescPairsDeriv x rest| := by
        have hsplit :
            polyDescPairsDerivPerturbed x (p :: rest) -
                polyDescPairsDeriv x (p :: rest) =
              ((rest.length : ℝ) * (p.1 * (1 + p.2)) *
                  x ^ (rest.length - 1) -
                (rest.length : ℝ) * p.1 *
                  x ^ (rest.length - 1)) +
              (polyDescPairsDerivPerturbed x rest -
                polyDescPairsDeriv x rest) := by
          simp [polyDescPairsDerivPerturbed, polyDescPairsDeriv]
          ring
        rw [hsplit]
        exact abs_add_le _ _
      have hcombine :
          |(rest.length : ℝ) * (p.1 * (1 + p.2)) *
                x ^ (rest.length - 1) -
              (rest.length : ℝ) * p.1 *
                x ^ (rest.length - 1)| +
            |polyDescPairsDerivPerturbed x rest -
              polyDescPairsDeriv x rest| ≤
            eta * polyDescPairsDerivAbs x (p :: rest) := by
        have hsum := add_le_add hhead htail
        simpa [polyDescPairsDerivAbs, mul_add] using hsum
      exact le_trans htri hcombine

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

/-- Higham, 2nd ed., Chapter 5, Algorithm 5.2, first-derivative core:
one rounded coupled Horner update for `(p, p')`.  The derivative component is
updated first, using the old value component, as in the displayed algorithm. -/
noncomputable def fl_hornerDerivativeStep
    (fp : FPModel) (x : ℝ) (state : ℝ × ℝ) (a : ℝ) : ℝ × ℝ :=
  let d := fl_hornerStep fp x state.2 state.1
  let y := fl_hornerStep fp x state.1 a
  (y, d)

/-- Rounded Algorithm 5.2 specialized to the value and first derivative. -/
noncomputable def fl_hornerDerivativeDesc
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ × ℝ
  | [] => (0, 0)
  | a :: rest => rest.foldl (fl_hornerDerivativeStep fp x) (a, 0)

lemma fl_hornerDerivativeFold_fst_eq (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (y d : ℝ),
      (rest.foldl (fl_hornerDerivativeStep fp x) (y, d)).1 =
        rest.foldl (fl_hornerStep fp x) y := by
  intro rest
  induction rest with
  | nil =>
      intro y d
      rfl
  | cons a rest ih =>
      intro y d
      simp [List.foldl, fl_hornerDerivativeStep, ih]

/-- The value component of rounded Algorithm 5.2 is ordinary rounded Horner
evaluation. -/
theorem fl_hornerDerivativeDesc_fst_eq_fl_hornerDesc
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    (fl_hornerDerivativeDesc fp x coeffsDesc).1 =
      fl_hornerDesc fp x coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons a rest =>
      simpa [fl_hornerDerivativeDesc, fl_hornerDesc]
        using fl_hornerDerivativeFold_fst_eq fp x rest a 0

/-- Rounded synthetic-division quotient coefficients generated by the value
component of Algorithm 5.2 while it walks over the remaining descending
coefficients. -/
noncomputable def fl_hornerSyntheticQuotientFold
    (fp : FPModel) (x y : ℝ) : List ℝ → List ℝ
  | [] => []
  | [_a0] => [y]
  | a :: b :: rest =>
      y :: fl_hornerSyntheticQuotientFold fp x
        (fl_hornerStep fp x y a) (b :: rest)

/-- Rounded synthetic-division quotient coefficients for `coeffsDesc`, in
descending order.  These are the computed analogues of
`hornerSyntheticQuotientDesc`. -/
noncomputable def fl_hornerSyntheticQuotientDesc
    (fp : FPModel) (x : ℝ) : List ℝ → List ℝ
  | [] => []
  | [_a] => []
  | a :: b :: rest => fl_hornerSyntheticQuotientFold fp x a (b :: rest)

lemma fl_hornerSyntheticQuotientFold_length
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (y : ℝ),
      (fl_hornerSyntheticQuotientFold fp x y rest).length =
        rest.length := by
  intro rest
  induction rest with
  | nil =>
      intro y
      simp [fl_hornerSyntheticQuotientFold]
  | cons a rest ih =>
      intro y
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientFold]
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientFold] using
            ih (fl_hornerStep fp x y a)

/-- The computed synthetic-division quotient has one fewer coefficient than
the original polynomial coefficient list. -/
theorem fl_hornerSyntheticQuotientDesc_length
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    (fl_hornerSyntheticQuotientDesc fp x coeffsDesc).length =
      coeffsDesc.length - 1 := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerSyntheticQuotientDesc]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientDesc]
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientDesc] using
            fl_hornerSyntheticQuotientFold_length fp x (b :: tail) a

lemma fl_hornerDerivativeFold_snd_eq_fl_hornerSyntheticQuotientFold
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (y d : ℝ),
      (rest.foldl (fl_hornerDerivativeStep fp x) (y, d)).2 =
        (fl_hornerSyntheticQuotientFold fp x y rest).foldl
          (fl_hornerStep fp x) d := by
  intro rest
  induction rest with
  | nil =>
      intro y d
      rfl
  | cons a rest ih =>
      intro y d
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientFold,
            fl_hornerDerivativeStep]
      | cons b tail =>
          simpa [List.foldl, fl_hornerSyntheticQuotientFold,
            fl_hornerDerivativeStep] using
            ih (fl_hornerStep fp x y a)
              (fl_hornerStep fp x d y)

/-- Algorithm 5.2's rounded first-derivative component is a rounded Horner
evaluation, from a zero initial derivative accumulator, of the computed
synthetic-division quotient coefficients. -/
theorem fl_hornerDerivativeDesc_snd_eq_fl_hornerFoldFromZero_fl_synthetic_quotient
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    (fl_hornerDerivativeDesc fp x coeffsDesc).2 =
      fl_hornerFoldFromZeroDesc fp x
        (fl_hornerSyntheticQuotientDesc fp x coeffsDesc) := by
  cases coeffsDesc with
  | nil =>
      rfl
  | cons a rest =>
      cases rest with
      | nil =>
          rfl
      | cons b tail =>
          simpa [fl_hornerDerivativeDesc,
            fl_hornerSyntheticQuotientDesc,
            fl_hornerFoldFromZeroDesc] using
            fl_hornerDerivativeFold_snd_eq_fl_hornerSyntheticQuotientFold
              fp x (b :: tail) a 0

/-- Local rounded-operation model for one Algorithm 5.2 value/first-derivative
step.  The derivative update and value update each use one multiplication and
one addition. -/
theorem fl_hornerDerivativeStep_unroll
    (fp : FPModel) (x : ℝ) (state : ℝ × ℝ) (a : ℝ) :
    ∃ δdMul δdAdd δyMul δyAdd : ℝ,
      |δdMul| ≤ fp.u ∧
      |δdAdd| ≤ fp.u ∧
      |δyMul| ≤ fp.u ∧
      |δyAdd| ≤ fp.u ∧
      fl_hornerDerivativeStep fp x state a =
        (((x * state.1) * (1 + δyMul) + a) * (1 + δyAdd),
          ((x * state.2) * (1 + δdMul) + state.1) *
            (1 + δdAdd)) := by
  obtain ⟨δdMul, δdAdd, hδdMul, hδdAdd, hd⟩ :=
    fl_hornerStep_unroll fp x state.2 state.1
  obtain ⟨δyMul, δyAdd, hδyMul, hδyAdd, hy⟩ :=
    fl_hornerStep_unroll fp x state.1 a
  refine ⟨δdMul, δdAdd, δyMul, δyAdd,
    hδdMul, hδdAdd, hδyMul, hδyAdd, ?_⟩
  simp [fl_hornerDerivativeStep, hy, hd]

/-- Forward-form local error bounds for one rounded Algorithm 5.2
value/first-derivative step. -/
theorem fl_hornerDerivativeStep_forward_local_error_bounds
    (fp : FPModel) (x : ℝ) (state : ℝ × ℝ) (a : ℝ) :
    let next := fl_hornerDerivativeStep fp x state a
    |next.1 - hornerStep x state.1 a| ≤
        fp.u * (|x| * |state.1| + |fp.fl_mul x state.1 + a|) ∧
      |next.2 - hornerStep x state.2 state.1| ≤
        fp.u * (|x| * |state.2| + |fp.fl_mul x state.2 + state.1|) := by
  dsimp
  constructor
  · simpa [fl_hornerDerivativeStep]
      using fl_hornerStep_forward_local_error_bound fp x state.1 a
  · simpa [fl_hornerDerivativeStep]
      using fl_hornerStep_forward_local_error_bound fp x state.2 state.1

/-! ### Rounded all-order Algorithm 5.2 -/

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

/-- Rounded Algorithm 5.2 output at order `i`.  The integer factorial is the
exact loop counter represented as a real input; the final scale multiplication
is a floating-point operation. -/
noncomputable def fl_hornerHigherDerivativeOutput
    (fp : FPModel) (alpha : ℝ) (coeffsDesc : List ℝ) (i : ℕ) : ℝ :=
  fp.fl_mul (Nat.factorial i : ℝ)
    (fl_hornerTaylorFunctionDesc fp alpha coeffsDesc i)

/-- Finite `i = 0:k` rounded output surface for Algorithm 5.2. -/
noncomputable def fl_hornerHigherDerivativeOutputs
    (fp : FPModel) (alpha : ℝ) (k : ℕ)
    (coeffsDesc : List ℝ) : Fin (k + 1) → ℝ :=
  fun i => fl_hornerHigherDerivativeOutput fp alpha coeffsDesc i.val

/-- End-to-end rounded error bound for every Algorithm 5.2 output order,
including the final factorial scaling multiplication. -/
theorem fl_hornerHigherDerivativeOutput_error_bound
    (fp : FPModel) (alpha : ℝ) (coeffsDesc : List ℝ) (i : ℕ) :
    |fl_hornerHigherDerivativeOutput fp alpha coeffsDesc i -
        hornerFormalDerivativeFunctionDesc alpha coeffsDesc i| ≤
      fp.u * |(Nat.factorial i : ℝ) *
          fl_hornerTaylorFunctionDesc fp alpha coeffsDesc i| +
        (Nat.factorial i : ℝ) *
          fl_hornerTaylorFunctionForwardBudgetDesc
            fp alpha coeffsDesc i := by
  have hstate :=
    fl_hornerTaylorFunctionDesc_error_bound fp alpha coeffsDesc i
  have hscale :=
    fl_mul_error_of_operand_error fp (Nat.factorial i : ℝ)
      (fl_hornerTaylorFunctionDesc fp alpha coeffsDesc i)
      (hornerTaylorFunctionDesc alpha coeffsDesc i)
      (fl_hornerTaylorFunctionForwardBudgetDesc fp alpha coeffsDesc i)
      hstate
  rw [← polyDescHigherDeriv_eq_hornerFormalDerivativeFunctionDesc]
  simpa [fl_hornerHigherDerivativeOutput, polyDescHigherDeriv,
    abs_of_nonneg (show (0 : ℝ) ≤ (Nat.factorial i : ℝ) by positivity)]
    using hscale

/-- Finite-vector form of the all-order rounded output bound. -/
theorem fl_hornerHigherDerivativeOutputs_error_bound
    (fp : FPModel) (alpha : ℝ) (k : ℕ)
    (coeffsDesc : List ℝ) (i : Fin (k + 1)) :
    |fl_hornerHigherDerivativeOutputs fp alpha k coeffsDesc i -
        hornerFormalDerivativeFunctionDesc alpha coeffsDesc i.val| ≤
      fp.u * |(Nat.factorial i.val : ℝ) *
          fl_hornerTaylorFunctionDesc fp alpha coeffsDesc i.val| +
        (Nat.factorial i.val : ℝ) *
          fl_hornerTaylorFunctionForwardBudgetDesc
            fp alpha coeffsDesc i.val := by
  exact fl_hornerHigherDerivativeOutput_error_bound
    fp alpha coeffsDesc i.val

private lemma fl_hornerDerivativeStep_backward_algebra_nil
    (x d y deltaDMul deltaDAdd thetaDTail thetaD thetaCarry : ℝ)
    (hD :
      (1 + deltaDMul) * (1 + deltaDAdd) * (1 + thetaDTail) =
        1 + thetaD)
    (hCarry :
      (1 + deltaDAdd) * (1 + thetaDTail) = 1 + thetaCarry) :
    ((x * d) * (1 + deltaDMul) + y) * (1 + deltaDAdd) *
        (1 + thetaDTail) =
      d * (1 + thetaD) * x + y * (1 + thetaCarry) := by
  rw [← hD, ← hCarry]
  ring

private lemma fl_hornerDerivativeStep_backward_algebra_cons
    (x z m d y a deltaDMul deltaDAdd deltaYMul deltaYAdd thetaDTail
      thetaYTail thetaD thetaCarry thetaValue thetaA thetaY : ℝ)
    (hD :
      (1 + deltaDMul) * (1 + deltaDAdd) * (1 + thetaDTail) =
        1 + thetaD)
    (hCarry :
      (1 + deltaDAdd) * (1 + thetaDTail) = 1 + thetaCarry)
    (hValue :
      (1 + deltaYMul) * (1 + deltaYAdd) * (1 + thetaYTail) =
        1 + thetaValue)
    (hA :
      (1 + deltaYAdd) * (1 + thetaYTail) = 1 + thetaA)
    (hY :
      (1 + thetaCarry) + m * (1 + thetaValue) =
        (m + 1) * (1 + thetaY)) :
    ((x * d) * (1 + deltaDMul) + y) * (1 + deltaDAdd) *
        (1 + thetaDTail) * (x * z) +
      m * (((x * y) * (1 + deltaYMul) + a) * (1 + deltaYAdd) *
        (1 + thetaYTail)) * z =
      d * (1 + thetaD) * (x * (x * z)) +
        (m + 1) * y * (1 + thetaY) * (x * z) +
        m * a * (1 + thetaA) * z := by
  have hycombine :
      y * (1 + thetaCarry) * (x * z) +
          m * y * (1 + thetaValue) * (x * z) =
        (m + 1) * y * (1 + thetaY) * (x * z) := by
    calc
      y * (1 + thetaCarry) * (x * z) +
          m * y * (1 + thetaValue) * (x * z) =
          ((1 + thetaCarry) + m * (1 + thetaValue)) *
            y * (x * z) := by
        ring
      _ = ((m + 1) * (1 + thetaY)) * y * (x * z) := by
        rw [hY]
      _ = (m + 1) * y * (1 + thetaY) * (x * z) := by
        ring
  rw [← hD, ← hA, ← hycombine, ← hCarry, ← hValue]
  ring

/-- Coupled coefficientwise backward-error expansion for the first-derivative
component of rounded Algorithm 5.2.

Unlike the quotient-splitting proof below, this theorem keeps the value and
derivative recurrences coupled.  The leading derivative coefficient receives a
weighted average of the two rounded paths, so every coefficient perturbation
stays within the same `gamma (2 * rest.length)` envelope. -/
theorem fl_hornerDerivativeFold_snd_backward_error_coefficients
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (y d : ℝ),
      gammaValid fp (2 * rest.length) →
      ∃ thetaD thetaY : ℝ, ∃ pairs : List (ℝ × ℝ),
        |thetaD| ≤ gamma fp (2 * rest.length) ∧
        |thetaY| ≤ gamma fp (2 * rest.length) ∧
        pairs.map Prod.fst = rest ∧
        (∀ p ∈ pairs, |p.2| ≤ gamma fp (2 * rest.length)) ∧
        (rest.foldl (fl_hornerDerivativeStep fp x) (y, d)).2 =
          d * (1 + thetaD) * x ^ rest.length +
            (rest.length : ℝ) * y * (1 + thetaY) *
              x ^ (rest.length - 1) +
            polyDescPairsDerivPerturbed x pairs := by
  intro rest
  induction rest with
  | nil =>
      intro y d hvalid
      refine ⟨0, 0, [], ?_, ?_, ?_, ?_, ?_⟩
      · simpa using gamma_nonneg fp hvalid
      · simpa using gamma_nonneg fp hvalid
      · simp
      · intro p hp
        simp at hp
      · simp [polyDescPairsDerivPerturbed]
  | cons a rest ih =>
      intro y d hvalid
      let yNext := fl_hornerStep fp x y a
      let dNext := fl_hornerStep fp x d y
      have htailValid : gammaValid fp (2 * rest.length) :=
        gammaValid_mono fp (by simp) hvalid
      obtain ⟨thetaDTail, thetaYTail, pairsTail,
        hthetaDTail, hthetaYTail, hpairsTail, hpairsTailBound,
        hfoldTail⟩ := ih yNext dNext htailValid
      obtain ⟨deltaDMul, hdeltaDMul, hdmul⟩ := fp.model_mul x d
      obtain ⟨deltaDAdd, hdeltaDAdd, hdadd⟩ :=
        fp.model_add (fp.fl_mul x d) y
      obtain ⟨deltaYMul, hdeltaYMul, hymul⟩ := fp.model_mul x y
      obtain ⟨deltaYAdd, hdeltaYAdd, hyadd⟩ :=
        fp.model_add (fp.fl_mul x y) a
      have hdstep :
          dNext = ((x * d) * (1 + deltaDMul) + y) *
            (1 + deltaDAdd) := by
        unfold dNext fl_hornerStep
        rw [hdadd, hdmul]
      have hystep :
          yNext = ((x * y) * (1 + deltaYMul) + a) *
            (1 + deltaYAdd) := by
        unfold yNext fl_hornerStep
        rw [hyadd, hymul]
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
      have hdeltaDMul1 : |deltaDMul| ≤ gamma fp 1 :=
        le_trans hdeltaDMul (u_le_gamma fp one_pos hvalid1)
      have hdeltaDAdd1 : |deltaDAdd| ≤ gamma fp 1 :=
        le_trans hdeltaDAdd (u_le_gamma fp one_pos hvalid1)
      have hdeltaYMul1 : |deltaYMul| ≤ gamma fp 1 :=
        le_trans hdeltaYMul (u_le_gamma fp one_pos hvalid1)
      have hdeltaYAdd1 : |deltaYAdd| ≤ gamma fp 1 :=
        le_trans hdeltaYAdd (u_le_gamma fp one_pos hvalid1)
      obtain ⟨thetaDMulAdd, hthetaDMulAdd, hthetaDMulAddEq⟩ :=
        gamma_mul fp 1 1 deltaDMul deltaDAdd hdeltaDMul1
          hdeltaDAdd1 hvalid2
      obtain ⟨thetaD, hthetaD, hthetaDEq⟩ :=
        gamma_mul fp 2 (2 * rest.length) thetaDMulAdd thetaDTail
          hthetaDMulAdd hthetaDTail hvalid2Tail
      obtain ⟨thetaCarry, hthetaCarry, hthetaCarryEq⟩ :=
        gamma_mul fp 1 (2 * rest.length) deltaDAdd thetaDTail
          hdeltaDAdd1 hthetaDTail hvalid1Tail
      obtain ⟨thetaYMulAdd, hthetaYMulAdd, hthetaYMulAddEq⟩ :=
        gamma_mul fp 1 1 deltaYMul deltaYAdd hdeltaYMul1
          hdeltaYAdd1 hvalid2
      obtain ⟨thetaValue, hthetaValue, hthetaValueEq⟩ :=
        gamma_mul fp 2 (2 * rest.length) thetaYMulAdd thetaYTail
          hthetaYMulAdd hthetaYTail hvalid2Tail
      obtain ⟨thetaA, hthetaA, hthetaAEq⟩ :=
        gamma_mul fp 1 (2 * rest.length) deltaYAdd thetaYTail
          hdeltaYAdd1 hthetaYTail hvalid1Tail
      let thetaY : ℝ :=
        (thetaCarry + (rest.length : ℝ) * thetaValue) /
          ((rest.length : ℝ) + 1)
      have hthetaDFull :
          |thetaD| ≤ gamma fp (2 * (a :: rest).length) :=
        le_trans hthetaD (gamma_mono fp (by simp; omega) hvalid)
      have hthetaCarryFull :
          |thetaCarry| ≤ gamma fp (2 * (a :: rest).length) :=
        le_trans hthetaCarry (gamma_mono fp (by simp; omega) hvalid)
      have hthetaValueFull :
          |thetaValue| ≤ gamma fp (2 * (a :: rest).length) :=
        le_trans hthetaValue (gamma_mono fp (by simp; omega) hvalid)
      have hthetaAFull :
          |thetaA| ≤ gamma fp (2 * (a :: rest).length) :=
        le_trans hthetaA (gamma_mono fp (by simp; omega) hvalid)
      have hgammaFull_nonneg :
          0 ≤ gamma fp (2 * (a :: rest).length) :=
        gamma_nonneg fp hvalid
      have hm_nonneg : 0 ≤ (rest.length : ℝ) := by
        exact_mod_cast rest.length.zero_le
      have hm1_pos : 0 < (rest.length : ℝ) + 1 := by
        exact_mod_cast Nat.succ_pos rest.length
      have hm1_ne : (rest.length : ℝ) + 1 ≠ 0 := ne_of_gt hm1_pos
      have hthetaYFull :
          |thetaY| ≤ gamma fp (2 * (a :: rest).length) := by
        have hnum :
            |thetaCarry + (rest.length : ℝ) * thetaValue| ≤
              ((rest.length : ℝ) + 1) *
                gamma fp (2 * (a :: rest).length) := by
          have hmul_abs :
              |(rest.length : ℝ) * thetaValue| =
                (rest.length : ℝ) * |thetaValue| := by
            rw [abs_mul, abs_of_nonneg hm_nonneg]
          calc
            |thetaCarry + (rest.length : ℝ) * thetaValue| ≤
                |thetaCarry| + |(rest.length : ℝ) * thetaValue| :=
              abs_add_le _ _
            _ = |thetaCarry| + (rest.length : ℝ) * |thetaValue| := by
              rw [hmul_abs]
            _ ≤ gamma fp (2 * (a :: rest).length) +
                (rest.length : ℝ) *
                  gamma fp (2 * (a :: rest).length) := by
              exact add_le_add hthetaCarryFull
                (mul_le_mul_of_nonneg_left hthetaValueFull hm_nonneg)
            _ = ((rest.length : ℝ) + 1) *
                gamma fp (2 * (a :: rest).length) := by
              ring
        calc
          |thetaY| =
              |thetaCarry + (rest.length : ℝ) * thetaValue| /
                ((rest.length : ℝ) + 1) := by
            simp [thetaY, abs_div, abs_of_pos hm1_pos]
          _ ≤ (((rest.length : ℝ) + 1) *
                gamma fp (2 * (a :: rest).length)) /
                ((rest.length : ℝ) + 1) :=
            div_le_div_of_nonneg_right hnum (le_of_lt hm1_pos)
          _ = gamma fp (2 * (a :: rest).length) := by
            field_simp [hm1_ne]
      refine ⟨thetaD, thetaY, (a, thetaA) :: pairsTail,
        hthetaDFull, hthetaYFull, ?_, ?_, ?_⟩
      · simp [hpairsTail]
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · rcases hp
          exact hthetaAFull
        · exact le_trans (hpairsTailBound p hp)
            (gamma_mono fp (by simp) hvalid)
      · have hpairsLen : pairsTail.length = rest.length := by
          have hlen := congrArg List.length hpairsTail
          simpa using hlen
        have hthetaDProd :
            (1 + deltaDMul) * (1 + deltaDAdd) *
                (1 + thetaDTail) =
              1 + thetaD := by
          rw [hthetaDMulAddEq, hthetaDEq]
        have hthetaCarryProd :
            (1 + deltaDAdd) * (1 + thetaDTail) =
              1 + thetaCarry :=
          hthetaCarryEq
        have hthetaValueProd :
            (1 + deltaYMul) * (1 + deltaYAdd) *
                (1 + thetaYTail) =
              1 + thetaValue := by
          rw [hthetaYMulAddEq, hthetaValueEq]
        have hthetaAProd :
            (1 + deltaYAdd) * (1 + thetaYTail) =
              1 + thetaA :=
          hthetaAEq
        have hthetaYAvg :
            (1 + thetaCarry) +
                (rest.length : ℝ) * (1 + thetaValue) =
              ((rest.length : ℝ) + 1) * (1 + thetaY) := by
          dsimp [thetaY]
          field_simp [hm1_ne]
          ring
        have hstepPair :
            fl_hornerDerivativeStep fp x (y, d) a = (yNext, dNext) := by
          simp [fl_hornerDerivativeStep, yNext, dNext]
        simp only [List.foldl]
        rw [hstepPair, hfoldTail, hdstep, hystep]
        cases rest with
        | nil =>
            simp [polyDescPairsDerivPerturbed, hpairsLen]
            have hthetaYEq : thetaY = thetaCarry := by
              dsimp [thetaY]
              norm_num
            rw [hthetaYEq]
            simpa [mul_comm, mul_left_comm, mul_assoc, add_comm,
              add_left_comm, add_assoc] using
              fl_hornerDerivativeStep_backward_algebra_nil
                x d y deltaDMul deltaDAdd thetaDTail thetaD thetaCarry
                hthetaDProd hthetaCarryProd
        | cons b tail =>
            have halg :=
              fl_hornerDerivativeStep_backward_algebra_cons
                x (x ^ tail.length) ((b :: tail).length : ℝ) d y a
                deltaDMul deltaDAdd deltaYMul deltaYAdd thetaDTail
                thetaYTail thetaD thetaCarry thetaValue thetaA thetaY
                hthetaDProd hthetaCarryProd hthetaValueProd hthetaAProd
                hthetaYAvg
            have halgTail :=
              congrArg
                (fun t => t + polyDescPairsDerivPerturbed x pairsTail)
                halg
            have hpowRest :
                x ^ tail.length * x = x * x ^ tail.length := by
              ring
            have hpowRestSucc :
                x ^ (tail.length + 1) = x * x ^ tail.length := by
              rw [pow_succ]
              ring
            have hpowFull :
                x ^ (tail.length + (1 + 1)) =
                  x * (x * x ^ tail.length) := by
              rw [show tail.length + (1 + 1) = tail.length + 2 by omega]
              rw [pow_add]
              ring
            have hpowFullPred :
                x ^ (tail.length + (1 + 1) - 1) =
                  x * x ^ tail.length := by
              rw [show tail.length + (1 + 1) - 1 =
                  tail.length + 1 by omega]
              rw [pow_succ]
              ring
            simpa only [polyDescPairsDerivPerturbed, hpairsLen,
              List.length_cons, Nat.succ_sub_one, Nat.cast_add,
              Nat.cast_one, hpowRest, hpowRestSucc, hpowFull,
              hpowFullPred, mul_assoc, add_assoc] using halgTail

/-- Direct coupled backward-error form of Higham (5.7) for the first
derivative: the rounded derivative output is the exact derivative of a
coefficientwise-perturbed polynomial, with every coefficient perturbation
bounded by `gamma (2 * (coeffsDesc.length - 1))`. -/
theorem fl_hornerDerivativeDesc_snd_backward_error_coefficients_coupled
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    ∃ pairs : List (ℝ × ℝ),
      pairs.map Prod.fst = coeffsDesc ∧
      (∀ p ∈ pairs,
        |p.2| ≤ gamma fp (2 * (coeffsDesc.length - 1))) ∧
      (fl_hornerDerivativeDesc fp x coeffsDesc).2 =
        polyDescPairsDerivPerturbed x pairs := by
  cases coeffsDesc with
  | nil =>
      refine ⟨[], ?_, ?_, ?_⟩
      · simp
      · intro p hp
        simp at hp
      · simp [fl_hornerDerivativeDesc, polyDescPairsDerivPerturbed]
  | cons a rest =>
      have hrestValid : gammaValid fp (2 * rest.length) := by
        simpa using hvalid
      obtain ⟨thetaD, thetaY, pairsRest, _hthetaD, hthetaY,
        hpairsRest, hpairsRestBound, hfold⟩ :=
          fl_hornerDerivativeFold_snd_backward_error_coefficients
            fp x rest a 0 hrestValid
      refine ⟨(a, thetaY) :: pairsRest, ?_, ?_, ?_⟩
      · simp [hpairsRest]
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · rcases hp
          simpa using hthetaY
        · simpa using hpairsRestBound p hp
      · have hpairsLen : pairsRest.length = rest.length := by
          have hlen := congrArg List.length hpairsRest
          simpa using hlen
        simpa [fl_hornerDerivativeDesc, polyDescPairsDerivPerturbed,
          hpairsLen, mul_assoc] using hfold

/-- Direct coupled forward-error form for the first derivative.  This closes
the (5.7) finite precursor without routing through the computed synthetic
quotient budget. -/
theorem fl_hornerDerivativeDesc_snd_forward_error_bound_coupled
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
        polyDescDeriv x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) *
        polyDescDerivAbs x coeffsDesc := by
  obtain ⟨pairs, hpairs, hpairsBound, hfl⟩ :=
    fl_hornerDerivativeDesc_snd_backward_error_coefficients_coupled
      fp x coeffsDesc hvalid
  have hpert :=
    abs_polyDescPairsDerivPerturbed_sub_polyDescPairsDeriv_le x
      (gamma fp (2 * (coeffsDesc.length - 1)))
      (gamma_nonneg fp hvalid) pairs hpairsBound
  have hpoly :
      polyDescPairsDeriv x pairs = polyDescDeriv x coeffsDesc := by
    rw [polyDescPairsDeriv_eq_polyDescDeriv_map_fst, hpairs]
  have habs :
      polyDescPairsDerivAbs x pairs = polyDescDerivAbs x coeffsDesc := by
    rw [polyDescPairsDerivAbs_eq_polyDescDerivAbs_map_fst, hpairs]
  simpa [hfl, hpoly, habs] using hpert

/-- Quadratic-and-higher gamma remainder in the direct first-derivative
bound. -/
noncomputable def fl_hornerDerivativeDescFirstOrderRemainder
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) : ℝ :=
  let nops : ℕ := 2 * (coeffsDesc.length - 1)
  ((((nops : ℝ) * fp.u) ^ 2) /
      (1 - (nops : ℝ) * fp.u)) *
    polyDescDerivAbs x coeffsDesc

theorem fl_hornerDerivativeDescFirstOrderRemainder_eq_zero_of_u_eq_zero
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) (hu : fp.u = 0) :
    fl_hornerDerivativeDescFirstOrderRemainder fp x coeffsDesc = 0 := by
  simp [fl_hornerDerivativeDescFirstOrderRemainder, hu]

/-- Higham (5.7), direct first-order derivative error display:
`2*n*u*ptilde'(x)` plus the explicit quadratic-and-higher gamma remainder. -/
theorem fl_hornerDerivativeDesc_first_derivative_error_bound
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
        polyDescDeriv x coeffsDesc| ≤
      (((2 * (coeffsDesc.length - 1) : ℕ) : ℝ) * fp.u) *
          polyDescDerivAbs x coeffsDesc +
        fl_hornerDerivativeDescFirstOrderRemainder fp x coeffsDesc := by
  let nops : ℕ := 2 * (coeffsDesc.length - 1)
  let D : ℝ := polyDescDerivAbs x coeffsDesc
  have hbase :=
    fl_hornerDerivativeDesc_snd_forward_error_bound_coupled
      fp x coeffsDesc hvalid
  have hgamma :
      gamma fp nops =
        (nops : ℝ) * fp.u +
          (((nops : ℝ) * fp.u) ^ 2) /
            (1 - (nops : ℝ) * fp.u) := by
    simpa [nops] using gamma_eq_linear_plus_quadratic_remainder
      fp nops hvalid
  have hrewrite :
      gamma fp nops * D =
        ((nops : ℝ) * fp.u) * D +
          fl_hornerDerivativeDescFirstOrderRemainder fp x coeffsDesc := by
    unfold fl_hornerDerivativeDescFirstOrderRemainder
    dsimp [nops, D]
    rw [hgamma]
    ring
  simpa [nops, D] using le_trans hbase (le_of_eq hrewrite)

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

/-- Higham (5.6), second-solve component: the rounded first-derivative output
is exact evaluation of a componentwise-perturbed version of the computed
synthetic-division quotient.  The remaining (5.5) part is the perturbation of
that computed quotient relative to the exact quotient. -/
theorem fl_hornerDerivativeDesc_snd_backward_error_coefficients
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    ∃ pairs : List (ℝ × ℝ),
      pairs.map Prod.fst =
        fl_hornerSyntheticQuotientDesc fp x coeffsDesc ∧
      (∀ p ∈ pairs,
        |p.2| ≤ gamma fp (2 * (coeffsDesc.length - 1))) ∧
      (fl_hornerDerivativeDesc fp x coeffsDesc).2 =
        polyDescPairsPerturbed x pairs := by
  let qhat := fl_hornerSyntheticQuotientDesc fp x coeffsDesc
  have hqLen :
      qhat.length = coeffsDesc.length - 1 := by
    simpa [qhat] using
      fl_hornerSyntheticQuotientDesc_length fp x coeffsDesc
  have hvalidQ : gammaValid fp (2 * qhat.length) := by
    simpa [hqLen] using hvalid
  obtain ⟨pairs, hpairs, hpairsBound, hfl⟩ :=
    fl_hornerFoldFromZeroDesc_backward_error_coefficients fp x qhat
      hvalidQ
  refine ⟨pairs, ?_, ?_, ?_⟩
  · simpa [qhat] using hpairs
  · intro p hp
    simpa [hqLen] using hpairsBound p hp
  · exact Eq.trans
      (fl_hornerDerivativeDesc_snd_eq_fl_hornerFoldFromZero_fl_synthetic_quotient
        fp x coeffsDesc)
      (by simpa [qhat] using hfl)

/-- Higham (5.6), second-solve forward form: the derivative component is close
to exact evaluation of the computed synthetic-division quotient. -/
theorem fl_hornerDerivativeDesc_snd_forward_error_bound_to_fl_quotient
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    let qhat := fl_hornerSyntheticQuotientDesc fp x coeffsDesc
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
        polyDesc x qhat| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) * polyDescAbs x qhat := by
  dsimp
  obtain ⟨pairs, hpairs, hpairsBound, hfl⟩ :=
    fl_hornerDerivativeDesc_snd_backward_error_coefficients fp x coeffsDesc
      hvalid
  have hpert :=
    abs_polyDescPairsPerturbed_sub_polyDescPairs_le x
      (gamma fp (2 * (coeffsDesc.length - 1)))
      (gamma_nonneg fp hvalid) pairs hpairsBound
  have hpoly :
      polyDescPairs x pairs =
        polyDesc x (fl_hornerSyntheticQuotientDesc fp x coeffsDesc) := by
    rw [polyDescPairs_eq_polyDesc_map_fst, hpairs]
  have habs :
      polyDescPairsAbs x pairs =
      polyDescAbs x (fl_hornerSyntheticQuotientDesc fp x coeffsDesc) := by
    rw [polyDescPairsAbs_eq_polyDescAbs_map_fst, hpairs]
  simpa [hfl, hpoly, habs] using hpert

/-- Reduction of the first-derivative error to the two source subproblems in
(5.5)-(5.6): the rounded derivative solve over the computed quotient, plus the
remaining error in the computed synthetic-division quotient itself. -/
theorem fl_hornerDerivativeDesc_snd_error_bound_via_fl_quotient
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    let qhat := fl_hornerSyntheticQuotientDesc fp x coeffsDesc
    let q := hornerSyntheticQuotientDesc x coeffsDesc
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
        polyDescDeriv x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) * polyDescAbs x qhat +
        |polyDesc x qhat - polyDesc x q| := by
  dsimp
  have hsolve :=
    fl_hornerDerivativeDesc_snd_forward_error_bound_to_fl_quotient
      fp x coeffsDesc hvalid
  have hqExact :
      polyDesc x (hornerSyntheticQuotientDesc x coeffsDesc) =
        polyDescDeriv x coeffsDesc :=
    hornerSyntheticQuotientDesc_eval_eq_polyDescDeriv x coeffsDesc
  have hsplit :
      (fl_hornerDerivativeDesc fp x coeffsDesc).2 -
          polyDescDeriv x coeffsDesc =
        ((fl_hornerDerivativeDesc fp x coeffsDesc).2 -
          polyDesc x (fl_hornerSyntheticQuotientDesc fp x coeffsDesc)) +
        (polyDesc x (fl_hornerSyntheticQuotientDesc fp x coeffsDesc) -
          polyDesc x (hornerSyntheticQuotientDesc x coeffsDesc)) := by
    rw [hqExact]
    ring
  rw [hsplit]
  exact le_trans (abs_add_le _ _)
    (add_le_add hsolve (le_refl _))

/-! ## Equation (5.5): bidiagonal synthetic-division system -/

/-- Higham Chapter 5, equation (5.5): the unit upper-bidiagonal matrix
`U_n(alpha)` with diagonal entries `1` and superdiagonal entries `-alpha`.
For coefficient vectors in ascending order, the exact synthetic-division
coefficients satisfy `U_n(alpha) q = a`. -/
noncomputable def highamBidiagonalU (alpha : ℝ) (n : ℕ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if j.val = i.val then 1
    else if j.val = i.val + 1 then -alpha
    else 0

theorem highamBidiagonalU_diag
    (alpha : ℝ) (n : ℕ) (i : Fin n) :
    highamBidiagonalU alpha n i i = 1 := by
  simp [highamBidiagonalU]

theorem highamBidiagonalU_superdiag
    (alpha : ℝ) (n : ℕ) (i j : Fin n)
    (hij : j.val = i.val + 1) :
    highamBidiagonalU alpha n i j = -alpha := by
  simp [highamBidiagonalU, hij]

theorem highamBidiagonalU_zero_of_not_diag_not_superdiag
    (alpha : ℝ) (n : ℕ) (i j : Fin n)
    (hdiag : j.val ≠ i.val) (hsuper : j.val ≠ i.val + 1) :
    highamBidiagonalU alpha n i j = 0 := by
  simp [highamBidiagonalU, hdiag, hsuper]

/-- Source-shaped componentwise majorant in (5.5):
`epsilon * |U^{-1}| |U| |qhat|`. -/
noncomputable def highamBidiagonalForwardErrorMajorant
    (alpha : ℝ) (n : ℕ) (Uinv : Fin n → Fin n → ℝ)
    (epsilon : ℝ) (qhat : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    epsilon *
      ∑ j : Fin n,
        |Uinv i j| *
          (∑ k : Fin n,
            |highamBidiagonalU alpha n j k| * |qhat k|)

/-- Higham (5.5), exact finite matrix bridge.  If `q` solves the exact
bidiagonal synthetic-division system `U q = a`, while `qhat` solves a
componentwise perturbed system `(U + DeltaU) qhat = a` with
`|DeltaU| <= epsilon |U|`, then the componentwise error is bounded by the
source matrix expression `epsilon |U^{-1}| |U| |qhat|`.

This is the exact version of the displayed first-order matrix form; replacing
`|qhat|` by `|q|` is the separate first-order/O(u^2) simplification tracked
under (5.7). -/
theorem highamBidiagonal_forward_error_from_backward
    (alpha : ℝ) (n : ℕ)
    (Uinv : Fin n → Fin n → ℝ)
    (q qhat a : Fin n → ℝ)
    (DeltaU : Fin n → Fin n → ℝ)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hInv : IsLeftInverse n (highamBidiagonalU alpha n) Uinv)
    (hUq :
      ∀ i : Fin n,
        ∑ j : Fin n, highamBidiagonalU alpha n i j * q j = a i)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (highamBidiagonalU alpha n i j + DeltaU i j) * qhat j =
            a i)
    (hDelta :
      ∀ i j : Fin n,
        |DeltaU i j| ≤ epsilon * |highamBidiagonalU alpha n i j|) :
    ∀ i : Fin n,
      |q i - qhat i| ≤
        highamBidiagonalForwardErrorMajorant alpha n Uinv epsilon qhat i := by
  intro i
  simpa [highamBidiagonalForwardErrorMajorant] using
    forward_error_from_backward_componentwise n
      (highamBidiagonalU alpha n) Uinv q qhat a DeltaU epsilon
      hepsilon hInv hUq hPerturbed hDelta i

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

/-- Source-shaped version of the computed-quotient evaluation majorant.  It
replaces rounded accumulators by exact accumulators plus an explicit propagated
error bound, which is the next bridge toward the first-order (5.7) display. -/
noncomputable def fl_hornerSyntheticQuotientEvalForwardSourceMajorant
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ → ℝ → ℝ
  | [], _y, _eps => 0
  | [_a0], _y, eps => eps
  | a :: b :: rest, y, eps =>
      eps * |x| ^ (b :: rest).length +
        fl_hornerSyntheticQuotientEvalForwardSourceMajorant fp x (b :: rest)
          (hornerStep x y a)
          (fp.u * ((2 + fp.u) * (|x| * (|y| + eps)) + |a|) +
            |x| * eps)

/-- Whole-polynomial specialization of the source-shaped computed-quotient
majorant, starting from the shared leading coefficient and zero accumulated
error. -/
noncomputable def fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | [_a] => 0
  | a :: b :: rest =>
      fl_hornerSyntheticQuotientEvalForwardSourceMajorant fp x
        (b :: rest) a 0

lemma fl_hornerSyntheticQuotientEvalForwardSourceMajorant_nonneg
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (y eps : ℝ),
      0 ≤ eps →
      0 ≤ fl_hornerSyntheticQuotientEvalForwardSourceMajorant fp x rest
        y eps := by
  intro rest
  induction rest with
  | nil =>
      intro y eps _heps
      simp [fl_hornerSyntheticQuotientEvalForwardSourceMajorant]
  | cons a rest ih =>
      intro y eps heps
      cases rest with
      | nil =>
          simpa [fl_hornerSyntheticQuotientEvalForwardSourceMajorant] using
            heps
      | cons b tail =>
          have hcoef : 0 ≤ 2 + fp.u := by nlinarith [fp.u_nonneg]
          have hy_eps : 0 ≤ |y| + eps :=
            add_nonneg (abs_nonneg y) heps
          have hinside :
              0 ≤ (2 + fp.u) * (|x| * (|y| + eps)) + |a| := by
            exact add_nonneg
              (mul_nonneg hcoef
                (mul_nonneg (abs_nonneg x) hy_eps))
              (abs_nonneg a)
          have hepsNext :
              0 ≤ fp.u *
                    ((2 + fp.u) * (|x| * (|y| + eps)) + |a|) +
                  |x| * eps := by
            exact add_nonneg
              (mul_nonneg fp.u_nonneg hinside)
              (mul_nonneg (abs_nonneg x) heps)
          have hhead :
              0 ≤ eps * |x| ^ (b :: tail).length :=
            mul_nonneg heps (pow_nonneg (abs_nonneg x) _)
          have htail :=
            ih (hornerStep x y a)
              (fp.u * ((2 + fp.u) * (|x| * (|y| + eps)) + |a|) +
                |x| * eps)
              hepsNext
          simpa [fl_hornerSyntheticQuotientEvalForwardSourceMajorant]
            using add_nonneg hhead htail

theorem fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant_nonneg
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    0 ≤ fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant fp x
      coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
            using
              fl_hornerSyntheticQuotientEvalForwardSourceMajorant_nonneg
                fp x (b :: tail) a 0 (by norm_num)

lemma fl_hornerSyntheticQuotientEvalForwardSourceMajorant_eq_zero_of_u_eq_zero_of_eps_eq_zero
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (y eps : ℝ),
      fp.u = 0 →
      eps = 0 →
      fl_hornerSyntheticQuotientEvalForwardSourceMajorant fp x rest
        y eps = 0 := by
  intro rest
  induction rest with
  | nil =>
      intro y eps _hu _heps
      simp [fl_hornerSyntheticQuotientEvalForwardSourceMajorant]
  | cons a rest ih =>
      intro y eps hu heps
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientEvalForwardSourceMajorant, heps]
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientEvalForwardSourceMajorant,
            hu, heps] using
            ih (hornerStep x y a) 0 hu rfl

theorem fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant_eq_zero_of_u_eq_zero
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) (hu : fp.u = 0) :
    fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant fp x coeffsDesc =
      0 := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
            using
              fl_hornerSyntheticQuotientEvalForwardSourceMajorant_eq_zero_of_u_eq_zero_of_eps_eq_zero
                fp x (b :: tail) a 0 hu rfl

/-- A finite, list-level forward majorant for the error in evaluating the
computed synthetic-division quotient against the exact one.  The argument
`eps` is a bound for the current value-accumulator error. -/
noncomputable def fl_hornerSyntheticQuotientEvalForwardMajorant
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ → ℝ → ℝ → ℝ
  | [], _yhat, _y, _eps => 0
  | [_a0], _yhat, _y, eps => eps
  | a :: b :: rest, yhat, y, eps =>
      eps * |x| ^ (b :: rest).length +
        fl_hornerSyntheticQuotientEvalForwardMajorant fp x (b :: rest)
          (fl_hornerStep fp x yhat a)
          (hornerStep x y a)
          (fl_hornerStepForwardErrorBudget fp x yhat a + |x| * eps)

/-- The whole-polynomial specialization of
`fl_hornerSyntheticQuotientEvalForwardMajorant`, starting from equal exact and
rounded leading accumulators. -/
noncomputable def fl_hornerSyntheticQuotientDescEvalForwardMajorant
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | [_a] => 0
  | a :: b :: rest =>
      fl_hornerSyntheticQuotientEvalForwardMajorant fp x (b :: rest) a a 0

/-- The rounded-data quotient-evaluation budget is dominated by the
source-shaped budget using the exact accumulator and an explicit error bound. -/
theorem fl_hornerSyntheticQuotientEvalForwardMajorant_le_source_majorant
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (yhat y eps epsBound : ℝ),
      0 ≤ eps →
      |yhat - y| ≤ eps →
      eps ≤ epsBound →
      fl_hornerSyntheticQuotientEvalForwardMajorant fp x rest
        yhat y eps ≤
        fl_hornerSyntheticQuotientEvalForwardSourceMajorant fp x rest
          y epsBound := by
  intro rest
  induction rest with
  | nil =>
      intro yhat y eps epsBound _heps _herr _heps_le
      simp [fl_hornerSyntheticQuotientEvalForwardMajorant,
        fl_hornerSyntheticQuotientEvalForwardSourceMajorant]
  | cons a rest ih =>
      intro yhat y eps epsBound heps herr heps_le
      cases rest with
      | nil =>
          simpa [fl_hornerSyntheticQuotientEvalForwardMajorant,
            fl_hornerSyntheticQuotientEvalForwardSourceMajorant]
            using heps_le
      | cons b tail =>
          let epsNext :=
            fl_hornerStepForwardErrorBudget fp x yhat a + |x| * eps
          let epsBoundNext :=
            fp.u * ((2 + fp.u) * (|x| * (|y| + epsBound)) + |a|) +
              |x| * epsBound
          have hepsBound_nonneg : 0 ≤ epsBound :=
            le_trans heps heps_le
          have hepsNext_nonneg : 0 ≤ epsNext := by
            exact add_nonneg
              (fl_hornerStepForwardErrorBudget_nonneg fp x yhat a)
              (mul_nonneg (abs_nonneg x) heps)
          have herrNext :
              |fl_hornerStep fp x yhat a - hornerStep x y a| ≤
                epsNext := by
            have hlocal :
                |fl_hornerStep fp x yhat a - hornerStep x yhat a| ≤
                  fl_hornerStepForwardErrorBudget fp x yhat a := by
              simpa [fl_hornerStepForwardErrorBudget]
                using fl_hornerStep_forward_local_error_bound fp x yhat a
            have hexact :
                |hornerStep x yhat a - hornerStep x y a| ≤
                  |x| * eps := by
              have hdiff :
                  hornerStep x yhat a - hornerStep x y a =
                    x * (yhat - y) := by
                unfold hornerStep
                ring
              rw [hdiff, abs_mul]
              exact mul_le_mul_of_nonneg_left herr (abs_nonneg x)
            have htri :
                |fl_hornerStep fp x yhat a - hornerStep x y a| ≤
                  |fl_hornerStep fp x yhat a - hornerStep x yhat a| +
                    |hornerStep x yhat a - hornerStep x y a| := by
              have hsplit :
                  fl_hornerStep fp x yhat a - hornerStep x y a =
                    (fl_hornerStep fp x yhat a -
                      hornerStep x yhat a) +
                    (hornerStep x yhat a - hornerStep x y a) := by
                ring
              rw [hsplit]
              exact abs_add_le _ _
            exact le_trans htri (by
              dsimp [epsNext]
              exact add_le_add hlocal hexact)
          have hlocalBound :
              fl_hornerStepForwardErrorBudget fp x yhat a ≤
                fp.u *
                  ((2 + fp.u) * (|x| * (|y| + epsBound)) + |a|) := by
            exact
              fl_hornerStepForwardErrorBudget_le_exact_abs_plus_error
                fp x yhat y a epsBound hepsBound_nonneg
                (le_trans herr heps_le)
          have heps_x_le :
              |x| * eps ≤ |x| * epsBound :=
            mul_le_mul_of_nonneg_left heps_le (abs_nonneg x)
          have hepsNext_le : epsNext ≤ epsBoundNext := by
            dsimp [epsNext, epsBoundNext]
            exact add_le_add hlocalBound heps_x_le
          have htail :=
            ih (fl_hornerStep fp x yhat a) (hornerStep x y a)
              epsNext epsBoundNext hepsNext_nonneg herrNext hepsNext_le
          have hpow_nonneg :
              0 ≤ |x| ^ (b :: tail).length :=
            pow_nonneg (abs_nonneg x) _
          have hhead :
              eps * |x| ^ (b :: tail).length ≤
                epsBound * |x| ^ (b :: tail).length :=
            mul_le_mul_of_nonneg_right heps_le hpow_nonneg
          have hcombine :=
            add_le_add hhead htail
          simpa [fl_hornerSyntheticQuotientEvalForwardMajorant,
            fl_hornerSyntheticQuotientEvalForwardSourceMajorant,
            epsNext, epsBoundNext] using hcombine

theorem fl_hornerSyntheticQuotientDescEvalForwardMajorant_le_source_majorant
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x coeffsDesc ≤
      fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant fp x
        coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerSyntheticQuotientDescEvalForwardMajorant,
        fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientDescEvalForwardMajorant,
            fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientDescEvalForwardMajorant,
            fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant]
            using
              fl_hornerSyntheticQuotientEvalForwardMajorant_le_source_majorant
                fp x (b :: tail) a a 0 0 (by norm_num) (by simp)
                (by norm_num)

lemma fl_hornerSyntheticQuotientEvalForwardMajorant_nonneg
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (yhat y eps : ℝ),
      0 ≤ eps →
      0 ≤ fl_hornerSyntheticQuotientEvalForwardMajorant fp x rest
        yhat y eps := by
  intro rest
  induction rest with
  | nil =>
      intro yhat y eps _heps
      simp [fl_hornerSyntheticQuotientEvalForwardMajorant]
  | cons a rest ih =>
      intro yhat y eps heps
      cases rest with
      | nil =>
          simpa [fl_hornerSyntheticQuotientEvalForwardMajorant] using heps
      | cons b tail =>
          have hnext :
              0 ≤ fl_hornerStepForwardErrorBudget fp x yhat a +
                  |x| * eps := by
            exact add_nonneg
              (fl_hornerStepForwardErrorBudget_nonneg fp x yhat a)
              (mul_nonneg (abs_nonneg x) heps)
          have hhead :
              0 ≤ eps * |x| ^ (b :: tail).length :=
            mul_nonneg heps (pow_nonneg (abs_nonneg x) _)
          have htail :=
            ih (fl_hornerStep fp x yhat a) (hornerStep x y a)
              (fl_hornerStepForwardErrorBudget fp x yhat a + |x| * eps)
              hnext
          simpa [fl_hornerSyntheticQuotientEvalForwardMajorant]
            using add_nonneg hhead htail

theorem fl_hornerSyntheticQuotientDescEvalForwardMajorant_nonneg
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    0 ≤ fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x
      coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerSyntheticQuotientDescEvalForwardMajorant]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientDescEvalForwardMajorant]
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientDescEvalForwardMajorant] using
            fl_hornerSyntheticQuotientEvalForwardMajorant_nonneg fp x
              (b :: tail) a a 0 (by norm_num)

lemma fl_hornerSyntheticQuotientFold_abs_le_exact_abs_plus_eval_majorant
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (yhat y eps : ℝ),
      0 ≤ eps →
      |yhat - y| ≤ eps →
      polyDescAbs x (fl_hornerSyntheticQuotientFold fp x yhat rest) ≤
        polyDescAbs x (hornerSyntheticQuotientFold x y rest) +
          fl_hornerSyntheticQuotientEvalForwardMajorant fp x rest
            yhat y eps := by
  intro rest
  induction rest with
  | nil =>
      intro yhat y eps _heps _herr
      simp [fl_hornerSyntheticQuotientFold,
        hornerSyntheticQuotientFold,
        fl_hornerSyntheticQuotientEvalForwardMajorant, polyDescAbs]
  | cons a rest ih =>
      intro yhat y eps heps herr
      cases rest with
      | nil =>
          have hyabs : |yhat| ≤ |y| + eps := by
            have htri : |yhat| ≤ |y| + |yhat - y| := by
              calc
                |yhat| = |y + (yhat - y)| := by
                  congr 1
                  ring
                _ ≤ |y| + |yhat - y| := abs_add_le _ _
            linarith
          simpa [fl_hornerSyntheticQuotientFold,
            hornerSyntheticQuotientFold,
            fl_hornerSyntheticQuotientEvalForwardMajorant, polyDescAbs]
            using hyabs
      | cons b tail =>
          let epsNext :=
            fl_hornerStepForwardErrorBudget fp x yhat a + |x| * eps
          have hepsNext : 0 ≤ epsNext := by
            exact add_nonneg
              (fl_hornerStepForwardErrorBudget_nonneg fp x yhat a)
              (mul_nonneg (abs_nonneg x) heps)
          have herrNext :
              |fl_hornerStep fp x yhat a - hornerStep x y a| ≤
                epsNext := by
            have hlocal :
                |fl_hornerStep fp x yhat a - hornerStep x yhat a| ≤
                  fl_hornerStepForwardErrorBudget fp x yhat a := by
              simpa [fl_hornerStepForwardErrorBudget]
                using fl_hornerStep_forward_local_error_bound fp x yhat a
            have hexact :
                |hornerStep x yhat a - hornerStep x y a| ≤
                  |x| * eps := by
              have hdiff :
                  hornerStep x yhat a - hornerStep x y a =
                    x * (yhat - y) := by
                unfold hornerStep
                ring
              rw [hdiff, abs_mul]
              exact mul_le_mul_of_nonneg_left herr (abs_nonneg x)
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
            simpa [epsNext] using
              le_trans htri (add_le_add hlocal hexact)
          have htail :=
            ih (fl_hornerStep fp x yhat a) (hornerStep x y a)
              epsNext hepsNext herrNext
          have hlenFl :
              (fl_hornerSyntheticQuotientFold fp x
                  (fl_hornerStep fp x yhat a) (b :: tail)).length =
                (b :: tail).length :=
            fl_hornerSyntheticQuotientFold_length fp x (b :: tail)
              (fl_hornerStep fp x yhat a)
          have hlenExact :
              (hornerSyntheticQuotientFold x (hornerStep x y a)
                  (b :: tail)).length = (b :: tail).length :=
            hornerSyntheticQuotientFold_length x (b :: tail)
              (hornerStep x y a)
          have hpow_nonneg :
              0 ≤ |x| ^ (b :: tail).length :=
            pow_nonneg (abs_nonneg x) _
          have hyabs : |yhat| ≤ |y| + eps := by
            have htri : |yhat| ≤ |y| + |yhat - y| := by
              calc
                |yhat| = |y + (yhat - y)| := by
                  congr 1
                  ring
                _ ≤ |y| + |yhat - y| := abs_add_le _ _
            linarith
          have hhead :
              |yhat| * |x| ^ (b :: tail).length ≤
                |y| * |x| ^ (b :: tail).length +
                  eps * |x| ^ (b :: tail).length := by
            calc
              |yhat| * |x| ^ (b :: tail).length ≤
                  (|y| + eps) * |x| ^ (b :: tail).length :=
                mul_le_mul_of_nonneg_right hyabs hpow_nonneg
              _ = |y| * |x| ^ (b :: tail).length +
                  eps * |x| ^ (b :: tail).length := by ring
          have hcombine :
              |yhat| * |x| ^ (b :: tail).length +
                  polyDescAbs x
                    (fl_hornerSyntheticQuotientFold fp x
                      (fl_hornerStep fp x yhat a) (b :: tail)) ≤
                |y| * |x| ^ (b :: tail).length +
                  polyDescAbs x
                    (hornerSyntheticQuotientFold x
                      (hornerStep x y a) (b :: tail)) +
                  (eps * |x| ^ (b :: tail).length +
                    fl_hornerSyntheticQuotientEvalForwardMajorant fp x
                      (b :: tail) (fl_hornerStep fp x yhat a)
                      (hornerStep x y a) epsNext) := by
            nlinarith [hhead, htail]
          simpa [fl_hornerSyntheticQuotientFold,
            hornerSyntheticQuotientFold, polyDescAbs, hlenFl, hlenExact,
            fl_hornerSyntheticQuotientEvalForwardMajorant, epsNext]
            using hcombine

theorem fl_hornerSyntheticQuotientDesc_abs_le_exact_abs_plus_eval_majorant
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    polyDescAbs x (fl_hornerSyntheticQuotientDesc fp x coeffsDesc) ≤
      polyDescAbs x (hornerSyntheticQuotientDesc x coeffsDesc) +
        fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerSyntheticQuotientDesc,
        hornerSyntheticQuotientDesc, polyDescAbs,
        fl_hornerSyntheticQuotientDescEvalForwardMajorant]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientDesc,
            hornerSyntheticQuotientDesc, polyDescAbs,
            fl_hornerSyntheticQuotientDescEvalForwardMajorant]
      | cons b tail =>
          have h :=
            fl_hornerSyntheticQuotientFold_abs_le_exact_abs_plus_eval_majorant
              fp x (b :: tail) a a 0 (by norm_num) (by simp)
          simpa [fl_hornerSyntheticQuotientDesc,
            hornerSyntheticQuotientDesc,
            fl_hornerSyntheticQuotientDescEvalForwardMajorant] using h

theorem fl_hornerSyntheticQuotientDesc_abs_le_derivAbs_plus_eval_majorant
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    polyDescAbs x (fl_hornerSyntheticQuotientDesc fp x coeffsDesc) ≤
      polyDescDerivAbs x coeffsDesc +
        fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x coeffsDesc := by
  exact le_trans
    (fl_hornerSyntheticQuotientDesc_abs_le_exact_abs_plus_eval_majorant
      fp x coeffsDesc)
    (add_le_add
      (polyDescAbs_hornerSyntheticQuotientDesc_le_polyDescDerivAbs
        x coeffsDesc)
      (le_refl _))

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

/-- List-level forward bound for the computed synthetic-division quotient.

This is the scalar/evaluation form of the remaining (5.5) quotient
perturbation: it bounds the difference between evaluating the rounded quotient
stream and evaluating the exact synthetic-division quotient stream. -/
theorem fl_hornerSyntheticQuotientFold_eval_forward_error_bound
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (yhat y eps : ℝ),
      0 ≤ eps →
      |yhat - y| ≤ eps →
      |polyDesc x (fl_hornerSyntheticQuotientFold fp x yhat rest) -
          polyDesc x (hornerSyntheticQuotientFold x y rest)| ≤
        fl_hornerSyntheticQuotientEvalForwardMajorant fp x rest
          yhat y eps := by
  intro rest
  induction rest with
  | nil =>
      intro yhat y eps _heps _herr
      simp [fl_hornerSyntheticQuotientFold,
        hornerSyntheticQuotientFold,
        fl_hornerSyntheticQuotientEvalForwardMajorant, polyDesc]
  | cons a rest ih =>
      intro yhat y eps heps herr
      cases rest with
      | nil =>
          simpa [fl_hornerSyntheticQuotientFold,
            hornerSyntheticQuotientFold,
            fl_hornerSyntheticQuotientEvalForwardMajorant, polyDesc]
            using herr
      | cons b tail =>
          let epsNext :=
            fl_hornerStepForwardErrorBudget fp x yhat a + |x| * eps
          have hepsNext : 0 ≤ epsNext := by
            exact add_nonneg
              (fl_hornerStepForwardErrorBudget_nonneg fp x yhat a)
              (mul_nonneg (abs_nonneg x) heps)
          have herrNext :
              |fl_hornerStep fp x yhat a - hornerStep x y a| ≤
                epsNext := by
            simpa [epsNext] using
              fl_hornerStep_error_bound_of_accumulator_error
                fp x yhat y a eps herr
          have htail :=
            ih (fl_hornerStep fp x yhat a) (hornerStep x y a)
              epsNext hepsNext herrNext
          have hlenFl :
              (fl_hornerSyntheticQuotientFold fp x
                  (fl_hornerStep fp x yhat a) (b :: tail)).length =
                (b :: tail).length :=
            fl_hornerSyntheticQuotientFold_length fp x (b :: tail)
              (fl_hornerStep fp x yhat a)
          have hlenExact :
              (hornerSyntheticQuotientFold x (hornerStep x y a)
                  (b :: tail)).length = (b :: tail).length :=
            hornerSyntheticQuotientFold_length x (b :: tail)
              (hornerStep x y a)
          have hsplit :
              polyDesc x
                  (fl_hornerSyntheticQuotientFold fp x yhat
                    (a :: b :: tail)) -
                polyDesc x
                  (hornerSyntheticQuotientFold x y
                    (a :: b :: tail)) =
              (yhat - y) * x ^ (b :: tail).length +
                (polyDesc x
                    (fl_hornerSyntheticQuotientFold fp x
                      (fl_hornerStep fp x yhat a) (b :: tail)) -
                  polyDesc x
                    (hornerSyntheticQuotientFold x
                      (hornerStep x y a) (b :: tail))) := by
            simp [fl_hornerSyntheticQuotientFold,
              hornerSyntheticQuotientFold, polyDesc, hlenFl, hlenExact]
            ring
          have hhead :
              |(yhat - y) * x ^ (b :: tail).length| ≤
                eps * |x| ^ (b :: tail).length := by
            rw [abs_mul, abs_pow]
            exact mul_le_mul_of_nonneg_right herr
              (pow_nonneg (abs_nonneg x) _)
          have htri :
              |(yhat - y) * x ^ (b :: tail).length +
                  (polyDesc x
                    (fl_hornerSyntheticQuotientFold fp x
                      (fl_hornerStep fp x yhat a) (b :: tail)) -
                  polyDesc x
                    (hornerSyntheticQuotientFold x
                      (hornerStep x y a) (b :: tail)))| ≤
                |(yhat - y) * x ^ (b :: tail).length| +
                  |polyDesc x
                    (fl_hornerSyntheticQuotientFold fp x
                      (fl_hornerStep fp x yhat a) (b :: tail)) -
                  polyDesc x
                    (hornerSyntheticQuotientFold x
                      (hornerStep x y a) (b :: tail))| :=
            abs_add_le _ _
          rw [hsplit]
          exact le_trans htri
            (by
              simpa [fl_hornerSyntheticQuotientEvalForwardMajorant,
                epsNext] using add_le_add hhead htail)

/-- Forward bound for the computed synthetic-division quotient attached to a
whole coefficient list. -/
theorem fl_hornerSyntheticQuotientDesc_eval_forward_error_bound
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) :
    |polyDesc x (fl_hornerSyntheticQuotientDesc fp x coeffsDesc) -
        polyDesc x (hornerSyntheticQuotientDesc x coeffsDesc)| ≤
      fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [fl_hornerSyntheticQuotientDesc,
        hornerSyntheticQuotientDesc, polyDesc,
        fl_hornerSyntheticQuotientDescEvalForwardMajorant]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [fl_hornerSyntheticQuotientDesc,
            hornerSyntheticQuotientDesc, polyDesc,
            fl_hornerSyntheticQuotientDescEvalForwardMajorant]
      | cons b tail =>
          have h :=
            fl_hornerSyntheticQuotientFold_eval_forward_error_bound
              fp x (b :: tail) a a 0 (by norm_num) (by simp)
          simpa [fl_hornerSyntheticQuotientDesc,
            hornerSyntheticQuotientDesc,
            fl_hornerSyntheticQuotientDescEvalForwardMajorant] using h

/-- Fully explicit finite first-derivative error bound obtained by combining
the rounded derivative solve with the list-level computed-quotient bound. -/
theorem fl_hornerDerivativeDesc_snd_forward_error_bound_with_quotient_majorant
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    let qhat := fl_hornerSyntheticQuotientDesc fp x coeffsDesc
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
        polyDescDeriv x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) * polyDescAbs x qhat +
        fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x
          coeffsDesc := by
  dsimp
  have hbase :=
    fl_hornerDerivativeDesc_snd_error_bound_via_fl_quotient
      fp x coeffsDesc hvalid
  have hq :=
    fl_hornerSyntheticQuotientDesc_eval_forward_error_bound
      fp x coeffsDesc
  exact le_trans hbase (add_le_add (le_refl _) hq)

/-- Adapter form of the Algorithm 5.2 derivative error bound: any proved
majorant for the rounded synthetic quotient and any proved majorant for the
quotient-evaluation perturbation combine additively.  This isolates the
remaining simplification needed for Higham (5.5)-(5.7). -/
theorem fl_hornerDerivativeDesc_snd_forward_error_bound_of_quotient_majorants
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1)))
    (qMajorant quotientMajorant : ℝ)
    (hqMajorant :
      polyDescAbs x (fl_hornerSyntheticQuotientDesc fp x coeffsDesc) ≤
        qMajorant)
    (hquotientMajorant :
      fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x coeffsDesc ≤
        quotientMajorant) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
        polyDescDeriv x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) * qMajorant +
        quotientMajorant := by
  have hbase :=
    fl_hornerDerivativeDesc_snd_forward_error_bound_with_quotient_majorant
      fp x coeffsDesc hvalid
  dsimp at hbase
  exact le_trans hbase
    (add_le_add
      (mul_le_mul_of_nonneg_left hqMajorant (gamma_nonneg fp hvalid))
      hquotientMajorant)

/-- Concrete finite precursor to Higham (5.7): the derivative error is bounded
by the derivative absolute majorant `ptilde'` plus the explicit recursive
computed-quotient budget.  The remaining source simplification is to bound that
budget by a first-order `n*u*ptilde'` term with exact higher-order constants. -/
theorem fl_hornerDerivativeDesc_snd_forward_error_bound_with_derivAbs_and_eval_majorant
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
        polyDescDeriv x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) *
          (polyDescDerivAbs x coeffsDesc +
            fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x
              coeffsDesc) +
        fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x
          coeffsDesc := by
  exact
    fl_hornerDerivativeDesc_snd_forward_error_bound_of_quotient_majorants
      fp x coeffsDesc hvalid
      (polyDescDerivAbs x coeffsDesc +
        fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x coeffsDesc)
      (fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x coeffsDesc)
      (fl_hornerSyntheticQuotientDesc_abs_le_derivAbs_plus_eval_majorant
        fp x coeffsDesc)
      (le_refl _)

/-- Source-budget variant of the finite precursor to Higham (5.7): the
remaining computed-quotient perturbation is bounded by a budget expressed with
exact Horner accumulators and an explicit propagated error term. -/
theorem fl_hornerDerivativeDesc_snd_forward_error_bound_with_derivAbs_and_source_majorant
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
        polyDescDeriv x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) *
          (polyDescDerivAbs x coeffsDesc +
            fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant fp x
              coeffsDesc) +
        fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant fp x
          coeffsDesc := by
  have hsource :
      fl_hornerSyntheticQuotientDescEvalForwardMajorant fp x coeffsDesc ≤
        fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant fp x
          coeffsDesc :=
    fl_hornerSyntheticQuotientDescEvalForwardMajorant_le_source_majorant
      fp x coeffsDesc
  have hq :
      polyDescAbs x (fl_hornerSyntheticQuotientDesc fp x coeffsDesc) ≤
        polyDescDerivAbs x coeffsDesc +
          fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant fp x
            coeffsDesc :=
    le_trans
      (fl_hornerSyntheticQuotientDesc_abs_le_derivAbs_plus_eval_majorant
        fp x coeffsDesc)
      (add_le_add (le_refl (polyDescDerivAbs x coeffsDesc)) hsource)
  exact
    fl_hornerDerivativeDesc_snd_forward_error_bound_of_quotient_majorants
      fp x coeffsDesc hvalid
      (polyDescDerivAbs x coeffsDesc +
        fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant fp x
          coeffsDesc)
      (fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant fp x
        coeffsDesc)
      hq
      hsource

/-- Remaining source-budget term after extracting the displayed first-order
coefficient from the derivative source-majorant bound.  The still-open (5.7)
step is to prove this term has the intended `O(u^2)` behavior, by bounding the
source quotient budget itself to first order. -/
noncomputable def fl_hornerDerivativeDescFirstOrderSourceRemainder
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) : ℝ :=
  let nops : ℕ := 2 * (coeffsDesc.length - 1)
  let D : ℝ := polyDescDerivAbs x coeffsDesc
  let S : ℝ :=
    fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant fp x
      coeffsDesc
  ((((nops : ℝ) * fp.u) ^ 2) / (1 - (nops : ℝ) * fp.u)) *
      (D + S) +
    (nops : ℝ) * fp.u * S + S

theorem fl_hornerDerivativeDescFirstOrderSourceRemainder_eq_zero_of_u_eq_zero
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) (hu : fp.u = 0) :
    fl_hornerDerivativeDescFirstOrderSourceRemainder fp x coeffsDesc = 0 := by
  have hS :=
    fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant_eq_zero_of_u_eq_zero
      fp x coeffsDesc hu
  simp [fl_hornerDerivativeDescFirstOrderSourceRemainder, hu, hS]

/-- First-order display form for the derivative bound, with the printed
`2*n*u*ptilde'` coefficient exposed and the remaining exact source-budget
terms named explicitly. -/
theorem fl_hornerDerivativeDesc_snd_forward_error_bound_first_order_source_remainder
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
        polyDescDeriv x coeffsDesc| ≤
      (((2 * (coeffsDesc.length - 1) : ℕ) : ℝ) * fp.u) *
          polyDescDerivAbs x coeffsDesc +
        fl_hornerDerivativeDescFirstOrderSourceRemainder fp x coeffsDesc := by
  let nops : ℕ := 2 * (coeffsDesc.length - 1)
  let D : ℝ := polyDescDerivAbs x coeffsDesc
  let S : ℝ :=
    fl_hornerSyntheticQuotientDescEvalForwardSourceMajorant fp x
      coeffsDesc
  have hbase :=
    fl_hornerDerivativeDesc_snd_forward_error_bound_with_derivAbs_and_source_majorant
      fp x coeffsDesc hvalid
  have hgamma :
      gamma fp nops =
        (nops : ℝ) * fp.u +
          (((nops : ℝ) * fp.u) ^ 2) /
            (1 - (nops : ℝ) * fp.u) := by
    simpa [nops] using gamma_eq_linear_plus_quadratic_remainder
      fp nops hvalid
  have hrewrite :
      gamma fp nops * (D + S) + S =
        ((nops : ℝ) * fp.u) * D +
          fl_hornerDerivativeDescFirstOrderSourceRemainder fp x
            coeffsDesc := by
    unfold fl_hornerDerivativeDescFirstOrderSourceRemainder
    dsimp [nops, D, S]
    rw [hgamma]
    ring
  simpa [nops, D, S] using le_trans hbase (le_of_eq hrewrite)

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

lemma fl_hornerSyntheticQuotientFold_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (x : ℝ) :
    ∀ (rest : List ℝ) (y : ℝ),
      fl_hornerSyntheticQuotientFold
          (FPModel.exactWithUnitRoundoff u0 hu0) x y rest =
        hornerSyntheticQuotientFold x y rest := by
  intro rest
  induction rest with
  | nil =>
      intro y
      rfl
  | cons a rest ih =>
      intro y
      cases rest with
      | nil =>
          rfl
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientFold,
            hornerSyntheticQuotientFold, fl_hornerStep, hornerStep,
            FPModel.exactWithUnitRoundoff] using ih (x * y + a)

/-- Exact arithmetic, packaged as an `FPModel`, produces the exact
synthetic-division quotient stream. -/
theorem fl_hornerSyntheticQuotientDesc_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (x : ℝ) (coeffsDesc : List ℝ) :
    fl_hornerSyntheticQuotientDesc
        (FPModel.exactWithUnitRoundoff u0 hu0) x coeffsDesc =
      hornerSyntheticQuotientDesc x coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      rfl
  | cons a rest =>
      cases rest with
      | nil =>
          rfl
      | cons b tail =>
          simpa [fl_hornerSyntheticQuotientDesc,
            hornerSyntheticQuotientDesc] using
            fl_hornerSyntheticQuotientFold_exactWithUnitRoundoff
              u0 hu0 x (b :: tail) a

lemma fl_hornerDerivativeExactFold_eq (u0 : ℝ) (hu0 : 0 ≤ u0)
    (x : ℝ) :
    ∀ (rest : List ℝ) (y d : ℝ),
      rest.foldl
          (fl_hornerDerivativeStep
            (FPModel.exactWithUnitRoundoff u0 hu0) x) (y, d) =
        rest.foldl (hornerDerivativeStep x) (y, d) := by
  intro rest
  induction rest with
  | nil =>
      intro y d
      rfl
  | cons a rest ih =>
      intro y d
      simpa [List.foldl, fl_hornerDerivativeStep, fl_hornerStep,
        hornerDerivativeStep, hornerStep, FPModel.exactWithUnitRoundoff]
        using ih (x * y + a) (x * d + y)

/-- Exact arithmetic, packaged as an `FPModel`, reduces rounded Algorithm 5.2's
first-derivative core to the exact coupled Horner recurrence. -/
theorem fl_hornerDerivativeDesc_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (x : ℝ) (coeffsDesc : List ℝ) :
    fl_hornerDerivativeDesc (FPModel.exactWithUnitRoundoff u0 hu0) x
        coeffsDesc =
      hornerDerivativeDesc x coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons a rest =>
      simpa [fl_hornerDerivativeDesc, hornerDerivativeDesc]
        using fl_hornerDerivativeExactFold_eq u0 hu0 x rest a 0

/-! ## Higham (5.14): the three complex matrix-polynomial forms -/

/-- Higham (5.14), `P₁(X) = a₀I + a₁X + ⋯ + aₙXⁿ`, with complex
scalar coefficients stored in descending order. -/
noncomputable def complexMatrixPolyP1Desc (n : ℕ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    List ℂ → Matrix (Fin n) (Fin n) ℂ
  | [] => 0
  | a :: rest => a • X ^ rest.length + complexMatrixPolyP1Desc n X rest

/-- One exact matrix Horner step for `P₁`; a scalar coefficient is inserted
as the scalar matrix `aI`. -/
noncomputable def complexMatrixHornerP1Step (n : ℕ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) (a : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Y * X + a • (1 : Matrix (Fin n) (Fin n) ℂ)

/-- Exact Horner evaluator for the `P₁` form in (5.14). -/
noncomputable def complexMatrixHornerP1Desc (n : ℕ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    List ℂ → Matrix (Fin n) (Fin n) ℂ
  | [] => 0
  | a :: rest =>
      rest.foldl (complexMatrixHornerP1Step n X)
        (a • (1 : Matrix (Fin n) (Fin n) ℂ))

lemma complexMatrixHornerP1Fold_eq_acc_mul_pow_add_poly
    (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∀ (rest : List ℂ) (Y : Matrix (Fin n) (Fin n) ℂ),
      rest.foldl (complexMatrixHornerP1Step n X) Y =
        Y * X ^ rest.length + complexMatrixPolyP1Desc n X rest := by
  intro rest
  induction rest with
  | nil =>
      intro Y
      simp [complexMatrixPolyP1Desc]
  | cons a rest ih =>
      intro Y
      rw [List.foldl, ih]
      simp only [complexMatrixPolyP1Desc, List.length_cons]
      rw [pow_succ']
      simp [complexMatrixHornerP1Step, add_mul, mul_assoc]
      ac_rfl

/-- Exact Horner evaluation realizes the full complex `P₁` expression in
(5.14). -/
theorem complexMatrixHornerP1Desc_eq_complexMatrixPolyP1Desc
    (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) (coeffsDesc : List ℂ) :
    complexMatrixHornerP1Desc n X coeffsDesc =
      complexMatrixPolyP1Desc n X coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons a rest =>
      simpa [complexMatrixHornerP1Desc, complexMatrixPolyP1Desc]
        using complexMatrixHornerP1Fold_eq_acc_mul_pow_add_poly
          n X rest (a • (1 : Matrix (Fin n) (Fin n) ℂ))

/-- Higham (5.14), `P₂(α) = A₀ + A₁α + ⋯ + Aₙαⁿ`, with complex
matrix coefficients stored in descending order. -/
noncomputable def complexMatrixPolyP2Desc (n : ℕ) (α : ℂ) :
    List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ
  | [] => 0
  | A :: rest =>
      (α ^ rest.length) • A + complexMatrixPolyP2Desc n α rest

/-- One exact Horner step for the scalar-argument/matrix-coefficient `P₂`
form in (5.14). -/
noncomputable def complexMatrixHornerP2Step (n : ℕ) (α : ℂ)
    (Y A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  α • Y + A

/-- Exact Horner evaluator for the `P₂` form in (5.14). -/
noncomputable def complexMatrixHornerP2Desc (n : ℕ) (α : ℂ) :
    List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ
  | [] => 0
  | A :: rest => rest.foldl (complexMatrixHornerP2Step n α) A

lemma complexMatrixHornerP2Fold_eq_pow_smul_acc_add_poly
    (n : ℕ) (α : ℂ) :
    ∀ (rest : List (Matrix (Fin n) (Fin n) ℂ))
      (Y : Matrix (Fin n) (Fin n) ℂ),
      rest.foldl (complexMatrixHornerP2Step n α) Y =
        (α ^ rest.length) • Y + complexMatrixPolyP2Desc n α rest := by
  intro rest
  induction rest with
  | nil =>
      intro Y
      simp [complexMatrixPolyP2Desc]
  | cons A rest ih =>
      intro Y
      rw [List.foldl, ih]
      simp only [complexMatrixPolyP2Desc, List.length_cons]
      rw [pow_succ']
      ext i j
      simp [complexMatrixHornerP2Step]
      ring

/-- Exact Horner evaluation realizes the full complex `P₂` expression in
(5.14). -/
theorem complexMatrixHornerP2Desc_eq_complexMatrixPolyP2Desc
    (n : ℕ) (α : ℂ)
    (coeffsDesc : List (Matrix (Fin n) (Fin n) ℂ)) :
    complexMatrixHornerP2Desc n α coeffsDesc =
      complexMatrixPolyP2Desc n α coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons A rest =>
      simpa [complexMatrixHornerP2Desc, complexMatrixPolyP2Desc]
        using complexMatrixHornerP2Fold_eq_pow_smul_acc_add_poly
          n α rest A

/-- Higham (5.14), `P₃(X) = A₀ + A₁X + ⋯ + AₙXⁿ`, over complex
matrices, with descending matrix coefficients. -/
noncomputable def complexMatrixPolyP3Desc (n : ℕ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ
  | [] => 0
  | A :: rest =>
      A * X ^ rest.length + complexMatrixPolyP3Desc n X rest

/-- Exact complex matrix Horner evaluator for `P₃` in (5.14). -/
noncomputable def complexMatrixHornerP3Desc (n : ℕ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ
  | [] => 0
  | A :: rest => rest.foldl (fun Y B => Y * X + B) A

lemma complexMatrixHornerP3Fold_eq_acc_mul_pow_add_poly
    (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∀ (rest : List (Matrix (Fin n) (Fin n) ℂ))
      (Y : Matrix (Fin n) (Fin n) ℂ),
      rest.foldl (fun Z B => Z * X + B) Y =
        Y * X ^ rest.length + complexMatrixPolyP3Desc n X rest := by
  intro rest
  induction rest with
  | nil =>
      intro Y
      simp [complexMatrixPolyP3Desc]
  | cons A rest ih =>
      intro Y
      rw [List.foldl, ih]
      simp only [complexMatrixPolyP3Desc, List.length_cons]
      rw [pow_succ']
      simp [add_mul, mul_assoc]
      abel

/-- Exact Horner evaluation realizes the full complex `P₃` expression in
(5.14), completing the three displayed complex forms. -/
theorem complexMatrixHornerP3Desc_eq_complexMatrixPolyP3Desc
    (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ)
    (coeffsDesc : List (Matrix (Fin n) (Fin n) ℂ)) :
    complexMatrixHornerP3Desc n X coeffsDesc =
      complexMatrixPolyP3Desc n X coeffsDesc := by
  cases coeffsDesc with
  | nil => rfl
  | cons A rest =>
      simpa [complexMatrixHornerP3Desc, complexMatrixPolyP3Desc]
        using complexMatrixHornerP3Fold_eq_acc_mul_pow_add_poly
          n X rest A

/-! ## Matrix polynomials -/

/-- Zero square matrix in the repository's function-shaped matrix
representation. -/
noncomputable def zeroMatrix (n : ℕ) : Fin n → Fin n → ℝ :=
  fun _ _ => 0

/-- Pointwise matrix addition in the repository's function-shaped matrix
representation. -/
noncomputable def matAdd (n : ℕ)
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A i j + B i j

/-- Higham (5.14), `P3(X) = A_0 + A_1 X + ... + A_n X^n`, represented with
descending matrix coefficients `[A_n, ..., A_0]`. -/
noncomputable def matrixPolyP3Desc (n : ℕ) (X : Fin n → Fin n → ℝ) :
    List (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | [] => zeroMatrix n
  | A :: rest =>
      matAdd n (matMul n A (matPow n X rest.length))
        (matrixPolyP3Desc n X rest)

/-- One exact Horner step for the matrix polynomial `P3` in (5.14), with
matrix coefficients on the left of powers of `X`. -/
noncomputable def matrixHornerP3Step (n : ℕ)
    (X Y A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matAdd n (matMul n Y X) A

/-- Exact Horner evaluation of `P3` from descending matrix coefficients
`[A_n, ..., A_0]`. -/
noncomputable def matrixHornerP3Desc (n : ℕ)
    (X : Fin n → Fin n → ℝ) :
    List (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | [] => zeroMatrix n
  | A :: rest => rest.foldl (matrixHornerP3Step n X) A

lemma matrixHornerP3Fold_eq_acc_mul_pow_add_polyDesc
    (n : ℕ) (X : Fin n → Fin n → ℝ) :
    ∀ (rest : List (Fin n → Fin n → ℝ)) (Y : Fin n → Fin n → ℝ),
      rest.foldl (matrixHornerP3Step n X) Y =
        matAdd n (matMul n Y (matPow n X rest.length))
          (matrixPolyP3Desc n X rest) := by
  intro rest
  induction rest with
  | nil =>
      intro Y
      ext i j
      simp [matrixPolyP3Desc, matAdd, zeroMatrix,
        matPow_zero, matMul_id_right]
  | cons A rest ih =>
      intro Y
      have hmul :
          matMul n (matrixHornerP3Step n X Y A)
              (matPow n X rest.length) =
            fun i j =>
              matMul n Y (matPow n X (rest.length + 1)) i j +
                matMul n A (matPow n X rest.length) i j := by
        calc
          matMul n (matrixHornerP3Step n X Y A)
              (matPow n X rest.length)
              =
            matMul n (fun i j => matMul n Y X i j + A i j)
              (matPow n X rest.length) := rfl
          _ =
            fun i j =>
              matMul n (matMul n Y X) (matPow n X rest.length) i j +
                matMul n A (matPow n X rest.length) i j :=
              matMul_add_left n (matMul n Y X) A (matPow n X rest.length)
          _ =
            fun i j =>
              matMul n Y (matPow n X (rest.length + 1)) i j +
                matMul n A (matPow n X rest.length) i j := by
              have hassoc :
                  matMul n (matMul n Y X) (matPow n X rest.length) =
                    matMul n Y (matPow n X (rest.length + 1)) := by
                rw [matMul_assoc]
                rfl
              rw [hassoc]
      rw [List.foldl, ih]
      ext i j
      simp [matrixPolyP3Desc, matrixHornerP3Step, matAdd] at hmul ⊢
      rw [congrFun (congrFun hmul i) j]
      ring

/-- Exact matrix Horner evaluation equals the displayed matrix polynomial
`P3(X) = A_0 + A_1 X + ... + A_n X^n` from (5.14), for descending
coefficient lists. -/
theorem matrixHornerP3Desc_eq_matrixPolyP3Desc
    (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ)) :
    matrixHornerP3Desc n X coeffsDesc =
      matrixPolyP3Desc n X coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      rfl
  | cons A rest =>
      have h :=
        matrixHornerP3Fold_eq_acc_mul_pow_add_polyDesc n X rest A
      ext i j
      simpa [matrixHornerP3Desc, matrixPolyP3Desc, matAdd] using
        congrFun (congrFun h i) j

lemma infNorm_zeroMatrix (n : ℕ) :
    infNorm (zeroMatrix n) = 0 := by
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      simp [zeroMatrix]
    · norm_num
  · exact infNorm_nonneg _

lemma infNorm_add_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ) :
    infNorm (fun i j => A i j + B i j) ≤ infNorm A + infNorm B := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      (∑ j : Fin n, |A i j + B i j|)
          ≤ ∑ j : Fin n, (|A i j| + |B i j|) :=
            Finset.sum_le_sum (fun j _ => abs_add_le (A i j) (B i j))
      _ = (∑ j : Fin n, |A i j|) + ∑ j : Fin n, |B i j| := by
            rw [Finset.sum_add_distrib]
      _ ≤ infNorm A + infNorm B :=
            add_le_add (row_sum_le_infNorm A i) (row_sum_le_infNorm B i)
  · exact add_nonneg (infNorm_nonneg A) (infNorm_nonneg B)

lemma oneNorm_add_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ) :
    oneNorm (fun i j => A i j + B i j) ≤ oneNorm A + oneNorm B := by
  apply oneNorm_le_of_col_sum_le
  · intro j
    calc
      (∑ i : Fin n, |A i j + B i j|)
          ≤ ∑ i : Fin n, (|A i j| + |B i j|) :=
            Finset.sum_le_sum (fun i _ => abs_add_le (A i j) (B i j))
      _ = (∑ i : Fin n, |A i j|) + ∑ i : Fin n, |B i j| := by
            rw [Finset.sum_add_distrib]
      _ ≤ oneNorm A + oneNorm B :=
            add_le_add (col_sum_le_oneNorm A j) (col_sum_le_oneNorm B j)
  · exact add_nonneg (oneNorm_nonneg A) (oneNorm_nonneg B)

lemma fl_matAdd_infNorm_error_bound
    (fp : FPModel) (n : ℕ)
    (A B : Fin n → Fin n → ℝ) :
    infNorm
        (fun i j => fp.fl_add (A i j) (B i j) - matAdd n A B i j) ≤
      fp.u * infNorm (matAdd n A B) := by
  apply infNorm_le_of_row_sum_le
  · intro i
    have hentry : ∀ j : Fin n,
        |fp.fl_add (A i j) (B i j) - matAdd n A B i j| ≤
          fp.u * |matAdd n A B i j| := by
      intro j
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add (A i j) (B i j)
      have hdiff :
          fp.fl_add (A i j) (B i j) - matAdd n A B i j =
            matAdd n A B i j * δ := by
        rw [hadd]
        simp [matAdd]
        ring
      calc
        |fp.fl_add (A i j) (B i j) - matAdd n A B i j|
            = |matAdd n A B i j| * |δ| := by
              rw [hdiff, abs_mul]
        _ ≤ |matAdd n A B i j| * fp.u :=
              mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
        _ = fp.u * |matAdd n A B i j| := by ring
    calc
      (∑ j : Fin n,
          |fp.fl_add (A i j) (B i j) - matAdd n A B i j|)
          ≤ ∑ j : Fin n, fp.u * |matAdd n A B i j| :=
            Finset.sum_le_sum (fun j _ => hentry j)
      _ = fp.u * ∑ j : Fin n, |matAdd n A B i j| := by
            rw [Finset.mul_sum]
      _ ≤ fp.u * infNorm (matAdd n A B) :=
            mul_le_mul_of_nonneg_left
              (row_sum_le_infNorm (matAdd n A B) i) fp.u_nonneg
  · exact mul_nonneg fp.u_nonneg (infNorm_nonneg _)

lemma fl_matAdd_oneNorm_error_bound
    (fp : FPModel) (n : ℕ)
    (A B : Fin n → Fin n → ℝ) :
    oneNorm
        (fun i j => fp.fl_add (A i j) (B i j) - matAdd n A B i j) ≤
      fp.u * oneNorm (matAdd n A B) := by
  apply oneNorm_le_of_col_sum_le
  · intro j
    have hentry : ∀ i : Fin n,
        |fp.fl_add (A i j) (B i j) - matAdd n A B i j| ≤
          fp.u * |matAdd n A B i j| := by
      intro i
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add (A i j) (B i j)
      have hdiff :
          fp.fl_add (A i j) (B i j) - matAdd n A B i j =
            matAdd n A B i j * δ := by
        rw [hadd]
        simp [matAdd]
        ring
      calc
        |fp.fl_add (A i j) (B i j) - matAdd n A B i j|
            = |matAdd n A B i j| * |δ| := by
              rw [hdiff, abs_mul]
        _ ≤ |matAdd n A B i j| * fp.u :=
              mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
        _ = fp.u * |matAdd n A B i j| := by ring
    calc
      (∑ i : Fin n,
          |fp.fl_add (A i j) (B i j) - matAdd n A B i j|)
          ≤ ∑ i : Fin n, fp.u * |matAdd n A B i j| :=
            Finset.sum_le_sum (fun i _ => hentry i)
      _ = fp.u * ∑ i : Fin n, |matAdd n A B i j| := by
            rw [Finset.mul_sum]
      _ ≤ fp.u * oneNorm (matAdd n A B) :=
            mul_le_mul_of_nonneg_left
              (col_sum_le_oneNorm (matAdd n A B) j) fp.u_nonneg
  · exact mul_nonneg fp.u_nonneg (oneNorm_nonneg _)

theorem fl_matMul_infNorm_error_bound
    (fp : FPModel) (n : ℕ)
    (A B : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    infNorm
        (fun i j =>
          fl_matMul fp n n n A B i j - matMul n A B i j) ≤
      gamma fp n * infNorm A * infNorm B := by
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hA : 0 ≤ infNorm A := infNorm_nonneg A
  have hB : 0 ≤ infNorm B := infNorm_nonneg B
  apply infNorm_le_of_row_sum_le
  · intro i
    have hcomp_sum :
        (∑ j : Fin n,
          |fl_matMul fp n n n A B i j - matMul n A B i j|) ≤
          ∑ j : Fin n, gamma fp n * ∑ k : Fin n, |A i k| * |B k j| := by
      apply Finset.sum_le_sum
      intro j _
      simpa [matMul] using matMul_error_bound fp n n n A B hn i j
    have hdouble :
        (∑ j : Fin n, ∑ k : Fin n, |A i k| * |B k j|) =
          ∑ k : Fin n, |A i k| * ∑ j : Fin n, |B k j| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    have hdouble_bound :
        (∑ j : Fin n, ∑ k : Fin n, |A i k| * |B k j|) ≤
          (∑ k : Fin n, |A i k|) * infNorm B := by
      rw [hdouble]
      calc
        ∑ k : Fin n, |A i k| * ∑ j : Fin n, |B k j|
            ≤ ∑ k : Fin n, |A i k| * infNorm B :=
                Finset.sum_le_sum (fun k _ =>
                  mul_le_mul_of_nonneg_left
                    (row_sum_le_infNorm B k) (abs_nonneg _))
        _ = (∑ k : Fin n, |A i k|) * infNorm B := by
                rw [Finset.sum_mul]
    calc
      (∑ j : Fin n,
          |fl_matMul fp n n n A B i j - matMul n A B i j|)
          ≤ ∑ j : Fin n, gamma fp n * ∑ k : Fin n, |A i k| * |B k j| :=
            hcomp_sum
      _ = gamma fp n * (∑ j : Fin n, ∑ k : Fin n, |A i k| * |B k j|) := by
            rw [← Finset.mul_sum]
      _ ≤ gamma fp n * ((∑ k : Fin n, |A i k|) * infNorm B) :=
            mul_le_mul_of_nonneg_left hdouble_bound hγ
      _ ≤ gamma fp n * (infNorm A * infNorm B) := by
            have hrowA : ∑ k : Fin n, |A i k| ≤ infNorm A :=
              row_sum_le_infNorm A i
            have hprod : (∑ k : Fin n, |A i k|) * infNorm B ≤
                infNorm A * infNorm B :=
              mul_le_mul_of_nonneg_right hrowA hB
            exact mul_le_mul_of_nonneg_left hprod hγ
      _ = gamma fp n * infNorm A * infNorm B := by ring
  · exact mul_nonneg (mul_nonneg hγ hA) hB

theorem fl_matMul_oneNorm_error_bound
    (fp : FPModel) (n : ℕ)
    (A B : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    oneNorm
        (fun i j =>
          fl_matMul fp n n n A B i j - matMul n A B i j) ≤
      gamma fp n * oneNorm A * oneNorm B := by
  simpa [matMul] using matMul_error_bound_oneNorm fp n A B hn

lemma oneNorm_matMul_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ) :
    oneNorm (matMul n A B) ≤ oneNorm A * oneNorm B := by
  apply oneNorm_le_of_col_sum_le
  · intro j
    have hsum :
        (∑ i : Fin n, |matMul n A B i j|) ≤
          ∑ i : Fin n, ∑ k : Fin n, |A i k| * |B k j| := by
      apply Finset.sum_le_sum
      intro i _
      calc
        |matMul n A B i j|
            = |∑ k : Fin n, A i k * B k j| := by rfl
        _ ≤ ∑ k : Fin n, |A i k * B k j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |A i k| * |B k j| := by
            apply Finset.sum_congr rfl
            intro k _
            rw [abs_mul]
    have hdouble :
        (∑ i : Fin n, ∑ k : Fin n, |A i k| * |B k j|) =
          ∑ k : Fin n, |B k j| * ∑ i : Fin n, |A i k| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_mul]
      ring
    have hdouble_bound :
        (∑ i : Fin n, ∑ k : Fin n, |A i k| * |B k j|) ≤
          oneNorm A * ∑ k : Fin n, |B k j| := by
      rw [hdouble]
      calc
        ∑ k : Fin n, |B k j| * ∑ i : Fin n, |A i k|
            ≤ ∑ k : Fin n, |B k j| * oneNorm A :=
                Finset.sum_le_sum (fun k _ =>
                  mul_le_mul_of_nonneg_left
                    (col_sum_le_oneNorm A k) (abs_nonneg _))
        _ = oneNorm A * ∑ k : Fin n, |B k j| := by
                rw [← Finset.sum_mul]
                ring
    calc
      (∑ i : Fin n, |matMul n A B i j|)
          ≤ ∑ i : Fin n, ∑ k : Fin n, |A i k| * |B k j| := hsum
      _ ≤ oneNorm A * ∑ k : Fin n, |B k j| := hdouble_bound
      _ ≤ oneNorm A * oneNorm B :=
            mul_le_mul_of_nonneg_left
              (col_sum_le_oneNorm B j) (oneNorm_nonneg A)
  · exact mul_nonneg (oneNorm_nonneg A) (oneNorm_nonneg B)

lemma oneNorm_matPow_le {n : ℕ}
    (M : Fin n → Fin n → ℝ) (k : ℕ) :
    oneNorm (matPow n M k) ≤ oneNorm M ^ k := by
  induction k with
  | zero =>
      simp only [matPow, pow_zero]
      apply oneNorm_le_of_col_sum_le
      · intro j
        unfold idMatrix
        have hentry : ∀ i : Fin n,
            |if i = j then (1 : ℝ) else 0| =
              if i = j then 1 else 0 := by
          intro i
          split <;> simp
        simp_rw [hentry]
        calc
          (∑ i : Fin n, if i = j then (1 : ℝ) else 0) = 1 := by
            rw [Finset.sum_eq_single j]
            · simp
            · intro i _ hij
              simp [hij]
            · intro hj
              exact False.elim (hj (Finset.mem_univ j))
          _ ≤ 1 := le_rfl
      · norm_num
  | succ k ih =>
      have hM : 0 ≤ oneNorm M := oneNorm_nonneg M
      calc
        oneNorm (matPow n M (k + 1))
            = oneNorm (matMul n M (matPow n M k)) := by
              rw [matPow_succ]
        _ ≤ oneNorm M * oneNorm (matPow n M k) :=
              oneNorm_matMul_le M (matPow n M k)
        _ ≤ oneNorm M * oneNorm M ^ k :=
              mul_le_mul_of_nonneg_left ih hM
        _ = oneNorm M ^ (k + 1) := by ring

/-- The scalar majorant `ptilde_3(||X||)` for the matrix polynomial in
Problem 5.6, using the infinity norm and descending matrix coefficients. -/
noncomputable def matrixPolyP3InfNormMajorant (n : ℕ)
    (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ)) : ℝ :=
  polyDesc (infNorm X) (coeffsDesc.map infNorm)

/-- The scalar majorant `ptilde_3(||X||)` for the matrix polynomial in
Problem 5.6, using the one norm and descending matrix coefficients. -/
noncomputable def matrixPolyP3OneNormMajorant (n : ℕ)
    (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ)) : ℝ :=
  polyDesc (oneNorm X) (coeffsDesc.map oneNorm)

theorem matrixPolyP3InfNormMajorant_nonneg
    (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ)) :
    0 ≤ matrixPolyP3InfNormMajorant n X coeffsDesc := by
  induction coeffsDesc with
  | nil =>
      simp [matrixPolyP3InfNormMajorant, polyDesc]
  | cons A rest ih =>
      have hterm :
          0 ≤ infNorm A * infNorm X ^ rest.length :=
        mul_nonneg (infNorm_nonneg A)
          (pow_nonneg (infNorm_nonneg X) _)
      simpa [matrixPolyP3InfNormMajorant, polyDesc] using
        add_nonneg hterm ih

theorem matrixPolyP3OneNormMajorant_nonneg
    (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ)) :
    0 ≤ matrixPolyP3OneNormMajorant n X coeffsDesc := by
  induction coeffsDesc with
  | nil =>
      simp [matrixPolyP3OneNormMajorant, polyDesc]
  | cons A rest ih =>
      have hterm :
          0 ≤ oneNorm A * oneNorm X ^ rest.length :=
        mul_nonneg (oneNorm_nonneg A)
          (pow_nonneg (oneNorm_nonneg X) _)
      simpa [matrixPolyP3OneNormMajorant, polyDesc] using
        add_nonneg hterm ih

theorem matrixPolyP3Desc_infNorm_le_majorant
    (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) :
    infNorm (matrixPolyP3Desc n X coeffsDesc) ≤
      matrixPolyP3InfNormMajorant n X coeffsDesc := by
  induction coeffsDesc with
  | nil =>
      simpa [matrixPolyP3Desc, matrixPolyP3InfNormMajorant, polyDesc]
        using le_of_eq (infNorm_zeroMatrix n)
  | cons A rest ih =>
      let term : Fin n → Fin n → ℝ := matMul n A (matPow n X rest.length)
      let tail : Fin n → Fin n → ℝ := matrixPolyP3Desc n X rest
      have hadd :
          infNorm (matAdd n term tail) ≤ infNorm term + infNorm tail := by
        simpa [matAdd] using infNorm_add_le term tail
      have hmul :
          infNorm term ≤ infNorm A * infNorm (matPow n X rest.length) := by
        simpa [term] using
          infNorm_matMul_le hnpos A (matPow n X rest.length)
      have hpow :
          infNorm (matPow n X rest.length) ≤ infNorm X ^ rest.length :=
        infNorm_matPow_le hnpos X rest.length
      have hterm :
          infNorm term ≤ infNorm A * infNorm X ^ rest.length :=
        le_trans hmul
          (mul_le_mul_of_nonneg_left hpow (infNorm_nonneg A))
      calc
        infNorm (matrixPolyP3Desc n X (A :: rest))
            = infNorm (matAdd n term tail) := rfl
        _ ≤ infNorm term + infNorm tail := hadd
        _ ≤ infNorm A * infNorm X ^ rest.length +
              matrixPolyP3InfNormMajorant n X rest :=
            add_le_add hterm ih
        _ = matrixPolyP3InfNormMajorant n X (A :: rest) := by
            simp [matrixPolyP3InfNormMajorant, polyDesc]

theorem matrixPolyP3Desc_oneNorm_le_majorant
    (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ)) :
    oneNorm (matrixPolyP3Desc n X coeffsDesc) ≤
      matrixPolyP3OneNormMajorant n X coeffsDesc := by
  induction coeffsDesc with
  | nil =>
      have hone_zero : oneNorm (zeroMatrix n) = 0 := by
        unfold oneNorm
        simpa [zeroMatrix] using infNorm_zeroMatrix n
      simpa [matrixPolyP3Desc, matrixPolyP3OneNormMajorant, polyDesc]
        using le_of_eq hone_zero
  | cons A rest ih =>
      let term : Fin n → Fin n → ℝ := matMul n A (matPow n X rest.length)
      let tail : Fin n → Fin n → ℝ := matrixPolyP3Desc n X rest
      have hadd :
          oneNorm (matAdd n term tail) ≤ oneNorm term + oneNorm tail := by
        simpa [matAdd] using oneNorm_add_le term tail
      have hmul :
          oneNorm term ≤ oneNorm A * oneNorm (matPow n X rest.length) := by
        simpa [term] using
          oneNorm_matMul_le A (matPow n X rest.length)
      have hpow :
          oneNorm (matPow n X rest.length) ≤ oneNorm X ^ rest.length :=
        oneNorm_matPow_le X rest.length
      have hterm :
          oneNorm term ≤ oneNorm A * oneNorm X ^ rest.length :=
        le_trans hmul
          (mul_le_mul_of_nonneg_left hpow (oneNorm_nonneg A))
      calc
        oneNorm (matrixPolyP3Desc n X (A :: rest))
            = oneNorm (matAdd n term tail) := rfl
        _ ≤ oneNorm term + oneNorm tail := hadd
        _ ≤ oneNorm A * oneNorm X ^ rest.length +
              matrixPolyP3OneNormMajorant n X rest :=
            add_le_add hterm ih
        _ = matrixPolyP3OneNormMajorant n X (A :: rest) := by
            simp [matrixPolyP3OneNormMajorant, polyDesc]

theorem matrixHornerP3Fold_infNorm_le_acc_majorant
    (n : ℕ) (X Y : Fin n → Fin n → ℝ)
    (rest : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) :
    infNorm (rest.foldl (matrixHornerP3Step n X) Y) ≤
      infNorm Y * infNorm X ^ rest.length +
        matrixPolyP3InfNormMajorant n X rest := by
  rw [matrixHornerP3Fold_eq_acc_mul_pow_add_polyDesc n X rest Y]
  let term : Fin n → Fin n → ℝ := matMul n Y (matPow n X rest.length)
  let tail : Fin n → Fin n → ℝ := matrixPolyP3Desc n X rest
  have hadd :
      infNorm (matAdd n term tail) ≤ infNorm term + infNorm tail := by
    simpa [matAdd] using infNorm_add_le term tail
  have hmul :
      infNorm term ≤ infNorm Y * infNorm (matPow n X rest.length) := by
    simpa [term] using
      infNorm_matMul_le hnpos Y (matPow n X rest.length)
  have hpow :
      infNorm (matPow n X rest.length) ≤ infNorm X ^ rest.length :=
    infNorm_matPow_le hnpos X rest.length
  have hterm :
      infNorm term ≤ infNorm Y * infNorm X ^ rest.length :=
    le_trans hmul
      (mul_le_mul_of_nonneg_left hpow (infNorm_nonneg Y))
  have htail :
      infNorm tail ≤ matrixPolyP3InfNormMajorant n X rest := by
    simpa [tail] using matrixPolyP3Desc_infNorm_le_majorant n X rest hnpos
  calc
    infNorm (matAdd n term tail)
        ≤ infNorm term + infNorm tail := hadd
    _ ≤ infNorm Y * infNorm X ^ rest.length +
          matrixPolyP3InfNormMajorant n X rest :=
        add_le_add hterm htail

theorem matrixHornerP3Fold_oneNorm_le_acc_majorant
    (n : ℕ) (X Y : Fin n → Fin n → ℝ)
    (rest : List (Fin n → Fin n → ℝ)) :
    oneNorm (rest.foldl (matrixHornerP3Step n X) Y) ≤
      oneNorm Y * oneNorm X ^ rest.length +
        matrixPolyP3OneNormMajorant n X rest := by
  rw [matrixHornerP3Fold_eq_acc_mul_pow_add_polyDesc n X rest Y]
  let term : Fin n → Fin n → ℝ := matMul n Y (matPow n X rest.length)
  let tail : Fin n → Fin n → ℝ := matrixPolyP3Desc n X rest
  have hadd :
      oneNorm (matAdd n term tail) ≤ oneNorm term + oneNorm tail := by
    simpa [matAdd] using oneNorm_add_le term tail
  have hmul :
      oneNorm term ≤ oneNorm Y * oneNorm (matPow n X rest.length) := by
    simpa [term] using
      oneNorm_matMul_le Y (matPow n X rest.length)
  have hpow :
      oneNorm (matPow n X rest.length) ≤ oneNorm X ^ rest.length :=
    oneNorm_matPow_le X rest.length
  have hterm :
      oneNorm term ≤ oneNorm Y * oneNorm X ^ rest.length :=
    le_trans hmul
      (mul_le_mul_of_nonneg_left hpow (oneNorm_nonneg Y))
  have htail :
      oneNorm tail ≤ matrixPolyP3OneNormMajorant n X rest := by
    simpa [tail] using matrixPolyP3Desc_oneNorm_le_majorant n X rest
  calc
    oneNorm (matAdd n term tail)
        ≤ oneNorm term + oneNorm tail := hadd
    _ ≤ oneNorm Y * oneNorm X ^ rest.length +
          matrixPolyP3OneNormMajorant n X rest :=
        add_le_add hterm htail

lemma infNorm_le_sub_add {n : ℕ}
    (A B : Fin n → Fin n → ℝ) :
    infNorm A ≤ infNorm (fun i j => A i j - B i j) + infNorm B := by
  calc
    infNorm A =
        infNorm (fun i j => (A i j - B i j) + B i j) := by
          congr 1
          ext i j
          ring
    _ ≤ infNorm (fun i j => A i j - B i j) + infNorm B :=
        infNorm_add_le (fun i j => A i j - B i j) B

lemma oneNorm_le_sub_add {n : ℕ}
    (A B : Fin n → Fin n → ℝ) :
    oneNorm A ≤ oneNorm (fun i j => A i j - B i j) + oneNorm B := by
  calc
    oneNorm A =
        oneNorm (fun i j => (A i j - B i j) + B i j) := by
          congr 1
          ext i j
          ring
    _ ≤ oneNorm (fun i j => A i j - B i j) + oneNorm B :=
        oneNorm_add_le (fun i j => A i j - B i j) B

/-- Rounded matrix addition, entry by entry. -/
noncomputable def fl_matAdd (fp : FPModel) (n : ℕ)
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => fp.fl_add (A i j) (B i j)

/-- One rounded matrix-Horner step for `P3`: first form the rounded matrix
product `fl(YX)`, then round the entrywise addition with `A`. -/
noncomputable def fl_matrixHornerP3Step
    (fp : FPModel) (n : ℕ)
    (X Y A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fl_matAdd fp n (fl_matMul fp n n n Y X) A

/-- Rounded matrix-Horner evaluation of `P3` from descending matrix
coefficients `[A_n, ..., A_0]`. -/
noncomputable def fl_matrixHornerP3Desc
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    List (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | [] => zeroMatrix n
  | A :: rest => rest.foldl (fl_matrixHornerP3Step fp n X) A

/-- Local infinity-norm budget for one rounded matrix-Horner step. -/
noncomputable def matrixHornerP3StepInfErrorBudget
    (fp : FPModel) (n : ℕ)
    (X Y A : Fin n → Fin n → ℝ) : ℝ :=
  fp.u * infNorm (matAdd n (fl_matMul fp n n n Y X) A) +
    gamma fp n * infNorm Y * infNorm X

/-- Local one-norm budget for one rounded matrix-Horner step. -/
noncomputable def matrixHornerP3StepOneNormErrorBudget
    (fp : FPModel) (n : ℕ)
    (X Y A : Fin n → Fin n → ℝ) : ℝ :=
  fp.u * oneNorm (matAdd n (fl_matMul fp n n n Y X) A) +
    gamma fp n * oneNorm Y * oneNorm X

theorem fl_matrixHornerP3Step_infNorm_error_bound
    (fp : FPModel) (n : ℕ)
    (X Y A : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    infNorm
        (fun i j =>
          fl_matrixHornerP3Step fp n X Y A i j -
            matrixHornerP3Step n X Y A i j) ≤
      matrixHornerP3StepInfErrorBudget fp n X Y A := by
  let Bhat : Fin n → Fin n → ℝ := fl_matMul fp n n n Y X
  let B : Fin n → Fin n → ℝ := matMul n Y X
  let Eadd : Fin n → Fin n → ℝ :=
    fun i j => fl_matAdd fp n Bhat A i j - matAdd n Bhat A i j
  let Emul : Fin n → Fin n → ℝ := fun i j => Bhat i j - B i j
  have hdecomp :
      (fun i j =>
          fl_matrixHornerP3Step fp n X Y A i j -
            matrixHornerP3Step n X Y A i j) =
        fun i j => Eadd i j + Emul i j := by
    ext i j
    simp [fl_matrixHornerP3Step, matrixHornerP3Step,
      fl_matAdd, matAdd, Eadd, Emul, Bhat, B]
    ring
  rw [hdecomp]
  have hAdd :
      infNorm Eadd ≤ fp.u * infNorm (matAdd n Bhat A) := by
    simpa [Eadd] using fl_matAdd_infNorm_error_bound fp n Bhat A
  have hMul :
      infNorm Emul ≤ gamma fp n * infNorm Y * infNorm X := by
    simpa [Emul, Bhat, B] using
      fl_matMul_infNorm_error_bound fp n Y X hn
  calc
    infNorm (fun i j => Eadd i j + Emul i j)
        ≤ infNorm Eadd + infNorm Emul := infNorm_add_le Eadd Emul
    _ ≤ fp.u * infNorm (matAdd n Bhat A) +
          gamma fp n * infNorm Y * infNorm X :=
        add_le_add hAdd hMul
    _ = matrixHornerP3StepInfErrorBudget fp n X Y A := rfl

theorem fl_matrixHornerP3Step_oneNorm_error_bound
    (fp : FPModel) (n : ℕ)
    (X Y A : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    oneNorm
        (fun i j =>
          fl_matrixHornerP3Step fp n X Y A i j -
            matrixHornerP3Step n X Y A i j) ≤
      matrixHornerP3StepOneNormErrorBudget fp n X Y A := by
  let Bhat : Fin n → Fin n → ℝ := fl_matMul fp n n n Y X
  let B : Fin n → Fin n → ℝ := matMul n Y X
  let Eadd : Fin n → Fin n → ℝ :=
    fun i j => fl_matAdd fp n Bhat A i j - matAdd n Bhat A i j
  let Emul : Fin n → Fin n → ℝ := fun i j => Bhat i j - B i j
  have hdecomp :
      (fun i j =>
          fl_matrixHornerP3Step fp n X Y A i j -
            matrixHornerP3Step n X Y A i j) =
        fun i j => Eadd i j + Emul i j := by
    ext i j
    simp [fl_matrixHornerP3Step, matrixHornerP3Step,
      fl_matAdd, matAdd, Eadd, Emul, Bhat, B]
    ring
  rw [hdecomp]
  have hAdd :
      oneNorm Eadd ≤ fp.u * oneNorm (matAdd n Bhat A) := by
    simpa [Eadd] using fl_matAdd_oneNorm_error_bound fp n Bhat A
  have hMul :
      oneNorm Emul ≤ gamma fp n * oneNorm Y * oneNorm X := by
    simpa [Emul, Bhat, B] using
      fl_matMul_oneNorm_error_bound fp n Y X hn
  calc
    oneNorm (fun i j => Eadd i j + Emul i j)
        ≤ oneNorm Eadd + oneNorm Emul := oneNorm_add_le Eadd Emul
    _ ≤ fp.u * oneNorm (matAdd n Bhat A) +
          gamma fp n * oneNorm Y * oneNorm X :=
        add_le_add hAdd hMul
    _ = matrixHornerP3StepOneNormErrorBudget fp n X Y A := rfl

theorem matrixHornerP3StepInfErrorBudget_le_acc_majorant
    (fp : FPModel) (n : ℕ)
    (X Yhat A : Fin n → Fin n → ℝ) (eta mu : ℝ)
    (hnpos : 0 < n) (hn : gammaValid fp n)
    (hYhat : infNorm Yhat ≤ eta + mu) :
    matrixHornerP3StepInfErrorBudget fp n X Yhat A ≤
      fp.u * ((1 + gamma fp n) * (eta + mu) * infNorm X +
          infNorm A) +
        gamma fp n * (eta + mu) * infNorm X := by
  let Bhat : Fin n → Fin n → ℝ := fl_matMul fp n n n Yhat X
  let B : Fin n → Fin n → ℝ := matMul n Yhat X
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hX : 0 ≤ infNorm X := infNorm_nonneg X
  have hY : 0 ≤ infNorm Yhat := infNorm_nonneg Yhat
  have hsrc_nonneg : 0 ≤ eta + mu := le_trans hY hYhat
  have hBhat :
      infNorm Bhat ≤ (1 + gamma fp n) * infNorm Yhat * infNorm X := by
    have htri := infNorm_le_sub_add Bhat B
    have herr :
        infNorm (fun i j => Bhat i j - B i j) ≤
          gamma fp n * infNorm Yhat * infNorm X := by
      simpa [Bhat, B] using
        fl_matMul_infNorm_error_bound fp n Yhat X hn
    have hmul :
        infNorm B ≤ infNorm Yhat * infNorm X := by
      simpa [B] using infNorm_matMul_le hnpos Yhat X
    calc
      infNorm Bhat
          ≤ infNorm (fun i j => Bhat i j - B i j) + infNorm B := htri
      _ ≤ gamma fp n * infNorm Yhat * infNorm X +
            infNorm Yhat * infNorm X := add_le_add herr hmul
      _ = (1 + gamma fp n) * infNorm Yhat * infNorm X := by
          ring
  have hadd :
      infNorm (matAdd n Bhat A) ≤
        (1 + gamma fp n) * infNorm Yhat * infNorm X + infNorm A := by
    calc
      infNorm (matAdd n Bhat A)
          ≤ infNorm Bhat + infNorm A := by
            simpa [matAdd] using infNorm_add_le Bhat A
      _ ≤ (1 + gamma fp n) * infNorm Yhat * infNorm X +
            infNorm A := add_le_add hBhat le_rfl
  have hfactor₁ : 0 ≤ (1 + gamma fp n) * infNorm X :=
    mul_nonneg (by linarith) hX
  have hYterm :
      (1 + gamma fp n) * infNorm Yhat * infNorm X ≤
        (1 + gamma fp n) * (eta + mu) * infNorm X := by
    calc
      (1 + gamma fp n) * infNorm Yhat * infNorm X
          = ((1 + gamma fp n) * infNorm X) * infNorm Yhat := by
            ring
      _ ≤ ((1 + gamma fp n) * infNorm X) * (eta + mu) :=
            mul_le_mul_of_nonneg_left hYhat hfactor₁
      _ = (1 + gamma fp n) * (eta + mu) * infNorm X := by
            ring
  have hadd_source :
      infNorm (matAdd n Bhat A) ≤
        (1 + gamma fp n) * (eta + mu) * infNorm X + infNorm A :=
    le_trans hadd (add_le_add hYterm le_rfl)
  have hfactor₂ : 0 ≤ gamma fp n * infNorm X :=
    mul_nonneg hγ hX
  have hγterm :
      gamma fp n * infNorm Yhat * infNorm X ≤
        gamma fp n * (eta + mu) * infNorm X := by
    calc
      gamma fp n * infNorm Yhat * infNorm X
          = (gamma fp n * infNorm X) * infNorm Yhat := by
            ring
      _ ≤ (gamma fp n * infNorm X) * (eta + mu) :=
            mul_le_mul_of_nonneg_left hYhat hfactor₂
      _ = gamma fp n * (eta + mu) * infNorm X := by
            ring
  unfold matrixHornerP3StepInfErrorBudget
  exact add_le_add
    (mul_le_mul_of_nonneg_left hadd_source fp.u_nonneg)
    hγterm

theorem matrixHornerP3StepOneNormErrorBudget_le_acc_majorant
    (fp : FPModel) (n : ℕ)
    (X Yhat A : Fin n → Fin n → ℝ) (eta mu : ℝ)
    (hn : gammaValid fp n)
    (hYhat : oneNorm Yhat ≤ eta + mu) :
    matrixHornerP3StepOneNormErrorBudget fp n X Yhat A ≤
      fp.u * ((1 + gamma fp n) * (eta + mu) * oneNorm X +
          oneNorm A) +
        gamma fp n * (eta + mu) * oneNorm X := by
  let Bhat : Fin n → Fin n → ℝ := fl_matMul fp n n n Yhat X
  let B : Fin n → Fin n → ℝ := matMul n Yhat X
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hX : 0 ≤ oneNorm X := oneNorm_nonneg X
  have hY : 0 ≤ oneNorm Yhat := oneNorm_nonneg Yhat
  have hsrc_nonneg : 0 ≤ eta + mu := le_trans hY hYhat
  have hBhat :
      oneNorm Bhat ≤ (1 + gamma fp n) * oneNorm Yhat * oneNorm X := by
    have htri := oneNorm_le_sub_add Bhat B
    have herr :
        oneNorm (fun i j => Bhat i j - B i j) ≤
          gamma fp n * oneNorm Yhat * oneNorm X := by
      simpa [Bhat, B] using
        fl_matMul_oneNorm_error_bound fp n Yhat X hn
    have hmul :
        oneNorm B ≤ oneNorm Yhat * oneNorm X := by
      simpa [B] using oneNorm_matMul_le Yhat X
    calc
      oneNorm Bhat
          ≤ oneNorm (fun i j => Bhat i j - B i j) + oneNorm B := htri
      _ ≤ gamma fp n * oneNorm Yhat * oneNorm X +
            oneNorm Yhat * oneNorm X := add_le_add herr hmul
      _ = (1 + gamma fp n) * oneNorm Yhat * oneNorm X := by
          ring
  have hadd :
      oneNorm (matAdd n Bhat A) ≤
        (1 + gamma fp n) * oneNorm Yhat * oneNorm X + oneNorm A := by
    calc
      oneNorm (matAdd n Bhat A)
          ≤ oneNorm Bhat + oneNorm A := by
            simpa [matAdd] using oneNorm_add_le Bhat A
      _ ≤ (1 + gamma fp n) * oneNorm Yhat * oneNorm X +
            oneNorm A := add_le_add hBhat le_rfl
  have hfactor₁ : 0 ≤ (1 + gamma fp n) * oneNorm X :=
    mul_nonneg (by linarith) hX
  have hYterm :
      (1 + gamma fp n) * oneNorm Yhat * oneNorm X ≤
        (1 + gamma fp n) * (eta + mu) * oneNorm X := by
    calc
      (1 + gamma fp n) * oneNorm Yhat * oneNorm X
          = ((1 + gamma fp n) * oneNorm X) * oneNorm Yhat := by
            ring
      _ ≤ ((1 + gamma fp n) * oneNorm X) * (eta + mu) :=
            mul_le_mul_of_nonneg_left hYhat hfactor₁
      _ = (1 + gamma fp n) * (eta + mu) * oneNorm X := by
            ring
  have hadd_source :
      oneNorm (matAdd n Bhat A) ≤
        (1 + gamma fp n) * (eta + mu) * oneNorm X + oneNorm A :=
    le_trans hadd (add_le_add hYterm le_rfl)
  have hfactor₂ : 0 ≤ gamma fp n * oneNorm X :=
    mul_nonneg hγ hX
  have hγterm :
      gamma fp n * oneNorm Yhat * oneNorm X ≤
        gamma fp n * (eta + mu) * oneNorm X := by
    calc
      gamma fp n * oneNorm Yhat * oneNorm X
          = (gamma fp n * oneNorm X) * oneNorm Yhat := by
            ring
      _ ≤ (gamma fp n * oneNorm X) * (eta + mu) :=
            mul_le_mul_of_nonneg_left hYhat hfactor₂
      _ = gamma fp n * (eta + mu) * oneNorm X := by
            ring
  unfold matrixHornerP3StepOneNormErrorBudget
  exact add_le_add
    (mul_le_mul_of_nonneg_left hadd_source fp.u_nonneg)
    hγterm

lemma matrixHornerP3Step_infNorm_lipschitz
    (n : ℕ) (hn : 0 < n)
    (X Y Z A : Fin n → Fin n → ℝ) :
    infNorm
        (fun i j =>
          matrixHornerP3Step n X Y A i j -
            matrixHornerP3Step n X Z A i j) ≤
      infNorm (fun i j => Y i j - Z i j) * infNorm X := by
  have hmat :
      (fun i j =>
          matrixHornerP3Step n X Y A i j -
            matrixHornerP3Step n X Z A i j) =
        matMul n (fun i j => Y i j - Z i j) X := by
    ext i j
    simp [matrixHornerP3Step, matAdd, matMul]
    calc
      (∑ k : Fin n, Y i k * X k j) - ∑ k : Fin n, Z i k * X k j
          = ∑ k : Fin n, (Y i k * X k j - Z i k * X k j) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ k : Fin n, (Y i k - Z i k) * X k j := by
            apply Finset.sum_congr rfl
            intro k _
            ring
  rw [hmat]
  exact infNorm_matMul_le hn (fun i j => Y i j - Z i j) X

lemma matrixHornerP3Step_oneNorm_lipschitz
    (n : ℕ)
    (X Y Z A : Fin n → Fin n → ℝ) :
    oneNorm
        (fun i j =>
          matrixHornerP3Step n X Y A i j -
            matrixHornerP3Step n X Z A i j) ≤
      oneNorm (fun i j => Y i j - Z i j) * oneNorm X := by
  have hmat :
      (fun i j =>
          matrixHornerP3Step n X Y A i j -
            matrixHornerP3Step n X Z A i j) =
        matMul n (fun i j => Y i j - Z i j) X := by
    ext i j
    simp [matrixHornerP3Step, matAdd, matMul]
    calc
      (∑ k : Fin n, Y i k * X k j) - ∑ k : Fin n, Z i k * X k j
          = ∑ k : Fin n, (Y i k * X k j - Z i k * X k j) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ k : Fin n, (Y i k - Z i k) * X k j := by
            apply Finset.sum_congr rfl
            intro k _
            ring
  rw [hmat]
  exact oneNorm_matMul_le (fun i j => Y i j - Z i j) X

/-- Recursive finite infinity-norm budget for a rounded matrix-Horner fold from
an already computed accumulator with current error budget `mu`. -/
noncomputable def matrixHornerP3ForwardInfErrorBudgetFrom
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    (Fin n → Fin n → ℝ) → ℝ →
      List (Fin n → Fin n → ℝ) → ℝ
  | _Yhat, mu, [] => mu
  | Yhat, mu, A :: rest =>
      let mu' :=
        matrixHornerP3StepInfErrorBudget fp n X Yhat A +
          mu * infNorm X
      matrixHornerP3ForwardInfErrorBudgetFrom fp n X
        (fl_matrixHornerP3Step fp n X Yhat A) mu' rest

/-- Top-level recursive finite infinity-norm budget for rounded matrix Horner.
The leading coefficient is used as the initial accumulator, so the initial
storage error is zero. -/
noncomputable def matrixHornerP3ForwardInfErrorBudget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    List (Fin n → Fin n → ℝ) → ℝ
  | [] => 0
  | A :: rest =>
      matrixHornerP3ForwardInfErrorBudgetFrom fp n X A 0 rest

/-- Recursive finite one-norm budget for a rounded matrix-Horner fold from an
already computed accumulator with current error budget `mu`. -/
noncomputable def matrixHornerP3ForwardOneNormErrorBudgetFrom
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    (Fin n → Fin n → ℝ) → ℝ →
      List (Fin n → Fin n → ℝ) → ℝ
  | _Yhat, mu, [] => mu
  | Yhat, mu, A :: rest =>
      let mu' :=
        matrixHornerP3StepOneNormErrorBudget fp n X Yhat A +
          mu * oneNorm X
      matrixHornerP3ForwardOneNormErrorBudgetFrom fp n X
        (fl_matrixHornerP3Step fp n X Yhat A) mu' rest

/-- Top-level recursive finite one-norm budget for rounded matrix Horner. -/
noncomputable def matrixHornerP3ForwardOneNormErrorBudget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    List (Fin n → Fin n → ℝ) → ℝ
  | [] => 0
  | A :: rest =>
      matrixHornerP3ForwardOneNormErrorBudgetFrom fp n X A 0 rest

theorem fl_matrixHornerP3Fold_infNorm_error_bound_from
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    ∀ (rest : List (Fin n → Fin n → ℝ))
      (Yhat Y : Fin n → Fin n → ℝ) (mu : ℝ),
      0 ≤ mu →
      infNorm (fun i j => Yhat i j - Y i j) ≤ mu →
      infNorm
          (fun i j =>
            rest.foldl (fl_matrixHornerP3Step fp n X) Yhat i j -
              rest.foldl (matrixHornerP3Step n X) Y i j) ≤
        matrixHornerP3ForwardInfErrorBudgetFrom fp n X Yhat mu rest := by
  intro rest
  induction rest with
  | nil =>
      intro Yhat Y mu _hmu herr
      simpa [matrixHornerP3ForwardInfErrorBudgetFrom] using herr
  | cons A rest ih =>
      intro Yhat Y mu hmu herr
      let Yhat' := fl_matrixHornerP3Step fp n X Yhat A
      let Y' := matrixHornerP3Step n X Y A
      let mu' :=
        matrixHornerP3StepInfErrorBudget fp n X Yhat A +
          mu * infNorm X
      have hbudget_nonneg :
          0 ≤ matrixHornerP3StepInfErrorBudget fp n X Yhat A := by
        have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
        have hY : 0 ≤ infNorm Yhat := infNorm_nonneg Yhat
        have hX : 0 ≤ infNorm X := infNorm_nonneg X
        unfold matrixHornerP3StepInfErrorBudget
        exact add_nonneg
          (mul_nonneg fp.u_nonneg (infNorm_nonneg _))
          (mul_nonneg (mul_nonneg hγ hY) hX)
      have hmu' : 0 ≤ mu' := by
        have hX : 0 ≤ infNorm X := infNorm_nonneg X
        exact add_nonneg hbudget_nonneg (mul_nonneg hmu hX)
      have hstep :
          infNorm (fun i j => Yhat' i j - Y' i j) ≤ mu' := by
        let Elocal : Fin n → Fin n → ℝ :=
          fun i j =>
            fl_matrixHornerP3Step fp n X Yhat A i j -
              matrixHornerP3Step n X Yhat A i j
        let Eprop : Fin n → Fin n → ℝ :=
          fun i j =>
            matrixHornerP3Step n X Yhat A i j -
              matrixHornerP3Step n X Y A i j
        have hdecomp :
            (fun i j => Yhat' i j - Y' i j) =
              fun i j => Elocal i j + Eprop i j := by
          ext i j
          simp [Yhat', Y', Elocal, Eprop]
        have hlocal :
            infNorm Elocal ≤
              matrixHornerP3StepInfErrorBudget fp n X Yhat A := by
          simpa [Elocal] using
            fl_matrixHornerP3Step_infNorm_error_bound fp n X Yhat A hn
        have hprop :
            infNorm Eprop ≤ mu * infNorm X := by
          have hprop0 :
              infNorm Eprop ≤
                infNorm (fun i j => Yhat i j - Y i j) * infNorm X := by
            simpa [Eprop] using
              matrixHornerP3Step_infNorm_lipschitz n hnpos X Yhat Y A
          exact le_trans hprop0
            (mul_le_mul_of_nonneg_right herr (infNorm_nonneg X))
        calc
          infNorm (fun i j => Yhat' i j - Y' i j)
              = infNorm (fun i j => Elocal i j + Eprop i j) := by
                rw [hdecomp]
          _ ≤ infNorm Elocal + infNorm Eprop := infNorm_add_le Elocal Eprop
          _ ≤ matrixHornerP3StepInfErrorBudget fp n X Yhat A +
                mu * infNorm X := add_le_add hlocal hprop
          _ = mu' := rfl
      simpa [matrixHornerP3ForwardInfErrorBudgetFrom, Yhat', Y', mu'] using
        ih Yhat' Y' mu' hmu' hstep

theorem fl_matrixHornerP3Desc_infNorm_error_bound
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    infNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixHornerP3Desc n X coeffsDesc i j) ≤
      matrixHornerP3ForwardInfErrorBudget fp n X coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      have hzero :
          (fun i j =>
            fl_matrixHornerP3Desc fp n X [] i j -
              matrixHornerP3Desc n X [] i j) =
            zeroMatrix n := by
        ext i j
        simp [fl_matrixHornerP3Desc, matrixHornerP3Desc, zeroMatrix]
      rw [hzero, matrixHornerP3ForwardInfErrorBudget]
      exact le_of_eq (infNorm_zeroMatrix n)
  | cons A rest =>
      have hinit :
          infNorm (fun i j => A i j - A i j) ≤ 0 := by
        have hzero :
            (fun i j => A i j - A i j) = zeroMatrix n := by
          ext i j
          simp [zeroMatrix]
        rw [hzero, infNorm_zeroMatrix]
      simpa [fl_matrixHornerP3Desc, matrixHornerP3Desc,
        matrixHornerP3ForwardInfErrorBudget] using
        fl_matrixHornerP3Fold_infNorm_error_bound_from
          fp n X hnpos hn rest A A 0 (by norm_num) hinit

theorem fl_matrixHornerP3Fold_oneNorm_error_bound_from
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∀ (rest : List (Fin n → Fin n → ℝ))
      (Yhat Y : Fin n → Fin n → ℝ) (mu : ℝ),
      0 ≤ mu →
      oneNorm (fun i j => Yhat i j - Y i j) ≤ mu →
      oneNorm
          (fun i j =>
            rest.foldl (fl_matrixHornerP3Step fp n X) Yhat i j -
              rest.foldl (matrixHornerP3Step n X) Y i j) ≤
        matrixHornerP3ForwardOneNormErrorBudgetFrom fp n X Yhat mu rest := by
  intro rest
  induction rest with
  | nil =>
      intro Yhat Y mu _hmu herr
      simpa [matrixHornerP3ForwardOneNormErrorBudgetFrom] using herr
  | cons A rest ih =>
      intro Yhat Y mu hmu herr
      let Yhat' := fl_matrixHornerP3Step fp n X Yhat A
      let Y' := matrixHornerP3Step n X Y A
      let mu' :=
        matrixHornerP3StepOneNormErrorBudget fp n X Yhat A +
          mu * oneNorm X
      have hbudget_nonneg :
          0 ≤ matrixHornerP3StepOneNormErrorBudget fp n X Yhat A := by
        have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
        have hY : 0 ≤ oneNorm Yhat := oneNorm_nonneg Yhat
        have hX : 0 ≤ oneNorm X := oneNorm_nonneg X
        unfold matrixHornerP3StepOneNormErrorBudget
        exact add_nonneg
          (mul_nonneg fp.u_nonneg (oneNorm_nonneg _))
          (mul_nonneg (mul_nonneg hγ hY) hX)
      have hmu' : 0 ≤ mu' := by
        have hX : 0 ≤ oneNorm X := oneNorm_nonneg X
        exact add_nonneg hbudget_nonneg (mul_nonneg hmu hX)
      have hstep :
          oneNorm (fun i j => Yhat' i j - Y' i j) ≤ mu' := by
        let Elocal : Fin n → Fin n → ℝ :=
          fun i j =>
            fl_matrixHornerP3Step fp n X Yhat A i j -
              matrixHornerP3Step n X Yhat A i j
        let Eprop : Fin n → Fin n → ℝ :=
          fun i j =>
            matrixHornerP3Step n X Yhat A i j -
              matrixHornerP3Step n X Y A i j
        have hdecomp :
            (fun i j => Yhat' i j - Y' i j) =
              fun i j => Elocal i j + Eprop i j := by
          ext i j
          simp [Yhat', Y', Elocal, Eprop]
        have hlocal :
            oneNorm Elocal ≤
              matrixHornerP3StepOneNormErrorBudget fp n X Yhat A := by
          simpa [Elocal] using
            fl_matrixHornerP3Step_oneNorm_error_bound fp n X Yhat A hn
        have hprop :
            oneNorm Eprop ≤ mu * oneNorm X := by
          have hprop0 :
              oneNorm Eprop ≤
                oneNorm (fun i j => Yhat i j - Y i j) * oneNorm X := by
            simpa [Eprop] using
              matrixHornerP3Step_oneNorm_lipschitz n X Yhat Y A
          exact le_trans hprop0
            (mul_le_mul_of_nonneg_right herr (oneNorm_nonneg X))
        calc
          oneNorm (fun i j => Yhat' i j - Y' i j)
              = oneNorm (fun i j => Elocal i j + Eprop i j) := by
                rw [hdecomp]
          _ ≤ oneNorm Elocal + oneNorm Eprop := oneNorm_add_le Elocal Eprop
          _ ≤ matrixHornerP3StepOneNormErrorBudget fp n X Yhat A +
                mu * oneNorm X := add_le_add hlocal hprop
          _ = mu' := rfl
      simpa [matrixHornerP3ForwardOneNormErrorBudgetFrom, Yhat', Y', mu'] using
        ih Yhat' Y' mu' hmu' hstep

theorem fl_matrixHornerP3Desc_oneNorm_error_bound
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    oneNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixHornerP3Desc n X coeffsDesc i j) ≤
      matrixHornerP3ForwardOneNormErrorBudget fp n X coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      have hzero :
          (fun i j =>
            fl_matrixHornerP3Desc fp n X [] i j -
              matrixHornerP3Desc n X [] i j) =
            zeroMatrix n := by
        ext i j
        simp [fl_matrixHornerP3Desc, matrixHornerP3Desc, zeroMatrix]
      rw [hzero, matrixHornerP3ForwardOneNormErrorBudget]
      have hone_zero : oneNorm (zeroMatrix n) = 0 := by
        unfold oneNorm
        simpa [zeroMatrix] using infNorm_zeroMatrix n
      exact le_of_eq hone_zero
  | cons A rest =>
      have hinit :
          oneNorm (fun i j => A i j - A i j) ≤ 0 := by
        have hzero :
            (fun i j => A i j - A i j) = zeroMatrix n := by
          ext i j
          simp [zeroMatrix]
        rw [hzero]
        have hone_zero : oneNorm (zeroMatrix n) = 0 := by
          unfold oneNorm
          simpa [zeroMatrix] using infNorm_zeroMatrix n
        rw [hone_zero]
      simpa [fl_matrixHornerP3Desc, matrixHornerP3Desc,
        matrixHornerP3ForwardOneNormErrorBudget] using
        fl_matrixHornerP3Fold_oneNorm_error_bound_from
          fp n X hn rest A A 0 (by norm_num) hinit

/-- Source-shaped local scalar infinity-norm budget for one rounded matrix
Horner step in Problem 5.6.  The parameter `eta` bounds the exact accumulator
and `mu` bounds the accumulated error, so the computed accumulator is charged
only through `eta + mu`. -/
noncomputable def matrixHornerP3ScalarInfStepBudget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (eta mu : ℝ) (A : Fin n → Fin n → ℝ) : ℝ :=
  fp.u * ((1 + gamma fp n) * (eta + mu) * infNorm X + infNorm A) +
    gamma fp n * (eta + mu) * infNorm X

/-- Source-shaped local scalar one-norm budget for one rounded matrix Horner
step in Problem 5.6. -/
noncomputable def matrixHornerP3ScalarOneNormStepBudget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (eta mu : ℝ) (A : Fin n → Fin n → ℝ) : ℝ :=
  fp.u * ((1 + gamma fp n) * (eta + mu) * oneNorm X + oneNorm A) +
    gamma fp n * (eta + mu) * oneNorm X

/-- Recursive source-shaped scalar infinity-norm budget for rounded matrix
Horner.  It follows only the scalar exact-accumulator majorant `eta` and scalar
error majorant `mu`, avoiding computed matrix norms in the recurrence. -/
noncomputable def matrixHornerP3ScalarInfForwardBudgetFrom
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    ℝ → ℝ → List (Fin n → Fin n → ℝ) → ℝ
  | _eta, mu, [] => mu
  | eta, mu, A :: rest =>
      let eta' := eta * infNorm X + infNorm A
      let mu' :=
        matrixHornerP3ScalarInfStepBudget fp n X eta mu A +
          mu * infNorm X
      matrixHornerP3ScalarInfForwardBudgetFrom fp n X eta' mu' rest

/-- Top-level source-shaped scalar infinity-norm budget for rounded matrix
Horner. -/
noncomputable def matrixHornerP3ScalarInfForwardBudget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    List (Fin n → Fin n → ℝ) → ℝ
  | [] => 0
  | A :: rest =>
      matrixHornerP3ScalarInfForwardBudgetFrom fp n X (infNorm A) 0 rest

/-- Recursive source-shaped scalar one-norm budget for rounded matrix Horner. -/
noncomputable def matrixHornerP3ScalarOneNormForwardBudgetFrom
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    ℝ → ℝ → List (Fin n → Fin n → ℝ) → ℝ
  | _eta, mu, [] => mu
  | eta, mu, A :: rest =>
      let eta' := eta * oneNorm X + oneNorm A
      let mu' :=
        matrixHornerP3ScalarOneNormStepBudget fp n X eta mu A +
          mu * oneNorm X
      matrixHornerP3ScalarOneNormForwardBudgetFrom fp n X eta' mu' rest

/-- Top-level source-shaped scalar one-norm budget for rounded matrix Horner. -/
noncomputable def matrixHornerP3ScalarOneNormForwardBudget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ) :
    List (Fin n → Fin n → ℝ) → ℝ
  | [] => 0
  | A :: rest =>
      matrixHornerP3ScalarOneNormForwardBudgetFrom fp n X (oneNorm A) 0 rest

theorem matrixHornerP3ForwardInfErrorBudgetFrom_le_scalar
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    ∀ (rest : List (Fin n → Fin n → ℝ))
      (Yhat Y : Fin n → Fin n → ℝ) (eta mu muSrc : ℝ),
      0 ≤ mu →
      0 ≤ muSrc →
      0 ≤ eta →
      mu ≤ muSrc →
      infNorm (fun i j => Yhat i j - Y i j) ≤ mu →
      infNorm Y ≤ eta →
      matrixHornerP3ForwardInfErrorBudgetFrom fp n X Yhat mu rest ≤
        matrixHornerP3ScalarInfForwardBudgetFrom fp n X eta muSrc rest := by
  intro rest
  induction rest with
  | nil =>
      intro Yhat Y eta mu muSrc _hmu _hmuSrc _heta hle _herr _hY
      simpa [matrixHornerP3ForwardInfErrorBudgetFrom,
        matrixHornerP3ScalarInfForwardBudgetFrom] using hle
  | cons A rest ih =>
      intro Yhat Y eta mu muSrc hmu hmuSrc heta hle herr hY
      let Yhat' := fl_matrixHornerP3Step fp n X Yhat A
      let Y' := matrixHornerP3Step n X Y A
      let localBudget := matrixHornerP3StepInfErrorBudget fp n X Yhat A
      let mu' := localBudget + mu * infNorm X
      let eta' := eta * infNorm X + infNorm A
      let sourceStep :=
        matrixHornerP3ScalarInfStepBudget fp n X eta muSrc A
      let muSrc' := sourceStep + muSrc * infNorm X
      have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
      have hX : 0 ≤ infNorm X := infNorm_nonneg X
      have hYhat_norm : infNorm Yhat ≤ eta + muSrc := by
        calc
          infNorm Yhat
              ≤ infNorm (fun i j => Yhat i j - Y i j) + infNorm Y :=
                infNorm_le_sub_add Yhat Y
          _ ≤ mu + eta := add_le_add herr hY
          _ ≤ muSrc + eta := add_le_add hle le_rfl
          _ = eta + muSrc := by ring
      have hlocal_le : localBudget ≤ sourceStep := by
        simpa [localBudget, sourceStep, matrixHornerP3ScalarInfStepBudget] using
          matrixHornerP3StepInfErrorBudget_le_acc_majorant
            fp n X Yhat A eta muSrc hnpos hn hYhat_norm
      have hlocal_nonneg : 0 ≤ localBudget := by
        have hYhat_nonneg : 0 ≤ infNorm Yhat := infNorm_nonneg Yhat
        unfold localBudget matrixHornerP3StepInfErrorBudget
        exact add_nonneg
          (mul_nonneg fp.u_nonneg (infNorm_nonneg _))
          (mul_nonneg (mul_nonneg hγ hYhat_nonneg) hX)
      have hmu' : 0 ≤ mu' := by
        exact add_nonneg hlocal_nonneg (mul_nonneg hmu hX)
      have hsourceStep_nonneg : 0 ≤ sourceStep := by
        have hsum : 0 ≤ eta + muSrc := add_nonneg heta hmuSrc
        have honeγ : 0 ≤ 1 + gamma fp n := by linarith
        have hinside :
            0 ≤ (1 + gamma fp n) * (eta + muSrc) * infNorm X +
              infNorm A := by
          exact add_nonneg
            (mul_nonneg (mul_nonneg honeγ hsum) hX)
            (infNorm_nonneg A)
        have htail :
            0 ≤ gamma fp n * (eta + muSrc) * infNorm X :=
          mul_nonneg (mul_nonneg hγ hsum) hX
        simpa [sourceStep, matrixHornerP3ScalarInfStepBudget] using
          add_nonneg (mul_nonneg fp.u_nonneg hinside) htail
      have hmuSrc' : 0 ≤ muSrc' := by
        exact add_nonneg hsourceStep_nonneg (mul_nonneg hmuSrc hX)
      have hmu'_le : mu' ≤ muSrc' := by
        have hprop : mu * infNorm X ≤ muSrc * infNorm X :=
          mul_le_mul_of_nonneg_right hle hX
        calc
          mu' = localBudget + mu * infNorm X := rfl
          _ ≤ sourceStep + muSrc * infNorm X :=
              add_le_add hlocal_le hprop
          _ = muSrc' := rfl
      have heta' : 0 ≤ eta' := by
        exact add_nonneg (mul_nonneg heta hX) (infNorm_nonneg A)
      have herr' :
          infNorm (fun i j => Yhat' i j - Y' i j) ≤ mu' := by
        have h :=
          fl_matrixHornerP3Fold_infNorm_error_bound_from
            fp n X hnpos hn [A] Yhat Y mu hmu herr
        simpa [Yhat', Y', mu', localBudget,
          matrixHornerP3ForwardInfErrorBudgetFrom] using h
      have hY' : infNorm Y' ≤ eta' := by
        have hstep :
            infNorm Y' ≤ infNorm Y * infNorm X + infNorm A := by
          have hmul :
              infNorm (matMul n Y X) ≤ infNorm Y * infNorm X := by
            simpa using infNorm_matMul_le hnpos Y X
          have hadd :
              infNorm (matrixHornerP3Step n X Y A) ≤
                infNorm (matMul n Y X) + infNorm A := by
            simpa [matrixHornerP3Step, matAdd] using
              infNorm_add_le (matMul n Y X) A
          calc
            infNorm Y'
                ≤ infNorm (matMul n Y X) + infNorm A := by
                  simpa [Y'] using hadd
            _ ≤ infNorm Y * infNorm X + infNorm A :=
                add_le_add hmul le_rfl
        calc
          infNorm Y'
              ≤ infNorm Y * infNorm X + infNorm A := hstep
          _ ≤ eta * infNorm X + infNorm A :=
              add_le_add (mul_le_mul_of_nonneg_right hY hX) le_rfl
          _ = eta' := rfl
      have hrec :=
        ih Yhat' Y' eta' mu' muSrc'
          hmu' hmuSrc' heta' hmu'_le herr' hY'
      simpa [matrixHornerP3ForwardInfErrorBudgetFrom,
        matrixHornerP3ScalarInfForwardBudgetFrom, Yhat', mu', eta',
        sourceStep, muSrc', localBudget] using hrec

theorem matrixHornerP3ForwardOneNormErrorBudgetFrom_le_scalar
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∀ (rest : List (Fin n → Fin n → ℝ))
      (Yhat Y : Fin n → Fin n → ℝ) (eta mu muSrc : ℝ),
      0 ≤ mu →
      0 ≤ muSrc →
      0 ≤ eta →
      mu ≤ muSrc →
      oneNorm (fun i j => Yhat i j - Y i j) ≤ mu →
      oneNorm Y ≤ eta →
      matrixHornerP3ForwardOneNormErrorBudgetFrom fp n X Yhat mu rest ≤
        matrixHornerP3ScalarOneNormForwardBudgetFrom fp n X eta muSrc rest := by
  intro rest
  induction rest with
  | nil =>
      intro Yhat Y eta mu muSrc _hmu _hmuSrc _heta hle _herr _hY
      simpa [matrixHornerP3ForwardOneNormErrorBudgetFrom,
        matrixHornerP3ScalarOneNormForwardBudgetFrom] using hle
  | cons A rest ih =>
      intro Yhat Y eta mu muSrc hmu hmuSrc heta hle herr hY
      let Yhat' := fl_matrixHornerP3Step fp n X Yhat A
      let Y' := matrixHornerP3Step n X Y A
      let localBudget := matrixHornerP3StepOneNormErrorBudget fp n X Yhat A
      let mu' := localBudget + mu * oneNorm X
      let eta' := eta * oneNorm X + oneNorm A
      let sourceStep :=
        matrixHornerP3ScalarOneNormStepBudget fp n X eta muSrc A
      let muSrc' := sourceStep + muSrc * oneNorm X
      have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
      have hX : 0 ≤ oneNorm X := oneNorm_nonneg X
      have hYhat_norm : oneNorm Yhat ≤ eta + muSrc := by
        calc
          oneNorm Yhat
              ≤ oneNorm (fun i j => Yhat i j - Y i j) + oneNorm Y :=
                oneNorm_le_sub_add Yhat Y
          _ ≤ mu + eta := add_le_add herr hY
          _ ≤ muSrc + eta := add_le_add hle le_rfl
          _ = eta + muSrc := by ring
      have hlocal_le : localBudget ≤ sourceStep := by
        simpa [localBudget, sourceStep, matrixHornerP3ScalarOneNormStepBudget] using
          matrixHornerP3StepOneNormErrorBudget_le_acc_majorant
            fp n X Yhat A eta muSrc hn hYhat_norm
      have hlocal_nonneg : 0 ≤ localBudget := by
        have hYhat_nonneg : 0 ≤ oneNorm Yhat := oneNorm_nonneg Yhat
        unfold localBudget matrixHornerP3StepOneNormErrorBudget
        exact add_nonneg
          (mul_nonneg fp.u_nonneg (oneNorm_nonneg _))
          (mul_nonneg (mul_nonneg hγ hYhat_nonneg) hX)
      have hmu' : 0 ≤ mu' := by
        exact add_nonneg hlocal_nonneg (mul_nonneg hmu hX)
      have hsourceStep_nonneg : 0 ≤ sourceStep := by
        have hsum : 0 ≤ eta + muSrc := add_nonneg heta hmuSrc
        have honeγ : 0 ≤ 1 + gamma fp n := by linarith
        have hinside :
            0 ≤ (1 + gamma fp n) * (eta + muSrc) * oneNorm X +
              oneNorm A := by
          exact add_nonneg
            (mul_nonneg (mul_nonneg honeγ hsum) hX)
            (oneNorm_nonneg A)
        have htail :
            0 ≤ gamma fp n * (eta + muSrc) * oneNorm X :=
          mul_nonneg (mul_nonneg hγ hsum) hX
        simpa [sourceStep, matrixHornerP3ScalarOneNormStepBudget] using
          add_nonneg (mul_nonneg fp.u_nonneg hinside) htail
      have hmuSrc' : 0 ≤ muSrc' := by
        exact add_nonneg hsourceStep_nonneg (mul_nonneg hmuSrc hX)
      have hmu'_le : mu' ≤ muSrc' := by
        have hprop : mu * oneNorm X ≤ muSrc * oneNorm X :=
          mul_le_mul_of_nonneg_right hle hX
        calc
          mu' = localBudget + mu * oneNorm X := rfl
          _ ≤ sourceStep + muSrc * oneNorm X :=
              add_le_add hlocal_le hprop
          _ = muSrc' := rfl
      have heta' : 0 ≤ eta' := by
        exact add_nonneg (mul_nonneg heta hX) (oneNorm_nonneg A)
      have herr' :
          oneNorm (fun i j => Yhat' i j - Y' i j) ≤ mu' := by
        have h :=
          fl_matrixHornerP3Fold_oneNorm_error_bound_from
            fp n X hn [A] Yhat Y mu hmu herr
        simpa [Yhat', Y', mu', localBudget,
          matrixHornerP3ForwardOneNormErrorBudgetFrom] using h
      have hY' : oneNorm Y' ≤ eta' := by
        have hstep :
            oneNorm Y' ≤ oneNorm Y * oneNorm X + oneNorm A := by
          have hmul :
              oneNorm (matMul n Y X) ≤ oneNorm Y * oneNorm X := by
            simpa using oneNorm_matMul_le Y X
          have hadd :
              oneNorm (matrixHornerP3Step n X Y A) ≤
                oneNorm (matMul n Y X) + oneNorm A := by
            simpa [matrixHornerP3Step, matAdd] using
              oneNorm_add_le (matMul n Y X) A
          calc
            oneNorm Y'
                ≤ oneNorm (matMul n Y X) + oneNorm A := by
                  simpa [Y'] using hadd
            _ ≤ oneNorm Y * oneNorm X + oneNorm A :=
                add_le_add hmul le_rfl
        calc
          oneNorm Y'
              ≤ oneNorm Y * oneNorm X + oneNorm A := hstep
          _ ≤ eta * oneNorm X + oneNorm A :=
              add_le_add (mul_le_mul_of_nonneg_right hY hX) le_rfl
          _ = eta' := rfl
      have hrec :=
        ih Yhat' Y' eta' mu' muSrc'
          hmu' hmuSrc' heta' hmu'_le herr' hY'
      simpa [matrixHornerP3ForwardOneNormErrorBudgetFrom,
        matrixHornerP3ScalarOneNormForwardBudgetFrom, Yhat', mu', eta',
        sourceStep, muSrc', localBudget] using hrec

theorem matrixHornerP3ForwardInfErrorBudget_le_scalar
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    matrixHornerP3ForwardInfErrorBudget fp n X coeffsDesc ≤
      matrixHornerP3ScalarInfForwardBudget fp n X coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [matrixHornerP3ForwardInfErrorBudget,
        matrixHornerP3ScalarInfForwardBudget]
  | cons A rest =>
      have hinit :
          infNorm (fun i j => A i j - A i j) ≤ 0 := by
        have hzero :
            (fun i j => A i j - A i j) = zeroMatrix n := by
          ext i j
          simp [zeroMatrix]
        rw [hzero, infNorm_zeroMatrix]
      simpa [matrixHornerP3ForwardInfErrorBudget,
        matrixHornerP3ScalarInfForwardBudget] using
        matrixHornerP3ForwardInfErrorBudgetFrom_le_scalar
          fp n X hnpos hn rest A A (infNorm A) 0 0
          (by norm_num) (by norm_num) (infNorm_nonneg A)
          (by norm_num) hinit le_rfl

theorem matrixHornerP3ForwardOneNormErrorBudget_le_scalar
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    matrixHornerP3ForwardOneNormErrorBudget fp n X coeffsDesc ≤
      matrixHornerP3ScalarOneNormForwardBudget fp n X coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [matrixHornerP3ForwardOneNormErrorBudget,
        matrixHornerP3ScalarOneNormForwardBudget]
  | cons A rest =>
      have hinit :
          oneNorm (fun i j => A i j - A i j) ≤ 0 := by
        have hzero :
            (fun i j => A i j - A i j) = zeroMatrix n := by
          ext i j
          simp [zeroMatrix]
        rw [hzero]
        have hone_zero : oneNorm (zeroMatrix n) = 0 := by
          unfold oneNorm
          simpa [zeroMatrix] using infNorm_zeroMatrix n
        rw [hone_zero]
      simpa [matrixHornerP3ForwardOneNormErrorBudget,
        matrixHornerP3ScalarOneNormForwardBudget] using
        matrixHornerP3ForwardOneNormErrorBudgetFrom_le_scalar
          fp n X hn rest A A (oneNorm A) 0 0
          (by norm_num) (by norm_num) (oneNorm_nonneg A)
          (by norm_num) hinit le_rfl

/-- The exact scalar roundoff factor for the source-shaped matrix-Horner budget.
Its first-order part is `(n+1)u`, since `gamma fp n = n*u + O(u^2)`. -/
noncomputable def matrixHornerP3ScalarRoundoffFactor
    (fp : FPModel) (n : ℕ) : ℝ :=
  fp.u * (1 + gamma fp n) + gamma fp n

/-- Higher-order remainder after extracting the first-order `(n+1)u` part from
the scalar roundoff factor used in the matrix-Horner source budget. -/
noncomputable def matrixHornerP3ScalarRoundoffFactorRemainder
    (fp : FPModel) (n : ℕ) : ℝ :=
  fp.u * gamma fp n +
    (((n : ℝ) * fp.u) ^ 2) / (1 - (n : ℝ) * fp.u)

theorem matrixHornerP3ScalarRoundoffFactor_eq_first_order_add_remainder
    (fp : FPModel) (n : ℕ) (hn : gammaValid fp n) :
    matrixHornerP3ScalarRoundoffFactor fp n =
      ((n : ℝ) + 1) * fp.u +
        matrixHornerP3ScalarRoundoffFactorRemainder fp n := by
  unfold matrixHornerP3ScalarRoundoffFactor
    matrixHornerP3ScalarRoundoffFactorRemainder
  rw [gamma_eq_linear_plus_quadratic_remainder fp n hn]
  ring

theorem matrixHornerP3ScalarRoundoffFactorRemainder_eq_zero_of_u_eq_zero
    (fp : FPModel) (n : ℕ) (hu : fp.u = 0) :
    matrixHornerP3ScalarRoundoffFactorRemainder fp n = 0 := by
  simp [matrixHornerP3ScalarRoundoffFactorRemainder, gamma, hu]

lemma matrixHornerP3ScalarRoundoffFactor_nonneg
    (fp : FPModel) (n : ℕ) (hn : gammaValid fp n) :
    0 ≤ matrixHornerP3ScalarRoundoffFactor fp n := by
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have honeγ : 0 ≤ 1 + gamma fp n := by linarith
  unfold matrixHornerP3ScalarRoundoffFactor
  exact add_nonneg (mul_nonneg fp.u_nonneg honeγ) hγ

lemma fp_u_le_matrixHornerP3ScalarRoundoffFactor
    (fp : FPModel) (n : ℕ) (hn : gammaValid fp n) :
    fp.u ≤ matrixHornerP3ScalarRoundoffFactor fp n := by
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hprod : 0 ≤ fp.u * gamma fp n := mul_nonneg fp.u_nonneg hγ
  unfold matrixHornerP3ScalarRoundoffFactor
  nlinarith

theorem matrixHornerP3ScalarInfStepBudget_le_factor
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (eta mu : ℝ) (A : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    matrixHornerP3ScalarInfStepBudget fp n X eta mu A ≤
      matrixHornerP3ScalarRoundoffFactor fp n *
        ((eta + mu) * infNorm X + infNorm A) := by
  have hu_le :
      fp.u ≤ matrixHornerP3ScalarRoundoffFactor fp n :=
    fp_u_le_matrixHornerP3ScalarRoundoffFactor fp n hn
  have hA : 0 ≤ infNorm A := infNorm_nonneg A
  calc
    matrixHornerP3ScalarInfStepBudget fp n X eta mu A
        =
          matrixHornerP3ScalarRoundoffFactor fp n *
              ((eta + mu) * infNorm X) +
            fp.u * infNorm A := by
          unfold matrixHornerP3ScalarInfStepBudget
            matrixHornerP3ScalarRoundoffFactor
          ring
    _ ≤
          matrixHornerP3ScalarRoundoffFactor fp n *
              ((eta + mu) * infNorm X) +
            matrixHornerP3ScalarRoundoffFactor fp n * infNorm A :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hu_le hA)
    _ =
          matrixHornerP3ScalarRoundoffFactor fp n *
            ((eta + mu) * infNorm X + infNorm A) := by
        ring

theorem matrixHornerP3ScalarOneNormStepBudget_le_factor
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (eta mu : ℝ) (A : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    matrixHornerP3ScalarOneNormStepBudget fp n X eta mu A ≤
      matrixHornerP3ScalarRoundoffFactor fp n *
        ((eta + mu) * oneNorm X + oneNorm A) := by
  have hu_le :
      fp.u ≤ matrixHornerP3ScalarRoundoffFactor fp n :=
    fp_u_le_matrixHornerP3ScalarRoundoffFactor fp n hn
  have hA : 0 ≤ oneNorm A := oneNorm_nonneg A
  calc
    matrixHornerP3ScalarOneNormStepBudget fp n X eta mu A
        =
          matrixHornerP3ScalarRoundoffFactor fp n *
              ((eta + mu) * oneNorm X) +
            fp.u * oneNorm A := by
          unfold matrixHornerP3ScalarOneNormStepBudget
            matrixHornerP3ScalarRoundoffFactor
          ring
    _ ≤
          matrixHornerP3ScalarRoundoffFactor fp n *
              ((eta + mu) * oneNorm X) +
            matrixHornerP3ScalarRoundoffFactor fp n * oneNorm A :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hu_le hA)
    _ =
          matrixHornerP3ScalarRoundoffFactor fp n *
            ((eta + mu) * oneNorm X + oneNorm A) := by
        ring

theorem matrixHornerP3ScalarInfForwardBudgetFrom_le_geometric_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∀ (rest : List (Fin n → Fin n → ℝ)) (eta mu rho : ℝ),
      0 ≤ eta →
      0 ≤ mu →
      0 ≤ rho →
      mu ≤ rho * eta →
      matrixHornerP3ScalarInfForwardBudgetFrom fp n X eta mu rest ≤
        (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^ rest.length) *
            (1 + rho) - 1) *
          (eta * infNorm X ^ rest.length +
            matrixPolyP3InfNormMajorant n X rest) := by
  intro rest
  induction rest with
  | nil =>
      intro eta mu rho _heta _hmu _hrho hmu_le
      simpa [matrixHornerP3ScalarInfForwardBudgetFrom,
        matrixPolyP3InfNormMajorant, polyDesc] using hmu_le
  | cons A rest ih =>
      intro eta mu rho heta hmu hrho hmu_le
      let r := matrixHornerP3ScalarRoundoffFactor fp n
      let eta' := eta * infNorm X + infNorm A
      let step := matrixHornerP3ScalarInfStepBudget fp n X eta mu A
      let mu' := step + mu * infNorm X
      let rho' := (1 + r) * (1 + rho) - 1
      have hr : 0 ≤ r := by
        simpa [r] using matrixHornerP3ScalarRoundoffFactor_nonneg fp n hn
      have hX : 0 ≤ infNorm X := infNorm_nonneg X
      have hA : 0 ≤ infNorm A := infNorm_nonneg A
      have heta' : 0 ≤ eta' := by
        exact add_nonneg (mul_nonneg heta hX) hA
      have hstep_nonneg : 0 ≤ step := by
        have hsum : 0 ≤ eta + mu := add_nonneg heta hmu
        have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
        have honeγ : 0 ≤ 1 + gamma fp n := by linarith
        have hinside :
            0 ≤ (1 + gamma fp n) * (eta + mu) * infNorm X +
              infNorm A := by
          exact add_nonneg
            (mul_nonneg (mul_nonneg honeγ hsum) hX)
            hA
        have htail :
            0 ≤ gamma fp n * (eta + mu) * infNorm X :=
          mul_nonneg (mul_nonneg hγ hsum) hX
        simpa [step, matrixHornerP3ScalarInfStepBudget] using
          add_nonneg (mul_nonneg fp.u_nonneg hinside) htail
      have hmu' : 0 ≤ mu' := by
        exact add_nonneg hstep_nonneg (mul_nonneg hmu hX)
      have hstep_le :
          step ≤ r * ((eta + mu) * infNorm X + infNorm A) := by
        simpa [step, r] using
          matrixHornerP3ScalarInfStepBudget_le_factor
            fp n X eta mu A hn
      have hsum_le :
          (eta + mu) * infNorm X + infNorm A ≤
            (eta + rho * eta) * infNorm X + infNorm A := by
        have hbase : eta + mu ≤ eta + rho * eta :=
          add_le_add le_rfl hmu_le
        exact add_le_add (mul_le_mul_of_nonneg_right hbase hX) le_rfl
      have hstep_le_rho :
          step ≤ r * ((eta + rho * eta) * infNorm X + infNorm A) :=
        le_trans hstep_le (mul_le_mul_of_nonneg_left hsum_le hr)
      have hmu_x_le :
          mu * infNorm X ≤ rho * eta * infNorm X :=
        mul_le_mul_of_nonneg_right hmu_le hX
      have hr_le_rho' : r ≤ rho' := by
        have hprod : 0 ≤ r * rho := mul_nonneg hr hrho
        dsimp [rho']
        nlinarith
      have hrho' : 0 ≤ rho' := le_trans hr hr_le_rho'
      have hmu'_le : mu' ≤ rho' * eta' := by
        calc
          mu'
              = step + mu * infNorm X := rfl
          _ ≤
              r * ((eta + rho * eta) * infNorm X + infNorm A) +
                rho * eta * infNorm X :=
              add_le_add hstep_le_rho hmu_x_le
          _ =
              rho' * (eta * infNorm X) + r * infNorm A := by
              dsimp [rho']
              ring
          _ ≤ rho' * (eta * infNorm X) + rho' * infNorm A :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_right hr_le_rho' hA)
          _ = rho' * eta' := by
              dsimp [eta']
              ring
      have hrec :=
        ih eta' mu' rho' heta' hmu' hrho' hmu'_le
      have hcoef :
          ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^ rest.length *
                (1 + rho') - 1) =
            ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
                (rest.length + 1) * (1 + rho) - 1) := by
        dsimp [rho', r]
        rw [pow_succ]
        ring
      have harg :
          eta' * infNorm X ^ rest.length +
              matrixPolyP3InfNormMajorant n X rest =
            eta * infNorm X ^ (rest.length + 1) +
              matrixPolyP3InfNormMajorant n X (A :: rest) := by
        dsimp [eta']
        simp [matrixPolyP3InfNormMajorant, polyDesc]
        ring
      calc
        matrixHornerP3ScalarInfForwardBudgetFrom fp n X eta mu (A :: rest)
            =
              matrixHornerP3ScalarInfForwardBudgetFrom fp n X eta' mu' rest := by
            simp [matrixHornerP3ScalarInfForwardBudgetFrom, eta', mu', step]
        _ ≤
            ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
                  rest.length * (1 + rho') - 1) *
              (eta' * infNorm X ^ rest.length +
                matrixPolyP3InfNormMajorant n X rest) := hrec
        _ =
            ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
                  (A :: rest).length * (1 + rho) - 1) *
              (eta * infNorm X ^ (A :: rest).length +
                matrixPolyP3InfNormMajorant n X (A :: rest)) := by
            rw [List.length_cons, hcoef, harg]

theorem matrixHornerP3ScalarOneNormForwardBudgetFrom_le_geometric_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∀ (rest : List (Fin n → Fin n → ℝ)) (eta mu rho : ℝ),
      0 ≤ eta →
      0 ≤ mu →
      0 ≤ rho →
      mu ≤ rho * eta →
      matrixHornerP3ScalarOneNormForwardBudgetFrom fp n X eta mu rest ≤
        (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^ rest.length) *
            (1 + rho) - 1) *
          (eta * oneNorm X ^ rest.length +
            matrixPolyP3OneNormMajorant n X rest) := by
  intro rest
  induction rest with
  | nil =>
      intro eta mu rho _heta _hmu _hrho hmu_le
      simpa [matrixHornerP3ScalarOneNormForwardBudgetFrom,
        matrixPolyP3OneNormMajorant, polyDesc] using hmu_le
  | cons A rest ih =>
      intro eta mu rho heta hmu hrho hmu_le
      let r := matrixHornerP3ScalarRoundoffFactor fp n
      let eta' := eta * oneNorm X + oneNorm A
      let step := matrixHornerP3ScalarOneNormStepBudget fp n X eta mu A
      let mu' := step + mu * oneNorm X
      let rho' := (1 + r) * (1 + rho) - 1
      have hr : 0 ≤ r := by
        simpa [r] using matrixHornerP3ScalarRoundoffFactor_nonneg fp n hn
      have hX : 0 ≤ oneNorm X := oneNorm_nonneg X
      have hA : 0 ≤ oneNorm A := oneNorm_nonneg A
      have heta' : 0 ≤ eta' := by
        exact add_nonneg (mul_nonneg heta hX) hA
      have hstep_nonneg : 0 ≤ step := by
        have hsum : 0 ≤ eta + mu := add_nonneg heta hmu
        have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
        have honeγ : 0 ≤ 1 + gamma fp n := by linarith
        have hinside :
            0 ≤ (1 + gamma fp n) * (eta + mu) * oneNorm X +
              oneNorm A := by
          exact add_nonneg
            (mul_nonneg (mul_nonneg honeγ hsum) hX)
            hA
        have htail :
            0 ≤ gamma fp n * (eta + mu) * oneNorm X :=
          mul_nonneg (mul_nonneg hγ hsum) hX
        simpa [step, matrixHornerP3ScalarOneNormStepBudget] using
          add_nonneg (mul_nonneg fp.u_nonneg hinside) htail
      have hmu' : 0 ≤ mu' := by
        exact add_nonneg hstep_nonneg (mul_nonneg hmu hX)
      have hstep_le :
          step ≤ r * ((eta + mu) * oneNorm X + oneNorm A) := by
        simpa [step, r] using
          matrixHornerP3ScalarOneNormStepBudget_le_factor
            fp n X eta mu A hn
      have hsum_le :
          (eta + mu) * oneNorm X + oneNorm A ≤
            (eta + rho * eta) * oneNorm X + oneNorm A := by
        have hbase : eta + mu ≤ eta + rho * eta :=
          add_le_add le_rfl hmu_le
        exact add_le_add (mul_le_mul_of_nonneg_right hbase hX) le_rfl
      have hstep_le_rho :
          step ≤ r * ((eta + rho * eta) * oneNorm X + oneNorm A) :=
        le_trans hstep_le (mul_le_mul_of_nonneg_left hsum_le hr)
      have hmu_x_le :
          mu * oneNorm X ≤ rho * eta * oneNorm X :=
        mul_le_mul_of_nonneg_right hmu_le hX
      have hr_le_rho' : r ≤ rho' := by
        have hprod : 0 ≤ r * rho := mul_nonneg hr hrho
        dsimp [rho']
        nlinarith
      have hrho' : 0 ≤ rho' := le_trans hr hr_le_rho'
      have hmu'_le : mu' ≤ rho' * eta' := by
        calc
          mu'
              = step + mu * oneNorm X := rfl
          _ ≤
              r * ((eta + rho * eta) * oneNorm X + oneNorm A) +
                rho * eta * oneNorm X :=
              add_le_add hstep_le_rho hmu_x_le
          _ =
              rho' * (eta * oneNorm X) + r * oneNorm A := by
              dsimp [rho']
              ring
          _ ≤ rho' * (eta * oneNorm X) + rho' * oneNorm A :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_right hr_le_rho' hA)
          _ = rho' * eta' := by
              dsimp [eta']
              ring
      have hrec :=
        ih eta' mu' rho' heta' hmu' hrho' hmu'_le
      have hcoef :
          ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^ rest.length *
                (1 + rho') - 1) =
            ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
                (rest.length + 1) * (1 + rho) - 1) := by
        dsimp [rho', r]
        rw [pow_succ]
        ring
      have harg :
          eta' * oneNorm X ^ rest.length +
              matrixPolyP3OneNormMajorant n X rest =
            eta * oneNorm X ^ (rest.length + 1) +
              matrixPolyP3OneNormMajorant n X (A :: rest) := by
        dsimp [eta']
        simp [matrixPolyP3OneNormMajorant, polyDesc]
        ring
      calc
        matrixHornerP3ScalarOneNormForwardBudgetFrom fp n X eta mu (A :: rest)
            =
              matrixHornerP3ScalarOneNormForwardBudgetFrom fp n X eta' mu' rest := by
            simp [matrixHornerP3ScalarOneNormForwardBudgetFrom, eta', mu',
              step]
        _ ≤
            ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
                  rest.length * (1 + rho') - 1) *
              (eta' * oneNorm X ^ rest.length +
                matrixPolyP3OneNormMajorant n X rest) := hrec
        _ =
            ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
                  (A :: rest).length * (1 + rho) - 1) *
              (eta * oneNorm X ^ (A :: rest).length +
                matrixPolyP3OneNormMajorant n X (A :: rest)) := by
            rw [List.length_cons, hcoef, harg]

theorem matrixHornerP3ScalarInfForwardBudget_le_geometric_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    matrixHornerP3ScalarInfForwardBudget fp n X coeffsDesc ≤
      (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
          (coeffsDesc.length - 1)) - 1) *
        matrixPolyP3InfNormMajorant n X coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [matrixHornerP3ScalarInfForwardBudget,
        matrixPolyP3InfNormMajorant, polyDesc]
  | cons A rest =>
      have h :=
        matrixHornerP3ScalarInfForwardBudgetFrom_le_geometric_majorant
          fp n X hn rest (infNorm A) 0 0
          (infNorm_nonneg A) (by norm_num) (by norm_num) (by simp)
      simpa [matrixHornerP3ScalarInfForwardBudget,
        matrixPolyP3InfNormMajorant, polyDesc] using h

theorem matrixHornerP3ScalarOneNormForwardBudget_le_geometric_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    matrixHornerP3ScalarOneNormForwardBudget fp n X coeffsDesc ≤
      (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
          (coeffsDesc.length - 1)) - 1) *
        matrixPolyP3OneNormMajorant n X coeffsDesc := by
  cases coeffsDesc with
  | nil =>
      simp [matrixHornerP3ScalarOneNormForwardBudget,
        matrixPolyP3OneNormMajorant, polyDesc]
  | cons A rest =>
      have h :=
        matrixHornerP3ScalarOneNormForwardBudgetFrom_le_geometric_majorant
          fp n X hn rest (oneNorm A) 0 0
          (oneNorm_nonneg A) (by norm_num) (by norm_num) (by simp)
      simpa [matrixHornerP3ScalarOneNormForwardBudget,
        matrixPolyP3OneNormMajorant, polyDesc] using h

/-- Higher-order remainder after extracting the source first-order coefficient
`degree*(n+1)u` from the matrix-Horner geometric budget factor. -/
noncomputable def matrixHornerP3GeometricFirstOrderRemainder
    (fp : FPModel) (n degree : ℕ) : ℝ :=
  (degree : ℝ) * matrixHornerP3ScalarRoundoffFactorRemainder fp n +
    (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^ degree - 1) -
      (degree : ℝ) * matrixHornerP3ScalarRoundoffFactor fp n)

theorem matrixHornerP3GeometricFactor_eq_first_order_add_remainder
    (fp : FPModel) (n degree : ℕ) (hn : gammaValid fp n) :
    ((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^ degree - 1) =
      (degree : ℝ) * (((n : ℝ) + 1) * fp.u) +
        matrixHornerP3GeometricFirstOrderRemainder fp n degree := by
  unfold matrixHornerP3GeometricFirstOrderRemainder
  rw [matrixHornerP3ScalarRoundoffFactor_eq_first_order_add_remainder
    fp n hn]
  ring

theorem matrixHornerP3GeometricFirstOrderRemainder_eq_zero_of_u_eq_zero
    (fp : FPModel) (n degree : ℕ) (hu : fp.u = 0) :
    matrixHornerP3GeometricFirstOrderRemainder fp n degree = 0 := by
  simp [matrixHornerP3GeometricFirstOrderRemainder,
    matrixHornerP3ScalarRoundoffFactorRemainder,
    matrixHornerP3ScalarRoundoffFactor, gamma, hu]

theorem fl_matrixHornerP3Fold_infNorm_le_acc_majorant_add_budget_from
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (rest : List (Fin n → Fin n → ℝ))
    (Yhat Y : Fin n → Fin n → ℝ) (mu : ℝ)
    (hnpos : 0 < n) (hn : gammaValid fp n)
    (hmu : 0 ≤ mu)
    (herr : infNorm (fun i j => Yhat i j - Y i j) ≤ mu) :
    infNorm (rest.foldl (fl_matrixHornerP3Step fp n X) Yhat) ≤
      infNorm Y * infNorm X ^ rest.length +
        matrixPolyP3InfNormMajorant n X rest +
        matrixHornerP3ForwardInfErrorBudgetFrom fp n X Yhat mu rest := by
  have htri :=
    infNorm_le_sub_add
      (rest.foldl (fl_matrixHornerP3Step fp n X) Yhat)
      (rest.foldl (matrixHornerP3Step n X) Y)
  have herr_fold :=
    fl_matrixHornerP3Fold_infNorm_error_bound_from
      fp n X hnpos hn rest Yhat Y mu hmu herr
  have hexact :=
    matrixHornerP3Fold_infNorm_le_acc_majorant n X Y rest hnpos
  calc
    infNorm (rest.foldl (fl_matrixHornerP3Step fp n X) Yhat)
        ≤
          infNorm
            (fun i j =>
              rest.foldl (fl_matrixHornerP3Step fp n X) Yhat i j -
                rest.foldl (matrixHornerP3Step n X) Y i j) +
            infNorm (rest.foldl (matrixHornerP3Step n X) Y) := htri
    _ ≤
          matrixHornerP3ForwardInfErrorBudgetFrom fp n X Yhat mu rest +
            (infNorm Y * infNorm X ^ rest.length +
              matrixPolyP3InfNormMajorant n X rest) :=
        add_le_add herr_fold hexact
    _ =
          infNorm Y * infNorm X ^ rest.length +
            matrixPolyP3InfNormMajorant n X rest +
            matrixHornerP3ForwardInfErrorBudgetFrom fp n X Yhat mu rest := by
        ring

theorem fl_matrixHornerP3Fold_oneNorm_le_acc_majorant_add_budget_from
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (rest : List (Fin n → Fin n → ℝ))
    (Yhat Y : Fin n → Fin n → ℝ) (mu : ℝ)
    (hn : gammaValid fp n)
    (hmu : 0 ≤ mu)
    (herr : oneNorm (fun i j => Yhat i j - Y i j) ≤ mu) :
    oneNorm (rest.foldl (fl_matrixHornerP3Step fp n X) Yhat) ≤
      oneNorm Y * oneNorm X ^ rest.length +
        matrixPolyP3OneNormMajorant n X rest +
        matrixHornerP3ForwardOneNormErrorBudgetFrom fp n X Yhat mu rest := by
  have htri :=
    oneNorm_le_sub_add
      (rest.foldl (fl_matrixHornerP3Step fp n X) Yhat)
      (rest.foldl (matrixHornerP3Step n X) Y)
  have herr_fold :=
    fl_matrixHornerP3Fold_oneNorm_error_bound_from
      fp n X hn rest Yhat Y mu hmu herr
  have hexact :=
    matrixHornerP3Fold_oneNorm_le_acc_majorant n X Y rest
  calc
    oneNorm (rest.foldl (fl_matrixHornerP3Step fp n X) Yhat)
        ≤
          oneNorm
            (fun i j =>
              rest.foldl (fl_matrixHornerP3Step fp n X) Yhat i j -
                rest.foldl (matrixHornerP3Step n X) Y i j) +
            oneNorm (rest.foldl (matrixHornerP3Step n X) Y) := htri
    _ ≤
          matrixHornerP3ForwardOneNormErrorBudgetFrom fp n X Yhat mu rest +
            (oneNorm Y * oneNorm X ^ rest.length +
              matrixPolyP3OneNormMajorant n X rest) :=
        add_le_add herr_fold hexact
    _ =
          oneNorm Y * oneNorm X ^ rest.length +
            matrixPolyP3OneNormMajorant n X rest +
            matrixHornerP3ForwardOneNormErrorBudgetFrom fp n X Yhat mu rest := by
        ring

theorem fl_matrixHornerP3Desc_infNorm_error_bound_to_matrixPolyP3Desc
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    infNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      matrixHornerP3ForwardInfErrorBudget fp n X coeffsDesc := by
  rw [← matrixHornerP3Desc_eq_matrixPolyP3Desc n X coeffsDesc]
  exact fl_matrixHornerP3Desc_infNorm_error_bound
    fp n X coeffsDesc hnpos hn

theorem fl_matrixHornerP3Desc_oneNorm_error_bound_to_matrixPolyP3Desc
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    oneNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      matrixHornerP3ForwardOneNormErrorBudget fp n X coeffsDesc := by
  rw [← matrixHornerP3Desc_eq_matrixPolyP3Desc n X coeffsDesc]
  exact fl_matrixHornerP3Desc_oneNorm_error_bound
    fp n X coeffsDesc hn

theorem fl_matrixHornerP3Desc_infNorm_le_majorant_add_budget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    infNorm (fl_matrixHornerP3Desc fp n X coeffsDesc) ≤
      matrixPolyP3InfNormMajorant n X coeffsDesc +
        matrixHornerP3ForwardInfErrorBudget fp n X coeffsDesc := by
  have htri :=
    infNorm_le_sub_add
      (fl_matrixHornerP3Desc fp n X coeffsDesc)
      (matrixHornerP3Desc n X coeffsDesc)
  have herr :=
    fl_matrixHornerP3Desc_infNorm_error_bound
      fp n X coeffsDesc hnpos hn
  have hexact :
      infNorm (matrixHornerP3Desc n X coeffsDesc) ≤
        matrixPolyP3InfNormMajorant n X coeffsDesc := by
    rw [matrixHornerP3Desc_eq_matrixPolyP3Desc n X coeffsDesc]
    exact matrixPolyP3Desc_infNorm_le_majorant n X coeffsDesc hnpos
  calc
    infNorm (fl_matrixHornerP3Desc fp n X coeffsDesc)
        ≤
          infNorm
            (fun i j =>
              fl_matrixHornerP3Desc fp n X coeffsDesc i j -
                matrixHornerP3Desc n X coeffsDesc i j) +
            infNorm (matrixHornerP3Desc n X coeffsDesc) := htri
    _ ≤
          matrixHornerP3ForwardInfErrorBudget fp n X coeffsDesc +
            matrixPolyP3InfNormMajorant n X coeffsDesc :=
        add_le_add herr hexact
    _ =
          matrixPolyP3InfNormMajorant n X coeffsDesc +
            matrixHornerP3ForwardInfErrorBudget fp n X coeffsDesc := by
        ring

theorem fl_matrixHornerP3Desc_oneNorm_le_majorant_add_budget
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    oneNorm (fl_matrixHornerP3Desc fp n X coeffsDesc) ≤
      matrixPolyP3OneNormMajorant n X coeffsDesc +
        matrixHornerP3ForwardOneNormErrorBudget fp n X coeffsDesc := by
  have htri :=
    oneNorm_le_sub_add
      (fl_matrixHornerP3Desc fp n X coeffsDesc)
      (matrixHornerP3Desc n X coeffsDesc)
  have herr :=
    fl_matrixHornerP3Desc_oneNorm_error_bound
      fp n X coeffsDesc hn
  have hexact :
      oneNorm (matrixHornerP3Desc n X coeffsDesc) ≤
        matrixPolyP3OneNormMajorant n X coeffsDesc := by
    rw [matrixHornerP3Desc_eq_matrixPolyP3Desc n X coeffsDesc]
    exact matrixPolyP3Desc_oneNorm_le_majorant n X coeffsDesc
  calc
    oneNorm (fl_matrixHornerP3Desc fp n X coeffsDesc)
        ≤
          oneNorm
            (fun i j =>
              fl_matrixHornerP3Desc fp n X coeffsDesc i j -
                matrixHornerP3Desc n X coeffsDesc i j) +
            oneNorm (matrixHornerP3Desc n X coeffsDesc) := htri
    _ ≤
          matrixHornerP3ForwardOneNormErrorBudget fp n X coeffsDesc +
            matrixPolyP3OneNormMajorant n X coeffsDesc :=
        add_le_add herr hexact
    _ =
          matrixPolyP3OneNormMajorant n X coeffsDesc +
            matrixHornerP3ForwardOneNormErrorBudget fp n X coeffsDesc := by
        ring

theorem matrixPolynomialP3_horner_infNorm_error_bound_of_budget_le_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (C : ℝ) (hnpos : 0 < n) (hn : gammaValid fp n)
    (hbudget :
      matrixHornerP3ForwardInfErrorBudget fp n X coeffsDesc ≤
        C * matrixPolyP3InfNormMajorant n X coeffsDesc) :
    infNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      C * matrixPolyP3InfNormMajorant n X coeffsDesc := by
  exact le_trans
    (fl_matrixHornerP3Desc_infNorm_error_bound_to_matrixPolyP3Desc
      fp n X coeffsDesc hnpos hn)
    hbudget

theorem matrixPolynomialP3_horner_oneNorm_error_bound_of_budget_le_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (C : ℝ) (hn : gammaValid fp n)
    (hbudget :
      matrixHornerP3ForwardOneNormErrorBudget fp n X coeffsDesc ≤
        C * matrixPolyP3OneNormMajorant n X coeffsDesc) :
    oneNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      C * matrixPolyP3OneNormMajorant n X coeffsDesc := by
  exact le_trans
    (fl_matrixHornerP3Desc_oneNorm_error_bound_to_matrixPolyP3Desc
      fp n X coeffsDesc hn)
    hbudget

theorem matrixPolynomialP3_horner_infNorm_error_bound_of_scalar_budget_le_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (C : ℝ) (hnpos : 0 < n) (hn : gammaValid fp n)
    (hbudget :
      matrixHornerP3ScalarInfForwardBudget fp n X coeffsDesc ≤
        C * matrixPolyP3InfNormMajorant n X coeffsDesc) :
    infNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      C * matrixPolyP3InfNormMajorant n X coeffsDesc := by
  exact
    matrixPolynomialP3_horner_infNorm_error_bound_of_budget_le_majorant
      fp n X coeffsDesc C hnpos hn
      (le_trans
        (matrixHornerP3ForwardInfErrorBudget_le_scalar
          fp n X coeffsDesc hnpos hn)
        hbudget)

theorem matrixPolynomialP3_horner_oneNorm_error_bound_of_scalar_budget_le_majorant
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (C : ℝ) (hn : gammaValid fp n)
    (hbudget :
      matrixHornerP3ScalarOneNormForwardBudget fp n X coeffsDesc ≤
        C * matrixPolyP3OneNormMajorant n X coeffsDesc) :
    oneNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      C * matrixPolyP3OneNormMajorant n X coeffsDesc := by
  exact
    matrixPolynomialP3_horner_oneNorm_error_bound_of_budget_le_majorant
      fp n X coeffsDesc C hn
      (le_trans
        (matrixHornerP3ForwardOneNormErrorBudget_le_scalar
          fp n X coeffsDesc hn)
        hbudget)

theorem matrixPolynomialP3_horner_infNorm_error_bound_geometric
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    infNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
          (coeffsDesc.length - 1)) - 1) *
        matrixPolyP3InfNormMajorant n X coeffsDesc := by
  exact
    matrixPolynomialP3_horner_infNorm_error_bound_of_scalar_budget_le_majorant
      fp n X coeffsDesc
      (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
          (coeffsDesc.length - 1)) - 1)
      hnpos hn
      (matrixHornerP3ScalarInfForwardBudget_le_geometric_majorant
        fp n X coeffsDesc hn)

theorem matrixPolynomialP3_horner_oneNorm_error_bound_geometric
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    oneNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
          (coeffsDesc.length - 1)) - 1) *
        matrixPolyP3OneNormMajorant n X coeffsDesc := by
  exact
    matrixPolynomialP3_horner_oneNorm_error_bound_of_scalar_budget_le_majorant
      fp n X coeffsDesc
      (((1 + matrixHornerP3ScalarRoundoffFactor fp n) ^
          (coeffsDesc.length - 1)) - 1)
      hn
      (matrixHornerP3ScalarOneNormForwardBudget_le_geometric_majorant
        fp n X coeffsDesc hn)

theorem matrixPolynomialP3_horner_infNorm_error_bound_first_order_remainder
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) (hn : gammaValid fp n) :
    infNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      (((coeffsDesc.length - 1 : ℕ) : ℝ) *
          (((n : ℝ) + 1) * fp.u) +
        matrixHornerP3GeometricFirstOrderRemainder
          fp n (coeffsDesc.length - 1)) *
        matrixPolyP3InfNormMajorant n X coeffsDesc := by
  have h :=
    matrixPolynomialP3_horner_infNorm_error_bound_geometric
      fp n X coeffsDesc hnpos hn
  rw [matrixHornerP3GeometricFactor_eq_first_order_add_remainder
    fp n (coeffsDesc.length - 1) hn] at h
  simpa using h

theorem matrixPolynomialP3_horner_oneNorm_error_bound_first_order_remainder
    (fp : FPModel) (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hn : gammaValid fp n) :
    oneNorm
        (fun i j =>
          fl_matrixHornerP3Desc fp n X coeffsDesc i j -
            matrixPolyP3Desc n X coeffsDesc i j) ≤
      (((coeffsDesc.length - 1 : ℕ) : ℝ) *
          (((n : ℝ) + 1) * fp.u) +
        matrixHornerP3GeometricFirstOrderRemainder
          fp n (coeffsDesc.length - 1)) *
        matrixPolyP3OneNormMajorant n X coeffsDesc := by
  have h :=
    matrixPolynomialP3_horner_oneNorm_error_bound_geometric
      fp n X coeffsDesc hn
  rw [matrixHornerP3GeometricFactor_eq_first_order_add_remainder
    fp n (coeffsDesc.length - 1) hn] at h
  simpa using h

end NumStability
