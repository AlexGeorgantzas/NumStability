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
import NumStability.Source.Higham.Chapter05.Section01.Horner.Basic
import NumStability.Source.Higham.Chapter05.Section02.DerivativeEvaluation.SyntheticDivision

/-!
# Chapter05 Problem01 DifferentiatedHorner Basic

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

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

end NumStability
