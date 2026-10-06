import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace HighamBench

open scoped BigOperators

noncomputable def p05MatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, A i k * B k j

noncomputable def p05Transpose {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A j i

noncomputable def p05AbsMatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, |A i k| * |B k j|

structure P05FiniteRoundToNearestFormat where
  radix : ℕ
  precision : ℕ
  minExponent : ℤ
  maxExponent : ℤ
  radix_ge_two : 2 ≤ radix
  precision_pos : 0 < precision
  exponent_range_nonempty : minExponent < maxExponent
  representable : ℝ → Prop
  representable_finite : Set.Finite {x | representable x}
  representable_radix_expansion : ∀ x, representable x →
    x = 0 ∨ ∃ m e : ℤ,
      m.natAbs < radix ^ precision ∧
      minExponent ≤ e ∧ e ≤ maxExponent ∧
      x = (m : ℝ) * (radix : ℝ) ^ (e - ((precision : ℤ) - 1))
  safeRange : ℝ → Prop
  round : ℝ → ℝ
  unitRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff
  unitRoundoff_le_half : unitRoundoff ≤ 1 / 2
  unitRoundoff_scale :
    unitRoundoff * (2 * (radix : ℝ) ^ (precision - 1)) = 1
  zero_representable : representable 0
  one_representable : representable 1
  neg_representable : ∀ x, representable x → representable (-x)
  round_representable : ∀ x, safeRange x → representable (round x)
  round_nearest : ∀ x, safeRange x → ∀ z, representable z →
    |x - round x| ≤ |x - z|
  round_error_to_output : ∀ x, safeRange x →
    |round x - x| ≤ unitRoundoff * |round x|
  round_nonnegative : ∀ x, 0 ≤ x → safeRange x → 0 ≤ round x
  sqrt_round_square_error : ∀ x, 0 ≤ x → representable x →
    safeRange (Real.sqrt x) →
      |(round (Real.sqrt x)) ^ 2 - x| ≤
        2 * unitRoundoff * |(round (Real.sqrt x)) ^ 2|
  round_exact : ∀ x, representable x → round x = x

inductive P05SumTree : ℕ → Type
  | leaf : P05SumTree 1
  | node {m n : ℕ} : P05SumTree m → P05SumTree n → P05SumTree (m + n)

noncomputable def p05SumTreeEval
    (fmt : P05FiniteRoundToNearestFormat) {n : ℕ}
    (tree : P05SumTree n) (v : Fin n → ℝ) : ℝ :=
  match tree with
  | .leaf => v ⟨0, by norm_num⟩
  | .node left right =>
      fmt.round
        (p05SumTreeEval fmt left (fun i => v (Fin.castAdd _ i)) +
          p05SumTreeEval fmt right (fun i => v (Fin.natAdd _ i)))

def p05SumTreeSafe
    (fmt : P05FiniteRoundToNearestFormat) {n : ℕ}
    (tree : P05SumTree n) (v : Fin n → ℝ) : Prop :=
  match tree with
  | .leaf => fmt.representable (v ⟨0, by norm_num⟩)
  | .node left right =>
      p05SumTreeSafe fmt left (fun i => v (Fin.castAdd _ i)) ∧
      p05SumTreeSafe fmt right (fun i => v (Fin.natAdd _ i)) ∧
      fmt.safeRange
        (p05SumTreeEval fmt left (fun i => v (Fin.castAdd _ i)) +
          p05SumTreeEval fmt right (fun i => v (Fin.natAdd _ i)))

noncomputable def p05RoundedProducts {m : ℕ}
    (fmt : P05FiniteRoundToNearestFormat)
    (a b : Fin m → ℝ) : Fin m → ℝ :=
  fun i => fmt.round (a i * b i)

noncomputable def p05Lemma41Summands {m : ℕ}
    (fmt : P05FiniteRoundToNearestFormat)
    (a b : Fin m → ℝ) (c : ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases c (fun i => -p05RoundedProducts fmt a b i)

noncomputable def p05BackwardSource {m : ℕ}
    (computedProduct : ℝ) (products : Fin m → ℝ) :
    Option (Fin m) → ℝ
  | none => computedProduct
  | some i => products i

inductive P05ProtectedSumTrace (fmt : P05FiniteRoundToNearestFormat) :
    (termCount : ℕ) → (pivotValue outsideExact outsideAbs computed : ℝ) → Prop
  | leaf (pivotValue : ℝ) (pivot_representable : fmt.representable pivotValue) :
      P05ProtectedSumTrace fmt 1 pivotValue 0 0 pivotValue
  | merge {outerCount siblingCount : ℕ}
      {pivotValue siblingExact siblingAbs siblingComputed outerExact outerAbs computed : ℝ}
      (pivot_representable : fmt.representable pivotValue)
      (sibling_count_pos : 0 < siblingCount)
      (sibling_abs_nonneg : 0 ≤ siblingAbs)
      (sibling_exact_abs_le : |siblingExact| ≤ siblingAbs)
      (sibling_computed_representable : fmt.representable siblingComputed)
      (sibling_error_bound :
        |siblingComputed - siblingExact| ≤
          (siblingCount : ℝ) * fmt.unitRoundoff * siblingAbs)
      (merge_safe : fmt.safeRange (pivotValue + siblingComputed))
      (outer : P05ProtectedSumTrace fmt outerCount
        (fmt.round (pivotValue + siblingComputed)) outerExact outerAbs computed) :
      P05ProtectedSumTrace fmt (outerCount + siblingCount) pivotValue
        (siblingExact + outerExact) (siblingAbs + outerAbs) computed

structure P05Lemma41Run (m : ℕ) where
  format : P05FiniteRoundToNearestFormat
  a : Fin m → ℝ
  b : Fin m → ℝ
  bK : ℝ
  c : ℝ
  a_representable : ∀ i, format.representable (a i)
  b_representable : ∀ i, format.representable (b i)
  bK_representable : format.representable bK
  c_representable : format.representable c
  bK_nonzero : bK ≠ 0
  product_safe : ∀ i, format.safeRange (a i * b i)
  tree : P05SumTree (m + 1)
  order : Equiv.Perm (Fin (m + 1))
  tree_safe : p05SumTreeSafe format tree
    (fun i => p05Lemma41Summands format a b c (order i))
  numerator : ℝ
  numerator_eq : numerator = p05SumTreeEval format tree
    (fun i => p05Lemma41Summands format a b c (order i))
  protected_sum_trace : P05ProtectedSumTrace format (m + 1) c
    (-(∑ i : Fin m, a i * b i))
    (∑ i : Fin m, |a i * b i|) numerator
  yHat : ℝ
  no_division_when_unit : bK = 1 → yHat = numerator
  division_safe : bK ≠ 1 → format.safeRange (numerator / bK)
  rounded_division : bK ≠ 1 → yHat = format.round (numerator / bK)

def p05PrefixIndex {n : ℕ} (k : Fin n) (s : Fin k.val) : Fin n :=
  ⟨s.val, lt_trans s.isLt k.isLt⟩

structure P05Lemma43Run (m : ℕ) where
  format : P05FiniteRoundToNearestFormat
  a : Fin m → ℝ
  b : Fin m → ℝ
  c : ℝ
  a_representable : ∀ i, format.representable (a i)
  b_representable : ∀ i, format.representable (b i)
  c_representable : format.representable c
  product_safe : ∀ i, format.safeRange (a i * b i)
  tree : P05SumTree (m + 1)
  order : Equiv.Perm (Fin (m + 1))
  tree_safe : p05SumTreeSafe format tree
    (fun i => p05Lemma41Summands format a b c (order i))
  numerator : ℝ
  numerator_eq : numerator = p05SumTreeEval format tree
    (fun i => p05Lemma41Summands format a b c (order i))
  protected_sum_trace : P05ProtectedSumTrace format (m + 1) c
    (-(∑ i : Fin m, a i * b i))
    (∑ i : Fin m, |a i * b i|) numerator
  numerator_nonneg : 0 ≤ numerator
  sqrt_safe : format.safeRange (Real.sqrt numerator)
  yHat : ℝ
  rounded_sqrt : yHat = format.round (Real.sqrt numerator)

noncomputable def p05CholeskyPrefixDot {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ k : Fin i.val,
    R (p05PrefixIndex i k) i * R (p05PrefixIndex i k) j

noncomputable def p05CholeskyPrefixAbsDot {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ k : Fin i.val,
    |R (p05PrefixIndex i k) i| * |R (p05PrefixIndex i k) j|

noncomputable def p05CholeskyThroughDot {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  p05CholeskyPrefixDot R i j + R i i * R i j

noncomputable def p05CholeskyThroughAbsDot {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  p05CholeskyPrefixAbsDot R i j + |R i i| * |R i j|

structure P05CholeskyOffDiagonalEntry {n : ℕ}
    (fmt : P05FiniteRoundToNearestFormat)
    (A R : Fin n → Fin n → ℝ) (i j : Fin n) where
  execution : P05Lemma41Run i.val
  format_eq : execution.format = fmt
  left_input_eq : ∀ k,
    execution.a k = R (p05PrefixIndex i k) i
  right_input_eq : ∀ k,
    execution.b k = R (p05PrefixIndex i k) j
  denominator_eq : execution.bK = R i i
  protected_input_eq : execution.c = A i j
  computed_output_eq : execution.yHat = R i j

structure P05CholeskyDiagonalEntry {n : ℕ}
    (fmt : P05FiniteRoundToNearestFormat)
    (A R : Fin n → Fin n → ℝ) (j : Fin n) where
  execution : P05Lemma43Run j.val
  format_eq : execution.format = fmt
  left_input_eq : ∀ k,
    execution.a k = R (p05PrefixIndex j k) j
  right_input_eq : ∀ k,
    execution.b k = R (p05PrefixIndex j k) j
  protected_input_eq : execution.c = A j j
  computed_output_eq : execution.yHat = R j j

structure P05CholeskyRun (n : ℕ) where
  format : P05FiniteRoundToNearestFormat
  dimension_pos : 0 < n
  A : Fin n → Fin n → ℝ
  RHat : Fin n → Fin n → ℝ
  A_representable : ∀ i j, format.representable (A i j)
  A_symmetric : ∀ i j, A i j = A j i
  RHat_lower_zero : ∀ i j, j.val < i.val → RHat i j = 0
  off_diagonal_entry : ∀ i j, i.val < j.val →
    P05CholeskyOffDiagonalEntry format A RHat i j
  diagonal_entry : ∀ j,
    P05CholeskyDiagonalEntry format A RHat j

end HighamBench
