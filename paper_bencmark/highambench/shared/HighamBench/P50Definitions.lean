import Mathlib

open scoped BigOperators

namespace HighamBench

abbrev P50Matrix (m : ℕ) := Fin m → Fin m → ℝ

def p50Coeff (m : ℕ) (A : Fin (m + 1) → ℝ) (k : ℕ) : ℝ :=
  if hk : k < m + 1 then A ⟨k, hk⟩ else 0

def p50Term (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (k : ℕ) : ℝ :=
  alpha ^ k * beta ^ (m - k) * p50Coeff m A k

/-- Homogeneous scalar specialization of the matrix polynomial in equation (1.1). -/
noncomputable def p50Polynomial (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) : ℝ :=
  ∑ k : Fin (m + 1), alpha ^ k.val * beta ^ (m - k.val) * A k

/-- The lower-coefficient polynomial appearing in the upper-right blocks of E. -/
noncomputable def p50Low (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) : ℝ :=
  ∑ k ∈ Finset.range (m - j.val),
    alpha ^ k * beta ^ (m - j.val - 1 - k) * p50Coeff m A k

/-- The upper-coefficient polynomial appearing on and below the diagonal of E. -/
noncomputable def p50High (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) : ℝ :=
  ∑ q ∈ Finset.range (j.val + 1),
    alpha ^ q * beta ^ (j.val - q) * p50Coeff m A (m - j.val + q)

/-- Scalar specialization of the homogeneous first companion pencil in (3.1). -/
noncomputable def p50FirstCompanion (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) : P50Matrix m :=
  fun i j =>
    if hi : i.val = 0 then
      if hj : j.val = 0 then
        alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩
      else
        beta * A ⟨m - 1 - j.val, by omega⟩
    else if hsub : i.val = j.val + 1 then
      -beta
    else if i = j then
      alpha
    else
      0

/-- The explicit multiplier E from Lemma 3.4, in the scalar n=1 case. -/
noncomputable def p50Multiplier (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) : P50Matrix m :=
  fun i j =>
    if hj : j.val = 0 then
      alpha ^ (m - i.val - 1) * beta ^ i.val
    else if hij : i.val < j.val then
      -(alpha ^ (j.val - i.val - 1) * beta ^ (i.val + 1) *
        p50Low m A alpha beta j)
    else
      alpha ^ (m - i.val - 1) * beta ^ (i.val - j.val) *
        p50High m A alpha beta j

noncomputable def p50MatMul {m : ℕ}
    (A B : P50Matrix m) : P50Matrix m :=
  fun i j => ∑ k : Fin m, A i k * B k j

end HighamBench
