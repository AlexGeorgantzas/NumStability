import Mathlib

namespace HighamBench

open scoped BigOperators

/-! Paper-local exact model of the unit lower-bidiagonal factors and the
subtraction-free `dqd2` recurrence in Lemma 4.1 and Algorithm 4.1. -/

/-- The strictly lower shift carrying the subdiagonal data `b`. -/
noncomputable def p34LowerShift (n : ℕ) (b : ℕ → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if i.val = j.val + 1 then b j.val else 0

/-- A unit lower-bidiagonal matrix with subdiagonal data `b`. -/
noncomputable def p34UnitLowerBidiagonal (n : ℕ) (b : ℕ → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  1 + p34LowerShift n b

/-- The auxiliary subtraction-free recurrence `d_i` from equation (4.3). -/
noncomputable def p34DqdD (b c : ℕ → ℝ) : ℕ → ℝ
  | 0 => b 0
  | i + 1 => b (i + 1) * p34DqdD b c i / (c i + p34DqdD b c i)

/-- The first transformed subdiagonal. The recurrence stops at index `q`. -/
noncomputable def p34DqdB (q : ℕ) (b c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 =>
      if i + 1 < q then
        b (i + 1) * c i / (c i + p34DqdD b c i)
      else b (i + 1)

/-- The second transformed subdiagonal. The recurrence stops at index `q`. -/
noncomputable def p34DqdC (q : ℕ) (b c : ℕ → ℝ) : ℕ → ℝ :=
  fun i => if i < q then c i + p34DqdD b c i else c i

end HighamBench
