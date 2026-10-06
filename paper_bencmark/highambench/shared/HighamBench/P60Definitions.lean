import Mathlib

open scoped BigOperators

namespace HighamBench

abbrev P60Square (r : ℕ) := Matrix (Fin r) (Fin r) ℝ

abbrev P60Column (r : ℕ) := Matrix (Fin r) (Fin 1) ℝ

noncomputable def p60ChainTrain {n r : ℕ} :
    (d : ℕ) →
      (Fin d → Fin n → P60Square r) →
      (Fin n → P60Column r) →
      (Fin (d + 1) → Fin n) → P60Column r
  | 0, _, Z, indices => Z (indices 0)
  | d + 1, Q, Z, indices =>
      Q 0 (indices 0) *
        p60ChainTrain d (fun k => Q k.succ) Z (Fin.tail indices)

noncomputable def p60ChainGram {n r d : ℕ}
    (Q : Fin d → Fin n → P60Square r)
    (Z : Fin n → P60Column r) : P60Square r :=
  ∑ indices : Fin (d + 1) → Fin n,
    p60ChainTrain d Q Z indices *
      Matrix.transpose (p60ChainTrain d Q Z indices)

end HighamBench
