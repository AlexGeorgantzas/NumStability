import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped BigOperators Matrix.Norms.Frobenius

namespace HighamBench

abbrev P10Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

noncomputable def p10MatMul (n : ℕ) (A B : P10Matrix n) : P10Matrix n :=
  A * B

abbrev P10ThreeBlockMatrix (n : ℕ) :=
  Matrix (Fin 3) (Fin 3) (P10Matrix n)

noncomputable def p10MultiplicationReductionInput {n : ℕ}
    (A B : P10Matrix n) : P10ThreeBlockMatrix n :=
  !![(1 : P10Matrix n), A, 0;
     0, 1, B;
     0, 0, 1]

noncomputable def p10MultiplicationReductionInverse {n : ℕ}
    (A B : P10Matrix n) : P10ThreeBlockMatrix n :=
  !![(1 : P10Matrix n), -A, p10MatMul n A B;
     0, 1, -B;
     0, 0, 1]

noncomputable def p10ThreeBlockMul {n : ℕ}
    (X Y : P10ThreeBlockMatrix n) : P10ThreeBlockMatrix n :=
  X * Y

noncomputable def p10ThreeBlockIdentity (n : ℕ) : P10ThreeBlockMatrix n :=
  1

def P10MultiplicationViaInverse {n : ℕ} (A B : P10Matrix n) : Prop :=
  p10ThreeBlockMul (p10MultiplicationReductionInput A B)
      (p10MultiplicationReductionInverse A B) =
      p10ThreeBlockIdentity n ∧
    p10ThreeBlockMul (p10MultiplicationReductionInverse A B)
      (p10MultiplicationReductionInput A B) =
      p10ThreeBlockIdentity n ∧
    p10MultiplicationReductionInverse A B (0 : Fin 3) (2 : Fin 3) =
      p10MatMul n A B

end HighamBench
