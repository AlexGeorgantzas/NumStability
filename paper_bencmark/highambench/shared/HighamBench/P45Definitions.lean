import Mathlib

open scoped BigOperators

namespace HighamBench

abbrev P45Vector (n : ℕ) := Fin n → ℝ
abbrev P45Matrix (n : ℕ) := Fin n → Fin n → ℝ

noncomputable def p45MatMul {n : ℕ}
    (A B : P45Matrix n) : P45Matrix n :=
  fun i j => ∑ k : Fin n, A i k * B k j

noncomputable def p45MatVec {n : ℕ}
    (A : P45Matrix n) (x : P45Vector n) : P45Vector n :=
  fun i => ∑ j : Fin n, A i j * x j

def p45Id (n : ℕ) : P45Matrix n :=
  fun i j => if i = j then 1 else 0

noncomputable def p45VecNorm (x : P45Vector n) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

noncomputable def p45Inner (x y : P45Vector n) : ℝ :=
  ∑ i : Fin n, x i * y i

def p45Basis (j : Fin n) : P45Vector n :=
  fun i => if i = j then 1 else 0

/-- The exact plane rotation used in the QR factorization in the proof of
P45, Lemma 5.1. -/
noncomputable def p45GivensRotation (n : ℕ) (p q : Fin n) (c s : ℝ) :
    P45Matrix n :=
  fun i j =>
    if i = p ∧ j = p then c
    else if i = q ∧ j = q then c
    else if i = p ∧ j = q then s
    else if i = q ∧ j = p then -s
    else if i = j then 1
    else 0

/-- One valid Givens rotation in the product `Omega_m ... Omega_k` used in
the proof of P45, Lemma 5.1. -/
structure P45GivensStep (n : ℕ) where
  p : Fin n
  q : Fin n
  c : ℝ
  s : ℝ
  distinct : p ≠ q
  unit : c ^ 2 + s ^ 2 = 1

noncomputable def P45GivensStep.matrix {n : ℕ}
    (step : P45GivensStep n) : P45Matrix n :=
  p45GivensRotation n step.p step.q step.c step.s

/-- Ordered product of the Givens rotations. If the list is
`[Omega_k, ..., Omega_m]`, this returns `Omega_m ... Omega_k`. -/
noncomputable def p45GivensProduct {n : ℕ} :
    List (P45GivensStep n) → P45Matrix n
  | [] => p45Id n
  | step :: steps => p45MatMul (p45GivensProduct steps) step.matrix

end HighamBench
