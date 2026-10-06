import Mathlib

open scoped BigOperators

namespace HighamBench

abbrev P58Matrix (m n : ℕ) := Fin m → Fin n → ℝ

def p58Transpose {m n : ℕ} (A : P58Matrix m n) : P58Matrix n m :=
  fun j i => A i j

def p58RectMul {m n p : ℕ}
    (A : P58Matrix m n) (B : P58Matrix n p) : P58Matrix m p :=
  fun i j => ∑ k : Fin n, A i k * B k j

def p58MatVec {m n : ℕ}
    (A : P58Matrix m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => ∑ j : Fin n, A i j * x j

def p58Id (n : ℕ) : P58Matrix n n :=
  fun i j => if i = j then 1 else 0

def p58Sub {m n : ℕ}
    (A B : P58Matrix m n) : P58Matrix m n :=
  fun i j => A i j - B i j

noncomputable def p58FrobSq {m n : ℕ} (A : P58Matrix m n) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2

def p58RangeProjection {m l : ℕ}
    (Q : P58Matrix m l) : P58Matrix m m :=
  p58RectMul Q (p58Transpose Q)

def p58Project {m l n : ℕ}
    (Q : P58Matrix m l) (A : P58Matrix m n) : P58Matrix m n :=
  p58RectMul (p58RangeProjection Q) A

def p58Lift {m l n : ℕ}
    (Q : P58Matrix m l) (B : P58Matrix l n) : P58Matrix m n :=
  p58RectMul Q B

end HighamBench
