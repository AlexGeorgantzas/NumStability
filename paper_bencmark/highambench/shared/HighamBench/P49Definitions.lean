import Mathlib

open scoped BigOperators

namespace HighamBench

abbrev P49Vector (n : ℕ) := Fin n → ℝ
abbrev P49Matrix (n : ℕ) := Fin n → Fin n → ℝ

noncomputable def p49Dot {n : ℕ} (x y : P49Vector n) : ℝ :=
  ∑ i : Fin n, x i * y i

noncomputable def p49VecNorm {n : ℕ} (x : P49Vector n) : ℝ :=
  Real.sqrt (p49Dot x x)

noncomputable def p49MatVec {n : ℕ}
    (A : P49Matrix n) (x : P49Vector n) : P49Vector n :=
  fun i => ∑ j : Fin n, A i j * x j

/-- The induced Euclidean-norm upper-bound relation used in P49, Section 2. -/
def p49OpNormBound {n : ℕ} (A : P49Matrix n) (bound : ℝ) : Prop :=
  ∀ z, p49VecNorm (p49MatVec A z) ≤ bound * p49VecNorm z

def p49Id (n : ℕ) : P49Matrix n :=
  fun i j => if i = j then 1 else 0

def p49Transpose {n : ℕ} (A : P49Matrix n) : P49Matrix n :=
  fun i j => A j i

def p49Symmetric {n : ℕ} (A : P49Matrix n) : Prop :=
  p49Transpose A = A

def p49Orthogonal {n : ℕ} (A : P49Matrix n) : Prop :=
  (∀ i j : Fin n,
      (∑ k : Fin n, A k i * A k j) = if i = j then 1 else 0) ∧
  (∀ i j : Fin n,
      (∑ k : Fin n, A i k * A j k) = if i = j then 1 else 0)

noncomputable def p49Householder {n : ℕ}
    (v : P49Vector n) (beta : ℝ) : P49Matrix n :=
  fun i j => p49Id n i j - beta * v i * v j

def p49ScaleMatrix {n : ℕ} (a : ℝ) (A : P49Matrix n) : P49Matrix n :=
  fun i j => a * A i j

end HighamBench
