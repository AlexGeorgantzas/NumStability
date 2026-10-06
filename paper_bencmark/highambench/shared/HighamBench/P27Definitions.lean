import Mathlib

namespace HighamBench

open scoped BigOperators

abbrev P27Vector (n : ℕ) := Fin n → ℝ

abbrev P27Coupling (k q : ℕ) := Matrix (Fin k) (Fin q) ℝ

noncomputable def p27VecNormSq {n : ℕ} (x : P27Vector n) : ℝ :=
  ∑ i, x i ^ 2

noncomputable def p27PairNormSq {k q : ℕ}
    (u : P27Vector k) (v : P27Vector q) : ℝ :=
  p27VecNormSq u + p27VecNormSq v

noncomputable def p27MatVec {k q : ℕ}
    (X : P27Coupling k q) (v : P27Vector q) : P27Vector k :=
  fun i ↦ ∑ j, X i j * v j

/-- The action of the block matrix `W₁` in the proof of Theorem 3.2. -/
noncomputable def p27W1 {k q : ℕ} (X : P27Coupling k q) (α : ℝ)
    (u : P27Vector k) (v : P27Vector q) : P27Vector k × P27Vector q :=
  (u + p27MatVec X v, α • v)

/-- The action of the block matrix `W₂` in the proof of Theorem 3.2. -/
noncomputable def p27W2 {k q : ℕ} (X : P27Coupling k q) (α : ℝ)
    (u : P27Vector k) (v : P27Vector q) : P27Vector k × P27Vector q :=
  (α • u - p27MatVec X v, v)

/-- A squared Euclidean operator-gain bound for a block transformation. -/
def P27SquaredGainBound {k q : ℕ}
    (W : P27Vector k → P27Vector q → P27Vector k × P27Vector q)
    (gSq : ℝ) : Prop :=
  ∀ u v, p27PairNormSq (W u v).1 (W u v).2 ≤
    gSq * p27PairNormSq u v

/-- The quantities used in the proof of Theorem 3.2.  Here `X` represents
`Aₖ⁻¹Bₖ`, `ratio i j` represents `γⱼ(Cₖ)/ωᵢ(Aₖ)`, and the final
two fields are the two applications of the cited singular-value product
comparison. -/
structure P27Theorem32Data (k q : ℕ) where
  f : ℝ
  X : P27Coupling k q
  ratio : P27Coupling k q
  alpha : ℝ
  sigmaMTop : Fin k → ℝ
  sigmaMTail : Fin q → ℝ
  sigmaA : Fin k → ℝ
  sigmaC : Fin q → ℝ
  p_lt_f : ∀ i j, X i j ^ 2 + ratio i j ^ 2 < f ^ 2
  alpha_sq_le : alpha ^ 2 ≤ ∑ i, ∑ j, ratio i j ^ 2
  hornJohnson_top : ∀ gSq, 0 ≤ gSq →
    P27SquaredGainBound (p27W1 X alpha) gSq →
    ∀ i, sigmaMTop i ≤ sigmaA i * Real.sqrt gSq
  hornJohnson_tail : ∀ gSq, 0 ≤ gSq →
    P27SquaredGainBound (p27W2 X alpha) gSq →
    ∀ j, sigmaC j ≤ sigmaMTail j * Real.sqrt gSq

noncomputable def p27StrongFactor (k q : ℕ) (f : ℝ) : ℝ :=
  Real.sqrt (1 + f ^ 2 * (k : ℝ) * (q : ℝ))

end HighamBench
