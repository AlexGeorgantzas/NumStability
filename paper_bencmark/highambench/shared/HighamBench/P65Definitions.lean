import Mathlib

namespace HighamBench

open scoped BigOperators

/-! Blanchard–Higham–Mary, Algorithm 3.1: recursive block sums with a
power-of-two pairwise sum of the block results. -/

structure P65FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)

noncomputable def p65Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P65GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p65RecursiveSum (fp : P65FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0

private lemma p65LeftLt (r : ℕ) (i : Fin (2 ^ r)) :
    i.val < 2 ^ (r + 1) := by
  have := i.isLt
  simp [pow_succ]
  omega

private lemma p65RightLt (r : ℕ) (i : Fin (2 ^ r)) :
    i.val + 2 ^ r < 2 ^ (r + 1) := by
  have := i.isLt
  simp [pow_succ]
  omega

noncomputable def p65PairwiseSum (fp : P65FPModel) :
    (r : ℕ) → (Fin (2 ^ r) → ℝ) → ℝ
  | 0, v => v ⟨0, by norm_num⟩
  | r + 1, v => fp.fl_add
      (p65PairwiseSum fp r (fun i => v ⟨i.val, p65LeftLt r i⟩))
      (p65PairwiseSum fp r (fun i => v ⟨i.val + 2 ^ r, p65RightLt r i⟩))

noncomputable def p65FABsum (fp : P65FPModel) (b r : ℕ)
    (x : Fin (2 ^ r) → Fin b → ℝ) : ℝ :=
  p65PairwiseSum fp r (fun i => p65RecursiveSum fp b (x i))

end HighamBench
