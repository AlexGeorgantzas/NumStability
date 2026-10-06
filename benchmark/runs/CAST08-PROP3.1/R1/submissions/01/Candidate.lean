import NumStability.Algorithms.Summation.Recursive.Core

open scoped BigOperators

namespace HighamBenchCandidate

/-- The `j`th consecutive block at the next level consists of the indices
`j * b^levels + i`, for `0 ≤ i < b^levels`. -/
def blockIndex (b levels : ℕ) (j : Fin b) (i : Fin (b ^ levels)) :
    Fin (b ^ (levels + 1)) :=
  ⟨j.val * b ^ levels + i.val, by
    have h₁ : j.val * b ^ levels + i.val < (j.val + 1) * b ^ levels := by
      simpa [Nat.add_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Nat.add_lt_add_left i.isLt (j.val * b ^ levels)
    have h₂ : (j.val + 1) * b ^ levels ≤ b * b ^ levels :=
      Nat.mul_le_mul_right (b ^ levels) (Nat.succ_le_of_lt j.isLt)
    calc
      j.val * b ^ levels + i.val < (j.val + 1) * b ^ levels := h₁
      _ ≤ b * b ^ levels := h₂
      _ = b ^ (levels + 1) := by simp [pow_succ, Nat.mul_comm]
  ⟩

/-- Equal-block superblock summation. Level zero is a single input. Each
higher level recursively computes `b` consecutive child totals and adds them
left to right using the rounded addition of `fp`. Thus level one is ordinary
recursive summation, and level `t` has `b^t` inputs and exactly `t` summation
levels. The final transfer omitted by Figure 3.1(a)'s propagation loop is
included, as in the paper's prose and Figure 3.2. -/
noncomputable def superblockSum (fp : NumStability.FPModel) (b : ℕ) :
    (levels : ℕ) → (Fin (b ^ levels) → ℝ) → ℝ
  | 0, v => v ⟨0, by simp⟩
  | levels + 1, v =>
      NumStability.fl_recursiveSum fp b (fun j =>
        superblockSum fp b levels (fun i => v (blockIndex b levels j i)))

/-- Castaldo–Whaley–Chronopoulos, Proposition 3.1, for positive integral
equal blocking factors. The abstract standard relative-error model excludes
overflow and underflow; `gammaValid` is the paper's `t(b-1)u < 1` guard. -/
theorem target :
    ∀ (t b : ℕ),
      0 < t → 0 < b →
      (∀ (fp : NumStability.FPModel),
        NumStability.gammaValid fp (t * (b - 1)) →
        ∀ v : Fin (b ^ t) → ℝ,
          |superblockSum fp b t v - ∑ i : Fin (b ^ t), v i| ≤
            NumStability.gamma fp (t * (b - 1)) *
              ∑ i : Fin (b ^ t), |v i|) ∧
      (∀ factors : Fin t → ℕ,
        (∀ i, 0 < factors i) →
        (∏ i : Fin t, factors i) = b ^ t →
        t * (b - 1) ≤ ∑ i : Fin t, (factors i - 1)) ∧
      (∏ _i : Fin t, b) = b ^ t ∧
      (∑ _i : Fin t, (b - 1)) = t * (b - 1) := by
  sorry

end HighamBenchCandidate
