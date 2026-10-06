import NumStability.Algorithms.Summation.Recursive.Core

namespace HighamBenchCandidate

open NumStability
open scoped BigOperators

/-- Equal contiguous blocks at each level, with `B` child totals combined
left to right. Level zero is a single already computed input product. -/
noncomputable def superblockSum (fp : FPModel) (B : ℕ) :
    (t : ℕ) → (Fin (B ^ t) → ℝ) → ℝ
  | 0, v => v ⟨0, by simp⟩
  | t + 1, v =>
      fl_recursiveSum fp B (fun j =>
        superblockSum fp B t (fun i =>
          v ⟨j.val * B ^ t + i.val, by
            have hj := j.isLt
            have hi := i.isLt
            rw [pow_succ]
            calc
              j.val * B ^ t + i.val < j.val * B ^ t + B ^ t :=
                Nat.add_lt_add_left hi _
              _ = (j.val + 1) * B ^ t := by ring
              _ ≤ B * B ^ t :=
                Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hj)
              _ = B ^ t * B := Nat.mul_comm _ _⟩))

/-- The equal-block superblock dot product: one rounded multiplication
per input, followed by `t` levels of rounded left-to-right sums. -/
noncomputable def superblockDot (fp : FPModel) (t B N : ℕ)
    (hN : B ^ t = N) (x y : Fin N → ℝ) : ℝ :=
  superblockSum fp B t (fun i =>
    fp.fl_mul (x (Fin.cast hN i)) (y (Fin.cast hN i)))

/-- Castaldo–Whaley–Chronopoulos (2008), Proposition 3.2, equation (3.2).
The paper excludes overflow and underflow and uses the standard relative-error
model represented here by `FPModel`. The mathematical equal-block hierarchy
follows Section 3 and Figure 3.2; Figure 3.1(a)'s printed carry loop omits
level zero. -/
theorem target :
    ∀ (fp : FPModel) (t B N : ℕ)
      (ht : 0 < t) (hB : 0 < B) (hN : B ^ t = N)
      (x y : Fin N → ℝ),
      gammaValid fp (t * (B - 1) + 1) →
      |superblockDot fp t B N hN x y -
          ∑ i : Fin N, x i * y i| ≤
        gamma fp (t * (B - 1) + 1) *
          ∑ i : Fin N, |x i * y i| := by
  sorry

end HighamBenchCandidate
