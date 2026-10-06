import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.Summation.Recursive.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace HighamBenchCandidate

open NumStability
open scoped BigOperators

/-- Position `i` of block `j` in superblock `s`, in the original vector order. -/
def superblockIndex (b m : ℕ) (s j : Fin m) (i : Fin b) : Fin (b * m * m) :=
  ⟨(s.val * m + j.val) * b + i.val, by
    have hblock : s.val * m + j.val < m * m := by
      have hfirst : s.val * m + j.val < (s.val + 1) * m := by
        nlinarith [j.isLt]
      exact lt_of_lt_of_le hfirst
        (Nat.mul_le_mul_right m (Nat.succ_le_of_lt s.isLt))
    have hfirst : (s.val * m + j.val) * b + i.val <
        (s.val * m + j.val + 1) * b := by
      nlinarith [i.isLt]
    calc
      (s.val * m + j.val) * b + i.val <
          (s.val * m + j.val + 1) * b := hfirst
      _ ≤ (m * m) * b :=
        Nat.mul_le_mul_right b (Nat.succ_le_of_lt hblock)
      _ = b * m * m := by ring⟩

/-- Figure 3.1(b): rounded length-`b` inner dots, then `m` block totals per
superblock, then `m` superblock totals. Both outer levels start from zero. -/
noncomputable def fixedThreeLevelDot (fp : FPModel) (b m : ℕ)
    (x y : Fin (b * m * m) → ℝ) : ℝ :=
  fl_recursiveSum fp m (fun s =>
    fl_recursiveSum fp m (fun j =>
      fl_dotProduct fp b
        (fun i => x (superblockIndex b m s j i))
        (fun i => y (superblockIndex b m s j i))))

/-- Castaldo–Whaley–Chronopoulos, §3.1, fixed three-level superblock bound.
`FPModel` supplies the paper's relative-error laws in the regime without
overflow or underflow. -/
theorem target (fp : FPModel) (b m : ℕ) (hb : 0 < b) (hm : 0 < m)
    (x y : Fin (b * m * m) → ℝ)
    (hvalid : gammaValid fp (b + 2 * (m - 1))) :
    |fixedThreeLevelDot fp b m x y -
      ∑ k : Fin (b * m * m), x k * y k| ≤
      gamma fp (b + 2 * (m - 1)) *
        ∑ k : Fin (b * m * m), |x k * y k| := by
  sorry

end HighamBenchCandidate
