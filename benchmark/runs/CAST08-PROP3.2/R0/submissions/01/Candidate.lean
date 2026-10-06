import Mathlib

namespace HighamBenchCandidate

/-- The paper's standard relative-error model for floating-point addition and
multiplication, with unit roundoff `u` and no overflow or underflow. -/
def RelativeRounding (u : ℝ) (roundAdd roundMul : ℝ → ℝ → ℝ) : Prop :=
  (∀ a b : ℝ, ∃ δ : ℝ, |δ| ≤ u ∧
    roundAdd a b = (a + b) * (1 + δ)) ∧
  (∀ a b : ℝ, ∃ δ : ℝ, |δ| ≤ u ∧
    roundMul a b = (a * b) * (1 + δ))

/-- A left-to-right block sum. The first value initializes the accumulator;
adding it to zero is exact in the source's model. -/
def roundBlock (roundAdd : ℝ → ℝ → ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: as => as.foldl roundAdd a

/-- The equal-block hierarchy: at each of `levels` levels, combine `blockSize`
consecutive child totals in their natural order. At level zero there is one
already rounded product. -/
def superblock (roundAdd : ℝ → ℝ → ℝ) (blockSize : ℕ) :
    (levels : ℕ) → List ℝ → ℝ
  | 0, values => values.headD 0
  | levels + 1, values =>
      roundBlock roundAdd
        ((List.range blockSize).map fun j =>
          superblock roundAdd blockSize levels
            ((values.drop (j * blockSize ^ levels)).take (blockSize ^ levels)))

/-- Round every input product before the `levels`-level summation. -/
def superblockDot (roundAdd roundMul : ℝ → ℝ → ℝ)
    (levels blockSize : ℕ) (x y : Fin (blockSize ^ levels) → ℝ) : ℝ :=
  superblock roundAdd blockSize levels
    (List.ofFn fun i : Fin (blockSize ^ levels) => roundMul (x i) (y i))

/-- Higham's gamma factor for an error counter `k`. -/
noncomputable def gamma (u : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) * u / (1 - (k : ℝ) * u)

/-- Castaldo–Whaley–Chronopoulos, Proposition 3.2 and (3.2), for every
integral equal-block `t`-level superblock dot product. Figure 3.1(a)'s
`j`-loop skips level zero; this follows the hierarchy in the surrounding
prose, Figure 3.2, and Proposition 3.1 instead. -/
theorem target
    (levels blockSize : ℕ) (hlevels : 0 < levels) (hblock : 0 < blockSize)
    (u : ℝ) (hu : 0 ≤ u)
    (roundAdd roundMul : ℝ → ℝ → ℝ)
    (hround : RelativeRounding u roundAdd roundMul)
    (hgamma : ((levels * (blockSize - 1) + 1 : ℕ) : ℝ) * u < 1)
    (x y : Fin (blockSize ^ levels) → ℝ) :
    |superblockDot roundAdd roundMul levels blockSize x y -
        ∑ i : Fin (blockSize ^ levels), x i * y i| ≤
      gamma u (levels * (blockSize - 1) + 1) *
        ∑ i : Fin (blockSize ^ levels), |x i * y i| := by
  sorry

end HighamBenchCandidate
