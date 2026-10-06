import Mathlib

namespace HighamBenchCandidate

/-- Independent relative errors for the rounded products and for additions at
all three levels of the fixed-block algorithm. -/
structure RoundErrors (b m : ℕ) where
  product : Fin (b * m * m) → ℝ
  innerAdd : Fin m → Fin m → Fin b → ℝ
  blockAdd : Fin m → Fin m → ℝ
  superAdd : Fin m → ℝ

/-- The standard relative-error model for multiplication and addition, with
unit roundoff `u`. The first addition to a zero accumulator is exact. -/
def RoundErrors.Valid {b m : ℕ} (e : RoundErrors b m) (u : ℝ) : Prop :=
  (∀ k, |e.product k| ≤ u) ∧
  (∀ s j i, |e.innerAdd s j i| ≤ u) ∧
  (∀ s j, |e.blockAdd s j| ≤ u) ∧
  (∀ s, |e.superAdd s| ≤ u)

/-- The consecutive position of entry `i` of block `j` of superblock `s`. -/
def flatIndex {b m : ℕ} (s j : Fin m) (i : Fin b) : Fin (b * m * m) :=
  finCongr (by ac_rfl) (finProdFinEquiv (finProdFinEquiv (s, j), i))

/-- Recursive summation in list order. An initial zero plus the first term is
exact, as for floating-point addition without overflow or underflow. -/
def roundedSum {n : ℕ} (term : Fin n → ℝ) (δ : Fin n → ℝ) : ℝ :=
  ((List.finRange n).foldl
    (fun acc k =>
      match acc with
      | none => some (term k)
      | some a => some ((a + term k) * (1 + δ k)))
    (none : Option ℝ)).getD 0

/-- Rounded length-`b` inner dot product for one consecutive block. -/
def innerDot {b m : ℕ} (x y : Fin (b * m * m) → ℝ)
    (e : RoundErrors b m) (s j : Fin m) : ℝ :=
  roundedSum
    (fun i => (x (flatIndex s j i) * y (flatIndex s j i)) *
      (1 + e.product (flatIndex s j i)))
    (e.innerAdd s j)

/-- Three-level fixed-`b` superblock dot product, retaining the input order. -/
def superblockDot {b m : ℕ} (x y : Fin (b * m * m) → ℝ)
    (e : RoundErrors b m) : ℝ :=
  roundedSum
    (fun s => roundedSum (fun j => innerDot x y e s j) (e.blockAdd s))
    e.superAdd

/-- Higham's `γ_k = ku/(1-ku)` bound. -/
noncomputable def gamma (u : ℝ) (k : ℕ) : ℝ := (k * u) / (1 - k * u)

/-- Section 3.1 of Castaldo, Whaley, and Chronopoulos (2008), for Figure 3.1(b).
Here `N = b*m*m`, with positive integral block size `b` and `m` blocks per
superblock and superblocks in total. -/
theorem target :
    ∀ (b m : ℕ), 0 < b → 0 < m →
    ∀ (u : ℝ), 0 ≤ u →
    ∀ (x y : Fin (b * m * m) → ℝ) (e : RoundErrors b m),
      e.Valid u →
      (((b + 2 * (m - 1) : ℕ) : ℝ) * u < 1) →
      |superblockDot x y e - ∑ k : Fin (b * m * m), x k * y k| ≤
        gamma u (b + 2 * (m - 1)) *
          ∑ k : Fin (b * m * m), |x k * y k| := by
  sorry

end HighamBenchCandidate
