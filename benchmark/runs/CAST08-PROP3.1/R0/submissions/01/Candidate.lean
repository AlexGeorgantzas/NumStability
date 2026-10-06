import Mathlib

namespace HighamBenchCandidate

/-- Sum `count + 1` child totals from left to right. The first total is
loaded directly; each later addition incurs its own relative error. -/
def roundedPrefix (δ : ℕ → ℕ → ℕ → ℝ) (level node : ℕ)
    (child : ℕ → ℝ) : ℕ → ℝ
  | 0 => child 0
  | k + 1 =>
      (roundedPrefix δ level node child k + child (k + 1)) *
        (1 + δ level node k)

/-- At level zero the nodes are inputs. Each further level combines `b`
consecutive nodes of the preceding level, in their original order. This is the
mathematical t-level summation in Section 3 and Figure 3.2. The literal loop
in Figure 3.1(a) omits the final transfer to temporary zero, so it does not
implement the described summation as printed. -/
def superblockLevel (b : ℕ) (x : ℕ → ℝ)
    (δ : ℕ → ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, node => x node
  | level + 1, node =>
      roundedPrefix δ level node
        (fun j => superblockLevel b x δ level (node * b + j)) (b - 1)

/-- The independently rounded additions actually performed in a `t` level
equal-block summation satisfy the standard relative-error model. -/
def admissibleErrors (t b : ℕ) (u : ℝ)
    (δ : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ level node step : ℕ,
    level < t → node < b ^ (t - level - 1) → step < b - 1 →
      |δ level node step| ≤ u

noncomputable def gamma (u : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) * u / (1 - (m : ℝ) * u)

/-- Proposition 3.1: equal integral blocking is optimal for the error
counter, and its recursively computed sum has the corresponding forward
error bound under the standard no-overflow/no-underflow relative model. -/
theorem target :
    ∀ (t b : ℕ), 0 < t → 0 < b →
      (∀ factors : Fin t → ℕ,
        (∀ i, 0 < factors i) →
        (∏ i : Fin t, factors i) = b ^ t →
        t * (b - 1) ≤ ∑ i : Fin t, (factors i - 1)) ∧
      (∏ _i : Fin t, b) = b ^ t ∧
      (∑ _i : Fin t, (b - 1)) = t * (b - 1) ∧
      (∀ (u : ℝ) (x : Fin (b ^ t) → ℝ)
          (δ : ℕ → ℕ → ℕ → ℝ),
        0 < u → (t * (b - 1) : ℕ) * u < 1 →
        admissibleErrors t b u δ →
        |superblockLevel b
            (fun n => if h : n < b ^ t then x ⟨n, h⟩ else 0)
            δ t 0 - ∑ i : Fin (b ^ t), x i| ≤
          gamma u (t * (b - 1)) *
            ∑ i : Fin (b ^ t), |x i|) := by
  sorry

end HighamBenchCandidate
