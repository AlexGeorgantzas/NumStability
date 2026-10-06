import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Higham Theorem 13.5 recurrence constants

Source correspondence for the partitioned-LU error recurrences in Higham,
*Accuracy and Stability of Numerical Algorithms*, second edition, Theorem
13.5. The module defines `blockErrorDelta` and `blockErrorTheta`, proves their
recurrence and nonnegativity properties, derives linear and cubic majorants,
and establishes the cubic asymptotic bound for the conventional BLAS-3
constants.

These definitions remain source-owned because their recurrence and constants
encode the numbered theorem rather than a general block-LU interface.
-/

namespace NumStability

open Filter Asymptotics

/-- δ(m) for the partitioned LU backward error recurrence in Theorem 13.5.
    δ counts block elimination steps minus one: δ(m) = m−1 for m ≥ 1.
    In the book: δ(n,r) with n = m·r gives δ = m−1. -/
noncomputable def blockErrorDelta : ℕ → ℝ
  | 0 => 0
  | m + 1 => (m : ℝ)

/-- θ(m) for the partitioned LU backward error recurrence in Theorem 13.5.
    Recurrence: θ(0) = 0, θ(1) = c₃, θ(m+2) = max{c₃, c₂, 1 + c₁ + δ(m+1) + θ(m+1)}.
    c₁, c₂, c₃ are BLAS-3 error constants (scalar parameters).
    For conventional BLAS3: c₁(m,n,p) = n², c₂(m,p) = m², c₃(r) = r. -/
noncomputable def blockErrorTheta (c₁ c₂ c₃ : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => c₃
  | m + 2 => max (max c₃ c₂)
    (1 + c₁ + blockErrorDelta (m + 1) + blockErrorTheta c₁ c₂ c₃ (m + 1))

lemma blockErrorDelta_nonneg (m : ℕ) : 0 ≤ blockErrorDelta m := by
  cases m with
  | zero => simp [blockErrorDelta]
  | succ m => simp [blockErrorDelta]

lemma blockErrorTheta_nonneg_of_c3_nonneg (c₁ c₂ c₃ : ℝ) (hc₃ : 0 ≤ c₃)
    (m : ℕ) :
    0 ≤ blockErrorTheta c₁ c₂ c₃ m := by
  cases m with
  | zero => simp [blockErrorTheta]
  | succ m =>
      cases m with
      | zero => simpa [blockErrorTheta] using hc₃
      | succ m =>
          have hmax₁ : 0 ≤ max c₃ c₂ := le_trans hc₃ (le_max_left c₃ c₂)
          exact le_trans hmax₁
            (le_max_left (max c₃ c₂)
              (1 + c₁ + blockErrorDelta (m + 1) +
                blockErrorTheta c₁ c₂ c₃ (m + 1)))

/-- Source-form recurrence for Theorem 13.5's `δ`: after the base one-block
    case, adding one more block increments the constant by one. -/
theorem blockErrorDelta_succ_succ (m : ℕ) :
    blockErrorDelta (m + 2) = 1 + blockErrorDelta (m + 1) := by
  cases m with
  | zero => simp [blockErrorDelta]
  | succ m =>
      simp [blockErrorDelta]
      ring

/-- Source-form recurrence for Theorem 13.5's `θ`, in block-count notation. -/
theorem blockErrorTheta_succ_succ (c₁ c₂ c₃ : ℝ) (m : ℕ) :
    blockErrorTheta c₁ c₂ c₃ (m + 2) =
      max (max c₃ c₂)
        (1 + c₁ + blockErrorDelta (m + 1) +
          blockErrorTheta c₁ c₂ c₃ (m + 1)) := by
  rfl

lemma blockErrorDelta_le_self (m : ℕ) :
    blockErrorDelta m ≤ (m : ℝ) := by
  cases m with
  | zero => simp [blockErrorDelta]
  | succ m => simp [blockErrorDelta]

/-- Higham, 2nd ed., Chapter 13, Section 13.2, p.250:
    recurrence-bound dependency for the `θ(n,r)=O(n^3)` statement.

    If every local increment in the `θ` recurrence is bounded by a common
    budget `K`, then `θ(k)` is bounded by `kK` through block count `m`. -/
theorem blockErrorTheta_le_linear_of_step_bound
    (c₁ c₂ c₃ K : ℝ) (m : ℕ)
    (hK : 0 ≤ K)
    (hc₂ : c₂ ≤ K) (hc₃ : c₃ ≤ K)
    (hstep : ∀ q : ℕ, q < m → 1 + c₁ + blockErrorDelta q ≤ K) :
    ∀ k : ℕ, k ≤ m → blockErrorTheta c₁ c₂ c₃ k ≤ (k : ℝ) * K := by
  intro k hk
  induction k with
  | zero =>
      simp [blockErrorTheta]
  | succ k ih =>
      cases k with
      | zero =>
          simpa [blockErrorTheta] using hc₃
      | succ k =>
          rw [blockErrorTheta_succ_succ]
          apply max_le
          · apply max_le
            · calc
                c₃ ≤ K := hc₃
                _ ≤ ((k + 2 : ℕ) : ℝ) * K := by
                  have hfactor : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
                    have hk0 : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
                    have hcast : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by norm_num
                    rw [hcast]
                    linarith
                  nlinarith [mul_le_mul_of_nonneg_right hfactor hK]
            · calc
                c₂ ≤ K := hc₂
                _ ≤ ((k + 2 : ℕ) : ℝ) * K := by
                  have hfactor : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
                    have hk0 : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
                    have hcast : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by norm_num
                    rw [hcast]
                    linarith
                  nlinarith [mul_le_mul_of_nonneg_right hfactor hK]
          · have hkpred : k + 1 ≤ m := Nat.le_of_succ_le hk
            have hq : k + 1 < m := Nat.lt_of_succ_le hk
            have htheta :
                blockErrorTheta c₁ c₂ c₃ (k + 1) ≤ ((k + 1 : ℕ) : ℝ) * K :=
              ih hkpred
            have hlocal : 1 + c₁ + blockErrorDelta (k + 1) ≤ K :=
              hstep (k + 1) hq
            calc
              1 + c₁ + blockErrorDelta (k + 1) +
                  blockErrorTheta c₁ c₂ c₃ (k + 1)
                  ≤ K + ((k + 1 : ℕ) : ℝ) * K := by linarith
              _ = ((k + 2 : ℕ) : ℝ) * K := by
                have hleft : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_num
                have hright : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by norm_num
                rw [hleft, hright]
                ring

/-- Higham, 2nd ed., Chapter 13, Section 13.2, p.250:
    cubic envelope for `θ` when the BLAS3 constants supplied at size `m` are
    bounded quadratically in `m`.

    This is the finite bound behind the source's conventional
    `θ(n,r)=O(n^3)` sentence. -/
theorem blockErrorTheta_le_cubic_of_quadratic_constants
    (C c₁ c₂ c₃ : ℝ) (m : ℕ)
    (hC : 0 ≤ C) (hc₁ : c₁ ≤ C * ((m : ℝ) + 1) ^ 2)
    (hc₂ : c₂ ≤ C * ((m : ℝ) + 1) ^ 2)
    (hc₃ : c₃ ≤ C * ((m : ℝ) + 1) ^ 2) :
    blockErrorTheta c₁ c₂ c₃ m ≤
      (C + 2) * ((m : ℝ) + 1) ^ 3 := by
  let M : ℝ := (m : ℝ) + 1
  let K : ℝ := (C + 2) * M ^ 2
  have hK : 0 ≤ K := by
    dsimp [K]
    nlinarith [sq_nonneg M, hC]
  have hC_sq_le_K : C * M ^ 2 ≤ K := by
    dsimp [K]
    nlinarith [sq_nonneg M]
  have hc₂K : c₂ ≤ K := le_trans (by simpa [M] using hc₂) hC_sq_le_K
  have hc₃K : c₃ ≤ K := le_trans (by simpa [M] using hc₃) hC_sq_le_K
  have hstep : ∀ q : ℕ, q < m → 1 + c₁ + blockErrorDelta q ≤ K := by
    intro q hq
    have hδ : blockErrorDelta q ≤ M ^ 2 := by
      have hqle : (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.le_of_lt hq
      have hδself : blockErrorDelta q ≤ (q : ℝ) := blockErrorDelta_le_self q
      have hm_le_sq : (m : ℝ) ≤ M ^ 2 := by
        dsimp [M]
        nlinarith [sq_nonneg ((m : ℝ))]
      linarith
    have h1 : (1 : ℝ) ≤ M ^ 2 := by
      have hM_ge_one : (1 : ℝ) ≤ M := by
        dsimp [M]
        have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
        linarith
      nlinarith [sq_nonneg (M - 1)]
    have hc₁K : c₁ ≤ C * M ^ 2 := by simpa [M] using hc₁
    dsimp [K]
    nlinarith
  have hlin := blockErrorTheta_le_linear_of_step_bound
    c₁ c₂ c₃ K m hK hc₂K hc₃K hstep m (Nat.le_refl m)
  have hmM : (m : ℝ) ≤ M := by
    dsimp [M]
    linarith
  calc
    blockErrorTheta c₁ c₂ c₃ m ≤ (m : ℝ) * K := hlin
    _ ≤ M * K := by exact mul_le_mul_of_nonneg_right hmM hK
    _ = (C + 2) * ((m : ℝ) + 1) ^ 3 := by
      dsimp [K, M]
      ring

/-- Higham, 2nd ed., Chapter 13, Section 13.2, p.250:
    asymptotic `θ(n,r)=O(n^3)` envelope from the scalar recurrence.

    The hypotheses say that the size-indexed BLAS3 constants used to instantiate
    the recurrence are bounded by a common quadratic envelope in the block
    count.  This is the source-faithful asymptotic content of the conventional
    BLAS3 sentence, separated from the larger computed-factor theorem. -/
theorem higham13_theta_isBigO_cubic_of_quadratic_constants
    (C : ℝ) (c₁ c₂ c₃ : ℕ → ℝ)
    (hC : 0 ≤ C)
    (hc₃_nonneg : ∀ n : ℕ, 0 ≤ c₃ n)
    (hc₁ : ∀ n : ℕ, c₁ n ≤ C * ((n : ℝ) + 1) ^ 2)
    (hc₂ : ∀ n : ℕ, c₂ n ≤ C * ((n : ℝ) + 1) ^ 2)
    (hc₃ : ∀ n : ℕ, c₃ n ≤ C * ((n : ℝ) + 1) ^ 2) :
    (fun n : ℕ => blockErrorTheta (c₁ n) (c₂ n) (c₃ n) n)
      =O[atTop] (fun n : ℕ => ((n : ℝ) + 1) ^ 3) := by
  refine IsBigO.of_bound (C + 2) ?_
  exact Filter.Eventually.of_forall fun n => by
    have hbound := blockErrorTheta_le_cubic_of_quadratic_constants
      C (c₁ n) (c₂ n) (c₃ n) n hC (hc₁ n) (hc₂ n) (hc₃ n)
    have hnonneg : 0 ≤ blockErrorTheta (c₁ n) (c₂ n) (c₃ n) n := by
      exact blockErrorTheta_nonneg_of_c3_nonneg (c₁ n) (c₂ n) (c₃ n)
        (hc₃_nonneg n) n
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)] using hbound

/-- Higham, 2nd ed., Chapter 13, Section 13.2, p.250:
    conventional BLAS3 constants give the displayed cubic growth of `θ`.

    This corollary instantiates the preceding theorem with the quadratic
    matrix-size envelope for the matrix-multiply and triangular-solve constants,
    and with a fixed nonnegative diagonal-block LU constant `r`.  The shifted
    cubic `(n+1)^3` is the repository's concrete asymptotic representative for
    the source's `O(n^3)` claim. -/
theorem higham13_theta_conventional_isBigO_cubic (r : ℝ) (hr : 0 ≤ r) :
    (fun n : ℕ =>
        blockErrorTheta (((n : ℝ) + 1) ^ 2) (((n : ℝ) + 1) ^ 2) r n)
      =O[atTop] (fun n : ℕ => ((n : ℝ) + 1) ^ 3) := by
  refine higham13_theta_isBigO_cubic_of_quadratic_constants (max 1 r)
    (fun n : ℕ => ((n : ℝ) + 1) ^ 2)
    (fun n : ℕ => ((n : ℝ) + 1) ^ 2)
    (fun _n : ℕ => r)
    ?_ ?_ ?_ ?_ ?_
  · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 r)
  · intro _n
    exact hr
  · intro n
    simpa using
      mul_le_mul_of_nonneg_right (le_max_left 1 r) (sq_nonneg ((n : ℝ) + 1))
  · intro n
    simpa using
      mul_le_mul_of_nonneg_right (le_max_left 1 r) (sq_nonneg ((n : ℝ) + 1))
  · intro n
    have hM_sq : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
      have hM_ge_one : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
        linarith
      nlinarith [sq_nonneg ((n : ℝ) + 1 - 1)]
    calc
      r ≤ max 1 r := le_max_right 1 r
      _ ≤ max 1 r * ((n : ℝ) + 1) ^ 2 := by
        have hC : 0 ≤ max 1 r :=
          le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 r)
        nlinarith [mul_le_mul_of_nonneg_left hM_sq hC]

end NumStability
