import Mathlib

namespace HighamBench

open scoped BigOperators

/-! Paper-local rounded triangular inverses and final product for Method D in Section 3.4. -/

structure P62FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_sub : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_div : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_sub : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_sub x y = (x - y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)
  model_div : ∀ x y : ℝ, y ≠ 0 → ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_div x y = (x / y) * (1 + δ)

abbrev P62Matrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

noncomputable def p62Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P62GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p62MatMul {m n p : ℕ}
    (A : P62Matrix m n) (B : P62Matrix n p) : P62Matrix m p :=
  fun i j => ∑ k : Fin n, A i k * B k j

noncomputable def p62RoundedDotProduct (fp : P62FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n'
        (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p62RoundedMatMul (fp : P62FPModel) {m n p : ℕ}
    (A : P62Matrix m n) (B : P62Matrix n p) : P62Matrix m p :=
  fun i j => p62RoundedDotProduct fp n (A i) (fun k => B k j)

noncomputable def p62ForwardSubSteps (fp : P62FPModel) (n : ℕ)
    (L : P62Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ), k ≤ n → (Fin n → ℝ) → Fin n → ℝ
  | 0, _, x => x
  | k + 1, hk, x =>
      have hlt : n - k - 1 < n := by omega
      let ik : Fin n := ⟨n - k - 1, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      p62ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'

noncomputable def p62ForwardSub (fp : P62FPModel) (n : ℕ)
    (L : P62Matrix n n) (b : Fin n → ℝ) : Fin n → ℝ :=
  p62ForwardSubSteps fp n L b n (le_refl n) (fun _ => 0)

noncomputable def p62BackSubSteps (fp : P62FPModel) (n : ℕ)
    (U : P62Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ), k ≤ n → (Fin n → ℝ) → Fin n → ℝ
  | 0, _, x => x
  | k + 1, hk, x =>
      have hlt : k < n := hk
      let ik : Fin n := ⟨k, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      p62BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x'

noncomputable def p62BackSub (fp : P62FPModel) (n : ℕ)
    (U : P62Matrix n n) (b : Fin n → ℝ) : Fin n → ℝ :=
  p62BackSubSteps fp n U b n (le_refl n) (fun _ => 0)

/-- Method 1 in Section 2 applied to each column of the lower triangular inverse. -/
noncomputable def p62LowerInverse (fp : P62FPModel) (n : ℕ)
    (L : P62Matrix n n) : P62Matrix n n :=
  fun i j => p62ForwardSub fp n L (fun k => if k = j then 1 else 0) i

/-- The upper-triangular analogue of Method 1. -/
noncomputable def p62UpperInverse (fp : P62FPModel) (n : ℕ)
    (U : P62Matrix n n) : P62Matrix n n :=
  fun i j => p62BackSub fp n U (fun k => if k = j then 1 else 0) i

/-- Method D's final rounded product of the two computed triangular inverses. -/
noncomputable def p62ComputedInverse (fp : P62FPModel) (n : ℕ)
    (L U : P62Matrix n n) : P62Matrix n n :=
  p62RoundedMatMul fp (p62UpperInverse fp n U) (p62LowerInverse fp n L)

end HighamBench
