import Mathlib

namespace HighamBench

open scoped BigOperators

/-! Paper-local rounded matrix product and triangular solve for Method B in Section 6. -/

structure P61FPModel where
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

abbrev P61Matrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

noncomputable def p61Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P61GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p61MatMul {m n p : ℕ}
    (A : P61Matrix m n) (B : P61Matrix n p) : P61Matrix m p :=
  fun i j => ∑ k : Fin n, A i k * B k j

noncomputable def p61RoundedDotProduct (fp : P61FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n'
        (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p61RoundedMatMul (fp : P61FPModel) {m n p : ℕ}
    (A : P61Matrix m n) (B : P61Matrix n p) : P61Matrix m p :=
  fun i j => p61RoundedDotProduct fp n (A i) (fun k => B k j)

noncomputable def p61ForwardSubSteps (fp : P61FPModel) (n : ℕ)
    (L : P61Matrix n n) (b : Fin n → ℝ) :
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
      p61ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'

noncomputable def p61ForwardSub (fp : P61FPModel) (n : ℕ)
    (L : P61Matrix n n) (b : Fin n → ℝ) : Fin n → ℝ :=
  p61ForwardSubSteps fp n L b n (le_refl n) (fun _ => 0)

/-- The off-diagonal block produced by Method B of the divide-and-conquer inverse. -/
noncomputable def p61MethodBOffDiagonal (fp : P61FPModel) {n r p : ℕ}
    (L22 : P61Matrix n n) (L21 : P61Matrix n r)
    (X11 : P61Matrix r p) : P61Matrix n p :=
  fun i j => p61ForwardSub fp n L22
    (fun k => -(p61RoundedMatMul fp L21 X11 k j)) i

end HighamBench
