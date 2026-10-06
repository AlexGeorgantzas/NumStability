import Mathlib

namespace HighamBench

open scoped BigOperators

/-! Paper-local GE leaf solves and rounded block product for the block Hessenberg stage in Section 4. -/

structure P64FPModel where
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

abbrev P64Matrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

noncomputable def p64Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P64GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p64MatMul {m n p : ℕ}
    (A : P64Matrix m n) (B : P64Matrix n p) : P64Matrix m p :=
  fun i j => ∑ k : Fin n, A i k * B k j

noncomputable def p64RoundedDotProduct (fp : P64FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n'
        (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p64RoundedMatMul (fp : P64FPModel) {m n p : ℕ}
    (A : P64Matrix m n) (B : P64Matrix n p) : P64Matrix m p :=
  fun i j => p64RoundedDotProduct fp n (A i) (fun k => B k j)

noncomputable def p64ForwardSubSteps (fp : P64FPModel) (n : ℕ)
    (L : P64Matrix n n) (b : Fin n → ℝ) :
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
      p64ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'

noncomputable def p64ForwardSub (fp : P64FPModel) (n : ℕ)
    (L : P64Matrix n n) (b : Fin n → ℝ) : Fin n → ℝ :=
  p64ForwardSubSteps fp n L b n (le_refl n) (fun _ => 0)

noncomputable def p64BackSubSteps (fp : P64FPModel) (n : ℕ)
    (U : P64Matrix n n) (b : Fin n → ℝ) :
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
      p64BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x'

noncomputable def p64BackSub (fp : P64FPModel) (n : ℕ)
    (U : P64Matrix n n) (b : Fin n → ℝ) : Fin n → ℝ :=
  p64BackSubSteps fp n U b n (le_refl n) (fun _ => 0)

/-- A GE leaf's computed LU factorization, as used for small systems in Section 3. -/
structure P64LUCertificate (fp : P64FPModel) (n : ℕ)
    (A L U : P64Matrix n n) : Prop where
  L_diag : ∀ i : Fin n, L i i = 1
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0
  backward_bound : ∀ i j : Fin n,
    |(∑ k : Fin n, L i k * U k j) - A i j| ≤
      p64Gamma fp.u n * ∑ k : Fin n, |L i k| * |U k j|

noncomputable def p64LUSolve (fp : P64FPModel) (n : ℕ)
    (L U : P64Matrix n n) (b : Fin n → ℝ) : Fin n → ℝ :=
  p64BackSub fp n U (p64ForwardSub fp n L b)

noncomputable def p64RoundedMatVec (fp : P64FPModel) (n : ℕ)
    (A : P64Matrix n n) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => p64RoundedDotProduct fp n (A i) x

end HighamBench
