import Mathlib

open scoped BigOperators

namespace HighamBench

/-- Exact unit-lower/upper factorization certificate used to express the
factorization displayed in P43, equation (3.5). -/
structure P43LUFactSpec (n : ℕ) (A L : Fin n → Fin n → ℝ)
    (U : Fin n → Fin n → ℝ) : Prop where
  L_diag : ∀ i : Fin n, L i i = 1
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0
  product_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j

/-- Scalar-panel (b = 1) form of the sparse matrix G displayed in
Theorem 3.4, equation (3.5).

The first parameter is the reduction-tree height. The sequence a contains
the successive scalar pivot blocks, u is the first transformed trailing
entry, r is the original row-panel entry, and q is its trailing entry. -/
noncomputable def p43Chain :
    (H : ℕ) → (ℕ → ℝ) → ℝ → ℝ → ℝ → Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ
  | 0, a, u, r, q =>
      fun i j =>
        Fin.cases
          (Fin.cases (a 0) (fun _ => u) j)
          (fun _ => Fin.cases r (fun _ => q) j)
          i
  | H + 1, a, u, r, q =>
      fun i j =>
        Fin.cases
          (Fin.cases (a 0)
            (fun j' => if j'.val = H + 1 then u else 0) j)
          (fun i' =>
            Fin.cases
              (if i' = 0 then a 1 else 0)
              (fun j' =>
                p43Chain H (fun t => a (t + 1)) 0 (-r) q i' j')
              j)
          i

/-- The bottom-right index of the scalar chain matrix. -/
def p43Last (H : ℕ) : Fin (H + 2) :=
  Fin.last (H + 1)

/-- The unit-lower factors and inverse actions used in the proof of P43,
Theorem 3.6. The probe vectors model the paper's bounded vectors
`Abar_i * Ubar_(i+1)⁻¹`; the level vectors record their repeated action along
the reduction-tree path. All inverse actions are exposed as matrix equations. -/
structure P43CALUMultiplierProcess (b H : ℕ)
    (ell : ℕ → ℕ → ℕ → ℝ)
    (probeIn probeOut z : ℕ → ℕ → ℝ) : Prop where
  base_bound :
    ∀ i, i < b → |z 0 i| ≤ 1
  probe_input_bound :
    ∀ h, h < H → ∀ i, i < b →
      |probeIn h i| ≤ 1
  unit_diagonal :
    ∀ h, h < H → ∀ i, i < b →
      ell h i i = 1
  upper_zero :
    ∀ h, h < H → ∀ i, i < b → ∀ k, k < b → i < k →
      ell h i k = 0
  coefficient_bound :
    ∀ h, h < H → ∀ i, i < b → ∀ k, k < i →
      |ell h i k| ≤ 1
  probe_equation :
    ∀ h, h < H → ∀ i, i < b →
      ∑ k ∈ Finset.range b, ell h i k * probeOut h k =
        probeIn h i
  level_equation :
    ∀ h, h < H → ∀ i, i < b →
      ∑ k ∈ Finset.range b, ell h i k * z (h + 1) k =
        z h i
end HighamBench
