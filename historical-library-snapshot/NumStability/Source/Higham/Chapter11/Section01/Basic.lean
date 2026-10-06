import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLTStep

/-!
# Higham Chapter 11: Basic

Canonical owner materialized from the reviewed Chapter 11 route contract.
-/

namespace NumStability

open scoped BigOperators

/-! ## Chapter 11 intro and §11.1 block LDL^T factorization -/

/-- **Equation (11.1)** source predicate:
`P A P^T = L D L^T`, with unit lower triangular `L` and symmetric block
diagonal `D` with diagonal blocks of size one or two. -/
abbrev higham11_1_BlockLDLTSpec (n : ℕ)
    (A L D : Fin n → Fin n → ℝ) (σ : Fin n → Fin n) : Prop :=
  BlockLDLTSpec n A L D σ

/-- **Equation (11.2)** nonsingularity condition for the first pivot block. -/
def higham11_2_NonsingularPivotBlock
    (s : ℕ) (E E_inv : Fin s → Fin s → ℝ) : Prop :=
  (∀ i j : Fin s, ∑ k : Fin s, E i k * E_inv k j = if i = j then 1 else 0) ∧
  (∀ i j : Fin s, ∑ k : Fin s, E_inv i k * E k j = if i = j then 1 else 0)

/-- **Equation (11.3)** symmetric Schur complement
`B - C E^{-1} C^T` from the first block LDL^T step. -/
noncomputable def higham11_3_symmetricSchurComplement (m s : ℕ)
    (B : Fin m → Fin m → ℝ)
    (C : Fin m → Fin s → ℝ)
    (E_inv : Fin s → Fin s → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => B i j - ∑ p : Fin s, ∑ q : Fin s, C i p * E_inv p q * C j q

/-- **Equation (11.3), `s = 1` exact factorization step**: with pivot `A 0 0 ≠ 0`,
the 1×1-pivot unit-lower-triangular `L` and block-diagonal `D` (pivot + trailing
Schur complement) reproduce `A` exactly, `∑ L·D·Lᵀ = A`.  The exact base of the
diagonal-pivoting recursion behind Theorem 11.3. -/
theorem higham11_3_oneByOne_step_factorization (m : ℕ)
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (ha : A 0 0 ≠ 0) (hsym : ∀ i : Fin m, A 0 i.succ = A i.succ 0)
    (L D : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hL0 : L 0 0 = 1)
    (hLcol : ∀ i : Fin m, L i.succ 0 = A i.succ 0 / A 0 0)
    (hL0s : ∀ j : Fin m, L 0 j.succ = 0)
    (hLtr : ∀ i j : Fin m, L i.succ j.succ = if i = j then 1 else 0)
    (hD00 : D 0 0 = A 0 0)
    (hD0s : ∀ j : Fin m, D 0 j.succ = 0)
    (hDs0 : ∀ i : Fin m, D i.succ 0 = 0)
    (hDtr : ∀ i j : Fin m, D i.succ j.succ
      = A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) :
    ∀ I J : Fin (m + 1),
      (∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = A I J :=
  oneByOne_step_factorization m A ha hsym L D hL0 hLcol hL0s hLtr
    hD00 hD0s hDs0 hDtr

/-- **Eq (11.1)/(11.3) inductive step** for the exact block-LDLᵀ recursion: with
the trailing block factorized recursively (`hIH : L_S·D_S·L_Sᵀ = S`, the Schur
complement) and first-stage 1×1-pivot multipliers, the assembled `L,D` reproduce
`A` exactly.  Iterating gives the exact `PAPᵀ = LDLᵀ` behind Theorem 11.3. -/
theorem higham11_3_blockLDLT_assemble_step (n : ℕ)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (ha : A 0 0 ≠ 0) (hsym : ∀ i : Fin n, A 0 i.succ = A i.succ 0)
    (S L_S D_S : Fin n → Fin n → ℝ)
    (hS : ∀ i j : Fin n, S i j = A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0)
    (hIH : ∀ i j : Fin n, (∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂) = S i j)
    (L D : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hL0 : L 0 0 = 1)
    (hLcol : ∀ i : Fin n, L i.succ 0 = A i.succ 0 / A 0 0)
    (hL0s : ∀ j : Fin n, L 0 j.succ = 0)
    (hLtr : ∀ i j : Fin n, L i.succ j.succ = L_S i j)
    (hD00 : D 0 0 = A 0 0)
    (hD0s : ∀ j : Fin n, D 0 j.succ = 0)
    (hDs0 : ∀ i : Fin n, D i.succ 0 = 0)
    (hDtr : ∀ i j : Fin n, D i.succ j.succ = D_S i j) :
    ∀ I J : Fin (n + 1),
      (∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = A I J :=
  blockLDLT_assemble_step n A ha hsym S L_S D_S hS hIH L D
    hL0 hLcol hL0s hLtr hD00 hD0s hDs0 hDtr

/-- **Eq (11.1)/(11.2) exact factorization existence** (no-2×2-pivot case): a
symmetric `A` all of whose successive Schur-complement pivots are nonzero
(`AllOnePivots`) has an exact `LDLᵀ` factorization `∑ L·D·Lᵀ = A`.  The exact
`PAPᵀ = LDLᵀ` recursion (P = I) underlying Theorem 11.3. -/
theorem higham11_1_exact_blockLDLT_all_oneByOne (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, A i j = A j i) (hp : AllOnePivots n A) :
    ∃ L D : Fin n → Fin n → ℝ,
      ∀ I J, (∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = A I J :=
  exact_blockLDLT_all_oneByOne n A hsym hp


end NumStability
