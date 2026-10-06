import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms LinearSystems SymmetricIndefinite ErrorAnalysis BlockLDLTStep

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.CholeskyIndefinite` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Equation (11.3), `s = 1` case** — one 1×1-pivot block-LDLᵀ elimination step
    is an exact factorization (exact arithmetic).  For a symmetric
    `A : Fin (m+1) → Fin (m+1) → ℝ` with nonzero pivot `A 0 0`, the unit lower
    triangular `L` (first column `A i0 / A00` below the pivot, identity in the
    trailing block) and the block-diagonal `D` (pivot `A00`, trailing Schur
    complement `A i j − A i0·A 0j / A00`) satisfy
    `∑_{k₁,k₂} L I k₁·D k₁ k₂·L J k₂ = A I J`.  This is the exact base of the
    diagonal-pivoting recursion underlying Theorem 11.3 (the floating-point
    version adds the rounding error `fl_oneByOne_schur_step_error`). -/
theorem oneByOne_step_factorization (m : ℕ) (A : Fin (m + 1) → Fin (m + 1) → ℝ)
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
      (∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = A I J := by
  have inner : ∀ (I k₁ J : Fin (m + 1)),
      (∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = L I k₁ * (∑ k₂, D k₁ k₂ * L J k₂) := by
    intro I k₁ J; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  have cdl0 : ∀ J : Fin (m + 1), (∑ k₂, D 0 k₂ * L J k₂) = A 0 0 * L J 0 := by
    intro J; rw [Fin.sum_univ_succ, hD00]
    have : (∑ k₂ : Fin m, D 0 k₂.succ * L J k₂.succ) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hD0s k, zero_mul]
    rw [this, add_zero]
  have cdls : ∀ (i : Fin m) (J : Fin (m + 1)),
      (∑ k₂, D i.succ k₂ * L J k₂)
        = ∑ k₂' : Fin m, D i.succ k₂'.succ * L J k₂'.succ := by
    intro i J; rw [Fin.sum_univ_succ, hDs0 i, zero_mul, zero_add]
  intro I J
  rw [Fin.sum_univ_succ, inner I 0 J, cdl0 J]
  have hrest : (∑ i : Fin m, ∑ k₂, L I i.succ * D i.succ k₂ * L J k₂)
      = ∑ i : Fin m, L I i.succ * (∑ k₂' : Fin m, D i.succ k₂'.succ * L J k₂'.succ) := by
    apply Finset.sum_congr rfl; intro i _; rw [inner I i.succ J, cdls i J]
  rw [hrest]
  rcases Fin.eq_zero_or_eq_succ I with hI | ⟨i0, hI⟩ <;>
    rcases Fin.eq_zero_or_eq_succ J with hJ | ⟨j0, hJ⟩ <;> subst hI <;> subst hJ
  · have : (∑ i : Fin m, L 0 i.succ *
        (∑ k₂' : Fin m, D i.succ k₂'.succ * L 0 k₂'.succ)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hL0s i, zero_mul]
    rw [this, hL0, add_zero]; ring
  · have : (∑ i : Fin m, L 0 i.succ *
        (∑ k₂' : Fin m, D i.succ k₂'.succ * L j0.succ k₂'.succ)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hL0s i, zero_mul]
    rw [this, hL0, add_zero, hLcol j0, hsym j0]; field_simp
  · have hz : (∑ i : Fin m, L i0.succ i.succ *
        (∑ k₂' : Fin m, D i.succ k₂'.succ * L 0 k₂'.succ)) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [show (∑ k₂' : Fin m, D i.succ k₂'.succ * L 0 k₂'.succ) = 0 from
          Finset.sum_eq_zero fun k _ => by rw [hL0s k, mul_zero], mul_zero]
    rw [hz, add_zero, hLcol i0, hL0]; field_simp
  · have hrsum : (∑ i : Fin m, L i0.succ i.succ *
        (∑ k₂' : Fin m, D i.succ k₂'.succ * L j0.succ k₂'.succ))
        = A i0.succ j0.succ - A i0.succ 0 * A 0 j0.succ / A 0 0 := by
      rw [Finset.sum_eq_single i0]
      · rw [hLtr i0 i0, if_pos rfl, one_mul, Finset.sum_eq_single j0]
        · rw [hDtr i0 j0, hLtr j0 j0, if_pos rfl, mul_one]
        · intro k _ hk; rw [hLtr j0 k, if_neg (Ne.symm hk), mul_zero]
        · intro h; exact absurd (Finset.mem_univ j0) h
      · intro i _ hi; rw [hLtr i0 i, if_neg (Ne.symm hi), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i0) h
    rw [hrsum, hLcol i0, hLcol j0, hsym j0]; field_simp; ring

/-- **Inductive step of the exact block-LDLᵀ recursion** (1×1 pivot), Higham
    eq (11.1)/(11.3).  Generalises `oneByOne_step_factorization`: the trailing
    block of `L`/`D` is a *recursively computed* factorization
    `L_S·D_S·L_Sᵀ = S` of the Schur complement `S` (the induction hypothesis
    `hIH`), not the identity.  With first-stage multipliers `A i0/A00` and Schur
    complement `S i j = A i.succ j.succ − A i.succ 0·A 0 j.succ / A00`, the
    assembled factors reproduce `A` exactly.  Iterating this is the exact
    `PAPᵀ = LDLᵀ` recursion underlying Theorem 11.3. -/
theorem blockLDLT_assemble_step (n : ℕ) (A : Fin (n + 1) → Fin (n + 1) → ℝ)
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
      (∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = A I J := by
  have inner : ∀ (I k₁ J : Fin (n + 1)),
      (∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = L I k₁ * (∑ k₂, D k₁ k₂ * L J k₂) := by
    intro I k₁ J; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  have cdl0 : ∀ J : Fin (n + 1), (∑ k₂, D 0 k₂ * L J k₂) = A 0 0 * L J 0 := by
    intro J; rw [Fin.sum_univ_succ, hD00]
    have : (∑ k₂ : Fin n, D 0 k₂.succ * L J k₂.succ) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hD0s k, zero_mul]
    rw [this, add_zero]
  have cdls : ∀ (i : Fin n) (J : Fin (n + 1)),
      (∑ k₂, D i.succ k₂ * L J k₂)
        = ∑ k₂' : Fin n, D_S i k₂' * L J k₂'.succ := by
    intro i J; rw [Fin.sum_univ_succ, hDs0 i, zero_mul, zero_add]
    apply Finset.sum_congr rfl; intro k _; rw [hDtr i k]
  intro I J
  rw [Fin.sum_univ_succ, inner I 0 J, cdl0 J]
  have hrest : (∑ i : Fin n, ∑ k₂, L I i.succ * D i.succ k₂ * L J k₂)
      = ∑ i : Fin n, L I i.succ * (∑ k₂' : Fin n, D_S i k₂' * L J k₂'.succ) := by
    apply Finset.sum_congr rfl; intro i _; rw [inner I i.succ J, cdls i J]
  rw [hrest]
  rcases Fin.eq_zero_or_eq_succ I with hI | ⟨i0, hI⟩ <;>
    rcases Fin.eq_zero_or_eq_succ J with hJ | ⟨j0, hJ⟩ <;> subst hI <;> subst hJ
  · have : (∑ i : Fin n, L 0 i.succ *
        (∑ k₂' : Fin n, D_S i k₂' * L 0 k₂'.succ)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hL0s i, zero_mul]
    rw [this, hL0, add_zero]; ring
  · have : (∑ i : Fin n, L 0 i.succ *
        (∑ k₂' : Fin n, D_S i k₂' * L j0.succ k₂'.succ)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hL0s i, zero_mul]
    rw [this, hL0, add_zero, hLcol j0, hsym j0]; field_simp
  · have hz : (∑ i : Fin n, L i0.succ i.succ *
        (∑ k₂' : Fin n, D_S i k₂' * L 0 k₂'.succ)) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [show (∑ k₂' : Fin n, D_S i k₂' * L 0 k₂'.succ) = 0 from
          Finset.sum_eq_zero fun k _ => by rw [hL0s k, mul_zero], mul_zero]
    rw [hz, add_zero, hLcol i0, hL0]; field_simp
  · have htrail : (∑ i : Fin n, L i0.succ i.succ *
        (∑ k₂' : Fin n, D_S i k₂' * L j0.succ k₂'.succ)) = S i0 j0 := by
      rw [← hIH i0 j0]
      apply Finset.sum_congr rfl; intro i _
      rw [hLtr i0 i, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [hLtr j0 k]; ring
    rw [htrail, hLcol i0, hLcol j0, hS i0 j0, hsym j0]
    field_simp; ring

/-- Schur complement of the leading 1×1 pivot,
`S i j = A i.succ j.succ − A i.succ 0 · A 0 j.succ / A 0 0`. -/
noncomputable def schurCompl (n : ℕ) (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0

/-- Symmetry is inherited by the Schur complement. -/
theorem schurCompl_symm (n : ℕ) (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, A i j = A j i) :
    ∀ i j : Fin n, schurCompl n A i j = schurCompl n A j i := by
  intro i j
  simp only [schurCompl]
  rw [hsym i.succ j.succ, hsym i.succ 0, hsym 0 j.succ]; ring

/-- The successive leading 1×1 pivots of the diagonal-pivoting recursion are all
nonzero (the "no 2×2 pivot needed / leading principal minors nonzero" case). -/
def AllOnePivots : (n : ℕ) → (Fin n → Fin n → ℝ) → Prop
  | 0, _ => True
  | (n + 1), A => A 0 0 ≠ 0 ∧ AllOnePivots n (schurCompl n A)

/-- **Exact all-1×1 block-LDLᵀ factorization existence** (Higham eqs (11.1)/(11.2),
the no-2×2-pivot / root-free `LDLᵀ` case).  If `A` is symmetric and every
successive Schur-complement pivot is nonzero (`AllOnePivots`), there exist factors
`L, D` with `∑ L·D·Lᵀ = A` — the exact `PAPᵀ = LDLᵀ` recursion (with `P = I`)
underlying Theorem 11.3, obtained by iterating `blockLDLT_assemble_step`. -/
theorem exact_blockLDLT_all_oneByOne :
    ∀ (n : ℕ) (A : Fin n → Fin n → ℝ),
      (∀ i j, A i j = A j i) → AllOnePivots n A →
      ∃ L D : Fin n → Fin n → ℝ,
        ∀ I J, (∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = A I J := by
  intro n
  induction n with
  | zero => intro A _ _; exact ⟨A, A, fun I => I.elim0⟩
  | succ n ih =>
    intro A hsym hp
    obtain ⟨ha, hpS⟩ := hp
    obtain ⟨L_S, D_S, hprodS⟩ := ih (schurCompl n A) (schurCompl_symm n A hsym) hpS
    refine ⟨fun I J => Fin.cases (Fin.cases 1 (fun _ => 0) J)
              (fun i => Fin.cases (A i.succ 0 / A 0 0) (fun j => L_S i j) J) I,
            fun I J => Fin.cases (Fin.cases (A 0 0) (fun _ => 0) J)
              (fun i => Fin.cases 0 (fun j => D_S i j) J) I, ?_⟩
    apply blockLDLT_assemble_step n A ha (fun i => hsym 0 i.succ)
      (schurCompl n A) L_S D_S (fun i j => rfl) hprodS
    · simp
    · intro i; simp
    · intro j; simp
    · intro i j; simp
    · simp
    · intro j; simp
    · intro i; simp
    · intro i j; simp

end NumStability
