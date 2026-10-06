import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms LinearSystems Cholesky PositiveSemidefinite ScaledStage

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter10` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- The √-scaled matrix `H = D⁻¹AD⁻¹`, `D = diag(√a_ii)`, has unit
    diagonal. -/
lemma scaled_matrix_unit_diag {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hAdiag : ∀ i : Fin n, 0 < A i i) (i : Fin n) :
    A i i / (Real.sqrt (A i i) * Real.sqrt (A i i)) = 1 := by
  rw [Real.mul_self_sqrt (hAdiag i).le]
  exact div_self (hAdiag i).ne'

/-- The √-scaled matrix of a PSD matrix is PSD (congruence by the
    positive diagonal scaling). -/
lemma scaled_matrix_isPosSemiDef {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (hAdiag : ∀ i : Fin n, 0 < A i i) :
    IsPosSemiDef n
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) := by
  constructor
  · intro i j
    show A i j / (Real.sqrt (A i i) * Real.sqrt (A j j)) =
      A j i / (Real.sqrt (A j j) * Real.sqrt (A i i))
    rw [hPSD.1 i j, mul_comm]
  · intro x
    have h := hPSD.2 (fun i => x i / Real.sqrt (A i i))
    calc (0:ℝ) ≤ ∑ i : Fin n, ∑ j : Fin n,
          x i / Real.sqrt (A i i) * A i j *
          (x j / Real.sqrt (A j j)) := h
      _ = ∑ i : Fin n, ∑ j : Fin n, x i *
          (A i j / (Real.sqrt (A i i) * Real.sqrt (A j j))) * x j := by
          refine Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => ?_
          have hi := Real.sqrt_pos.mpr (hAdiag i)
          have hj := Real.sqrt_pos.mpr (hAdiag j)
          field_simp

/-- **Scaled interior mass from an operator-norm certificate**
    (Theorem 10.7 normwise stage route): if the `D`-scaled residual
    `E_ij = Δ_ij/(√a_i√a_j)` carries `opNorm2Le E ε`, the weighted
    perturbation mass obeys `|yᵀΔy| ≤ ε·∑ a_i y_i²` — exactly the
    normwise hypothesis of `bordered_perturbation_floor_normwise`,
    with no dimension factor. -/
lemma scaled_interior_mass_normwise {m : ℕ}
    (Δ : Fin m → Fin m → ℝ) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ε : ℝ)
    (hcert : opNorm2Le
      (fun i j : Fin m => Δ i j /
        (Real.sqrt (a i) * Real.sqrt (a j))) ε)
    (y : Fin m → ℝ)
    (hnz : ∀ i j : Fin m, a i = 0 ∨ a j = 0 → Δ i j = 0) :
    |∑ i : Fin m, ∑ j : Fin m, y i * Δ i j * y j| ≤
      ε * ∑ i : Fin m, a i * y i ^ 2 := by
  set z : Fin m → ℝ := fun i => y i * Real.sqrt (a i) with hz
  have habs := quadForm_abs_le_of_opNorm2Le m
    (fun i j : Fin m => Δ i j /
      (Real.sqrt (a i) * Real.sqrt (a j))) ε hcert z
  have hquad : ∑ i : Fin m, ∑ j : Fin m,
      z i * (Δ i j / (Real.sqrt (a i) * Real.sqrt (a j))) * z j =
      ∑ i : Fin m, ∑ j : Fin m, y i * Δ i j * y j := by
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    by_cases hi : a i = 0
    · rw [hnz i j (Or.inl hi)]
      simp
    by_cases hj : a j = 0
    · rw [hnz i j (Or.inr hj)]
      simp
    · have hi' := lt_of_le_of_ne (ha i) (Ne.symm hi)
      have hj' := lt_of_le_of_ne (ha j) (Ne.symm hj)
      have hsi := Real.sqrt_pos.mpr hi'
      have hsj := Real.sqrt_pos.mpr hj'
      show y i * Real.sqrt (a i) *
        (Δ i j / (Real.sqrt (a i) * Real.sqrt (a j))) *
        (y j * Real.sqrt (a j)) = y i * Δ i j * y j
      field_simp
  have hnorm : ∑ i : Fin m, z i ^ 2 =
      ∑ i : Fin m, a i * y i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    show (y i * Real.sqrt (a i)) ^ 2 = a i * y i ^ 2
    rw [mul_pow, Real.sq_sqrt (ha i)]
    ring
  rw [hquad, hnorm] at habs
  exact habs

/-- **Scaled border mass from a vector-norm certificate** (Theorem
    10.7 normwise stage route): if the `D`-scaled border perturbation
    has squared norm at most `ε²t`, then
    `|2∑yᵢδᵢ| ≤ ε(t + ∑aᵢyᵢ²)` — Cauchy–Schwarz in the scaled inner
    product followed by AM–GM, again with no dimension factor. -/
lemma scaled_border_mass_normwise {m : ℕ}
    (δ : Fin m → ℝ) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ε t : ℝ) (hε0 : 0 ≤ ε) (ht0 : 0 ≤ t)
    (hnz : ∀ i : Fin m, a i = 0 → δ i = 0)
    (hcert : ∑ i : Fin m,
      (if a i = 0 then 0 else δ i ^ 2 / a i) ≤ ε ^ 2 * t)
    (y : Fin m → ℝ) :
    |2 * ∑ i : Fin m, y i * δ i| ≤
      ε * (t + ∑ i : Fin m, a i * y i ^ 2) := by
  set W : ℝ := ∑ i : Fin m, a i * y i ^ 2 with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ =>
    mul_nonneg (ha i) (sq_nonneg _)
  -- Cauchy–Schwarz in the scaled coordinates
  have hcs : (∑ i : Fin m, y i * δ i) ^ 2 ≤
      W * (ε ^ 2 * t) := by
    have hsplit : ∑ i : Fin m, y i * δ i =
        ∑ i : Fin m, (y i * Real.sqrt (a i)) *
          (if a i = 0 then 0 else δ i / Real.sqrt (a i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : a i = 0
      · rw [if_pos hi, hnz i hi]
        simp
      · rw [if_neg hi]
        have hi' := lt_of_le_of_ne (ha i) (Ne.symm hi)
        have hsi := Real.sqrt_pos.mpr hi'
        field_simp
    rw [hsplit]
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => y i * Real.sqrt (a i))
      (fun i => if a i = 0 then 0 else δ i / Real.sqrt (a i))
    have hL : ∑ i : Fin m, (y i * Real.sqrt (a i)) ^ 2 = W := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (ha i)]
      ring
    have hR : ∑ i : Fin m,
        (if a i = 0 then 0 else δ i / Real.sqrt (a i)) ^ 2 =
        ∑ i : Fin m, (if a i = 0 then 0 else δ i ^ 2 / a i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : a i = 0
      · rw [if_pos hi, if_pos hi]
        norm_num
      · rw [if_neg hi, if_neg hi, div_pow, Real.sq_sqrt (ha i)]
    rw [hL, hR] at h
    calc (∑ i : Fin m, (y i * Real.sqrt (a i)) *
          (if a i = 0 then 0 else δ i / Real.sqrt (a i))) ^ 2
        ≤ W * ∑ i : Fin m,
            (if a i = 0 then 0 else δ i ^ 2 / a i) := h
      _ ≤ W * (ε ^ 2 * t) :=
          mul_le_mul_of_nonneg_left hcert hW0
  -- AM–GM assembly
  have hsum : |∑ i : Fin m, y i * δ i| ≤
      ε * Real.sqrt t * Real.sqrt W := by
    have h1 : |∑ i : Fin m, y i * δ i| ^ 2 ≤
        (ε * Real.sqrt t * Real.sqrt W) ^ 2 := by
      rw [sq_abs]
      calc (∑ i : Fin m, y i * δ i) ^ 2
          ≤ W * (ε ^ 2 * t) := hcs
        _ = (ε * Real.sqrt t * Real.sqrt W) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt ht0,
              Real.sq_sqrt hW0]
            ring
    have h2 : (0:ℝ) ≤ ε * Real.sqrt t * Real.sqrt W := by
      positivity
    nlinarith [abs_nonneg (∑ i : Fin m, y i * δ i), h1, h2]
  have hamgm : 2 * (Real.sqrt t * Real.sqrt W) ≤ t + W := by
    have hsq := sq_nonneg (Real.sqrt t - Real.sqrt W)
    have hts : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
    have hWs : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW0
    nlinarith
  calc |2 * ∑ i : Fin m, y i * δ i|
      = 2 * |∑ i : Fin m, y i * δ i| := by
        rw [abs_mul]
        norm_num
    _ ≤ 2 * (ε * Real.sqrt t * Real.sqrt W) := by linarith [hsum]
    _ = ε * (2 * (Real.sqrt t * Real.sqrt W)) := by ring
    _ ≤ ε * (t + W) := mul_le_mul_of_nonneg_left hamgm hε0

/-- Quadratic-form-certificate variant of the scaled interior mass
    (composes with zero-pad restriction, unlike the `opNorm2Le`
    form). -/
lemma scaled_interior_mass_normwise_quad {m : ℕ}
    (Δ : Fin m → Fin m → ℝ) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ε : ℝ)
    (hcert : ∀ z : Fin m → ℝ,
      |∑ i : Fin m, ∑ j : Fin m, z i *
        (Δ i j / (Real.sqrt (a i) * Real.sqrt (a j))) * z j| ≤
      ε * ∑ i : Fin m, z i ^ 2)
    (y : Fin m → ℝ)
    (hnz : ∀ i j : Fin m, a i = 0 ∨ a j = 0 → Δ i j = 0) :
    |∑ i : Fin m, ∑ j : Fin m, y i * Δ i j * y j| ≤
      ε * ∑ i : Fin m, a i * y i ^ 2 := by
  set z : Fin m → ℝ := fun i => y i * Real.sqrt (a i) with hz
  have habs := hcert z
  have hquad : ∑ i : Fin m, ∑ j : Fin m,
      z i * (Δ i j / (Real.sqrt (a i) * Real.sqrt (a j))) * z j =
      ∑ i : Fin m, ∑ j : Fin m, y i * Δ i j * y j := by
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    by_cases hi : a i = 0
    · rw [hnz i j (Or.inl hi)]
      simp
    by_cases hj : a j = 0
    · rw [hnz i j (Or.inr hj)]
      simp
    · have hi' := lt_of_le_of_ne (ha i) (Ne.symm hi)
      have hj' := lt_of_le_of_ne (ha j) (Ne.symm hj)
      have hsi := Real.sqrt_pos.mpr hi'
      have hsj := Real.sqrt_pos.mpr hj'
      show y i * Real.sqrt (a i) *
        (Δ i j / (Real.sqrt (a i) * Real.sqrt (a j))) *
        (y j * Real.sqrt (a j)) = y i * Δ i j * y j
      field_simp
  have hnorm : ∑ i : Fin m, z i ^ 2 =
      ∑ i : Fin m, a i * y i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    show (y i * Real.sqrt (a i)) ^ 2 = a i * y i ^ 2
    rw [mul_pow, Real.sq_sqrt (ha i)]
    ring
  rw [hquad, hnorm] at habs
  exact habs

/-- **Per-stage border mass from full-column certificates** (Theorem
    10.7 sharp route): a scaled column-norm certificate on each full
    defect column restricts monotonically to every leading segment, so
    the border-mass hypothesis of the sharpened stage step follows for
    all stages from `n` column certificates. -/
theorem stage_border_mass_from_full {n : ℕ}
    (Δ : Fin n → Fin n → ℝ) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ε : ℝ) (hε0 : 0 ≤ ε)
    (t : Fin n → ℝ) (ht0 : ∀ j, 0 ≤ t j)
    (hnz : ∀ i j : Fin n, a i = 0 → Δ i j = 0)
    (hcertB : ∀ j : Fin n, ∑ i : Fin n,
      (if a i = 0 then 0 else Δ i j ^ 2 / a i) ≤ ε ^ 2 * t j)
    (j : Fin n) (y : Fin j.val → ℝ) :
    |2 * ∑ i : Fin j.val, y i * Δ ⟨i.val, by omega⟩ j| ≤
      ε * (t j + ∑ i : Fin j.val, a ⟨i.val, by omega⟩ * y i ^ 2) := by
  refine scaled_border_mass_normwise
    (fun i : Fin j.val => Δ ⟨i.val, by omega⟩ j)
    (fun i : Fin j.val => a ⟨i.val, by omega⟩) (fun i => ha _)
    ε (t j) hε0 (ht0 j) (fun i h => hnz _ _ h) ?_ y
  -- restrict the full column certificate to the leading segment
  refine le_trans ?_ (hcertB j)
  have hemb : Function.Injective
      (fun i : Fin j.val => (⟨i.val, by omega⟩ : Fin n)) := by
    intro p q hpq
    simpa [Fin.ext_iff] using hpq
  calc ∑ i : Fin j.val,
      (if a ⟨i.val, by omega⟩ = 0 then 0
        else Δ ⟨i.val, by omega⟩ j ^ 2 / a ⟨i.val, by omega⟩)
      = ∑ i ∈ Finset.univ.map ⟨fun i : Fin j.val =>
          (⟨i.val, by omega⟩ : Fin n), hemb⟩,
        (if a i = 0 then 0 else Δ i j ^ 2 / a i) := by
        rw [Finset.sum_map]
        simp only [Function.Embedding.coeFn_mk]
    _ ≤ ∑ i : Fin n, (if a i = 0 then 0 else Δ i j ^ 2 / a i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) fun i _ _ => ?_
        by_cases hi : a i = 0
        · rw [if_pos hi]
        · rw [if_neg hi]
          have := lt_of_le_of_ne (ha i) (Ne.symm hi)
          positivity

end NumStability
