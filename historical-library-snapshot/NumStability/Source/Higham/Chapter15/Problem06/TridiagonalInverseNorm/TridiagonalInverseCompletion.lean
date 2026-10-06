import Mathlib.Tactic
import NumStability.Algorithms.LU.TridiagonalCond
import NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.TridiagonalInverse

/-!
# Chapter15 Problem06 TridiagonalInverseNorm TridiagonalInverseCompletion

Canonical destination for material split out of
`NumStability.Algorithms.LU.Higham15Problem15_6Closure` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Higham15Problem15_6

open scoped BigOperators

open NumStability

def finVectorAt {n : ℕ} (v : Fin n → ℝ) (k : ℕ) : ℝ :=
  if h : k < n then v ⟨k, h⟩ else 0

@[simp] theorem finVectorAt_of_lt {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k < n) : finVectorAt v k = v ⟨k, hk⟩ := by
  simp [finVectorAt, hk]

def prefixScanNat (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => prefixScanNat w k + w k

def reverseSuffixScanNat (w : ℕ → ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => reverseSuffixScanNat w n k + w (n - 1 - k)

theorem prefixScanNat_eq_sum (w : ℕ → ℝ) : ∀ k : ℕ,
    prefixScanNat w k = ∑ j ∈ Finset.range k, w j := by
  intro k
  induction k with
  | zero => simp [prefixScanNat]
  | succ k ih =>
      rw [prefixScanNat, Finset.sum_range_succ, ih]

theorem reverseSuffixScanNat_eq_sum (w : ℕ → ℝ) (n : ℕ) : ∀ k : ℕ,
    reverseSuffixScanNat w n k =
      ∑ j ∈ Finset.range k, w (n - 1 - j) := by
  intro k
  induction k with
  | zero => simp [reverseSuffixScanNat]
  | succ k ih =>
      rw [reverseSuffixScanNat, Finset.sum_range_succ, ih]

theorem reverseSuffixScanNat_eq_sum_Ico (w : ℕ → ℝ)
    {n k : ℕ} (hk : k ≤ n) :
    reverseSuffixScanNat w n k =
      ∑ j ∈ Finset.Ico (n - k) n, w j := by
  rw [reverseSuffixScanNat_eq_sum]
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := by omega
    subst k
    simp
  · have hnpos : 0 < n := by omega
    have hadd : n - 1 + 1 = n := by omega
    have href := Finset.sum_Ico_reflect w 0 (m := k) (n := n - 1) (by omega)
    simpa [Nat.Ico_zero_eq_range, hadd] using href

theorem prefix_suffix_scan_split (f g : ℕ → ℝ)
    {n i : ℕ} (hi : i ≤ n) :
    prefixScanNat f i + reverseSuffixScanNat g n (n - i) =
      ∑ k ∈ Finset.range n, if k < i then f k else g k := by
  rw [prefixScanNat_eq_sum]
  have hs := reverseSuffixScanNat_eq_sum_Ico g
    (n := n) (k := n - i) (by omega)
  rw [hs]
  have hlo :
      (∑ k ∈ Finset.range i, f k) =
        ∑ k ∈ Finset.range i, if k < i then f k else g k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [Finset.mem_range.mp hk]
  have hhi :
      (∑ k ∈ Finset.Ico (n - (n - i)) n, g k) =
        ∑ k ∈ Finset.Ico i n, if k < i then f k else g k := by
    have hsub : n - (n - i) = i := by omega
    rw [hsub]
    apply Finset.sum_congr rfl
    intro k hk
    have hik : i ≤ k := (Finset.mem_Ico.mp hk).1
    simp [not_lt.mpr hik]
  rw [hlo, hhi]
  exact Finset.sum_range_add_sum_Ico _ hi

theorem prefixScanNat_const_mul (a : ℝ) (w : ℕ → ℝ) (k : ℕ) :
    prefixScanNat (fun j => a * w j) k = a * prefixScanNat w k := by
  rw [prefixScanNat_eq_sum, prefixScanNat_eq_sum, Finset.mul_sum]

theorem reverseSuffixScanNat_const_mul (a : ℝ) (w : ℕ → ℝ)
    (n k : ℕ) :
    reverseSuffixScanNat (fun j => a * w j) n k =
      a * reverseSuffixScanNat w n k := by
  rw [reverseSuffixScanNat_eq_sum, reverseSuffixScanNat_eq_sum,
    Finset.mul_sum]

noncomputable def problem15_6_lowerWeight {n : ℕ} (T : TridiagData n)
    (d : Fin n → ℝ) (k : ℕ) : ℝ :=
  |finVectorAt (problem15_6_q T) k| * finVectorAt d k

noncomputable def problem15_6_upperWeight {n : ℕ} (T : TridiagData n)
    (d : Fin n → ℝ) (k : ℕ) : ℝ :=
  |finVectorAt (problem15_6_y T) k| * finVectorAt d k

/-- Extensional two-scan formula for `|A⁻¹|d`.

The lower prefix stores `∑_{j<i}|qⱼ|dⱼ`; the reverse upper suffix stores
`∑_{j≥i}|yⱼ|dⱼ`.  Each row is assembled as
`|pᵢ| prefixᵢ + |xᵢ| suffixᵢ`.  The literal stored `Vector.scanl`/`map₂`
producer certified against this formula is in `Higham15Problem15_6Operational`. -/
noncomputable def problem15_6_absInvMul {n : ℕ} (T : TridiagData n)
    (d : Fin n → ℝ) : Fin n → ℝ := fun i =>
  |problem15_6_p T i| *
      prefixScanNat (problem15_6_lowerWeight T d) i.val +
    |problem15_6_x T i| *
      reverseSuffixScanNat (problem15_6_upperWeight T d)
        n (n - i.val)

/-- Infinity norm of the vector produced by the two-scan algorithm. -/
noncomputable def problem15_6_infNorm {n : ℕ} (T : TridiagData n)
    (d : Fin n → ℝ) : ℝ :=
  infNormVec (problem15_6_absInvMul T d)

/-- Scalar arithmetic for one length-`n` two-step factor recurrence.
The first nontrivial entry costs one negation and one division; every later
entry costs two products, one addition, one negation, and one division. -/
def problem15_6_recurrenceScalarOps (n : ℕ) : ℕ :=
  if n < 2 then 0 else 2 + 5 * (n - 2)

/-- Phase-by-phase scalar-arithmetic schedule.  Absolute values and maximum
comparisons are deliberately recorded separately below, following the usual
flop convention. -/
structure Problem15_6OperationSchedule where
  factorRecurrences : ℕ
  residualsAndNormalizations : ℕ
  weightProducts : ℕ
  scanAdds : ℕ
  rowAssembly : ℕ

def problem15_6_operationSchedule (n : ℕ) :
    Problem15_6OperationSchedule where
  factorRecurrences := 4 * problem15_6_recurrenceScalarOps n
  residualsAndNormalizations :=
    if n = 0 then 0 else 2 * n + if n = 1 then 0 else 6
  weightProducts := 2 * n
  scanAdds := 2 * n
  rowAssembly := 3 * n

def problem15_6_scalarOps (n : ℕ) : ℕ :=
  let s := problem15_6_operationSchedule n
  s.factorRecurrences + s.residualsAndNormalizations +
    s.weightProducts + s.scanAdds + s.rowAssembly

/-- Exact absolute-value evaluations: two weight vectors, two row factors,
and one infinity-norm pass. -/
def problem15_6_absEvaluations (n : ℕ) : ℕ := 5 * n

/-- Exact comparisons in the final maximum pass. -/
def problem15_6_maxComparisons (n : ℕ) : ℕ := n - 1

/-- Exact scalar arithmetic count in the source's nontrivial dimensions. -/
theorem problem15_6_scalarOps_exact {n : ℕ} (hn : 2 ≤ n) :
    problem15_6_scalarOps n = 29 * n - 26 := by
  simp [problem15_6_scalarOps, problem15_6_operationSchedule,
    problem15_6_recurrenceScalarOps,
    show ¬n < 2 by omega, show n ≠ 0 by omega, show n ≠ 1 by omega]
  omega

theorem problem15_6_scalarOps_zero :
    problem15_6_scalarOps 0 = 0 := by
  norm_num [problem15_6_scalarOps, problem15_6_operationSchedule,
    problem15_6_recurrenceScalarOps]

theorem problem15_6_scalarOps_one :
    problem15_6_scalarOps 1 = 9 := by
  norm_num [problem15_6_scalarOps, problem15_6_operationSchedule,
    problem15_6_recurrenceScalarOps]

/-- Concrete `O(n)` certificate for the complete producer. -/
theorem problem15_6_scalarOps_linear (n : ℕ) :
    problem15_6_scalarOps n ≤ 29 * n := by
  by_cases hn : 2 ≤ n
  · rw [problem15_6_scalarOps_exact hn]
    omega
  · have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl
    · norm_num [problem15_6_scalarOps_zero]
    · norm_num [problem15_6_scalarOps_one]

end Higham15Problem15_6
end NumStability
