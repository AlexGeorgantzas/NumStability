import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.OneNorm.FiniteIndex.Basic
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd Carrier BoydInterface

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydBridges` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- The `n × n` Gram matrix `Aᵀ A` for a literal rectangular real matrix. -/
noncomputable def rectGram {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ i : Fin m, A i j * A i k

/-- Entrywise nonnegativity of `A` implies entrywise nonnegativity of its
Gram matrix. -/
theorem rectGram_nonneg {m n : ℕ} {A : Fin m → Fin n → ℝ}
    (hA : ∀ i j, 0 ≤ A i j) :
    ∀ j k, 0 ≤ rectGram A j k := by
  intro j k
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hA i j) (hA i k)

/-- For a nonnegative matrix in positive domain dimension, irreducibility of
`Aᵀ A` forces every column of `A` to contain a positive entry. -/
theorem exists_pos_in_column_of_rectGram_irreducible {m n : ℕ}
    [Nontrivial (Fin n)] {A : Fin m → Fin n → ℝ}
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ)) :
    ∀ j, ∃ i, 0 < A i j := by
  intro j
  obtain ⟨k, hjk⟩ := hGram.exists_pos j
  change 0 < ∑ i : Fin m, A i j * A i k at hjk
  have hterms : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ A i j * A i k := fun i _ => mul_nonneg (hA i j) (hA i k)
  obtain ⟨i, _hi, hprod⟩ :=
    (Finset.sum_pos_iff_of_nonneg hterms).mp hjk
  refine ⟨i, ?_⟩
  nlinarith [hA i j, hA i k]

/-- A strictly positive input has a strictly positive image in every row that
contains a positive matrix entry. -/
theorem rectMatVec_pos_of_row_entry {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {x : Fin n → ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hx : ∀ j, 0 < x j)
    {i : Fin m} {j : Fin n} (hij : 0 < A i j) :
    0 < ∑ k : Fin n, A i k * x k := by
  apply (Finset.sum_pos_iff_of_nonneg
    (fun k _ => mul_nonneg (hA i k) (le_of_lt (hx k)))).2
  exact ⟨j, Finset.mem_univ j, mul_pos hij (hx j)⟩

/-- If every column of a nonnegative rectangular matrix has a positive entry,
one smooth general-`p` Algorithm 15.1 update maps positive vectors to positive
vectors.  This statement uses the actual `RectPNormPair.general` update, not a
separately postulated nonlinear map. -/
theorem rect_general_xnext_pos_of_pos_columns {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hcol : ∀ j, ∃ i, 0 < A i j)
    (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    ∀ j, 0 < (RectPNormPair.general hn hpq A).xnext x j := by
  let P := RectPNormPair.general hn hpq A
  have hypos_at_col : ∀ j : Fin n,
      ∃ i : Fin m, 0 < P.yof x i ∧ 0 < A i j := by
    intro j
    obtain ⟨i, hij⟩ := hcol j
    refine ⟨i, ?_, hij⟩
    change 0 < ∑ k : Fin n, A i k * x k
    exact rectMatVec_pos_of_row_entry hA hx hij
  have hypos_nonempty : P.yof x ≠ 0 := by
    obtain ⟨i, hi, _⟩ := hypos_at_col ⟨0, hn⟩
    intro hzero
    have hz := congrFun hzero i
    exact (ne_of_gt hi) (by simpa using hz)
  have hdualpos : ∀ i : Fin m, 0 < P.yof x i →
      0 < realLpDual hpq (P.yof x) i := by
    intro i hi
    rw [realLpDual_eq_realLpGradient hpq (P.yof x) hypos_nonempty]
    exact realLpGradient_pos_of_pos_coord hpq.lt (P.yof x)
      hypos_nonempty i hi
  have hynonneg : ∀ i : Fin m, 0 ≤ P.yof x i := by
    intro i
    change 0 ≤ ∑ k : Fin n, A i k * x k
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (hA i k) (le_of_lt (hx k))
  have hdualnonneg : ∀ i : Fin m, 0 ≤ realLpDual hpq (P.yof x) i :=
    realLpDual_nonneg_of_nonneg hpq (P.yof x) hypos_nonempty hynonneg
  have hzpos : ∀ j : Fin n, 0 < P.zof x j := by
    intro j
    obtain ⟨i, hyi, haij⟩ := hypos_at_col j
    change 0 < ∑ r : Fin m, A r j * realLpDual hpq (P.yof x) r
    apply (Finset.sum_pos_iff_of_nonneg (fun r _ =>
      mul_nonneg (hA r j) (hdualnonneg r))).2
    exact ⟨i, Finset.mem_univ i, mul_pos haij (hdualpos i hyi)⟩
  change ∀ j, 0 < realLpDualUnit hn hpq.symm (P.zof x) j
  exact realLpDualUnit_pos_of_pos hn hpq.symm (P.zof x) hzpos

/-- Source-shaped positivity preservation under the printed hypotheses
`A ≥ 0` and irreducible `Aᵀ A` (for nontrivial domain dimension). -/
theorem rect_general_xnext_pos_of_nonneg_gram_irreducible {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    ∀ j, 0 < (RectPNormPair.general hn hpq A).xnext x j :=
  rect_general_xnext_pos_of_pos_columns hn hpq A hA
    (exists_pos_in_column_of_rectGram_irreducible hA hGram) x hx

/-- Every iterate of the actual rectangular smooth Algorithm 15.1 trace stays
strictly positive under Boyd's printed matrix hypotheses. -/
theorem rect_general_xseq_pos_of_nonneg_gram_irreducible {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    (x0 : Fin n → ℝ) (hx0 : ∀ j, 0 < x0 j) :
    ∀ k j, 0 < (RectPNormPair.general hn hpq A).xseq x0 k j := by
  intro k
  induction k with
  | zero => simpa [RectPNormPair.xseq] using hx0
  | succ k ih =>
      simpa [RectPNormPair.xseq] using
        rect_general_xnext_pos_of_nonneg_gram_irreducible
          hn hpq A hA hGram
          ((RectPNormPair.general hn hpq A).xseq x0 k) ih

/-- The nonnegative `p`-unit sphere used as the compact state space for
Boyd's global iteration. -/
noncomputable def boydNonnegativeUnitCarrier {n : ℕ} (p : ℝ) :
    Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ realVecLpNorm p x = 1}

theorem isClosed_boydNonnegativeUnitCarrier {n : ℕ} {p : ℝ}
    (hp : 0 < p) : IsClosed (boydNonnegativeUnitCarrier (n := n) p) := by
  have hnonneg : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun i =>
      isClosed_le continuous_const (continuous_apply i)
  have hunit : IsClosed {x : Fin n → ℝ | realVecLpNorm p x = 1} :=
    isClosed_eq (continuous_realVecLpNorm hp) continuous_const
  simpa [boydNonnegativeUnitCarrier, Set.setOf_and] using hnonneg.inter hunit

theorem isCompact_boydNonnegativeUnitCarrier {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    IsCompact (boydNonnegativeUnitCarrier (n := n) p) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · exact isClosed_boydNonnegativeUnitCarrier hpq.pos
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨1, ?_⟩
    intro x hx
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hholder := realVecLpNorm_holder hpq (basisVec i) x
    have hbasis : realVecLpNorm q (basisVec i) = 1 :=
      realVecLpNorm_basisVec (le_of_lt hpq.symm.lt) i
    have hcoord : (∑ j : Fin n, basisVec i j * x j) = x i := by
      simp [basisVec]
    simpa [hcoord, hbasis, hx.2, Real.norm_eq_abs] using hholder

theorem boydCarrier_ne_zero {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    {x : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p) : x ≠ 0 := by
  intro hzero
  have hunit := hx.2
  rw [hzero, realVecLpNorm_zero hp] at hunit
  norm_num at hunit

theorem exists_pos_coord_of_mem_boydCarrier {n : ℕ} {p : ℝ}
    (hp : 1 ≤ p) {x : Fin n → ℝ}
    (hx : x ∈ boydNonnegativeUnitCarrier p) : ∃ j, 0 < x j := by
  have hxne := boydCarrier_ne_zero hp hx
  by_contra h
  push_neg at h
  apply hxne
  funext j
  exact le_antisymm (h j) (hx.1 j)

theorem rect_general_yof_ne_zero_of_mem_boydCarrier {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    {x : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p) :
    (RectPNormPair.general hn hpq A).yof x ≠ 0 := by
  obtain ⟨j, hxj⟩ := exists_pos_coord_of_mem_boydCarrier
    (le_of_lt hpq.lt) hx
  obtain ⟨i, haij⟩ :=
    exists_pos_in_column_of_rectGram_irreducible hA hGram j
  have hyi : 0 < (RectPNormPair.general hn hpq A).yof x i := by
    change 0 < ∑ k : Fin n, A i k * x k
    apply (Finset.sum_pos_iff_of_nonneg (fun k _ =>
      mul_nonneg (hA i k) (hx.1 k))).2
    exact ⟨j, Finset.mem_univ j, mul_pos haij hxj⟩
  intro hyzero
  have hi := congrFun hyzero i
  exact (ne_of_gt hyi) (by simpa using hi)

theorem rect_general_zof_nonneg_of_mem_boydCarrier {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    {x : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p) :
    ∀ j, 0 ≤ (RectPNormPair.general hn hpq A).zof x j := by
  have hyne := rect_general_yof_ne_zero_of_mem_boydCarrier
    hn hpq A hA hGram hx
  have hynonneg : ∀ i, 0 ≤ (RectPNormPair.general hn hpq A).yof x i := by
    intro i
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hx.1 j)
  have hdual := realLpDual_nonneg_of_nonneg hpq _ hyne hynonneg
  intro j
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hA i j) (hdual i)

theorem boydNonnegativeUnitCarrier_nonempty {n : ℕ} (hn : 0 < n)
    {p : ℝ} (hp : 1 ≤ p) :
    (boydNonnegativeUnitCarrier (n := n) p).Nonempty := by
  let i0 : Fin n := ⟨0, hn⟩
  refine ⟨basisVec i0, ?_, realVecLpNorm_basisVec hp i0⟩
  intro i
  by_cases hi : i = i0
  · simp [basisVec, hi]
  · simp [basisVec, hi]

theorem rectGram_mulVec_eq_transpose_yof {m n : ℕ}
    (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) (j : Fin n) :
    Matrix.mulVec
        (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ) x j =
      ∑ i : Fin m, A i j * (RectPNormPair.general hn hpq A).yof x i := by
  change (∑ k : Fin n, (∑ i : Fin m, A i j * A i k) * x k) =
    ∑ i : Fin m, A i j * (∑ k : Fin n, A i k * x k)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

end Ch15
end NumStability
