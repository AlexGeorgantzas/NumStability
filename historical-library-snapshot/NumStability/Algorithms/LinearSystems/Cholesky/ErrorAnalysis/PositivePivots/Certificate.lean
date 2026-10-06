import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskyDemmel
import NumStability.Algorithms.Cholesky.CholeskyFl
import NumStability.Algorithms.Cholesky.CholeskyNonsym
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates
import NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanMatrix
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.StageEmbedding.InteriorMass
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Certificate

Canonical destination for 1 declaration(s) relocated from
`NumStability.Algorithms.HighamChapter10` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- **Theorem 10.7 at the source-shaped threshold, certified form**: all
    rounded pivots are positive at `λ > ε + 2γ_{n+1}` given ONLY
    run-level normwise certificates — one quadratic-form certificate on
    the scaled full Gram defect and one scaled column-norm certificate
    per column — the per-stage mass hypotheses being discharged by
    zero-pad restriction. -/
theorem fl_cholesky_pivots_pos_sharp_certified (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (lam ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hfloor : ∀ j : Fin n, ∀ y : Fin j.val → ℝ,
      lam * ((∑ i : Fin j.val,
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j) ≤
        (∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j)
    (hcertI : ∀ z : Fin n → ℝ,
      |∑ i : Fin n, ∑ l : Fin n, z i *
        (((∑ p : Fin n, fl_cholesky fp n A p i *
            fl_cholesky fp n A p l) - A i l) /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) * z l| ≤
      ε * ∑ i : Fin n, z i ^ 2)
    (hcertB : ∀ j : Fin n, ∑ i : Fin n,
      (if A i i = 0 then 0 else
        ((∑ p : Fin n, fl_cholesky fp n A p i *
            fl_cholesky fp n A p j) - A i j) ^ 2 / A i i) ≤
      ε ^ 2 * ∑ p ∈ Finset.univ.filter
        (fun p : Fin n => p.val < j.val),
        fl_cholesky fp n A p j ^ 2)
    (hlam2ε : 2 * ε ≤ lam)
    (hthresh : ε + 2 * gamma fp (n + 1) < lam) :
    ∀ j : Fin n, 0 < fl_cholPivot fp n A j := by
  set Δ : Fin n → Fin n → ℝ := fun i l =>
    (∑ p : Fin n, fl_cholesky fp n A p i * fl_cholesky fp n A p l) -
      A i l with hΔ
  have hnzI : ∀ i l : Fin n, A i i = 0 ∨ A l l = 0 → Δ i l = 0 :=
    fun i l h => h.elim
      (fun h0 => absurd h0 (hAdiag i).ne')
      (fun h0 => absurd h0 (hAdiag l).ne')
  have hnzB : ∀ i l : Fin n, A i i = 0 → Δ i l = 0 :=
    fun i l h0 => absurd h0 (hAdiag i).ne'
  refine fl_cholesky_pivots_pos_sharp fp A hAdiag hn1 hγ1 lam ε
    hε0 hε1 hfloor ?_ ?_ hlam2ε hthresh
  · -- interior masses from the single full certificate
    intro j y
    have h := stage_interior_mass_from_full Δ (fun i => A i i)
      (fun i => (hAdiag i).le) ε hcertI hnzI j.val j.isLt.le y
    have hrw : ∀ i l : Fin j.val,
        Δ ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ =
        (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
          A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ := by
      intro i l
      show (∑ p : Fin n, _ * _) - _ = _
      rw [gram_sum_stage_trunc fp A j ⟨i.val, by omega⟩
        ⟨l.val, by omega⟩ i.isLt]
    calc |∑ i : Fin j.val, ∑ l : Fin j.val, y i *
          ((∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
            A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * y l|
        = |∑ i : Fin j.val, ∑ l : Fin j.val, y i *
            Δ ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l| := by
          congr 1
          exact Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun l _ => by rw [hrw i l]
      _ ≤ ε * ∑ i : Fin j.val,
            A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2 := h
  · -- border masses from the column certificates
    intro j y
    have h := stage_border_mass_from_full Δ (fun i => A i i)
      (fun i => (hAdiag i).le) ε hε0
      (fun w => ∑ p ∈ Finset.univ.filter
        (fun p : Fin n => p.val < w.val),
        fl_cholesky fp n A p w ^ 2)
      (fun w => Finset.sum_nonneg fun p _ => sq_nonneg _)
      hnzB hcertB j y
    have hrwB : ∀ i : Fin j.val,
        Δ ⟨i.val, by omega⟩ j =
        (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
          A ⟨i.val, by omega⟩ j := by
      intro i
      show (∑ p : Fin n, _ * _) - _ = _
      rw [gram_sum_stage_trunc fp A j ⟨i.val, by omega⟩ j i.isLt]
    have hrwT : (∑ p ∈ Finset.univ.filter
        (fun p : Fin n => p.val < j.val),
        fl_cholesky fp n A p j ^ 2) =
        ∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 :=
      (sum_fin_eq_sum_filter_lt' j.isLt.le
        (fun p => fl_cholesky fp n A p j ^ 2)).symm
    calc |2 * ∑ i : Fin j.val, y i *
          ((∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
            fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
            A ⟨i.val, by omega⟩ j)|
        = |2 * ∑ i : Fin j.val, y i * Δ ⟨i.val, by omega⟩ j| := by
          congr 2
          exact Finset.sum_congr rfl fun i _ => by rw [hrwB i]
      _ ≤ ε * ((∑ p ∈ Finset.univ.filter
            (fun p : Fin n => p.val < j.val),
            fl_cholesky fp n A p j ^ 2) +
          ∑ i : Fin j.val,
            A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) := h
      _ = ε * ((∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) +
          ∑ i : Fin j.val,
            A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) := by
          rw [hrwT]

end NumStability
