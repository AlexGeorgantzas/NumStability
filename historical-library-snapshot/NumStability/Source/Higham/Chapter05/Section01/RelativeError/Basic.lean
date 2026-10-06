import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.PolynomialEvaluation.RootProduct
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Chapter05 Section01 RelativeError Basic

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

lemma relErrorCounter_one_add
    (fp : FPModel) {δ : ℝ} (hδ : |δ| ≤ fp.u) :
    relErrorCounter fp 1 (1 + δ) := by
  refine ⟨fun _ => δ, fun _ => false, ?_, ?_⟩
  · intro _i
    exact hδ
  · simp

lemma relErrorCounter_one (fp : FPModel) :
    relErrorCounter fp 0 (1 : ℝ) := by
  refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · simp

/-- Root-product evaluation has exactly two relative-error factors per root:
one for forming `x - x_i` and one for multiplying it into the accumulator. -/
theorem fl_rootProductEvalFrom_exists_relErrorCounter
    (fp : FPModel) (x : ℝ) :
    ∀ (roots : List ℝ) (acc : ℝ),
      ∃ c : ℝ,
        relErrorCounter fp (2 * roots.length) c ∧
          fl_rootProductEvalFrom fp x roots acc =
            rootProductEvalFrom x roots acc * c := by
  intro roots
  induction roots with
  | nil =>
      intro acc
      refine ⟨1, ?_, ?_⟩
      · simpa using relErrorCounter_one fp
      · simp [fl_rootProductEvalFrom, rootProductEvalFrom]
  | cons r roots ih =>
      intro acc
      obtain ⟨δsub, hδsub, hsub⟩ := fp.model_sub x r
      obtain ⟨δmul, hδmul, hmul⟩ :=
        fp.model_mul acc (fp.fl_sub x r)
      let cLocal : ℝ := (1 + δsub) * (1 + δmul)
      have hfirst :
          fp.fl_mul acc (fp.fl_sub x r) =
            acc * (x - r) * cLocal := by
        simp [cLocal]
        rw [hmul, hsub]
        ring
      obtain ⟨cRest, hcRest, hrest⟩ :=
        ih (fp.fl_mul acc (fp.fl_sub x r))
      have hcLocal : relErrorCounter fp 2 cLocal := by
        have hsubCounter := relErrorCounter_one_add fp hδsub
        have hmulCounter := relErrorCounter_one_add fp hδmul
        simpa [cLocal, Nat.add_comm] using
          relErrorCounter_mul fp 1 1 (1 + δsub) (1 + δmul)
            hsubCounter hmulCounter
      refine ⟨cLocal * cRest, ?_, ?_⟩
      · have hcounter :=
          relErrorCounter_mul fp 2 (2 * roots.length)
            cLocal cRest hcLocal hcRest
        simpa [List.length_cons, Nat.mul_add, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc] using hcounter
      · simp [fl_rootProductEvalFrom, rootProductEvalFrom]
        rw [hrest, hfirst]
        rw [rootProductEvalFrom_smul x roots (acc * (x - r)) cLocal]
        ring

theorem fl_rootProductEvalFrom_forward_error_bound
    (fp : FPModel) (x : ℝ) (roots : List ℝ) (acc : ℝ)
    (hγ : gammaValid fp (2 * roots.length)) :
    |fl_rootProductEvalFrom fp x roots acc -
        rootProductEvalFrom x roots acc| ≤
      gamma fp (2 * roots.length) *
        |rootProductEvalFrom x roots acc| := by
  obtain ⟨c, hc, hfl⟩ :=
    fl_rootProductEvalFrom_exists_relErrorCounter fp x roots acc
  have hcγ := relErrorCounter_abs_sub_one_le_gamma
    fp (2 * roots.length) c hc hγ
  rw [hfl]
  calc
    |rootProductEvalFrom x roots acc * c -
        rootProductEvalFrom x roots acc|
        = |rootProductEvalFrom x roots acc| * |c - 1| := by
          have h :
              rootProductEvalFrom x roots acc * c -
                  rootProductEvalFrom x roots acc =
                rootProductEvalFrom x roots acc * (c - 1) := by
            ring
          rw [h, abs_mul]
    _ ≤ |rootProductEvalFrom x roots acc| *
          gamma fp (2 * roots.length) :=
        mul_le_mul_of_nonneg_left hcγ (abs_nonneg _)
    _ = gamma fp (2 * roots.length) *
          |rootProductEvalFrom x roots acc| := by ring

theorem fl_rootProductEval_forward_error_bound
    (fp : FPModel) (aLeading x : ℝ) (roots : List ℝ)
    (hγ : gammaValid fp (2 * roots.length)) :
    |fl_rootProductEval fp aLeading x roots -
        rootProductEval aLeading x roots| ≤
      gamma fp (2 * roots.length) *
        |rootProductEval aLeading x roots| := by
  simpa [fl_rootProductEval, rootProductEval] using
    fl_rootProductEvalFrom_forward_error_bound fp x roots aLeading hγ

end NumStability
