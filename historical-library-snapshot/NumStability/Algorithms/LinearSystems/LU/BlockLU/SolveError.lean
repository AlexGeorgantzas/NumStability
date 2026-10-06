import Mathlib.Logic.Equiv.Fin.Basic
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.FloatingPoint.Model

/-!
# Block LU solve-error foundations

Reusable reblocking lemmas for conventional flattened forward substitution in
block-LU solve-error analysis.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix

/-- Conventional flattened forward substitution, reblocked into uniform
    single-column rows for the subsequent recursive block-back solve. -/
noncomputable def dhsBlockForwardConventionalSolution {m r : ℕ}
    (fp : FPModel)
    (Lhat : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (b : Fin (m * r) → ℝ) :
    Fin m → Matrix (Fin r) (Fin 1) ℝ := fun i a _ =>
  fl_forwardSub fp (m * r) (blockMatrixFlatFin Lhat) b
    (finProdFinEquiv (i, a))

@[simp] theorem dhsBlockForwardConventionalSolution_apply {m r : ℕ}
    (fp : FPModel)
    (Lhat : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (b : Fin (m * r) → ℝ) (i : Fin m) (a : Fin r) (k : Fin 1) :
    dhsBlockForwardConventionalSolution fp Lhat b i a k =
      fl_forwardSub fp (m * r) (blockMatrixFlatFin Lhat) b
        (finProdFinEquiv (i, a)) := rfl

/-- Reflattening the reblocked conventional forward solution recovers the
    original scalar `fl_forwardSub` output exactly. -/
theorem dhsBlockForwardConventionalSolution_flat {m r : ℕ}
    (fp : FPModel)
    (Lhat : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (b : Fin (m * r) → ℝ) :
    blockMatrixRowsFlatFin (dhsBlockForwardConventionalSolution fp Lhat b) =
      (fun i (_k : Fin 1) =>
        fl_forwardSub fp (m * r) (blockMatrixFlatFin Lhat) b i) := by
  ext is k
  let q := finProdFinEquiv.symm is
  have his : finProdFinEquiv q = is := finProdFinEquiv.apply_symm_apply is
  rw [← his]
  rw [blockMatrixRowsFlatFin_apply,
    dhsBlockForwardConventionalSolution_apply]

end NumStability
