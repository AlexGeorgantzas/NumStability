import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Source.Higham.Chapter09.DoolittleClosure
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivot

/-!
# Chapter09 Theorem15 Barrlund Basic

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapters1To9SourceClosure` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators
open scoped Topology
open scoped Matrix.Norms.Operator

namespace NumStability

/-- Higham, Theorem 9.15 / equation (9.27), with the audited target-critical
`min` premise discharged by Barrlund's two resolvent arguments.

The extra inverse witnesses are structural: they certify the inverses of the
two perturbed triangular factors used in the two mirrored resolvent proofs.
No estimate on either unknown factor perturbation is assumed. -/
theorem higham9_15_barrlund_normwise_factor_bounds_without_min_premise
    {n : ℕ}
    (A L U ΔA ΔL ΔU Linv Uinv LΔLinv UΔUinv :
      Matrix (Fin n) (Fin n) ℝ)
    (hLU : L * U = A)
    (hPert : (L + ΔL) * (U + ΔU) = A + ΔA)
    (hΔL_strict : ∀ i j : Fin n, i.val ≤ j.val → ΔL i j = 0)
    (hΔU_upper : ∀ i j : Fin n, j.val < i.val → ΔU i j = 0)
    (hLinv_lower : ∀ i j : Fin n, i.val < j.val → Linv i j = 0)
    (hUinv_upper : ∀ i j : Fin n, j.val < i.val → Uinv i j = 0)
    (hLΔLinv_lower : ∀ i j : Fin n, i.val < j.val → LΔLinv i j = 0)
    (hUΔUinv_upper : ∀ i j : Fin n, j.val < i.val → UΔUinv i j = 0)
    (hLinvL : Linv * L = 1)
    (hLLinv : L * Linv = 1)
    (hUinvU : Uinv * U = 1)
    (hUΔUinvR : (U + ΔU) * UΔUinv = 1)
    (hLΔLinvL : LΔLinv * (L + ΔL) = 1)
    (hGlt : opNorm2 (Linv * ΔA * Uinv) < 1) :
    frobNormRect ΔL ≤
        opNorm2 L * frobNormRect (Linv * ΔA * Uinv) /
          (1 - opNorm2 (Linv * ΔA * Uinv)) ∧
      frobNormRect ΔU ≤
        frobNormRect (Linv * ΔA * Uinv) * opNorm2 U /
          (1 - opNorm2 (Linv * ΔA * Uinv)) := by
  let G : Matrix (Fin n) (Fin n) ℝ := Linv * ΔA * Uinv
  have hLrect : rectOpNorm2Le L (opNorm2 L) :=
    opNorm2Le_to_rectOpNorm2Le (opNorm2Le_opNorm2 L)
  have hGrect : rectOpNorm2Le G (opNorm2 G) :=
    opNorm2Le_to_rectOpNorm2Le (opNorm2Le_opNorm2 G)
  have hUt : opNorm2Le (matTranspose U) (opNorm2 U) :=
    opNorm2Le_transpose U (opNorm2_nonneg U) (opNorm2Le_opNorm2 U)
  have hUrect : rectOpNorm2Le (finiteTranspose U) (opNorm2 U) := by
    simpa [finiteTranspose, matTranspose] using
      opNorm2Le_to_rectOpNorm2Le hUt
  have hGt : opNorm2Le (matTranspose G) (opNorm2 G) :=
    opNorm2Le_transpose G (opNorm2_nonneg G) (opNorm2Le_opNorm2 G)
  have hGrectT : rectOpNorm2Le (finiteTranspose G) (opNorm2 G) := by
    simpa [finiteTranspose, matTranspose] using
      opNorm2Le_to_rectOpNorm2Le hGt
  constructor
  · simpa [G] using
      higham9_15_barrlund_deltaL_bound
        A L U ΔA ΔL ΔU Linv Uinv UΔUinv hLU hPert
        hΔL_strict hΔU_upper hLinv_lower hUΔUinv_upper
        hLinvL hLLinv hUinvU hUΔUinvR
        (opNorm2_nonneg L) (opNorm2_nonneg G) (by simpa [G] using hGlt)
        hLrect hGrect
  · simpa [G] using
      higham9_15_barrlund_deltaU_bound
        A L U ΔA ΔL ΔU Linv Uinv LΔLinv hLU hPert
        hΔL_strict hΔU_upper hUinv_upper hLΔLinv_lower
        hLLinv hUinvU hLΔLinvL
        (opNorm2_nonneg U) (opNorm2_nonneg G) (by simpa [G] using hGlt)
        hUrect hGrectT

/-- Source-normalized form of the preceding theorem.  This is the printed
Theorem 9.15 maximum-ratio conclusion with `‖G‖₂` and `‖G‖F`, and it contains
no hypothesis equivalent to the missing conclusion. -/
theorem higham9_15_barrlund_normwise_source_ratio_without_min_premise
    {n : ℕ} [Nonempty (Fin n)]
    (A L U ΔA ΔL ΔU Linv Uinv LΔLinv UΔUinv :
      Matrix (Fin n) (Fin n) ℝ)
    (hLU : L * U = A)
    (hPert : (L + ΔL) * (U + ΔU) = A + ΔA)
    (hΔL_strict : ∀ i j : Fin n, i.val ≤ j.val → ΔL i j = 0)
    (hΔU_upper : ∀ i j : Fin n, j.val < i.val → ΔU i j = 0)
    (hLinv_lower : ∀ i j : Fin n, i.val < j.val → Linv i j = 0)
    (hUinv_upper : ∀ i j : Fin n, j.val < i.val → Uinv i j = 0)
    (hLΔLinv_lower : ∀ i j : Fin n, i.val < j.val → LΔLinv i j = 0)
    (hUΔUinv_upper : ∀ i j : Fin n, j.val < i.val → UΔUinv i j = 0)
    (hLinvL : Linv * L = 1)
    (hLLinv : L * Linv = 1)
    (hUinvU : Uinv * U = 1)
    (hUΔUinvR : (U + ΔU) * UΔUinv = 1)
    (hLΔLinvL : LΔLinv * (L + ΔL) = 1)
    (hGlt : opNorm2 (Linv * ΔA * Uinv) < 1) :
    max (frobNormRect ΔL / opNorm2 L)
        (frobNormRect ΔU / opNorm2 U) ≤
      frobNormRect (Linv * ΔA * Uinv) /
        (1 - opNorm2 (Linv * ΔA * Uinv)) := by
  have hb :=
    higham9_15_barrlund_normwise_factor_bounds_without_min_premise
      A L U ΔA ΔL ΔU Linv Uinv LΔLinv UΔUinv hLU hPert
      hΔL_strict hΔU_upper hLinv_lower hUinv_upper
      hLΔLinv_lower hUΔUinv_upper hLinvL hLLinv hUinvU
      hUΔUinvR hLΔLinvL hGlt
  have hLrect : rectMatMul L Linv = idMatrix n := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hLLinv
    simpa [rectMatMul, Matrix.mul_apply, idMatrix] using hij
  have hUrect : rectMatMul Uinv U = idMatrix n := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hUinvU
    simpa [rectMatMul, Matrix.mul_apply, idMatrix] using hij
  have hLpos : 0 < opNorm2 L :=
    higham9_15_opNorm2_pos_of_rectMatMul_right_inverse L Linv hLrect
  have hUpos : 0 < opNorm2 U :=
    higham9_15_opNorm2_pos_of_rectMatMul_left_inverse U Uinv hUrect
  apply max_le
  · calc
      frobNormRect ΔL / opNorm2 L ≤
          (opNorm2 L * frobNormRect (Linv * ΔA * Uinv) /
            (1 - opNorm2 (Linv * ΔA * Uinv))) / opNorm2 L :=
        div_le_div_of_nonneg_right hb.1 (le_of_lt hLpos)
      _ = frobNormRect (Linv * ΔA * Uinv) /
          (1 - opNorm2 (Linv * ΔA * Uinv)) := by
        field_simp [ne_of_gt hLpos]
  · calc
      frobNormRect ΔU / opNorm2 U ≤
          (frobNormRect (Linv * ΔA * Uinv) * opNorm2 U /
            (1 - opNorm2 (Linv * ΔA * Uinv))) / opNorm2 U :=
        div_le_div_of_nonneg_right hb.2 (le_of_lt hUpos)
      _ = frobNormRect (Linv * ΔA * Uinv) /
          (1 - opNorm2 (Linv * ΔA * Uinv)) := by
        field_simp [ne_of_gt hUpos]

end NumStability
