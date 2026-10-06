import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter07.Corollary06.LinearSystemsConditioning.Results
import NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEFinalDivisionClosure
import NumStability.Source.Higham.Chapter14.Algorithm04.FinalDivisionStage.FinalizedErrorFamilies
import NumStability.Source.Higham.Chapter14.Algorithm04.Pivoting.GaussJordanPivoting
import NumStability.Source.Higham.Chapter14.Corollary06.SPD.Closure
import NumStability.Source.Higham.Chapter14.Corollary06.SPD.GaussJordanSPDCorollary
import NumStability.Source.Higham.Chapter14.Corollary06.SPD.UniformInverseBridge
import NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.WeakFamily
import NumStability.Source.Higham.Chapter14.Corollary07.PrintedTraceFamilies.ResidualAndForwardEndpoints

/-!
# UniformInverseRegularity

Canonical destination for the Chapter14.Corollary06 declarations relocated from the
historical path `NumStability.Algorithms.Ch14Cor146UniformInverseBridge` during wave R08.
Holds 2 declaration(s): 2 public.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- The inverse regularity required by the Corollary 14.6 family endpoint is
not an independent conclusion-shaped hypothesis.  It follows from:

* the actual finalized GJE family's LU backward certificate;
* the positive-pivot symmetric factor relation, which identifies the
  perturbed matrix with `R_hat^T R_hat`;
* a two-sided inverse of the scaled computed upper factor `R_hat`;
* a source inverse certificate.

In particular, both the repository `nonsingInv` identity for the perturbed
matrix and the entrywise `O(u)` perturbation are proved here. -/
theorem ch14ext_cor146_uniformInverseRegularity_of_finalizedGJE
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14GJEFinalizedFamily I l n A b)
    (R_inv : I -> Fin n -> Fin n -> Real)
    (hSPD : IsSymPosDef n A)
    (hpiv : forall t i, 0 < (F.initial t).matrix i i)
    (hsym : forall t i j,
      (F.initial t).matrix i j =
        (F.initial t).matrix i i * F.L_hat t j i)
    (hRinv : forall t,
      IsInverse n (ch14ext_cor146_scaledUpper n (F.initial t).matrix)
        (R_inv t))
    (hAinv : IsInverse n A A_inv) :
    Ch14Cor146UniformInverseRegularity l n A A_inv F.model F.L_hat
      (fun t => (F.initial t).matrix) := by
  let U : I -> Fin n -> Fin n -> Real := fun t => (F.initial t).matrix
  let R : I -> Fin n -> Fin n -> Real := fun t =>
    ch14ext_cor146_scaledUpper n (F.initial t).matrix
  have hGram : forall t,
      ch14ext_cor146ClosureAhat n A F.L_hat U t =
        matMul n (fun i j => R t j i) (R t) := by
    intro t
    have hstruct := ch14ext_cor146_positivePivot_cholesky_backward_error
      n (F.model t) A (F.L_hat t) (U t) hSPD
      (F.lu_certificate t) (hpiv t) (hsym t)
    funext i j
    simpa only [ch14ext_cor146ClosureAhat, U, R] using hstruct.2.1 i j
  have hNonsing : forall t,
      nonsingInv n (ch14ext_cor146ClosureAhat n A F.L_hat U t) =
        matMul n (R_inv t) (fun i j => R_inv t j i) := by
    intro t
    rw [hGram t]
    simpa [rectMatMul, finiteTranspose, matMul] using
      (nonsingInv_rectMatMul_transpose_self_of_IsInverse (hRinv t))
  have hPerturbedInv : forall t,
      IsInverse n (ch14ext_cor146ClosureAhat n A F.L_hat U t)
        (nonsingInv n (ch14ext_cor146ClosureAhat n A F.L_hat U t)) := by
    intro t
    have hNonsingGram := hNonsing t
    rw [hGram t] at hNonsingGram
    rw [hGram t, hNonsingGram]
    simpa [ch7CholeskyInverseGram, matTranspose] using
      (corollary7_6_cholesky_inverse_gram_isInverse
        (R t) (R_inv t) (hRinv t))
  have hPerturbation : forall i j,
      (fun t => ch14ext_cor146ClosureAhat n A F.L_hat U t i j - A i j)
        =O[l] (fun t => (F.model t).u) := by
    have hres := ch14ext_luBackward_productResidual_isBigO
      F.model A F.L_hat U F.unit_tendsto_zero F.lu_certificate F.valid_n
        F.L_hat_isBigO_one F.U_hat_isBigO_one
    intro i j
    convert hres i j using 1
    funext t
    simp only [ch14ext_cor146ClosureAhat,
      ch14ext_cor146_symmetricGEDelta, U]
    ring
  have hAhat_tendsto : Tendsto
      (fun t => ch14ext_cor146ClosureAhat n A F.L_hat U t) l
      (nhds A) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have hd := (hPerturbation i j).trans_tendsto F.unit_tendsto_zero
    simpa only [sub_add_cancel, zero_add] using hd.add_const (A i j)
  have hPerturbedInv_one : Ch14Cor146ClosureMatrixFamilyIsBigOOne l
      (fun t =>
        nonsingInv n (ch14ext_cor146ClosureAhat n A F.L_hat U t)) :=
    ch14ext_nonsingInv_family_isBigOOne_of_tendsto hAhat_tendsto
      (isSymPosDef_det_ne_zero A hSPD)
  exact
    { source_inverse := hAinv
      perturbed_inverse := hPerturbedInv
      perturbed_inverse_family_isBigO_one := hPerturbedInv_one
      perturbation_family_isBigO_u := hPerturbation }

/-- Build a `Ch14Cor146FinalizedRunFamily` without accepting its bundled
`uniform_inverse` field.  The field is derived by
`ch14ext_cor146_uniformInverseRegularity_of_finalizedGJE` from the actual
finalized GJE/LU run.  The inverse of the scaled computed upper factor is
itself the canonical inverse, justified here by triangularity and the
strictly positive computed pivots. -/
noncomputable def ch14ext_cor146FinalizedRunFamily_of_computedFactors
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real}
    {b x : Fin n -> Real}
    (gje : Ch14GJEFinalizedFamily I l n A b)
    (spd : IsSymPosDef n A)
    (exact_solution_nonzero : 0 < vecNorm2 x)
    (computed_pivots_pos : forall t i, 0 < (gje.initial t).matrix i i)
    (symmetric_factor_relation : forall t i j,
      (gje.initial t).matrix i j =
        (gje.initial t).matrix i i * gje.L_hat t j i)
    (gamma_small : forall t, (n : Real) * gamma (gje.model t) n < 1)
    (source_inverse : IsInverse n A A_inv)
    (exact_solution : forall i, matMulVec n A x i = b i) :
    Ch14Cor146FinalizedRunFamily I l n A A_inv b x := by
  let R : I -> Fin n -> Fin n -> Real := fun t =>
    ch14ext_cor146_scaledUpper n (gje.initial t).matrix
  let R_inv : I -> Fin n -> Fin n -> Real := fun t => nonsingInv n (R t)
  have hRupper : forall t i j, j.val < i.val -> R t i j = 0 := by
    intro t i j hji
    simp [R, ch14ext_cor146_scaledUpper,
      (gje.lu_certificate t).U_lower_zero i j hji]
  have hRdiag : forall t i, R t i i ≠ 0 := by
    intro t i
    apply div_ne_zero
    · exact ne_of_gt (computed_pivots_pos t i)
    · exact ne_of_gt (Real.sqrt_pos.2 (computed_pivots_pos t i))
  have hRinv : forall t, IsInverse n (R t) (R_inv t) := by
    intro t
    exact isInverse_nonsingInv_of_det_ne_zero n (R t)
      (det_ne_zero_of_upper_triangular_diag_ne_zero n (R t)
        (hRupper t) (hRdiag t))
  refine {
  gje := gje
  R_inv := R_inv
  spd := spd
  exact_solution_nonzero := exact_solution_nonzero
  computed_pivots_pos := computed_pivots_pos
  symmetric_factor_relation := symmetric_factor_relation
  scaled_upper_inverse := by
    intro t
    simpa only [R] using hRinv t
  gamma_small := gamma_small
  exact_solution := exact_solution
  uniform_inverse :=
    ch14ext_cor146_uniformInverseRegularity_of_finalizedGJE gje R_inv spd
      computed_pivots_pos symmetric_factor_relation (by
        intro t
        simpa only [R] using hRinv t) source_inverse
  }

end Ch14Ext
end NumStability
