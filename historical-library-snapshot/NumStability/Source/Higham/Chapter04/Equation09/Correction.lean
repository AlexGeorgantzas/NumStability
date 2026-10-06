import Mathlib.Algebra.BigOperators.Fin
import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import NumStability.Algorithms.Summation.Compensated.Kahan.ErrorBounds
import NumStability.Source.Higham.Chapter04.Equation08.ReturnedSum

namespace NumStability

/-!
# Higham equation (4.9): corrected ordinary returned-Kahan bound

This source module derives the forward-error correction to equation (4.9) from
the source-honest leading-`3u` backward theorem owned by equation (4.8).
-/

/-- Corrected ordinary returned-Kahan forward-error bound corresponding to the
source-honest leading-`3*u` backward-error theorem. -/
theorem fl_kahanSum_forward_error_bound_correctedReturnedMajorant
    (fp : FPModel) (n : Nat) (v : Fin n -> Real)
    (hu64 : fp.u <= 1 / 64)
    (hm : (n : Real) * fp.u ^ 2 <= 1 / 16) :
    |fl_kahanSum fp n v - Finset.univ.sum (fun i : Fin n => v i)| <=
      (3 * fp.u + (14 + 13 * (n : Real)) * fp.u ^ 2 +
        (12 + 13 * (n : Real)) * fp.u ^ 3) *
        Finset.univ.sum (fun i : Fin n => |v i|) := by
  exact
    fl_kahanSum_forward_error_bound_of_backward fp n v
      (fl_kahanSum_backward_error_source_bound_correctedReturnedMajorant
        fp n v hu64 hm)

/-- Corrected terminal corresponding to Higham (4.9) after the bare-model
strength discrepancy above: the actual returned Kahan error has the matching
explicit leading-3 absolute forward bound. -/
theorem highamCh4_equation49_modelStrengthCorrection_bareFPModel
    (fp : FPModel) (n : Nat) (v : Fin n -> Real)
    (hu64 : fp.u <= 1 / 64)
    (hm : (n : Real) * fp.u ^ 2 <= 1 / 16) :
    |fl_kahanSum fp n v - Finset.univ.sum (fun i : Fin n => v i)| <=
      (3 * fp.u + (14 + 13 * (n : Real)) * fp.u ^ 2 +
        (12 + 13 * (n : Real)) * fp.u ^ 3) *
        Finset.univ.sum (fun i : Fin n => |v i|) :=
  fl_kahanSum_forward_error_bound_correctedReturnedMajorant
    fp n v hu64 hm
