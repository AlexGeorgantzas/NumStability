/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreOrthogonalFiber

/-! # Higham Chapter 28: algebra for the second signed incidence

This file records the determinant factorization at an arbitrary external
spectral parameter.  It is the pointwise algebraic identity used when the
signed eigenline incidence transformation is applied a second time.
-/

namespace NumStability

noncomputable section

/-- At an incidence point with distinguished eigenvalue `u`, evaluating the
full shifted determinant at an external parameter `x` contributes the scalar
factor `u - x` times the shifted determinant of the deflated block. -/
theorem det_ginibreIncidenceFull_sub_externalShift
    {m : ℕ} (q : GinibreIncidenceCoordinates m) (x : ℝ) :
    ((show RSqMat (m + 1) from
        ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)) -
        x • (1 : RSqMat (m + 1))).det =
      (ginibreIncidenceEigenvalue q - x) *
        (ginibreIncidenceDeflatedBlock q -
          x • (1 : RSqMat m)).det := by
  have hchar :
      (Matrix.of
        (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q))).charpoly =
        (ginibreIncidenceDeflatedBlock q).charpoly *
          (Polynomial.X -
            Polynomial.C (ginibreIncidenceEigenvalue q)) := by
    calc
      (Matrix.of
        (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q))).charpoly =
          (ginibreCoordinatesMatrix (ginibreIncidenceChart q)).charpoly :=
        ginibreCoordinatesFinMatrix_charpoly (ginibreIncidenceChart q)
      _ = (ginibreIncidenceMatrix q).charpoly := by
        rw [ginibreCoordinatesMatrix_chart]
      _ = _ := ginibreIncidenceMatrix_charpoly_factor q
  rw [det_sub_smul_one_eq_neg_one_pow_mul_charpoly_eval,
    det_sub_smul_one_eq_neg_one_pow_mul_charpoly_eval]
  rw [hchar, Polynomial.eval_mul]
  have hlinear :
      (Polynomial.X - Polynomial.C (ginibreIncidenceEigenvalue q)).eval x =
        x - ginibreIncidenceEigenvalue q := by
    simp
  rw [hlinear]
  have hblock :
      (Matrix.of (ginibreIncidenceDeflatedBlock q)).charpoly =
        (ginibreIncidenceDeflatedBlock q).charpoly := by
    rfl
  rw [hblock]
  rw [pow_succ]
  ring

end

end NumStability
