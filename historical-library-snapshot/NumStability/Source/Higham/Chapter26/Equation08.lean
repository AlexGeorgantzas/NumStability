/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic

namespace NumStability

/-! # Higham Chapter 26, Equation 26.8

A precise finite-dimensional Fréchet-derivative interpretation of the linearized forward-error formula, plus affine exactness. This records a mathematically explicit interpretation of the terse printed formula; it does not supply hypotheses absent from the source.
-/

/-! ## Linearized forward error (26.8) -/

/-- The coordinate form of the derivative contribution in (26.8).  The
coefficient at coordinate `k` is the derivative applied to the `k`th unit
vector, and `delta k` is that elementary operation's local rounding error. -/
noncomputable def linearizedForwardError26_8 {N : Nat}
    (derivative : (Fin N → ℝ) →L[ℝ] ℝ)
    (delta : Fin N -> Real) : Real :=
  Finset.univ.sum (fun k => derivative (Pi.single k 1) * delta k)

/-- A linear functional on a finite real coordinate space is exactly the sum
of its coordinate derivatives. -/
theorem linearizedForwardError26_8_eq {N : Nat}
    (derivative : (Fin N → ℝ) →L[ℝ] ℝ)
    (delta : Fin N -> Real) :
    linearizedForwardError26_8 derivative delta = derivative delta := by
  classical
  have hdecomp : delta =
      Finset.univ.sum (fun k : Fin N => delta k • (Pi.single k 1 : Fin N -> Real)) := by
    funext i
    simp [Pi.single_apply]
  calc
    linearizedForwardError26_8 derivative delta =
        Finset.univ.sum (fun k => delta k * derivative (Pi.single k 1)) := by
      simp [linearizedForwardError26_8, mul_comm]
    _ = derivative (Finset.univ.sum
        (fun k : Fin N => delta k • (Pi.single k 1 : Fin N -> Real))) := by
      rw [map_sum]
      simp [map_smul, smul_eq_mul]
    _ = derivative delta := by rw [← hdecomp]

/-- Precise first-order meaning of Higham's equation (26.8).  The omitted
terms form a little-o remainder in the vector of elementary rounding errors. -/
theorem eq26_8_linearized_forward_error {N : Nat}
    (g : (Fin N -> Real) -> Real) (D : Fin N -> Real)
    (derivative : (Fin N → ℝ) →L[ℝ] ℝ)
    (hg : HasFDerivAt g derivative D) :
    (fun delta =>
      g (D + delta) - g D - linearizedForwardError26_8 derivative delta)
        =o[nhds 0] (fun delta : Fin N -> Real => delta) := by
  simpa only [linearizedForwardError26_8_eq] using
    (hasFDerivAt_iff_isLittleO_nhds_zero.mp hg)

/-- For the source's class of linear evaluation algorithms, the linearized
formula is exact rather than merely first order. -/
theorem eq26_8_exact_of_affine_increment {N : Nat}
    (g : (Fin N -> Real) -> Real) (D delta : Fin N -> Real)
    (derivative : (Fin N → ℝ) →L[ℝ] ℝ)
    (haffine : g (D + delta) = g D + derivative delta) :
    g (D + delta) - g D = linearizedForwardError26_8 derivative delta := by
  rw [haffine, linearizedForwardError26_8_eq]
  ring

end NumStability
