import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Rectangular
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.BlockTraversal
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.TriangularBartelsStewart.EndToEnd
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.TriangularBartelsStewart.RoundedSolve
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equation09.Assembly

/-!
# Source.Higham.Chapter16.Section02.BartelsStewart.Equation09.EndToEnd

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16Eq9EndToEnd.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 16.2, p. 308, equation (16.9): END-TO-END normwise residual
-- guarantee for the Sylvester solution computed by the Bartels-Stewart
-- (Schur) method, with the rounded-solve residual hypothesis DISCHARGED.
--
-- This file is the final glue between two proved Wave-14 modules:
--
-- * `Higham16RoundedTriangular` proves the (16.8) componentwise residual
--   `|C~ - R Z^ + Z^ S| <= gamma_{nm} (|R||Z^| + |Z^||S|)` entrywise for the
--   computed back-substitution solution `Z^ = flSylvesterSchurBackSubSolve`
--   of the Schur-coordinate system (supplied triangular factors, house
--   per-column shifted-determinant separation certificates).
-- * `Higham16Eq9Assembly` transports a Schur-coordinate Frobenius residual
--   bound `||Cs - (R Y - Y S)||_F <= c (||R||_F + ||S||_F) ||Y||_F`
--   (its hypothesis `hres`) through the orthogonal Schur factors into the
--   printed (16.9) bound in original coordinates.
--
-- Glue content proved here:
-- 1. Entrywise-domination => Frobenius domination applied to the (16.8)
--    budget, together with Frobenius submultiplicativity
--    `|| |R||Z^| ||_F <= ||R||_F ||Z^||_F` (`frobNormRect_rectMatMul_le`
--    composed with `frobNormRect_abs`), yields the Frobenius form of (16.8):
--    `||C~ - R Z^ + Z^ S||_F <= gamma_{nm} (||R||_F + ||S||_F) ||Z^||_F`.
-- 2. Feeding this as `hres` to the Eq9Assembly transport, at the exactly
--    transformed right-hand side `C~ = U^T C V`, discharges the residual
--    hypothesis and produces the end-to-end (16.9) guarantee
--    `||C - (A X^ - X^ B)||_F <=
--       gamma_{nm} (||A||_F + ||B||_F) ||X^||_F`
--    for the reconstructed computed solution `X^ = U Z^ V^T`, with NO
--    residual hypothesis remaining.
--
-- Honest scope (inherited from the two ingredient modules):
-- * The Schur factors are SUPPLIED exactly (orthogonal `U`, `V`, upper
--   triangular `R`, `S` with `A = U R U^T`, `B = V S V^T`), as in the
--   printed setting, which assumes the Schur decomposition has already been
--   computed; errors in computing the Schur factors are NOT modeled here
--   (the assembly module offers perturbed-factor variants under additional
--   hypotheses, which are not used in this file).
-- * The transformed right-hand side `C~ = U^T C V` and the reconstruction
--   `X^ = U Z^ V^T` are exact-arithmetic transforms; only the substitution
--   solve is rounded, matching the (16.7)-(16.8) model of pp. 307-308.
-- * The printed unspecified constant (Higham's `gamma~_{m,n}` class) is
--   realized as the explicit same-gamma-class envelope
--   `gamma_{nm} = nm*u/(1 - nm*u)` with the explicit index `nm`; no printed
--   letter constant is claimed.
-- * Only the strictly triangular (all 1x1 diagonal blocks) real Schur case
--   is covered, exactly as in the rounded-solve module.




namespace NumStability

namespace Wave14

open scoped BigOperators

-- ============================================================
-- Generic glue: componentwise product budget => Frobenius data scale
-- ============================================================

























































































/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.8)-(16.9):
    source-numbered alias for the entrywise componentwise-product residual
    budget to Frobenius data-scale bridge used by the end-to-end residual
    assembly. -/
alias H16_eq16_8_9_frobNormRect_le_gamma_dataScale_of_componentwise_product_budget :=
  frobNormRect_le_gamma_dataScale_of_componentwise_product_budget

-- ============================================================
-- (16.8) in Frobenius form: the discharged Schur-coordinate residual
-- ============================================================


































































/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.8)-(16.9):
    source-numbered alias for the raw triangular Schur-coordinate
    Frobenius residual bound discharged from the componentwise (16.8)
    theorem. -/
alias H16_eq16_8_frobNormRect_sylvesterResidualRect_triangular_backSub_le :=
  frobNormRect_sylvesterResidualRect_triangular_backSub_le

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.8)-(16.9):
    source-numbered alias for the Frobenius form of the (16.8) rounded
    triangular-solve residual bound, i.e. the discharged residual hypothesis
    of the (16.9) assembly. -/
alias H16_eq16_8_frobNormRect_sylvesterResidualRect_schurTriangular_backSub_le :=
  frobNormRect_sylvesterResidualRect_schurTriangular_backSub_le

-- ============================================================
-- The computed Bartels-Stewart solution
-- ============================================================






























/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.9):
    source-numbered alias for the definitional reconstruction of the computed
    Bartels-Stewart solution from the rounded Schur-coordinate solve. -/
alias H16_eq16_9_flBartelsStewartSchurSolve_eq :=
  flBartelsStewartSchurSolve_eq

-- ============================================================
-- (16.9) end to end: no residual hypothesis
-- ============================================================

/-- **Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.9)** (end-to-end,
    raw reconstruction form).  For the Bartels-Stewart computed solution
    `X^ = U Z^ V^T`, where `Z^` is the rounded back-substitution solve of
    the Schur-coordinate system at the exactly transformed right-hand side
    `C~ = U^T C V`, the overall normwise residual guarantee

    `||C - (A X^ - X^ B)||_F <= gamma_{nm} (||A||_F + ||B||_F) ||X^||_F`

    holds under the honest supplied-orthogonal-Schur-factor hypotheses
    (orthogonal `U`, `V`; `A = U R U^T`, `B = V S V^T`; upper-triangular
    `R`, `S`), the house per-column shifted-determinant separation
    certificates, and the gamma-envelope guard `gammaValid fp (n*m)` — with
    NO residual hypothesis: the (16.7)-(16.8) rounded-solve residual is
    proved by the rounded triangular module and glued here.  Higham prints
    an unspecified `gamma~_{m,n}` class constant; it is realized as the
    explicit envelope `gamma_{nm} = nm*u/(1 - nm*u)`.  Errors in computing
    the Schur factors, the RHS transform, and the reconstruction are not
    modeled, matching the printed (16.7)-(16.8) setting. -/
theorem frobNormRect_sylvesterResidualRect_bartels_stewart_end_to_end_le
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hR : IsUpperTriangularFn m R) (hS : IsUpperTriangularFn n S)
    (hshift : ∀ k : Fin n,
      ¬ Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)
    (hgv : gammaValid fp (n * m)) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (rectMatMul U
            (rectMatMul
              (flSylvesterSchurBackSubSolve fp m n R S
                (rectMatMul (matTranspose U) (rectMatMul C V)))
              (matTranspose V)))) ≤
      gamma fp (n * m) * (frobNormRect A + frobNormRect B) *
        frobNormRect
          (rectMatMul U
            (rectMatMul
              (flSylvesterSchurBackSubSolve fp m n R S
                (rectMatMul (matTranspose U) (rectMatMul C V)))
              (matTranspose V))) :=
  frobNormRect_sylvesterResidualRect_le_gamma_dataScale_of_schur_gamma_residual
    fp (n * m) m n U R A V S B C
    (flSylvesterSchurBackSubSolve fp m n R S
      (rectMatMul (matTranspose U) (rectMatMul C V)))
    hU hV hA hB
    (frobNormRect_sylvesterResidualRect_schurTriangular_backSub_le
      fp m n U R A V S B
      (rectMatMul (matTranspose U) (rectMatMul C V))
      hU hV hA hB hR hS hshift hgv)

/-- **Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.9)** (end-to-end,
    packaged Bartels-Stewart solution).  The computed Bartels-Stewart
    solution `X^ = flBartelsStewartSchurSolve` satisfies the overall
    normwise residual guarantee

    `||C - (A X^ - X^ B)||_F <= gamma_{nm} (||A||_F + ||B||_F) ||X^||_F`

    under the honest supplied-orthogonal-Schur-factor hypotheses, the house
    per-column shifted-determinant separation certificates, and
    `gammaValid fp (n*m)` — with NO residual hypothesis (the rounded-solve
    residual of (16.7)-(16.8) is proved, not assumed).  The printed
    unspecified `gamma~_{m,n}` class constant is realized as the explicit
    same-gamma-class envelope `gamma_{nm} = nm*u/(1 - nm*u)`. -/
theorem bartels_stewart_end_to_end_residual
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hR : IsUpperTriangularFn m R) (hS : IsUpperTriangularFn n S)
    (hshift : ∀ k : Fin n,
      ¬ Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)
    (hgv : gammaValid fp (n * m)) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (flBartelsStewartSchurSolve fp m n U R V S C)) ≤
      gamma fp (n * m) * (frobNormRect A + frobNormRect B) *
        frobNormRect (flBartelsStewartSchurSolve fp m n U R V S C) :=
  frobNormRect_sylvesterResidualRect_bartels_stewart_end_to_end_le
    fp m n U R A V S B C hU hV hA hB hR hS hshift hgv

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.9): source-numbered
    alias for the end-to-end Bartels-Stewart residual guarantee with no
    residual hypothesis (raw reconstruction form). -/
alias H16_eq16_9_frobNormRect_sylvesterResidualRect_bartels_stewart_end_to_end_le :=
  frobNormRect_sylvesterResidualRect_bartels_stewart_end_to_end_le

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.9): source-numbered
    alias for the end-to-end Bartels-Stewart residual guarantee with no
    residual hypothesis (packaged computed-solution form). -/
alias H16_eq16_9_end_to_end_bartels_stewart_residual :=
  bartels_stewart_end_to_end_residual

end Wave14

end NumStability
