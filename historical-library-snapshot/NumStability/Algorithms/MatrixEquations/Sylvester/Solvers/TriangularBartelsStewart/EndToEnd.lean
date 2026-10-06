import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Rectangular
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.BlockTraversal
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.TriangularBartelsStewart.RoundedSolve
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Algorithms.MatrixEquations.Sylvester.Solvers.TriangularBartelsStewart.EndToEnd

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
    generic entrywise-to-Frobenius glue.  If a residual matrix `E` obeys the
    (16.8)-shaped componentwise product budget
    `|E| <= g (|R||Z| + |Z||S|)` entrywise with `0 <= g`, then it obeys the
    Frobenius data-scale bound `||E||_F <= g (||R||_F + ||S||_F) ||Z||_F`.
    The proof is entrywise absolute-value domination of the Frobenius norm
    followed by the triangle inequality and Frobenius submultiplicativity of
    the absolute-value products (`|| |R||Z| ||_F <= ||R||_F ||Z||_F`, which
    is the per-entry Cauchy-Schwarz bound packaged in
    `frobNormRect_rectMatMul_le` and `frobNormRect_abs`).  The coefficient
    `g` is preserved verbatim; no printed constant is claimed. -/
theorem frobNormRect_le_gamma_dataScale_of_componentwise_product_budget
    {m n : Nat} (E : RMatFn m n) (R : RMatFn m m) (S : RMatFn n n)
    (Z : RMatFn m n) (g : Real) (hg : 0 ≤ g)
    (hentry : ∀ (i : Fin m) (k : Fin n),
      |E i k| ≤
        g * (matMulRect m m n (fun a b => |R a b|) (fun a b => |Z a b|) i k +
          matMulRect m n n (fun a b => |Z a b|) (fun a b => |S a b|) i k)) :
    frobNormRect E ≤
      g * (frobNormRect R + frobNormRect S) * frobNormRect Z := by
  have hP1 : ∀ (i : Fin m) (k : Fin n),
      0 ≤ matMulRect m m n (fun a b => |R a b|) (fun a b => |Z a b|) i k := by
    intro i k
    show 0 ≤ ∑ j : Fin m, |R i j| * |Z j k|
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hP2 : ∀ (i : Fin m) (k : Fin n),
      0 ≤ matMulRect m n n (fun a b => |Z a b|) (fun a b => |S a b|) i k := by
    intro i k
    show 0 ≤ ∑ j : Fin n, |Z i j| * |S j k|
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have h1 : frobNormRect E ≤
      frobNormRect (fun i k =>
        g * (matMulRect m m n (fun a b => |R a b|) (fun a b => |Z a b|) i k +
          matMulRect m n n (fun a b => |Z a b|) (fun a b => |S a b|) i k)) :=
    frobNormRect_le_of_entry_abs_le E _
      (fun i k => mul_nonneg hg (add_nonneg (hP1 i k) (hP2 i k)))
      hentry
  have h2 : frobNormRect (fun i k =>
        g * (matMulRect m m n (fun a b => |R a b|) (fun a b => |Z a b|) i k +
          matMulRect m n n (fun a b => |Z a b|) (fun a b => |S a b|) i k)) =
      g * frobNormRect (fun i k =>
        matMulRect m m n (fun a b => |R a b|) (fun a b => |Z a b|) i k +
          matMulRect m n n (fun a b => |Z a b|) (fun a b => |S a b|) i k) := by
    have h := frobNormRect_smul g (fun i k =>
      matMulRect m m n (fun a b => |R a b|) (fun a b => |Z a b|) i k +
        matMulRect m n n (fun a b => |Z a b|) (fun a b => |S a b|) i k)
    rw [abs_of_nonneg hg] at h
    exact h
  have h4 : frobNormRect
        (matMulRect m m n (fun a b => |R a b|) (fun a b => |Z a b|)) ≤
      frobNormRect R * frobNormRect Z := by
    have hsub := frobNormRect_rectMatMul_le
      (fun a b => |R a b|) (fun a b => |Z a b|)
    rw [frobNormRect_abs R, frobNormRect_abs Z] at hsub
    rw [matMulRect_eq_rectMatMul]
    exact hsub
  have h5 : frobNormRect
        (matMulRect m n n (fun a b => |Z a b|) (fun a b => |S a b|)) ≤
      frobNormRect Z * frobNormRect S := by
    have hsub := frobNormRect_rectMatMul_le
      (fun a b => |Z a b|) (fun a b => |S a b|)
    rw [frobNormRect_abs Z, frobNormRect_abs S] at hsub
    rw [matMulRect_eq_rectMatMul]
    exact hsub
  calc
    frobNormRect E ≤
        frobNormRect (fun i k =>
          g * (matMulRect m m n (fun a b => |R a b|)
              (fun a b => |Z a b|) i k +
            matMulRect m n n (fun a b => |Z a b|)
              (fun a b => |S a b|) i k)) := h1
    _ = g * frobNormRect (fun i k =>
          matMulRect m m n (fun a b => |R a b|) (fun a b => |Z a b|) i k +
            matMulRect m n n (fun a b => |Z a b|)
              (fun a b => |S a b|) i k) := h2
    _ ≤ g * (frobNormRect R * frobNormRect Z +
          frobNormRect Z * frobNormRect S) := by
        refine mul_le_mul_of_nonneg_left ?_ hg
        refine le_trans
          (frobNormRect_add_le
            (matMulRect m m n (fun a b => |R a b|) (fun a b => |Z a b|))
            (matMulRect m n n (fun a b => |Z a b|) (fun a b => |S a b|)))
          ?_
        exact add_le_add h4 h5
    _ = g * (frobNormRect R + frobNormRect S) * frobNormRect Z := by ring








-- ============================================================
-- (16.8) in Frobenius form: the discharged Schur-coordinate residual
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.8)-(16.9)
    (supplied triangular Schur-coordinate factors, Frobenius form).  The
    computed Schur-coordinate solution `Z^ = flSylvesterSchurBackSubSolve`
    satisfies

    `||C~ - R Z^ + Z^ S||_F <= gamma_{nm} (||R||_F + ||S||_F) ||Z^||_F`,

    the Frobenius-norm consequence of the (16.8) componentwise residual
    bound.  This is exactly the residual hypothesis (`hres`) shape consumed
    by the (16.9) assembly module, now proved rather than assumed.  The
    printed unspecified constant is realized as the explicit
    same-gamma-class envelope `gamma_{nm} = nm*u/(1 - nm*u)`. -/
theorem frobNormRect_sylvesterResidualRect_triangular_backSub_le
    (fp : FPModel) (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n)
    (hR : IsUpperTriangularFn m R) (hS : IsUpperTriangularFn n S)
    (hsep : ∀ (i : Fin m) (k : Fin n), R i i ≠ S k k)
    (hgv : gammaValid fp (n * m)) :
    frobNormRect
        (sylvesterResidualRect m n R S Ct
          (flSylvesterSchurBackSubSolve fp m n R S Ct)) ≤
      gamma fp (n * m) * (frobNormRect R + frobNormRect S) *
        frobNormRect (flSylvesterSchurBackSubSolve fp m n R S Ct) :=
  frobNormRect_le_gamma_dataScale_of_componentwise_product_budget
    (sylvesterResidualRect m n R S Ct
      (flSylvesterSchurBackSubSolve fp m n R S Ct))
    R S (flSylvesterSchurBackSubSolve fp m n R S Ct)
    (gamma fp (n * m)) (gamma_nonneg fp hgv)
    (fun i k =>
      sylvesterResidualRect_triangular_backSub_componentwise_le
        fp m n R S Ct hR hS hsep hgv i k)

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.8)-(16.9)
    (supplied Schur-factor form, Frobenius shape).  Under the honest
    supplied-orthogonal-Schur-factor hypotheses of the rounded-solve module
    — orthogonal `U`, `V` with `A = U R U^T`, `B = V S V^T`, upper
    triangular `R`, `S`, and the house per-column shifted-determinant
    separation certificates — the computed Schur-coordinate solution
    satisfies `||C~ - R Z^ + Z^ S||_F <=
    gamma_{nm} (||R||_F + ||S||_F) ||Z^||_F`.  This is the (16.9) residual
    hypothesis of the assembly module, discharged from the proved (16.8)
    componentwise bound; the constant is the explicit envelope
    `gamma_{nm}`. -/
theorem frobNormRect_sylvesterResidualRect_schurTriangular_backSub_le
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (Ct : RMatFn m n)
    (_hU : IsOrthogonal m U) (_hV : IsOrthogonal n V)
    (_hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (_hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hR : IsUpperTriangularFn m R) (hS : IsUpperTriangularFn n S)
    (hshift : ∀ k : Fin n,
      ¬ Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)
    (hgv : gammaValid fp (n * m)) :
    frobNormRect
        (sylvesterResidualRect m n R S Ct
          (flSylvesterSchurBackSubSolve fp m n R S Ct)) ≤
      gamma fp (n * m) * (frobNormRect R + frobNormRect S) *
        frobNormRect (flSylvesterSchurBackSubSolve fp m n R S Ct) :=
  frobNormRect_sylvesterResidualRect_triangular_backSub_le fp m n R S Ct
    hR hS
    (fun i k =>
      upperTriangularFn_diag_ne_of_shifted_det_ne_zero m R (S k k) hR
        (hshift k) i)
    hgv















-- ============================================================
-- The computed Bartels-Stewart solution
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.4)-(16.9):
    the computed Bartels-Stewart (Schur method) Sylvester solution.  Given
    supplied Schur factors `U`, `R`, `V`, `S` and right-hand side `C`, it is
    the exact reconstruction `X^ = U Z^ V^T` of the rounded back-substitution
    solution `Z^ = flSylvesterSchurBackSubSolve` of the Schur-coordinate
    system with the exactly transformed right-hand side `C~ = U^T C V`.
    Only the substitution solve is rounded, matching the printed
    (16.7)-(16.8) model. -/
noncomputable def flBartelsStewartSchurSolve (fp : FPModel) (m n : Nat)
    (U R : RMatFn m m) (V S : RMatFn n n) (C : RMatFn m n) : RMatFn m n :=
  rectMatMul U
    (rectMatMul
      (flSylvesterSchurBackSubSolve fp m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)))
      (matTranspose V))

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.9): definitional
    unfolding of the computed Bartels-Stewart solution
    `X^ = U Z^ V^T` with `Z^` the rounded Schur-coordinate solve at
    `C~ = U^T C V`. -/
theorem flBartelsStewartSchurSolve_eq (fp : FPModel) (m n : Nat)
    (U R : RMatFn m m) (V S : RMatFn n n) (C : RMatFn m n) :
    flBartelsStewartSchurSolve fp m n U R V S C =
      rectMatMul U
        (rectMatMul
          (flSylvesterSchurBackSubSolve fp m n R S
            (rectMatMul (matTranspose U) (rectMatMul C V)))
          (matTranspose V)) := rfl







-- ============================================================
-- (16.9) end to end: no residual hypothesis
-- ============================================================
































































































end Wave14

end NumStability
