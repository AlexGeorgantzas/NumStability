import NumStability.Source.Higham.Chapter16.HessenbergSchur.Results
import NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.HessenbergRounded

/-!
# Algorithms.Sylvester.Higham16HessenbergRounded

Historical declaration-bearing facade. Genuine-private and ambient-context retention closure remains here with its original identity.
-/

-- Algorithms/Sylvester/Higham16HessenbergRounded.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 16.2, pp. 307-308, equations (16.6)-(16.7): the ROUNDED
-- Hessenberg-Schur column-solve backward error for the shifted singleton
-- Schur-column coefficient `R - t I`.
--
-- Setting.  In the Hessenberg-Schur variant of the Bartels-Stewart algorithm
-- the left transformed factor `R` is upper *Hessenberg* (not triangular) and
-- the right factor `S` is (quasi-)upper-triangular.  Column `k` of the
-- transformed unknown is obtained by solving the (16.6) singleton column
-- system
--
--   (16.6)   (R - S_kk I) x_k = b_k
--
-- where the coefficient `R - t I` (with `t = S_kk`) inherits the
-- upper-Hessenberg zero pattern of `R`.  In the Hessenberg-Schur method this
-- shifted Hessenberg column system is solved by Gaussian elimination with
-- partial pivoting (GEPP) specialized to Hessenberg structure, for which
-- Wilkinson's growth bound gives `rho <= m` (Higham Theorem 9.10 / §9.4).
--
-- The EXACT structural handoff is already in place (Codex,
-- `Higham16HessenbergSchur.lean`):
--
--   * `sylvesterTriangularShiftedCoeff_isUpperHessenberg` : `R - t I` is upper
--     Hessenberg whenever `R` is;
--   * `exists_HessenbergGEPPUTrace_..._of_det_ne_zero` and the growth wrappers :
--     a nonsingular shifted Hessenberg coefficient admits the Chapter 9 EXACT
--     upper-Hessenberg GEPP `U`-trace with `growthFactorEntry <= m`.
--
-- The residual documented there is: "not rounded Bartels-Stewart arithmetic".
-- This file closes that residual at the honest strength the repository's
-- Chapter 9 rounded Hessenberg endpoint supports.
--
-- Ch9 rounded Hessenberg endpoint (`HighamChapter9.lean`, Theorem 9.10):
--   `higham9_10_hessenberg_lu_solve_backward_stable_tight`
-- takes the COMPUTED Hessenberg-GEPP factors `L_hat, U_hat` of the coefficient
-- `H`, carrying
--   * a factorization backward-error certificate `LUBackwardError H L_hat U_hat (gamma_m)`,
--   * nonzero computed pivots `L_hat_ii != 0`, `U_hat_ii != 0`,
--   * the Hessenberg growth inequality `sum_k |L_hat_ik| |U_hat_kj| <= m |H_ij|`
--     (Wilkinson's `rho <= m`, applied to the computed factors),
-- and produces the computed column solution
--   `x_hat = fl_backSub(U_hat, fl_forwardSub(L_hat, b))`
-- with the (16.7)-shaped rounded backward error
--   `(H + DeltaH) x_hat = b`,  `|DeltaH_ij| <= m * gamma_{3m} * |H_ij|`.
--
-- This file specializes that endpoint to `H = R - t I`, discharging the
-- upper-Hessenberg structure of the coefficient automatically through the
-- Codex handoff lemma, and delivering the (16.6)/(16.7)-shaped rounded column
-- backward error in both the row-sum form of the endpoint and the printed
-- `Matrix.mulVec` form, plus a max-entry normwise reading.
--
-- HONEST SCOPE AND RESIDUAL.
-- * The coefficient's upper-Hessenberg structure is discharged UNCONDITIONALLY
--   from the Codex handoff (`sylvesterTriangularShiftedCoeff_isUpperHessenberg`),
--   so nothing about the Hessenberg zero pattern is assumed.
-- * The computed Hessenberg-GEPP factor package (`LUBackwardError` at `gamma_m`,
--   nonzero computed pivots, and the computed-factor growth
--   `sum |L_hat||U_hat| <= m |H|`) is SUPPLIED as a hypothesis, exactly as at
--   the general Chapter 9 rounded LU-solve level
--   (`lu_solve_backward_error` / `higham9_4_lu_solve_backward_error`), which
--   likewise consumes `LUBackwardError` for the computed factors.  There is NO
--   repository theorem that PRODUCES `L_hat, U_hat` together with
--   `LUBackwardError` and the Hessenberg growth from a nonsingular Hessenberg
--   matrix by a rounded executable GEPP schedule; the Chapter 9 source note
--   (`higham9_3_exactDoolittle_recurrences_backward_error_gamma`) records this
--   as the still-open "rounded executable schedule that proves these recurrence
--   hypotheses for computed factors".  That production step is the precise
--   remaining residual; this file does NOT smuggle it into a hypothesis and
--   does NOT claim it.
-- * The Codex EXACT handoff supplies Wilkinson's `rho <= m` for the EXACT
--   elimination `U`-trace (`growthFactorEntry <= m`).  The rounded endpoint
--   needs the SAME `rho <= m` bound for the COMPUTED factors.  These agree in
--   exact arithmetic; bridging exact-trace growth to computed-factor growth is
--   exactly the open rounded-schedule gap above.  The wrapper
--   `..._structure_and_exact_growth_certificate` exposes both the automatic
--   Hessenberg structure and the exact-trace `growthFactorEntry <= m` witness
--   side by side with the rounded conclusion, keeping the exact/computed
--   arithmetic distinction visible rather than hidden.
-- * The printed unspecified constant `c_{m,n} u` of (16.7) is realized as the
--   explicit same-gamma-class envelope `m * gamma_{3m}`, matching the Chapter 9
--   Theorem 9.4 / Theorem 9.10 tight solve budget.  We do not claim the printed
--   letter constant.
-- * Only the singleton (1x1 diagonal block, `t = S_kk` scalar shift) column of
--   (16.6) is treated, matching the Codex singleton handoff; the 2x2-block
--   Hessenberg-Schur column solve remains open.



namespace NumStability

namespace Wave17

open scoped BigOperators

-- ============================================================
-- (16.7): rounded Hessenberg-Schur column-solve backward error
-- ============================================================

















































































































































-- ============================================================
-- Structure + exact-trace growth certificate (residual made explicit)
-- ============================================================
































































-- ============================================================
-- Source-numbered aliases
-- ============================================================


























-- ============================================================
-- Automatic (no-supplied-factor) real-Schur exact traversal aliases
-- ============================================================

/-- **Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8)**, automatic
    (no-supplied-factor) real-Schur exact traversal, existence form.

    Confirmation alias: under only `NoCommonComplexRightEigenvalue` for the
    original coefficients `A`, `B`, the real quasi-Schur factors are chosen
    INTERNALLY and the generated Bartels-Stewart recursion produces the exact
    original-coordinate Sylvester solution `U X V^T` together with the
    orthogonality, block-map, zero-below, two-block spectral, and generated
    step-formula certificates.  No Schur factors are supplied by the caller —
    the exact recursive traversal is fully automatic.  This is the exact
    infinite-precision route that the rounded Hessenberg column solve above
    refines column by column. -/
theorem H16_eq16_4_8_auto_realSchur_exists_original_solution_of_no_common
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B)) :
    ∃ (U R : RMatFn m m) (V S : RMatFn n n)
        (pA : Fin m → Nat) (pB : Fin n → Nat) (X : RMatFn m n),
      IsOrthogonal m U ∧
      IsOrthogonal n V ∧
      A = rectMatMul U (rectMatMul R (matTranspose U)) ∧
      B = rectMatMul V (rectMatMul S (matTranspose V)) ∧
      Monotone pA ∧
      (∀ c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card ≤ 2) ∧
      (∀ i j : Fin m, pA j < pA i → R i j = 0) ∧
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA ∧
      Monotone pB ∧
      (∀ c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card ≤ 2) ∧
      (∀ i j : Fin n, pB j < pB i → S i j = 0) ∧
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB ∧
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pB ∧
      IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_no_common
    m n A B C hnoOrig

/-- **Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8)**, automatic
    (no-supplied-factor) real-Schur exact traversal, unique-solvability form.

    Confirmation alias: under only `NoCommonComplexRightEigenvalue` for `A`,
    `B`, the internally chosen real quasi-Schur factors and the generated
    recursive candidate make the original-coordinate Sylvester equation
    `A X - X B = C` uniquely solvable, with no Schur factors supplied by the
    caller. -/
theorem H16_eq16_4_8_auto_realSchur_existsUnique_solution_of_no_common
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_no_common_generated_step_formula_witness
    m n A B C hnoOrig

end Wave17

end NumStability
