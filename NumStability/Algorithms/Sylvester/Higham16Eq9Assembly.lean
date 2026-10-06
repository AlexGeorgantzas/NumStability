-- Algorithms/Sylvester/Higham16Eq9Assembly.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 16.2, equation (16.9), p. 308: assembly of the overall normwise
-- residual guarantee for the Sylvester solution computed by the Schur
-- (Bartels-Stewart) method.
--
-- The printed argument has three ingredients:
--   (i)  the rounded quasi-triangular solve residual, equations
--        (16.7)-(16.8), p. 308: the computed Schur-coordinate solution
--        `Y` satisfies `||Cs - (R Y - Y S)||_F <= gamma * (||R||_F +
--        ||S||_F) * ||Y||_F` with `Cs = U^T C V`;
--   (ii) exact residual transport between Schur and original coordinates
--        (proved in `Higham16.lean`:
--        `sylvesterResidualRect_schur_transform_identity`,
--        `frobNormRect_sylvesterResidualRect_schur_transform`);
--   (iii) Frobenius-norm invariance under the orthogonal factors, which
--        also converts the data scale `(||R||_F + ||S||_F) ||Y||_F` into
--        `(||A||_F + ||B||_F) ||Xhat||_F`.
--
-- This file proves the assembly steps (ii)+(iii) in full and packages the
-- resulting (16.9)-shaped guarantee.  Ingredient (i) is the concern of the
-- rounded triangular-solve module (`Higham16RoundedTriangular`), which does
-- not exist yet at the time of writing; its statement shape is therefore
-- taken as an explicit hypothesis (`hres` below) and documented as such in
-- every docstring.  No rounded-arithmetic fact is claimed as proved here.
--
-- The sharper variants additionally allow backward-perturbed (rounded)
-- Schur factors `A + dA = U R U^T` with an exactly orthogonal `U` and a
-- normwise-relative Frobenius bound on `dA`.  That is precisely the
-- backward-error contract shape that the Chapter 19 Householder QR analysis
-- proves for the QR factorization step
-- (`H19.Theorem19_4.householder_qr_backward_error` /
-- `H19.Theorem19_4.HouseholderQRBackwardError.exists_frobNormRect_perturbation_bound`);
-- the corresponding QR-algorithm real-Schur-decomposition backward-error
-- theorem is not yet formalized, so the factor-perturbation bounds also
-- remain hypotheses, stated in exactly that ch19 shape.

import NumStability.Algorithms.Sylvester.Higham16
import NumStability.Analysis.Rounding
import NumStability.Algorithms.QR.Higham19

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

namespace Wave14

-- ============================================================
-- Norm transport helpers
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equations (16.5) and (16.9), p. 308:
    the rectangular Frobenius norm is invariant under the two-sided
    orthogonal transform `M |-> U M V^T` used by the Schur method.  This is
    the exact-arithmetic norm bridge that converts every Schur-coordinate
    Frobenius quantity in the (16.9) data scale back to original
    coordinates. -/
theorem frobNormRect_orthogonal_conjugation_eq {m n : Nat}
    (U : RMatFn m m) (M : RMatFn m n) (V : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V) :
    frobNormRect (rectMatMul U (rectMatMul M (matTranspose V))) =
      frobNormRect M := by
  calc
    frobNormRect (rectMatMul U (rectMatMul M (matTranspose V)))
        = frobNormRect (rectMatMul M (matTranspose V)) := by
          simpa [matMulRectLeft] using
            frobNormRect_orthogonal_left U
              (rectMatMul M (matTranspose V)) hU
    _ = frobNormRect M := by
          simpa [matMulRectRight] using
            frobNormRect_orthogonal_right M (matTranspose V) hV.transpose

/-- Higham, 2nd ed., Chapter 16.2, equations (16.5) and (16.9), p. 308:
    source-numbered alias for Frobenius invariance under the Schur
    two-sided orthogonal reconstruction map. -/
alias H16_eq16_5_9_frobNormRect_orthogonal_conjugation_eq :=
  frobNormRect_orthogonal_conjugation_eq

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308: the Frobenius
    norm of a matrix presented by an exact orthogonal Schur similarity
    `A = U R U^T` equals the Frobenius norm of its quasi-triangular factor.
    This converts the `||R||_F + ||S||_F` scale of the rounded solve bound
    (16.8) into the printed `||A||_F + ||B||_F` scale of (16.9). -/
theorem frobNormRect_eq_of_orthogonal_similarity {m : Nat}
    (U R A : RMatFn m m) (hU : IsOrthogonal m U)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U))) :
    frobNormRect A = frobNormRect R := by
  rw [hA]
  exact frobNormRect_orthogonal_conjugation_eq U R U hU hU

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308:
    source-numbered alias for equality of a supplied exact Schur factor and
    original matrix Frobenius scale. -/
alias H16_eq16_9_frobNormRect_eq_of_orthogonal_similarity :=
  frobNormRect_eq_of_orthogonal_similarity

-- ============================================================
-- (16.9) assembly: supplied exact orthogonal Schur factors
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308: overall
    normwise residual guarantee for the Schur-method Sylvester solution
    under supplied exact orthogonal Schur factors, with an arbitrary
    coefficient `c`.

    Hypothesis `hres` is the rounded quasi-triangular solve residual bound
    of equations (16.7)-(16.8), p. 308, in Schur coordinates:
    `||Cs - (R Y - Y S)||_F <= c (||R||_F + ||S||_F) ||Y||_F` with
    `Cs = U^T C V`.  The rounded-solve module that will discharge it
    (`Higham16RoundedTriangular`) is not yet available, so the bound is an
    explicit hypothesis; this theorem contributes the remaining printed
    content of (16.9): the residual and every Frobenius factor of the data
    scale transport exactly through the orthogonal Schur coordinates, so
    the identical bound holds in original coordinates for the reconstructed
    solution `Xhat = U Y V^T`.  The coefficient is preserved verbatim; in
    particular no specific printed constant is claimed. -/
theorem frobNormRect_sylvesterResidualRect_le_dataScale_of_schur_dataScale_residual
    (m n : Nat) (U R A : RMatFn m m) (V S B : RMatFn n n) (C Y : RMatFn m n)
    (c : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <=
        c * (frobNormRect R + frobNormRect S) * frobNormRect Y) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V)))) <=
      c * (frobNormRect A + frobNormRect B) *
        frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  have hnA : frobNormRect A = frobNormRect R :=
    frobNormRect_eq_of_orthogonal_similarity U R A hU hA
  have hnB : frobNormRect B = frobNormRect S :=
    frobNormRect_eq_of_orthogonal_similarity V S B hV hB
  have hnX :
      frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) =
        frobNormRect Y :=
    frobNormRect_orthogonal_conjugation_eq U Y V hU hV
  rw [frobNormRect_sylvesterResidualRect_schur_transform m n U R A V S B C Y
    hU hV hA hB, hnA, hnB, hnX]
  exact hres

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308: source-numbered
    alias for the coefficient-preserving (16.9) residual/data-scale
    assembly under supplied exact orthogonal Schur factors. -/
alias H16_eq16_9_frobNormRect_sylvesterResidualRect_le_dataScale_of_schur_dataScale_residual :=
  frobNormRect_sylvesterResidualRect_le_dataScale_of_schur_dataScale_residual

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308: the printed
    gamma-class display of the overall normwise residual guarantee,
    `||C - (A Xhat - Xhat B)||_F <= gamma_k (||A||_F + ||B||_F) ||Xhat||_F`
    for the Schur-method solution `Xhat = U Y V^T` under supplied exact
    orthogonal Schur factors.

    The index `k` is arbitrary and is meant to be instantiated by the
    rounded quasi-triangular solve analysis of equations (16.7)-(16.8)
    (hypothesis `hres`, see
    `frobNormRect_sylvesterResidualRect_le_dataScale_of_schur_dataScale_residual`);
    Higham prints a dimension-dependent `gamma_tilde` constant whose exact
    integer index is not claimed here. -/
theorem frobNormRect_sylvesterResidualRect_le_gamma_dataScale_of_schur_gamma_residual
    (fp : FPModel) (k : Nat)
    (m n : Nat) (U R A : RMatFn m m) (V S B : RMatFn n n) (C Y : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <=
        gamma fp k * (frobNormRect R + frobNormRect S) * frobNormRect Y) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V)))) <=
      gamma fp k * (frobNormRect A + frobNormRect B) *
        frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) :=
  frobNormRect_sylvesterResidualRect_le_dataScale_of_schur_dataScale_residual
    m n U R A V S B C Y (gamma fp k) hU hV hA hB hres

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308: source-numbered
    alias for the gamma-class display of the Schur-method residual
    guarantee under supplied exact orthogonal Schur factors. -/
alias H16_eq16_9_frobNormRect_sylvesterResidualRect_le_gamma_dataScale_of_schur_gamma_residual :=
  frobNormRect_sylvesterResidualRect_le_gamma_dataScale_of_schur_gamma_residual

-- ============================================================
-- (16.9) assembly: backward-perturbed (rounded) Schur factors
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308, sharper
    fully-rounded-factor variant with explicit coefficients: the Schur
    factors themselves are computed, so only backward-perturbed exact
    orthogonal factorizations `A + dA = U R U^T`, `B + dB = V S V^T` are
    available, with `||dA||_F <= epsA ||A||_F` and
    `||dB||_F <= epsB ||B||_F`.

    This is exactly the backward-error contract shape proved by the
    Chapter 19 Householder QR analysis for the QR factorization step
    (`H19.Theorem19_4.householder_qr_backward_error` composed with
    `H19.Theorem19_4.HouseholderQRBackwardError.exists_frobNormRect_perturbation_bound`);
    the QR-algorithm real-Schur backward-error theorem is not yet
    formalized, so `hdA`/`hdB` remain hypotheses in that shape.  Hypothesis
    `hres` is the rounded quasi-triangular solve residual bound of
    equations (16.7)-(16.8) in Schur coordinates for the perturbed data.

    Conclusion: the residual of `Xhat = U Y V^T` obeys the (16.9)-shaped
    bound with the per-matrix coefficients inflated from `c` to
    `c (1 + epsA) + epsA` and `c (1 + epsB) + epsB`; the inflation is exact
    first-order bookkeeping and no printed constant is claimed. -/
theorem frobNormRect_sylvesterResidualRect_le_dataScale_of_perturbed_schur_factors_residual
    (m n : Nat) (U R A dA : RMatFn m m) (V S B dB : RMatFn n n)
    (C Y : RMatFn m n) (c epsA epsB : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : forall i j,
      A i j + dA i j = rectMatMul U (rectMatMul R (matTranspose U)) i j)
    (hB : forall i j,
      B i j + dB i j = rectMatMul V (rectMatMul S (matTranspose V)) i j)
    (hdA : frobNormRect dA <= epsA * frobNormRect A)
    (hdB : frobNormRect dB <= epsB * frobNormRect B)
    (hc : 0 <= c)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <=
        c * (frobNormRect R + frobNormRect S) * frobNormRect Y) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V)))) <=
      ((c * (1 + epsA) + epsA) * frobNormRect A +
        (c * (1 + epsB) + epsB) * frobNormRect B) *
        frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  have hAfun :
      (fun a b => A a b + dA a b) =
        rectMatMul U (rectMatMul R (matTranspose U)) := by
    ext i j
    exact hA i j
  have hBfun :
      (fun a b => B a b + dB a b) =
        rectMatMul V (rectMatMul S (matTranspose V)) := by
    ext i j
    exact hB i j
  -- Residual decomposition against the exactly factorized perturbed data.
  have hfun :
      sylvesterResidualRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V))) =
        fun i j =>
          sylvesterResidualRect m n
              (fun a b => A a b + dA a b) (fun a b => B a b + dB a b) C
              (rectMatMul U (rectMatMul Y (matTranspose V))) i j +
            (rectMatMul dA
                (rectMatMul U (rectMatMul Y (matTranspose V))) i j -
              rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V)))
                dB i j) := by
    ext i j
    have hL :
        rectMatMul (fun a b => A a b + dA a b)
            (rectMatMul U (rectMatMul Y (matTranspose V))) i j =
          rectMatMul A
              (rectMatMul U (rectMatMul Y (matTranspose V))) i j +
            rectMatMul dA
              (rectMatMul U (rectMatMul Y (matTranspose V))) i j := by
      unfold rectMatMul
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    have hR :
        rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V)))
            (fun a b => B a b + dB a b) i j =
          rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V)))
              B i j +
            rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V)))
              dB i j := by
      unfold rectMatMul
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    unfold sylvesterResidualRect sylvesterOpRect
    simp only [matMulRect_eq_rectMatMul]
    rw [hL, hR]
    ring
  -- Transport the perturbed-data residual to Schur coordinates.
  have htrans :
      frobNormRect
          (sylvesterResidualRect m n
            (fun a b => A a b + dA a b) (fun a b => B a b + dB a b) C
            (rectMatMul U (rectMatMul Y (matTranspose V)))) =
        frobNormRect
          (sylvesterResidualRect m n R S
            (rectMatMul (matTranspose U) (rectMatMul C V)) Y) :=
    frobNormRect_sylvesterResidualRect_schur_transform m n U R
      (fun a b => A a b + dA a b) V S (fun a b => B a b + dB a b) C Y
      hU hV hAfun hBfun
  -- Frobenius scales of the perturbed data.
  have hnA :
      frobNormRect (fun a b => A a b + dA a b) = frobNormRect R :=
    frobNormRect_eq_of_orthogonal_similarity U R
      (fun a b => A a b + dA a b) hU hAfun
  have hnB :
      frobNormRect (fun a b => B a b + dB a b) = frobNormRect S :=
    frobNormRect_eq_of_orthogonal_similarity V S
      (fun a b => B a b + dB a b) hV hBfun
  have hnX :
      frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) =
        frobNormRect Y :=
    frobNormRect_orthogonal_conjugation_eq U Y V hU hV
  have hA'le :
      frobNormRect (fun a b => A a b + dA a b) <=
        (1 + epsA) * frobNormRect A := by
    have h1 := frobNormRect_add_le A dA
    linarith
  have hB'le :
      frobNormRect (fun a b => B a b + dB a b) <=
        (1 + epsB) * frobNormRect B := by
    have h1 := frobNormRect_add_le B dB
    linarith
  -- Main residual term.
  have t1 :
      frobNormRect
          (sylvesterResidualRect m n
            (fun a b => A a b + dA a b) (fun a b => B a b + dB a b) C
            (rectMatMul U (rectMatMul Y (matTranspose V)))) <=
        c * ((1 + epsA) * frobNormRect A + (1 + epsB) * frobNormRect B) *
          frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) := by
    calc
      frobNormRect
          (sylvesterResidualRect m n
            (fun a b => A a b + dA a b) (fun a b => B a b + dB a b) C
            (rectMatMul U (rectMatMul Y (matTranspose V)))) =
          frobNormRect
            (sylvesterResidualRect m n R S
              (rectMatMul (matTranspose U) (rectMatMul C V)) Y) := htrans
      _ <= c * (frobNormRect R + frobNormRect S) * frobNormRect Y := hres
      _ = c *
            (frobNormRect (fun a b => A a b + dA a b) +
              frobNormRect (fun a b => B a b + dB a b)) *
            frobNormRect
              (rectMatMul U (rectMatMul Y (matTranspose V))) := by
          rw [hnA, hnB, hnX]
      _ <= c * ((1 + epsA) * frobNormRect A + (1 + epsB) * frobNormRect B) *
            frobNormRect
              (rectMatMul U (rectMatMul Y (matTranspose V))) := by
          apply mul_le_mul_of_nonneg_right _
            (frobNormRect_nonneg
              (rectMatMul U (rectMatMul Y (matTranspose V))))
          exact mul_le_mul_of_nonneg_left (add_le_add hA'le hB'le) hc
  -- Perturbation cross terms.
  have t2 :
      frobNormRect
          (rectMatMul dA (rectMatMul U (rectMatMul Y (matTranspose V)))) <=
        epsA * frobNormRect A *
          frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) := by
    calc
      frobNormRect
          (rectMatMul dA (rectMatMul U (rectMatMul Y (matTranspose V)))) <=
          frobNormRect dA *
            frobNormRect
              (rectMatMul U (rectMatMul Y (matTranspose V))) :=
        frobNormRect_rectMatMul_le dA
          (rectMatMul U (rectMatMul Y (matTranspose V)))
      _ <= epsA * frobNormRect A *
            frobNormRect
              (rectMatMul U (rectMatMul Y (matTranspose V))) :=
        mul_le_mul_of_nonneg_right hdA
          (frobNormRect_nonneg
            (rectMatMul U (rectMatMul Y (matTranspose V))))
  have t3 :
      frobNormRect
          (rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V))) dB) <=
        epsB * frobNormRect B *
          frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) := by
    calc
      frobNormRect
          (rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V))) dB) <=
          frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) *
            frobNormRect dB :=
        frobNormRect_rectMatMul_le
          (rectMatMul U (rectMatMul Y (matTranspose V))) dB
      _ <= frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) *
            (epsB * frobNormRect B) :=
        mul_le_mul_of_nonneg_left hdB
          (frobNormRect_nonneg
            (rectMatMul U (rectMatMul Y (matTranspose V))))
      _ = epsB * frobNormRect B *
            frobNormRect
              (rectMatMul U (rectMatMul Y (matTranspose V))) := by
          ring
  -- Triangle inequality assembly.
  have hsplit :
      frobNormRect
          (sylvesterResidualRect m n A B C
            (rectMatMul U (rectMatMul Y (matTranspose V)))) <=
        frobNormRect
            (sylvesterResidualRect m n
              (fun a b => A a b + dA a b) (fun a b => B a b + dB a b) C
              (rectMatMul U (rectMatMul Y (matTranspose V)))) +
          (frobNormRect
              (rectMatMul dA
                (rectMatMul U (rectMatMul Y (matTranspose V)))) +
            frobNormRect
              (rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V)))
                dB)) := by
    rw [hfun]
    have h1 :=
      frobNormRect_add_le
        (sylvesterResidualRect m n
          (fun a b => A a b + dA a b) (fun a b => B a b + dB a b) C
          (rectMatMul U (rectMatMul Y (matTranspose V))))
        (fun i j =>
          rectMatMul dA
              (rectMatMul U (rectMatMul Y (matTranspose V))) i j -
            rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V)))
              dB i j)
    have h2 :=
      frobNormRect_sub_le
        (rectMatMul dA (rectMatMul U (rectMatMul Y (matTranspose V))))
        (rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V))) dB)
    linarith
  calc
    frobNormRect
        (sylvesterResidualRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V)))) <=
        frobNormRect
            (sylvesterResidualRect m n
              (fun a b => A a b + dA a b) (fun a b => B a b + dB a b) C
              (rectMatMul U (rectMatMul Y (matTranspose V)))) +
          (frobNormRect
              (rectMatMul dA
                (rectMatMul U (rectMatMul Y (matTranspose V)))) +
            frobNormRect
              (rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V)))
                dB)) := hsplit
    _ <= ((c * (1 + epsA) + epsA) * frobNormRect A +
          (c * (1 + epsB) + epsB) * frobNormRect B) *
          frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) := by
        nlinarith [t1, t2, t3]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308: source-numbered
    alias for the explicit-coefficient perturbed-Schur-factor residual
    guarantee. -/
alias H16_eq16_9_frobNormRect_sylvesterResidualRect_le_dataScale_of_perturbed_schur_factors_residual :=
  frobNormRect_sylvesterResidualRect_le_dataScale_of_perturbed_schur_factors_residual

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308: gamma-class
    fully-rounded-factor form of the overall Schur-method residual
    guarantee.

    The rounded quasi-triangular solve of equations (16.7)-(16.8)
    contributes a `gamma fp kSolve` coefficient (hypothesis `hres`; the
    module proving it is not yet available), and each computed Schur factor
    contributes a `gamma fp kFactor` normwise-relative backward
    perturbation of the ch19 Theorem 19.4 contract shape (hypotheses
    `hdA`/`hdB`; a QR-algorithm Schur backward-error theorem is not yet
    formalized).  By Higham's Lemma 3.3 composition rule
    (`gamma_sum_le`), the assembled coefficient stays in the same gamma
    class with the explicitly larger index `kSolve + kFactor`:
    `||C - (A Xhat - Xhat B)||_F <=
       gamma (kSolve + kFactor) (||A||_F + ||B||_F) ||Xhat||_F`.
    No claim is made that `kSolve + kFactor` matches the printed
    `gamma_tilde` integer. -/
theorem frobNormRect_sylvesterResidualRect_le_gamma_dataScale_of_rounded_schur_factors_residual
    (fp : FPModel) (kSolve kFactor : Nat)
    (m n : Nat) (U R A dA : RMatFn m m) (V S B dB : RMatFn n n)
    (C Y : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : forall i j,
      A i j + dA i j = rectMatMul U (rectMatMul R (matTranspose U)) i j)
    (hB : forall i j,
      B i j + dB i j = rectMatMul V (rectMatMul S (matTranspose V)) i j)
    (hdA : frobNormRect dA <= gamma fp kFactor * frobNormRect A)
    (hdB : frobNormRect dB <= gamma fp kFactor * frobNormRect B)
    (hvalid : gammaValid fp (kSolve + kFactor))
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <=
        gamma fp kSolve * (frobNormRect R + frobNormRect S) *
          frobNormRect Y) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V)))) <=
      gamma fp (kSolve + kFactor) *
        (frobNormRect A + frobNormRect B) *
        frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  have hcS : 0 <= gamma fp kSolve :=
    gamma_nonneg fp
      (gammaValid_mono fp (Nat.le_add_right kSolve kFactor) hvalid)
  have hC :=
    frobNormRect_sylvesterResidualRect_le_dataScale_of_perturbed_schur_factors_residual
      m n U R A dA V S B dB C Y
      (gamma fp kSolve) (gamma fp kFactor) (gamma fp kFactor)
      hU hV hA hB hdA hdB hcS hres
  have hsum :
      gamma fp kSolve + gamma fp kFactor +
          gamma fp kSolve * gamma fp kFactor <=
        gamma fp (kSolve + kFactor) :=
    gamma_sum_le fp kSolve kFactor hvalid
  have hz :
      0 <=
        (frobNormRect A + frobNormRect B) *
          frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) :=
    mul_nonneg
      (add_nonneg (frobNormRect_nonneg A) (frobNormRect_nonneg B))
      (frobNormRect_nonneg (rectMatMul U (rectMatMul Y (matTranspose V))))
  calc
    frobNormRect
        (sylvesterResidualRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V)))) <=
        ((gamma fp kSolve * (1 + gamma fp kFactor) + gamma fp kFactor) *
            frobNormRect A +
          (gamma fp kSolve * (1 + gamma fp kFactor) + gamma fp kFactor) *
            frobNormRect B) *
          frobNormRect
            (rectMatMul U (rectMatMul Y (matTranspose V))) := hC
    _ = (gamma fp kSolve + gamma fp kFactor +
          gamma fp kSolve * gamma fp kFactor) *
          ((frobNormRect A + frobNormRect B) *
            frobNormRect
              (rectMatMul U (rectMatMul Y (matTranspose V)))) := by
        ring
    _ <= gamma fp (kSolve + kFactor) *
          ((frobNormRect A + frobNormRect B) *
            frobNormRect
              (rectMatMul U (rectMatMul Y (matTranspose V)))) :=
        mul_le_mul_of_nonneg_right hsum hz
    _ = gamma fp (kSolve + kFactor) *
          (frobNormRect A + frobNormRect B) *
          frobNormRect
            (rectMatMul U (rectMatMul Y (matTranspose V))) := by
        ring

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308: source-numbered
    alias for the gamma-class fully-rounded-factor residual guarantee. -/
alias H16_eq16_9_frobNormRect_sylvesterResidualRect_le_gamma_dataScale_of_rounded_schur_factors_residual :=
  frobNormRect_sylvesterResidualRect_le_gamma_dataScale_of_rounded_schur_factors_residual

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308, with the
    Chapter 19 Theorem 19.4 coefficient: fully-rounded-factor Schur-method
    residual guarantee whose factor-perturbation hypotheses carry exactly
    the `H19.Theorem19_4.gamma_tilde` Householder QR backward-error
    coefficient proved in this repository
    (`H19.Theorem19_4.householder_qr_backward_error`, equation (19.11)).

    `gamma_tilde fp m m` unfolds to
    `gamma fp (m * householderConstructApplyGammaIndex m)`, so the
    assembled bound stays in the gamma class with index
    `kSolve + max (m * householderConstructApplyGammaIndex m)
                  (n * householderConstructApplyGammaIndex n)`.
    The perturbed-similarity hypotheses `hA`/`hB` themselves remain
    supplied data: Theorem 19.4 proves this contract for the one-sweep QR
    factorization `A + dA = Q Rhat`, while the QR-algorithm real-Schur
    similarity form is not yet formalized.  This wrapper documents and
    fixes the coefficient bookkeeping for that forthcoming composition. -/
theorem frobNormRect_sylvesterResidualRect_le_gamma_dataScale_of_theorem19_4_factor_coefficients
    (fp : FPModel) (kSolve : Nat)
    (m n : Nat) (U R A dA : RMatFn m m) (V S B dB : RMatFn n n)
    (C Y : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : forall i j,
      A i j + dA i j = rectMatMul U (rectMatMul R (matTranspose U)) i j)
    (hB : forall i j,
      B i j + dB i j = rectMatMul V (rectMatMul S (matTranspose V)) i j)
    (hdA : frobNormRect dA <=
      H19.Theorem19_4.gamma_tilde fp m m * frobNormRect A)
    (hdB : frobNormRect dB <=
      H19.Theorem19_4.gamma_tilde fp n n * frobNormRect B)
    (hvalid : gammaValid fp
      (kSolve +
        max (m * householderConstructApplyGammaIndex m)
          (n * householderConstructApplyGammaIndex n)))
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <=
        gamma fp kSolve * (frobNormRect R + frobNormRect S) *
          frobNormRect Y) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V)))) <=
      gamma fp
          (kSolve +
            max (m * householderConstructApplyGammaIndex m)
              (n * householderConstructApplyGammaIndex n)) *
        (frobNormRect A + frobNormRect B) *
        frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  have hvalidF :
      gammaValid fp
        (max (m * householderConstructApplyGammaIndex m)
          (n * householderConstructApplyGammaIndex n)) :=
    gammaValid_mono fp
      (Nat.le_add_left
        (max (m * householderConstructApplyGammaIndex m)
          (n * householderConstructApplyGammaIndex n)) kSolve)
      hvalid
  have hdA' :
      frobNormRect dA <=
        gamma fp
            (max (m * householderConstructApplyGammaIndex m)
              (n * householderConstructApplyGammaIndex n)) *
          frobNormRect A := by
    refine le_trans hdA ?_
    have hmono :
        H19.Theorem19_4.gamma_tilde fp m m <=
          gamma fp
            (max (m * householderConstructApplyGammaIndex m)
              (n * householderConstructApplyGammaIndex n)) := by
      simpa [H19.Theorem19_4.gamma_tilde] using
        gamma_mono fp
          (le_max_left (m * householderConstructApplyGammaIndex m)
            (n * householderConstructApplyGammaIndex n))
          hvalidF
    exact mul_le_mul_of_nonneg_right hmono (frobNormRect_nonneg A)
  have hdB' :
      frobNormRect dB <=
        gamma fp
            (max (m * householderConstructApplyGammaIndex m)
              (n * householderConstructApplyGammaIndex n)) *
          frobNormRect B := by
    refine le_trans hdB ?_
    have hmono :
        H19.Theorem19_4.gamma_tilde fp n n <=
          gamma fp
            (max (m * householderConstructApplyGammaIndex m)
              (n * householderConstructApplyGammaIndex n)) := by
      simpa [H19.Theorem19_4.gamma_tilde] using
        gamma_mono fp
          (le_max_right (m * householderConstructApplyGammaIndex m)
            (n * householderConstructApplyGammaIndex n))
          hvalidF
    exact mul_le_mul_of_nonneg_right hmono (frobNormRect_nonneg B)
  exact
    frobNormRect_sylvesterResidualRect_le_gamma_dataScale_of_rounded_schur_factors_residual
      fp kSolve
      (max (m * householderConstructApplyGammaIndex m)
        (n * householderConstructApplyGammaIndex n))
      m n U R A dA V S B dB C Y hU hV hA hB hdA' hdB' hvalid hres

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308:
    source-numbered alias for the fully-rounded-factor residual guarantee
    with Chapter 19 Theorem 19.4 factor-perturbation coefficients. -/
alias H16_eq16_9_frobNormRect_sylvesterResidualRect_le_gamma_dataScale_of_theorem19_4_factor_coefficients :=
  frobNormRect_sylvesterResidualRect_le_gamma_dataScale_of_theorem19_4_factor_coefficients

-- ============================================================
-- (16.9) assembly: rounded RHS transform and reconstruction budgets
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equations (16.5) and (16.9), p. 308:
    overall residual bound for the Schur method when the transformed
    right-hand side and the reconstructed solution are also computed
    quantities.

    `Dhat` is the computed Schur-coordinate right-hand side, within `eC`
    (Frobenius) of the exact transform `U^T C V`; `Xhat` is the computed
    reconstruction, within `eX` (Frobenius) of the exact product
    `U Y V^T`; `hres` is the rounded quasi-triangular solve residual bound
    of equations (16.7)-(16.8) against `Dhat` (the module proving it is
    not yet available, so it is an explicit hypothesis).  The conclusion
    keeps the exact-arithmetic scale `||Y||_F` and adds the two transform
    budgets additively; no hypothesis on the signs of `c`, `eC`, `eX` is
    needed.  See the companion
    `frobNormRect_sylvesterResidualRect_le_computedScale_of_schur_residual_with_transform_budgets`
    for the printed `||Xhat||_F`-scale display. -/
theorem frobNormRect_sylvesterResidualRect_le_of_schur_residual_with_transform_budgets
    (m n : Nat) (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Y Dhat Xhat : RMatFn m n) (c eC eX : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hDhat :
      frobNormRect
        (fun i j =>
          Dhat i j -
            rectMatMul (matTranspose U) (rectMatMul C V) i j) <= eC)
    (hXhat :
      frobNormRect
        (fun i j =>
          Xhat i j -
            rectMatMul U (rectMatMul Y (matTranspose V)) i j) <= eX)
    (hres :
      frobNormRect (sylvesterResidualRect m n R S Dhat Y) <=
        c * (frobNormRect R + frobNormRect S) * frobNormRect Y) :
    frobNormRect (sylvesterResidualRect m n A B C Xhat) <=
      c * (frobNormRect A + frobNormRect B) * frobNormRect Y +
        eC + (frobNormRect A + frobNormRect B) * eX := by
  have hnA : frobNormRect A = frobNormRect R :=
    frobNormRect_eq_of_orthogonal_similarity U R A hU hA
  have hnB : frobNormRect B = frobNormRect S :=
    frobNormRect_eq_of_orthogonal_similarity V S B hV hB
  -- Reconstruction split: residual at Xhat versus at the exact product.
  have hfunX :
      sylvesterResidualRect m n A B C Xhat =
        fun i j =>
          sylvesterResidualRect m n A B C
              (rectMatMul U (rectMatMul Y (matTranspose V))) i j -
            (rectMatMul A
                (fun a b =>
                  Xhat a b -
                    rectMatMul U (rectMatMul Y (matTranspose V)) a b) i j -
              rectMatMul
                (fun a b =>
                  Xhat a b -
                    rectMatMul U (rectMatMul Y (matTranspose V)) a b)
                B i j) := by
    ext i j
    have hL :
        rectMatMul A Xhat i j =
          rectMatMul A
              (rectMatMul U (rectMatMul Y (matTranspose V))) i j +
            rectMatMul A
              (fun a b =>
                Xhat a b -
                  rectMatMul U (rectMatMul Y (matTranspose V)) a b) i j := by
      unfold rectMatMul
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    have hR :
        rectMatMul Xhat B i j =
          rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V)))
              B i j +
            rectMatMul
              (fun a b =>
                Xhat a b -
                  rectMatMul U (rectMatMul Y (matTranspose V)) a b)
              B i j := by
      unfold rectMatMul
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    unfold sylvesterResidualRect sylvesterOpRect
    simp only [matMulRect_eq_rectMatMul]
    rw [hL, hR]
    ring
  -- Right-hand-side split in Schur coordinates.
  have hfunD :
      sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y =
        fun i j =>
          sylvesterResidualRect m n R S Dhat Y i j -
            (Dhat i j -
              rectMatMul (matTranspose U) (rectMatMul C V) i j) := by
    ext i j
    unfold sylvesterResidualRect
    ring
  -- Transport the exact-product residual and bound it.
  have hexact :
      frobNormRect
          (sylvesterResidualRect m n A B C
            (rectMatMul U (rectMatMul Y (matTranspose V)))) <=
        c * (frobNormRect A + frobNormRect B) * frobNormRect Y + eC := by
    have htrans :
        frobNormRect
            (sylvesterResidualRect m n A B C
              (rectMatMul U (rectMatMul Y (matTranspose V)))) =
          frobNormRect
            (sylvesterResidualRect m n R S
              (rectMatMul (matTranspose U) (rectMatMul C V)) Y) :=
      frobNormRect_sylvesterResidualRect_schur_transform m n U R A V S B
        C Y hU hV hA hB
    have hDsplit :
        frobNormRect
            (sylvesterResidualRect m n R S
              (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <=
          frobNormRect (sylvesterResidualRect m n R S Dhat Y) +
            frobNormRect
              (fun i j =>
                Dhat i j -
                  rectMatMul (matTranspose U) (rectMatMul C V) i j) := by
      rw [hfunD]
      exact
        frobNormRect_sub_le (sylvesterResidualRect m n R S Dhat Y)
          (fun i j =>
            Dhat i j -
              rectMatMul (matTranspose U) (rectMatMul C V) i j)
    rw [htrans, hnA, hnB]
    linarith
  -- Reconstruction cross terms.
  have hAE :
      frobNormRect
          (rectMatMul A
            (fun a b =>
              Xhat a b -
                rectMatMul U (rectMatMul Y (matTranspose V)) a b)) <=
        frobNormRect A * eX := by
    calc
      frobNormRect
          (rectMatMul A
            (fun a b =>
              Xhat a b -
                rectMatMul U (rectMatMul Y (matTranspose V)) a b)) <=
          frobNormRect A *
            frobNormRect
              (fun a b =>
                Xhat a b -
                  rectMatMul U (rectMatMul Y (matTranspose V)) a b) :=
        frobNormRect_rectMatMul_le A
          (fun a b =>
            Xhat a b - rectMatMul U (rectMatMul Y (matTranspose V)) a b)
      _ <= frobNormRect A * eX :=
        mul_le_mul_of_nonneg_left hXhat (frobNormRect_nonneg A)
  have hEB :
      frobNormRect
          (rectMatMul
            (fun a b =>
              Xhat a b -
                rectMatMul U (rectMatMul Y (matTranspose V)) a b) B) <=
        eX * frobNormRect B := by
    calc
      frobNormRect
          (rectMatMul
            (fun a b =>
              Xhat a b -
                rectMatMul U (rectMatMul Y (matTranspose V)) a b) B) <=
          frobNormRect
              (fun a b =>
                Xhat a b -
                  rectMatMul U (rectMatMul Y (matTranspose V)) a b) *
            frobNormRect B :=
        frobNormRect_rectMatMul_le
          (fun a b =>
            Xhat a b - rectMatMul U (rectMatMul Y (matTranspose V)) a b) B
      _ <= eX * frobNormRect B :=
        mul_le_mul_of_nonneg_right hXhat (frobNormRect_nonneg B)
  -- Assemble.
  have hXsplit :
      frobNormRect (sylvesterResidualRect m n A B C Xhat) <=
        frobNormRect
            (sylvesterResidualRect m n A B C
              (rectMatMul U (rectMatMul Y (matTranspose V)))) +
          (frobNormRect
              (rectMatMul A
                (fun a b =>
                  Xhat a b -
                    rectMatMul U (rectMatMul Y (matTranspose V)) a b)) +
            frobNormRect
              (rectMatMul
                (fun a b =>
                  Xhat a b -
                    rectMatMul U (rectMatMul Y (matTranspose V)) a b)
                B)) := by
    rw [hfunX]
    have h1 :=
      frobNormRect_sub_le
        (sylvesterResidualRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V))))
        (fun i j =>
          rectMatMul A
              (fun a b =>
                Xhat a b -
                  rectMatMul U (rectMatMul Y (matTranspose V)) a b) i j -
            rectMatMul
              (fun a b =>
                Xhat a b -
                  rectMatMul U (rectMatMul Y (matTranspose V)) a b)
              B i j)
    have h2 :=
      frobNormRect_sub_le
        (rectMatMul A
          (fun a b =>
            Xhat a b - rectMatMul U (rectMatMul Y (matTranspose V)) a b))
        (rectMatMul
          (fun a b =>
            Xhat a b - rectMatMul U (rectMatMul Y (matTranspose V)) a b)
          B)
    linarith
  linarith

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308:
    source-numbered alias for the transform-budget residual bound that keeps
    the exact Schur-coordinate `||Y||_F` scale. -/
alias H16_eq16_9_frobNormRect_sylvesterResidualRect_le_of_schur_residual_with_transform_budgets :=
  frobNormRect_sylvesterResidualRect_le_of_schur_residual_with_transform_budgets

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308: printed
    computed-solution-scale display of the transform-budget residual
    bound.  The exact-arithmetic scale `||Y||_F` of
    `frobNormRect_sylvesterResidualRect_le_of_schur_residual_with_transform_budgets`
    is relaxed to `||Xhat||_F + eX` for the computed reconstruction
    `Xhat`, which requires `0 <= c`.  All rounded ingredients ((16.7)-(16.8)
    solve residual, RHS-transform budget, reconstruction budget) remain
    explicit hypotheses documented in the primary theorem. -/
theorem frobNormRect_sylvesterResidualRect_le_computedScale_of_schur_residual_with_transform_budgets
    (m n : Nat) (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Y Dhat Xhat : RMatFn m n) (c eC eX : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hc : 0 <= c)
    (hDhat :
      frobNormRect
        (fun i j =>
          Dhat i j -
            rectMatMul (matTranspose U) (rectMatMul C V) i j) <= eC)
    (hXhat :
      frobNormRect
        (fun i j =>
          Xhat i j -
            rectMatMul U (rectMatMul Y (matTranspose V)) i j) <= eX)
    (hres :
      frobNormRect (sylvesterResidualRect m n R S Dhat Y) <=
        c * (frobNormRect R + frobNormRect S) * frobNormRect Y) :
    frobNormRect (sylvesterResidualRect m n A B C Xhat) <=
      c * (frobNormRect A + frobNormRect B) *
          (frobNormRect Xhat + eX) +
        eC + (frobNormRect A + frobNormRect B) * eX := by
  have hbase :=
    frobNormRect_sylvesterResidualRect_le_of_schur_residual_with_transform_budgets
      m n U R A V S B C Y Dhat Xhat c eC eX hU hV hA hB hDhat hXhat hres
  have hYle : frobNormRect Y <= frobNormRect Xhat + eX := by
    have h0 :
        frobNormRect Y =
          frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) :=
      (frobNormRect_orthogonal_conjugation_eq U Y V hU hV).symm
    have h1 :
        frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) <=
          frobNormRect Xhat +
            frobNormRect
              (fun i j =>
                Xhat i j -
                  rectMatMul U (rectMatMul Y (matTranspose V)) i j) := by
      calc
        frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V)))
            = frobNormRect
                (fun i j =>
                  Xhat i j -
                    (Xhat i j -
                      rectMatMul U
                        (rectMatMul Y (matTranspose V)) i j)) := by
              congr 1
              ext i j
              ring
        _ <= frobNormRect Xhat +
              frobNormRect
                (fun i j =>
                  Xhat i j -
                    rectMatMul U (rectMatMul Y (matTranspose V)) i j) :=
            frobNormRect_sub_le Xhat
              (fun i j =>
                Xhat i j -
                  rectMatMul U (rectMatMul Y (matTranspose V)) i j)
    linarith
  have hcoeff :
      0 <= c * (frobNormRect A + frobNormRect B) :=
    mul_nonneg hc
      (add_nonneg (frobNormRect_nonneg A) (frobNormRect_nonneg B))
  have hstep :
      c * (frobNormRect A + frobNormRect B) * frobNormRect Y <=
        c * (frobNormRect A + frobNormRect B) *
          (frobNormRect Xhat + eX) :=
    mul_le_mul_of_nonneg_left hYle hcoeff
  linarith

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), p. 308: source-numbered
    alias for the computed-solution-scale transform-budget residual
    display. -/
alias H16_eq16_9_frobNormRect_sylvesterResidualRect_le_computedScale_of_schur_residual_with_transform_budgets :=
  frobNormRect_sylvesterResidualRect_le_computedScale_of_schur_residual_with_transform_budgets

end Wave14

end NumStability
