-- Algorithms/Sylvester/Higham16RoundedTriangular.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 16.2, pp. 307-308, equations (16.7)-(16.8): the rounded
-- triangular-solve backward-error model for the vectorized Schur-form
-- Sylvester system, and its componentwise residual consequence.
--
-- Setting.  After the real Schur reduction (16.4)-(16.5), the transformed
-- Sylvester equation `R Z - Z S = C~` with upper-triangular factors `R`
-- (m x m) and `S` (n x n) is solved column by column by substitution
-- ((16.6)).  Higham observes that this whole process is the substitution
-- solve of one large `nm x nm` triangular linear system whose coefficient is
-- the vec/Kronecker matrix `P = I_n kron R - S^T kron I_m` of (16.2), and
-- that the standard Chapter 8 backward-error analysis (Theorem 8.5) of
-- substitution therefore applies:
--
--   (16.7)  (P + DeltaP) vec(Z^) = vec(C~),  |DeltaP| <= c_{m,n} u |P|,
--   (16.8)  |vec(C~) - P vec(Z^)| <= c_{m,n} u |P| |vec(Z^)|
--           (equivalently  |C~ - R Z^ + Z^ S| <= c_{m,n} u (|R||Z^| + |Z^||S|)).
--
-- This file proves exactly that instantiation:
--
-- * `sylvesterBackSubIndexEquiv` ranks the product index `(k, i)` (column
--   `k` of the unknown, row `i` inside the column) in the Bartels-Stewart
--   elimination order; under this ranking the vec/Kronecker coefficient of
--   the supplied triangular Schur-coordinate pair is genuinely upper
--   triangular (`sylvesterSchurBackSubCoeff_eq_zero_of_val_lt`), and its
--   diagonal entries are the eigenvalue differences `R_ii - S_kk`.
-- * `flSylvesterSchurBackSubSolveVec` is the computed solution: Chapter 8
--   floating-point back substitution (Algorithm 8.1, `fl_backSub`) applied
--   to the reordered vectorized system.  Back substitution processes the
--   reordered rows exactly in the Bartels-Stewart order (columns of `Z`
--   left to right, rows within a column bottom up).
-- * (16.7) is `sylvesterVecCoeff_triangular_backSub_backward_error`, an
--   instantiation of the Chapter 8 Theorem 8.5 endpoint
--   `backSub_backward_error`, transported through the index equivalence.
-- * (16.8) is derived in vectorized componentwise form
--   (`sylvesterVecCoeff_triangular_backSub_componentwise_residual`) and in
--   the printed matrix shape with the `|R||Z^| + |Z^||S|` budget
--   (`sylvesterResidualRect_triangular_backSub_componentwise_le`).
--
-- Honest scope:
-- * Schur factors are SUPPLIED (orthogonal `U`, `V` with upper-triangular
--   `R`, `S`), matching the printed setting, which assumes the Schur
--   decomposition has already been computed; errors in computing the Schur
--   factors and in forming `C~ = fl(U^T C V)` belong to the (16.9) overall
--   bound and are NOT asserted here.  The right-hand side `C~` is an
--   arbitrary supplied matrix, so it covers whatever transformed right-hand
--   side was computed upstream.
-- * The printed unspecified constant `c_{m,n} u` is realized as the explicit
--   same-gamma-class envelope `gamma_{nm} = nm*u/(1 - nm*u)` coming from the
--   Chapter 8 theorem on the `nm x nm` system.  We do not claim the printed
--   letter constant.
-- * The computed-solution model is the Chapter 8 dense back-substitution
--   loop: every superdiagonal entry of the reordered system participates in
--   the row recurrence, including the structural zeros of the Kronecker
--   coefficient.  The componentwise bound `|DeltaP| <= gamma_{nm} |P|`
--   forces the perturbation to vanish on that zero pattern, so the
--   backward-error conclusion is exactly the printed componentwise model.
-- * Only the strictly triangular (all 1x1 diagonal blocks) Schur case is
--   treated; the quasi-triangular 2x2-block variant of (16.7) remains open.

import NumStability.Algorithms.Sylvester.Higham16Spectrum
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Rev

namespace NumStability

namespace Wave14

open scoped BigOperators

-- ============================================================
-- The Bartels-Stewart elimination order on the product index
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equations (16.6)-(16.7): the
    Bartels-Stewart elimination order for the vectorized Schur-form Sylvester
    system.  The column-stacking product index `(k, i)` (column `k` of the
    transformed unknown, row `i` inside that column) is ranked by
    `i + m * (n - (k + 1))`, i.e. columns in increasing order and rows within
    a column from the bottom up, which is the order in which back
    substitution processes the reordered `nm x nm` system.  Under this
    ranking the vec/Kronecker coefficient of a supplied upper-triangular pair
    becomes genuinely upper triangular. -/
def sylvesterBackSubIndexEquiv (m n : Nat) :
    Prod (Fin n) (Fin m) ≃ Fin (n * m) :=
  (Equiv.prodCongr (Fin.revPerm : Equiv.Perm (Fin n))
    (Equiv.refl (Fin m))).trans finProdFinEquiv

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equations (16.6)-(16.7): explicit
    rank formula for the Bartels-Stewart elimination order.  The product
    index `(k, i)` is sent to `i + m * (n - (k + 1))`. -/
theorem sylvesterBackSubIndexEquiv_val (m n : Nat) (p : Prod (Fin n) (Fin m)) :
    (sylvesterBackSubIndexEquiv m n p).val =
      p.2.val + m * (n - (p.1.val + 1)) := rfl

/-- Higham, 2nd ed., Chapter 16.1, p. 306, equation (16.2): entrywise form of
    the vec/Kronecker Sylvester coefficient `I_n kron A - B^T kron I_m` on the
    column-stacking product index. -/
theorem sylvesterVecCoeff_pair_apply (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (p q : Prod (Fin n) (Fin m)) :
    sylvesterVecCoeff m n A B p q =
      (if p.1 = q.1 then A p.2 q.2 else 0) -
        (if p.2 = q.2 then B q.1 p.1 else 0) := by
  by_cases hp : p.1 = q.1 <;> by_cases hq : p.2 = q.2 <;>
    simp [sylvesterVecCoeff, Matrix.kronecker, Matrix.transpose_apply,
      Matrix.one_apply, hp, hq]

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equations (16.4)-(16.7):
    zero-pattern lemma for the Bartels-Stewart order.  If both supplied
    Schur-coordinate factors are upper triangular and the elimination rank of
    the product index `q` is strictly below that of `p`, then the
    vec/Kronecker coefficient entry at `(p, q)` vanishes.  This is the
    structural fact that makes the reordered vectorized system of (16.7) an
    upper-triangular linear system. -/
theorem sylvesterVecCoeff_eq_zero_of_rank_lt (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (hR : IsUpperTriangularFn m R) (hS : IsUpperTriangularFn n S)
    (p q : Prod (Fin n) (Fin m))
    (hlt : q.2.val + m * (n - (q.1.val + 1)) <
      p.2.val + m * (n - (p.1.val + 1))) :
    sylvesterVecCoeff m n R S p q = 0 := by
  rw [sylvesterVecCoeff_pair_apply]
  by_cases hkl : p.1 = q.1
  · have hprod : m * (n - (q.1.val + 1)) = m * (n - (p.1.val + 1)) := by
      rw [hkl]
    rw [hprod] at hlt
    have hji : q.2.val < p.2.val := lt_of_add_lt_add_right hlt
    have hRz : R p.2 q.2 = 0 := hR p.2 q.2 (Fin.lt_def.mpr hji)
    have hne : ¬(p.2 = q.2) := by
      intro h
      rw [h] at hji
      exact lt_irrefl _ hji
    simp [hkl, hRz, hne]
  · by_cases hij : p.2 = q.2
    · rw [hij] at hlt
      have hprodlt : m * (n - (q.1.val + 1)) < m * (n - (p.1.val + 1)) :=
        lt_of_add_lt_add_left hlt
      have hcol : n - (q.1.val + 1) < n - (p.1.val + 1) :=
        lt_of_mul_lt_mul_left hprodlt (Nat.zero_le m)
      have hkq : p.1.val < q.1.val := by
        have h1 := p.1.isLt
        have h2 := q.1.isLt
        omega
      have hSz : S q.1 p.1 = 0 := hS q.1 p.1 (Fin.lt_def.mpr hkq)
      simp [hkl, hij, hSz]
    · simp [hkl, hij]

-- ============================================================
-- The reordered nm x nm triangular system of (16.7)
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.7): the reordered
    `nm x nm` coefficient array of the vectorized Schur-form Sylvester
    system.  Row/column `a` of this array is the vec/Kronecker coefficient
    `I_n kron R - S^T kron I_m` of (16.2) read at the product indices of
    Bartels-Stewart elimination rank `a`. -/
noncomputable def sylvesterSchurBackSubCoeff (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) :
    Fin (n * m) → Fin (n * m) → Real :=
  fun a b =>
    sylvesterVecCoeff m n R S
      ((sylvesterBackSubIndexEquiv m n).symm a)
      ((sylvesterBackSubIndexEquiv m n).symm b)

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.7): the reordered
    right-hand side of the vectorized Schur-form system, i.e. `vec(C~)` read
    at the product index of elimination rank `a`. -/
noncomputable def sylvesterSchurBackSubRhs (m n : Nat) (Ct : RMatFn m n) :
    Fin (n * m) → Real :=
  fun a => Matrix.vec Ct ((sylvesterBackSubIndexEquiv m n).symm a)

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.7): reading the
    reordered coefficient array at the images of two product indices recovers
    the vec/Kronecker coefficient entry. -/
theorem sylvesterSchurBackSubCoeff_reindex (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (p q : Prod (Fin n) (Fin m)) :
    sylvesterSchurBackSubCoeff m n R S
        (sylvesterBackSubIndexEquiv m n p) (sylvesterBackSubIndexEquiv m n q) =
      sylvesterVecCoeff m n R S p q := by
  unfold sylvesterSchurBackSubCoeff
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.7): reading the
    reordered right-hand side at the image of a product index recovers the
    corresponding entry of `vec(C~)`. -/
theorem sylvesterSchurBackSubRhs_reindex (m n : Nat) (Ct : RMatFn m n)
    (p : Prod (Fin n) (Fin m)) :
    sylvesterSchurBackSubRhs m n Ct (sylvesterBackSubIndexEquiv m n p) =
      Matrix.vec Ct p := by
  unfold sylvesterSchurBackSubRhs
  rw [Equiv.symm_apply_apply]

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equations (16.4)-(16.7): under
    supplied upper-triangular Schur-coordinate factors, the reordered
    `nm x nm` coefficient array is upper triangular in the standard sense
    required by the Chapter 8 substitution analysis. -/
theorem sylvesterSchurBackSubCoeff_eq_zero_of_val_lt (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (hR : IsUpperTriangularFn m R) (hS : IsUpperTriangularFn n S) :
    ∀ a b : Fin (n * m), b.val < a.val →
      sylvesterSchurBackSubCoeff m n R S a b = 0 := by
  intro a b hab
  unfold sylvesterSchurBackSubCoeff
  apply sylvesterVecCoeff_eq_zero_of_rank_lt m n R S hR hS
  rw [← sylvesterBackSubIndexEquiv_val m n
      ((sylvesterBackSubIndexEquiv m n).symm a),
    ← sylvesterBackSubIndexEquiv_val m n
      ((sylvesterBackSubIndexEquiv m n).symm b),
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact hab

/-- Higham, 2nd ed., Chapter 16.1-16.2, pp. 306-307, equations (16.3) and
    (16.7): the diagonal of the reordered coefficient array consists of the
    eigenvalue differences `R_ii - S_kk` of the triangular factors. -/
theorem sylvesterSchurBackSubCoeff_diag (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (a : Fin (n * m)) :
    sylvesterSchurBackSubCoeff m n R S a a =
      R ((sylvesterBackSubIndexEquiv m n).symm a).2
          ((sylvesterBackSubIndexEquiv m n).symm a).2 -
        S ((sylvesterBackSubIndexEquiv m n).symm a).1
          ((sylvesterBackSubIndexEquiv m n).symm a).1 := by
  unfold sylvesterSchurBackSubCoeff
  rw [sylvesterVecCoeff_pair_apply]
  simp

/-- Higham, 2nd ed., Chapter 16.1-16.2, pp. 306-307, equations (16.3) and
    (16.7): diagonal-entry separation `R_ii ≠ S_kk` of the supplied
    triangular factors makes every diagonal entry of the reordered
    coefficient array nonzero, which is the solvability hypothesis of the
    Chapter 8 substitution analysis. -/
theorem sylvesterSchurBackSubCoeff_diag_ne_zero (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (hsep : ∀ (i : Fin m) (k : Fin n), R i i ≠ S k k) :
    ∀ a : Fin (n * m), sylvesterSchurBackSubCoeff m n R S a a ≠ 0 := by
  intro a
  rw [sylvesterSchurBackSubCoeff_diag]
  exact sub_ne_zero_of_ne (hsep _ _)

-- ============================================================
-- The computed solution: Chapter 8 back substitution on the big system
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equations (16.6)-(16.7): the
    computed vectorized solution of the Schur-form Sylvester system, modeled
    as Chapter 8 floating-point back substitution (Algorithm 8.1,
    `fl_backSub`) applied to the reordered `nm x nm` triangular system.
    Back substitution processes the reordered rows exactly in the
    Bartels-Stewart order: columns of the unknown from left to right, rows
    within a column from the bottom up. -/
noncomputable def flSylvesterSchurBackSubSolveVec (fp : FPModel) (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n) :
    Prod (Fin n) (Fin m) → Real :=
  fun p =>
    fl_backSub fp (n * m) (sylvesterSchurBackSubCoeff m n R S)
      (sylvesterSchurBackSubRhs m n Ct) (sylvesterBackSubIndexEquiv m n p)

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equations (16.6)-(16.7): the
    computed Schur-coordinate solution matrix, i.e. the un-vectorized form of
    `flSylvesterSchurBackSubSolveVec`. -/
noncomputable def flSylvesterSchurBackSubSolve (fp : FPModel) (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n) : RMatFn m n :=
  fun i k => flSylvesterSchurBackSubSolveVec fp m n R S Ct (k, i)

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.7): column-stacking
    the computed Schur-coordinate solution matrix recovers the computed
    vectorized solution. -/
theorem vec_flSylvesterSchurBackSubSolve (fp : FPModel) (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n) :
    Matrix.vec (flSylvesterSchurBackSubSolve fp m n R S Ct) =
      flSylvesterSchurBackSubSolveVec fp m n R S Ct := rfl

-- ============================================================
-- (16.7): rounded triangular-solve backward error
-- ============================================================

/-- **Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.7)** (supplied
    triangular Schur-coordinate factors).  The computed vectorized solution
    `x^ = flSylvesterSchurBackSubSolveVec` of the Schur-form Sylvester system
    — Chapter 8 back substitution applied to the reordered vec/Kronecker
    system — satisfies the exactly perturbed system

    `(P + DeltaP) x^ = vec(C~)` with `|DeltaP| <= gamma_{nm} |P|`

    componentwise, where `P = I_n kron R - S^T kron I_m` is the (16.2)
    coefficient of the triangular pair.  This instantiates the Chapter 8
    Theorem 8.5 endpoint `backSub_backward_error` on the vectorized Schur
    system; the printed unspecified constant `c_{m,n} u` is realized as the
    same-gamma-class envelope `gamma_{nm}`, and the diagonal separation
    hypothesis `R_ii ≠ S_kk` is the nonsingularity of the triangular system
    assumed by the printed analysis.  Errors from computing the Schur factors
    or the transformed right-hand side are not modeled here (they belong to
    (16.9)); `C~` is an arbitrary supplied right-hand side. -/
theorem sylvesterVecCoeff_triangular_backSub_backward_error
    (fp : FPModel) (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n)
    (hR : IsUpperTriangularFn m R) (hS : IsUpperTriangularFn n S)
    (hsep : ∀ (i : Fin m) (k : Fin n), R i i ≠ S k k)
    (hgv : gammaValid fp (n * m)) :
    ∃ ΔP : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real,
      (∀ p q, |ΔP p q| ≤ gamma fp (n * m) * |sylvesterVecCoeff m n R S p q|) ∧
      Matrix.mulVec (sylvesterVecCoeff m n R S + ΔP)
          (flSylvesterSchurBackSubSolveVec fp m n R S Ct) =
        Matrix.vec Ct := by
  obtain ⟨ΔT, hΔTbound, hΔTeq⟩ :=
    backSub_backward_error fp (n * m)
      (sylvesterSchurBackSubCoeff m n R S)
      (sylvesterSchurBackSubRhs m n Ct)
      (sylvesterSchurBackSubCoeff_diag_ne_zero m n R S hsep)
      (sylvesterSchurBackSubCoeff_eq_zero_of_val_lt m n R S hR hS)
      hgv
  refine ⟨fun p q =>
    ΔT (sylvesterBackSubIndexEquiv m n p) (sylvesterBackSubIndexEquiv m n q),
    ?_, ?_⟩
  · intro p q
    have hb := hΔTbound (sylvesterBackSubIndexEquiv m n p)
      (sylvesterBackSubIndexEquiv m n q)
    rw [sylvesterSchurBackSubCoeff_reindex] at hb
    exact hb
  · funext p
    have hrow := hΔTeq (sylvesterBackSubIndexEquiv m n p)
    rw [sylvesterSchurBackSubRhs_reindex] at hrow
    rw [← hrow]
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply]
    refine Fintype.sum_equiv (sylvesterBackSubIndexEquiv m n) _ _ ?_
    intro q
    rw [sylvesterSchurBackSubCoeff_reindex]
    rfl

-- ============================================================
-- (16.8): componentwise residual consequence
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.7)-(16.8): the
    generic implication from the componentwise perturbed-system certificate to
    the componentwise residual bound.  If `(P + DeltaP) x = c` with
    `|DeltaP| <= g |P|` componentwise, then
    `|c - P x| <= g (|P| |x|)` componentwise. -/
theorem componentwise_residual_of_perturbed_mulVec {ι : Type} [Fintype ι]
    (P ΔP : Matrix ι ι Real) (x c : ι → Real) (g : Real)
    (hbound : ∀ p q, |ΔP p q| ≤ g * |P p q|)
    (heq : Matrix.mulVec (P + ΔP) x = c) (p : ι) :
    |c p - Matrix.mulVec P x p| ≤ g * ∑ q, |P p q| * |x q| := by
  have hdiff : c p - Matrix.mulVec P x p = ∑ q, ΔP p q * x q := by
    have h1 := congrFun heq p
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply] at h1
    simp only [Matrix.mulVec, dotProduct]
    rw [← h1, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  rw [abs_mul]
  calc |ΔP p q| * |x q| ≤ (g * |P p q|) * |x q| :=
        mul_le_mul_of_nonneg_right (hbound p q) (abs_nonneg _)
    _ = g * (|P p q| * |x q|) := by ring

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8)** (supplied
    triangular Schur-coordinate factors, vectorized componentwise form).  The
    computed vectorized solution of the Schur-form Sylvester system satisfies

    `|vec(C~) - P x^| <= gamma_{nm} (|P| |x^|)`

    componentwise, the residual consequence of the (16.7) backward-error
    model.  The printed constant `c_{m,n} u` is realized as the
    same-gamma-class envelope `gamma_{nm}`. -/
theorem sylvesterVecCoeff_triangular_backSub_componentwise_residual
    (fp : FPModel) (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n)
    (hR : IsUpperTriangularFn m R) (hS : IsUpperTriangularFn n S)
    (hsep : ∀ (i : Fin m) (k : Fin n), R i i ≠ S k k)
    (hgv : gammaValid fp (n * m)) (p : Prod (Fin n) (Fin m)) :
    |Matrix.vec Ct p -
        Matrix.mulVec (sylvesterVecCoeff m n R S)
          (flSylvesterSchurBackSubSolveVec fp m n R S Ct) p| ≤
      gamma fp (n * m) *
        ∑ q, |sylvesterVecCoeff m n R S p q| *
          |flSylvesterSchurBackSubSolveVec fp m n R S Ct q| := by
  obtain ⟨ΔP, hbound, heq⟩ :=
    sylvesterVecCoeff_triangular_backSub_backward_error
      fp m n R S Ct hR hS hsep hgv
  exact componentwise_residual_of_perturbed_mulVec
    (sylvesterVecCoeff m n R S) ΔP
    (flSylvesterSchurBackSubSolveVec fp m n R S Ct)
    (Matrix.vec Ct) (gamma fp (n * m)) hbound heq p

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8): the
    componentwise row action of `|P| = |I_n kron A - B^T kron I_m|` is
    dominated by the un-vectorized budget
    `(|A| |X|)_{ik} + (|X| |B|)_{ik}`; this is the bridge from the vectorized
    bound `|P| |vec X|` to the printed matrix form
    `|A||X| + |X||B|` of the (16.8) right-hand side. -/
theorem sylvesterVecCoeff_abs_row_action_le (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (x : Prod (Fin n) (Fin m) → Real) (p : Prod (Fin n) (Fin m)) :
    ∑ q : Prod (Fin n) (Fin m), |sylvesterVecCoeff m n A B p q| * |x q| ≤
      (∑ j : Fin m, |A p.2 j| * |x (p.1, j)|) +
        ∑ l : Fin n, |B l p.1| * |x (l, p.2)| := by
  have habs : ∀ a b : Real, |a - b| ≤ |a| + |b| := fun a b => by
    simpa [sub_eq_add_neg] using abs_add_le a (-b)
  have hterm : ∀ q : Prod (Fin n) (Fin m),
      |sylvesterVecCoeff m n A B p q| * |x q| ≤
        (if p.1 = q.1 then |A p.2 q.2| else 0) * |x q| +
          (if p.2 = q.2 then |B q.1 p.1| else 0) * |x q| := by
    intro q
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg (x q))
    rw [sylvesterVecCoeff_pair_apply]
    refine le_trans (habs _ _) (le_of_eq ?_)
    congr 1
    · by_cases hp : p.1 = q.1 <;> simp [hp]
    · by_cases hq : p.2 = q.2 <;> simp [hq]
  refine le_trans (Finset.sum_le_sum fun q _ => hterm q) ?_
  rw [Finset.sum_add_distrib]
  apply add_le_add
  · apply le_of_eq
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single p.1]
    · simp
    · intro l _ hl
      apply Finset.sum_eq_zero
      intro j _
      simp [Ne.symm hl]
    · intro habs'
      exact absurd (Finset.mem_univ p.1) habs'
  · apply le_of_eq
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_eq_single p.2]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro habs'
      exact absurd (Finset.mem_univ p.2) habs'

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8)** (supplied
    triangular Schur-coordinate factors, printed matrix form).  The computed
    Schur-coordinate solution `Z^ = flSylvesterSchurBackSubSolve` satisfies
    the componentwise residual bound

    `|C~ - R Z^ + Z^ S| <= gamma_{nm} (|R| |Z^| + |Z^| |S|)`

    entrywise, the un-vectorized form of the (16.8) consequence of the
    (16.7) backward-error model.  The printed constant `c_{m,n} u` is
    realized as the same-gamma-class envelope `gamma_{nm}`. -/
theorem sylvesterResidualRect_triangular_backSub_componentwise_le
    (fp : FPModel) (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n)
    (hR : IsUpperTriangularFn m R) (hS : IsUpperTriangularFn n S)
    (hsep : ∀ (i : Fin m) (k : Fin n), R i i ≠ S k k)
    (hgv : gammaValid fp (n * m)) (i : Fin m) (k : Fin n) :
    |sylvesterResidualRect m n R S Ct
        (flSylvesterSchurBackSubSolve fp m n R S Ct) i k| ≤
      gamma fp (n * m) *
        (matMulRect m m n (fun a b => |R a b|)
            (fun a b => |flSylvesterSchurBackSubSolve fp m n R S Ct a b|) i k +
          matMulRect m n n
            (fun a b => |flSylvesterSchurBackSubSolve fp m n R S Ct a b|)
            (fun a b => |S a b|) i k) := by
  have hvec :=
    sylvesterVecCoeff_triangular_backSub_componentwise_residual
      fp m n R S Ct hR hS hsep hgv (k, i)
  rw [← vec_flSylvesterSchurBackSubSolve fp m n R S Ct] at hvec
  rw [sylvesterVecCoeff_mulVec_vec m n R S
    (flSylvesterSchurBackSubSolve fp m n R S Ct)] at hvec
  refine le_trans hvec ?_
  refine mul_le_mul_of_nonneg_left ?_ (gamma_nonneg fp hgv)
  refine le_trans (sylvesterVecCoeff_abs_row_action_le m n R S
    (Matrix.vec (flSylvesterSchurBackSubSolve fp m n R S Ct)) (k, i)) ?_
  refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · show (∑ j : Fin m, |R i j| *
        |Matrix.vec (flSylvesterSchurBackSubSolve fp m n R S Ct) (k, j)|) =
      ∑ j : Fin m, |R i j| * |flSylvesterSchurBackSubSolve fp m n R S Ct j k|
    rfl
  · show (∑ l : Fin n, |S l k| *
        |Matrix.vec (flSylvesterSchurBackSubSolve fp m n R S Ct) (l, i)|) =
      ∑ l : Fin n, |flSylvesterSchurBackSubSolve fp m n R S Ct i l| * |S l k|
    apply Finset.sum_congr rfl
    intro l _
    exact mul_comm _ _

-- ============================================================
-- Bridges to the house shifted-determinant certificates
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.6): an
    upper-triangular factor makes each shifted column coefficient `R - t I`
    upper triangular in the Mathlib block-triangular sense. -/
theorem sylvesterTriangularShiftedCoeff_blockTriangular (m : Nat)
    (R : RMatFn m m) (t : Real) (hR : IsUpperTriangularFn m R) :
    (sylvesterTriangularShiftedCoeff m R t).BlockTriangular id := by
  intro a b hba
  have hab : R a b = 0 := hR a b hba
  have hne : ¬(a = b) := by
    intro h
    subst h
    exact lt_irrefl _ hba
  simp [sylvesterTriangularShiftedCoeff, hab, hne]

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.6): diagonal entry of
    the shifted column coefficient `R - t I`. -/
theorem sylvesterTriangularShiftedCoeff_diag_apply (m : Nat)
    (R : RMatFn m m) (t : Real) (i : Fin m) :
    sylvesterTriangularShiftedCoeff m R t i i = R i i - t := by
  simp [sylvesterTriangularShiftedCoeff]

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equations (16.6)-(16.7): for an
    upper-triangular factor, nonsingularity of the shifted column coefficient
    `R - t I` forces every diagonal entry `R_ii` away from the shift `t`.
    This converts the house per-column determinant certificates into the
    diagonal separation used by the rounded substitution analysis. -/
theorem upperTriangularFn_diag_ne_of_shifted_det_ne_zero (m : Nat)
    (R : RMatFn m m) (t : Real) (hR : IsUpperTriangularFn m R)
    (hdet : ¬ Matrix.det (sylvesterTriangularShiftedCoeff m R t) = 0) :
    ∀ i : Fin m, R i i ≠ t := by
  intro i hri
  apply hdet
  rw [Matrix.det_of_upperTriangular
    (sylvesterTriangularShiftedCoeff_blockTriangular m R t hR)]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [sylvesterTriangularShiftedCoeff_diag_apply, hri, sub_self]

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equations (16.6)-(16.7): converse
    bridge; for an upper-triangular factor, diagonal separation from the
    shift makes the shifted column coefficient nonsingular. -/
theorem shifted_det_ne_zero_of_upperTriangularFn_diag_ne (m : Nat)
    (R : RMatFn m m) (t : Real) (hR : IsUpperTriangularFn m R)
    (hne : ∀ i : Fin m, R i i ≠ t) :
    ¬ Matrix.det (sylvesterTriangularShiftedCoeff m R t) = 0 := by
  rw [Matrix.det_of_upperTriangular
    (sylvesterTriangularShiftedCoeff_blockTriangular m R t hR)]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  rw [sylvesterTriangularShiftedCoeff_diag_apply]
  exact sub_ne_zero_of_ne (hne i)

-- ============================================================
-- Supplied Schur-factor wrappers
-- ============================================================

/-- **Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.7)** (supplied
    Schur-factor form).  Given supplied real Schur data for both sides —
    orthogonal `U`, `V` with `A = U R U^T`, `B = V S V^T`, upper-triangular
    `R`, `S` — and the house per-column shifted determinant certificates,
    the computed vectorized solution of the Schur-coordinate system
    satisfies the printed rounded triangular-solve backward-error model
    `(P + DeltaP) x^ = vec(C~)`, `|DeltaP| <= gamma_{nm} |P|` with
    `P = I_n kron R - S^T kron I_m`.  The factors are supplied exactly, as in
    the printed setting, which assumes the Schur decomposition has been
    computed; `C~` is the (already computed) transformed right-hand side.
    The printed constant `c_{m,n} u` is realized as the same-gamma-class
    envelope `gamma_{nm}`. -/
theorem sylvesterVecCoeff_schurTriangular_backSub_backward_error
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (Ct : RMatFn m n)
    (_hU : IsOrthogonal m U) (_hV : IsOrthogonal n V)
    (_hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (_hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hR : IsUpperTriangularFn m R) (hS : IsUpperTriangularFn n S)
    (hshift : ∀ k : Fin n,
      ¬ Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)
    (hgv : gammaValid fp (n * m)) :
    ∃ ΔP : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real,
      (∀ p q, |ΔP p q| ≤ gamma fp (n * m) * |sylvesterVecCoeff m n R S p q|) ∧
      Matrix.mulVec (sylvesterVecCoeff m n R S + ΔP)
          (flSylvesterSchurBackSubSolveVec fp m n R S Ct) =
        Matrix.vec Ct :=
  sylvesterVecCoeff_triangular_backSub_backward_error fp m n R S Ct hR hS
    (fun i k =>
      upperTriangularFn_diag_ne_of_shifted_det_ne_zero m R (S k k) hR
        (hshift k) i)
    hgv

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8)** (supplied
    Schur-factor form, vectorized).  Under the same supplied Schur data as
    the (16.7) wrapper, the computed vectorized solution satisfies the
    componentwise residual bound `|vec(C~) - P x^| <= gamma_{nm} (|P| |x^|)`. -/
theorem sylvesterVecCoeff_schurTriangular_backSub_componentwise_residual
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (Ct : RMatFn m n)
    (_hU : IsOrthogonal m U) (_hV : IsOrthogonal n V)
    (_hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (_hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hR : IsUpperTriangularFn m R) (hS : IsUpperTriangularFn n S)
    (hshift : ∀ k : Fin n,
      ¬ Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)
    (hgv : gammaValid fp (n * m)) (p : Prod (Fin n) (Fin m)) :
    |Matrix.vec Ct p -
        Matrix.mulVec (sylvesterVecCoeff m n R S)
          (flSylvesterSchurBackSubSolveVec fp m n R S Ct) p| ≤
      gamma fp (n * m) *
        ∑ q, |sylvesterVecCoeff m n R S p q| *
          |flSylvesterSchurBackSubSolveVec fp m n R S Ct q| :=
  sylvesterVecCoeff_triangular_backSub_componentwise_residual fp m n R S Ct
    hR hS
    (fun i k =>
      upperTriangularFn_diag_ne_of_shifted_det_ne_zero m R (S k k) hR
        (hshift k) i)
    hgv p

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8)** (supplied
    Schur-factor form, printed matrix shape).  Under the same supplied Schur
    data as the (16.7) wrapper, the computed Schur-coordinate solution `Z^`
    satisfies `|C~ - R Z^ + Z^ S| <= gamma_{nm} (|R| |Z^| + |Z^| |S|)`
    entrywise. -/
theorem sylvesterResidualRect_schurTriangular_backSub_componentwise_le
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (Ct : RMatFn m n)
    (_hU : IsOrthogonal m U) (_hV : IsOrthogonal n V)
    (_hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (_hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hR : IsUpperTriangularFn m R) (hS : IsUpperTriangularFn n S)
    (hshift : ∀ k : Fin n,
      ¬ Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)
    (hgv : gammaValid fp (n * m)) (i : Fin m) (k : Fin n) :
    |sylvesterResidualRect m n R S Ct
        (flSylvesterSchurBackSubSolve fp m n R S Ct) i k| ≤
      gamma fp (n * m) *
        (matMulRect m m n (fun a b => |R a b|)
            (fun a b => |flSylvesterSchurBackSubSolve fp m n R S Ct a b|) i k +
          matMulRect m n n
            (fun a b => |flSylvesterSchurBackSubSolve fp m n R S Ct a b|)
            (fun a b => |S a b|) i k) :=
  sylvesterResidualRect_triangular_backSub_componentwise_le fp m n R S Ct
    hR hS
    (fun i' k' =>
      upperTriangularFn_diag_ne_of_shifted_det_ne_zero m R (S k' k') hR
        (hshift k') i')
    hgv i k

-- ============================================================
-- Source-numbered aliases
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.7): source-numbered
    alias for the raw triangular-solve backward-error model of the vectorized
    Sylvester system. -/
alias H16_eq16_7_sylvesterVecCoeff_triangular_backSub_backward_error :=
  sylvesterVecCoeff_triangular_backSub_backward_error

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8):
    source-numbered alias for the raw vectorized componentwise residual
    consequence of the (16.7) backward-error model. -/
alias H16_eq16_8_sylvesterVecCoeff_triangular_backSub_componentwise_residual :=
  sylvesterVecCoeff_triangular_backSub_componentwise_residual

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8):
    source-numbered alias for the raw printed matrix form
    `|C~ - R Z^ + Z^ S| <= gamma_{nm} (|R||Z^| + |Z^||S|)` of the
    componentwise residual consequence. -/
alias H16_eq16_8_sylvesterResidualRect_triangular_backSub_componentwise_le :=
  sylvesterResidualRect_triangular_backSub_componentwise_le

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.7): source-numbered
    alias for the supplied Schur-factor rounded triangular-solve
    backward-error model of the vectorized Sylvester system. -/
alias H16_eq16_7_sylvesterVecCoeff_schurTriangular_backSub_backward_error :=
  sylvesterVecCoeff_schurTriangular_backSub_backward_error

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8):
    source-numbered alias for the vectorized componentwise residual
    consequence of the (16.7) backward-error model. -/
alias H16_eq16_8_sylvesterVecCoeff_schurTriangular_backSub_componentwise_residual :=
  sylvesterVecCoeff_schurTriangular_backSub_componentwise_residual

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8):
    source-numbered alias for the printed matrix form
    `|C~ - R Z^ + Z^ S| <= gamma_{nm} (|R||Z^| + |Z^||S|)` of the
    componentwise residual consequence. -/
alias H16_eq16_8_sylvesterResidualRect_schurTriangular_backSub_componentwise_le :=
  sylvesterResidualRect_schurTriangular_backSub_componentwise_le

end Wave14

end NumStability
