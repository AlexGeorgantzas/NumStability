-- Algorithms/Sylvester/Higham16QuasiQuasiRounded.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 16.2, pp. 307-308, equations (16.6)-(16.8), fully quasi-triangular
-- (real Schur) variant: the rounded block-substitution backward-error model
-- for the vectorized Schur-form Sylvester system when BOTH Schur factors are
-- quasi-upper-triangular -- the left factor `R` with adjacent 2 x 2 diagonal
-- ROW blocks marked by `dblR`, the right factor `S` with adjacent 2 x 2
-- diagonal COLUMN blocks marked by `dblS`.  This is the full real-Schur
-- generality of the printed Bartels-Stewart algorithm on p. 308.
--
-- Setting.  Wave 14 proved (16.7)-(16.8) for the strictly triangular pair;
-- Wave 15 proved the mixed case (quasi-triangular `R`, triangular `S`),
-- where the 2 x 2 blocks of `R` couple ADJACENT ranks in one unknown column
-- and the printed substitution needs only a rounded 2 x 2 kernel.  A 2 x 2
-- block of `S` at columns `(k, k+1)` instead couples the two unknown COLUMNS
-- at rank distance `m`, so the fully quasi-quasi case needs the INTERLEAVED
-- two-column elimination ordering: within a coupled column pair the two
-- unknown columns are interleaved row by row, and the reordered vec/Kronecker
-- coefficient `P = I_n kron R - S^T kron I_m` of (16.2) becomes block upper
-- triangular with diagonal blocks of size
--
--   1  (scalar row of `R`  x  singleton column of `S`),
--   2  (2 x 2 block of `R` x  singleton column of `S`; the Wave-15 blocks),
--   2  (scalar row of `R`  x  2 x 2 block of `S`; the two coupled columns),
--   4  (2 x 2 block of `R` x  2 x 2 block of `S`),
--
-- exactly the systems of order <= 4 the printed algorithm solves by Gaussian
-- elimination (Higham, p. 308).  This file supplies the rounded chain in
-- three layers:
--
-- * `flGESolve` is the rounded small-system Gaussian-elimination kernel,
--   parametric in the system size: GE WITHOUT pivoting in the Chapter 9
--   convention (eliminate the first column, recurse on the rounded Schur
--   complement, back-substitute the head row by a rounded subtraction fold
--   and division).  `flGESolve_backward_error` is its componentwise backward
--   error, the small-`n` analogue of Chapter 9 Theorems 9.3-9.4: under the
--   honest completion certificates (`flGEPivots`, every computed pivot
--   nonzero) the computed solution solves an exactly perturbed system with
--   `|DeltaM| <= gamma_{5n} * flGEBudget` entrywise, where `flGEBudget` is
--   the explicit `|L^||U^|`-shaped elimination budget in COMPUTED quantities
--   (multipliers and rounded Schur complements).  GE is not componentwise
--   backward stable relative to `|M|` alone, so the budget cannot be dropped
--   without a growth certificate; the fully componentwise form
--   (`flGESolve_backward_error_componentwise`) takes the standard budget
--   domination `flGEBudget <= (1 + rho) |M|` as an explicit hypothesis.
--   At size 2 the kernel is definitionally the Wave-15 `fl_solve2x2`
--   elimination schedule.
-- * `flPartitionBackSub` is the rounded block back substitution over an
--   arbitrary interval block partition (`IsBlockPartitionFn`) of an `N x N`
--   block upper-triangular system, every diagonal block solved by the
--   `flGESolve` kernel and every row folded by the Chapter 8 rounded
--   subtraction fold; `flPartitionBackSub_backward_error` is the block
--   analogue of Theorem 8.5 with the uniform envelope `gamma_{N + 5*B}`
--   (`B` a bound on the block sizes), plus the fully componentwise and
--   residual forms under per-block budget-domination certificates.
-- * The Sylvester instantiation: the interleaved two-column Bartels-Stewart
--   ranking `sylvesterQQIndexEquiv`, under which the (16.2) coefficient of a
--   quasi-triangular pair is block upper triangular for the induced 1/2/4
--   partition, and the (16.7)/(16.8)-shaped statements for the computed
--   solution `flSylvesterQQSchurBlockBackSubSolve` of the substitution
--   (16.6) under per-block separation/pivot/growth certificates.
--
-- Honest scope:
-- * Schur factors are SUPPLIED, as in the printed setting and in Waves
--   14-15; errors in computing the real Schur decompositions or the
--   transformed right-hand side belong to (16.9) and are not modeled here.
-- * All diagonal blocks are solved by GE WITHOUT pivoting.  The hypotheses
--   are the honest certificates that the eliminations run to completion:
--   every COMPUTED pivot of every block is nonzero (`flGEPivots`), the
--   Chapter 9 convention (Theorems 9.3-9.4 assume the elimination produces
--   nonzero computed pivots).  A pivoted kernel is not modeled.
-- * GE is not componentwise backward stable relative to `|M|` alone: the
--   unconditional bounds carry the explicit elimination budget `flGEBudget`
--   (the Theorem 9.3 `|L^||U^|` budget read on computed multipliers and
--   computed Schur complements).  The printed fully componentwise
--   `(16.7)`-shaped statements take the standard per-block growth
--   certificates `flGEBudget <= (1 + rho) |block|` as explicit hypotheses;
--   nothing is smuggled.
-- * The printed unspecified constant `c_{m,n} u` is realized as the honest
--   same-gamma-class envelope `gamma_{nm+20}`: Chapter 8 fold accumulation
--   on at most `nm` terms composed with the size-<=-4 kernel envelope
--   `gamma_{5*4} = gamma_20`.  We do not claim the printed letter constant.

import NumStability.Algorithms.Sylvester.Higham16QuasiRoundedSylvester

namespace NumStability

namespace Wave16

open scoped BigOperators
open Wave15

-- ============================================================
-- (1) The rounded small-system Gaussian-elimination kernel
-- ============================================================

/-- Higham, 2nd ed., Chapter 9.1 and Chapter 16.2, p. 308: the rounded
    first-stage Schur complement of Gaussian elimination without pivoting:
    `Sc i j = fl(M_{i+1,j+1} - fl(fl(M_{i+1,0}/M_{0,0}) * M_{0,j+1}))`,
    built from the `FPModel` primitives. -/
noncomputable def flGESchur (fp : FPModel) {N : Nat}
    (M : Fin (N + 2) → Fin (N + 2) → Real) :
    Fin (N + 1) → Fin (N + 1) → Real :=
  fun i j =>
    fp.fl_sub (M i.succ j.succ)
      (fp.fl_mul (fp.fl_div (M i.succ 0) (M 0 0)) (M 0 j.succ))

/-- Higham, 2nd ed., Chapter 9.1 and Chapter 16.2, p. 308: the rounded
    first-stage right-hand-side update of Gaussian elimination without
    pivoting: `c i = fl(b_{i+1} - fl(fl(M_{i+1,0}/M_{0,0}) * b_0))`. -/
noncomputable def flGERhs (fp : FPModel) {N : Nat}
    (M : Fin (N + 2) → Fin (N + 2) → Real) (b : Fin (N + 2) → Real) :
    Fin (N + 1) → Real :=
  fun i =>
    fp.fl_sub (b i.succ)
      (fp.fl_mul (fp.fl_div (M i.succ 0) (M 0 0)) (b 0))

/-- **Higham, 2nd ed., Chapter 9.1 and Chapter 16.2, p. 308**: the rounded
    linear-system solve by Gaussian elimination without pivoting, parametric
    in the system size: eliminate the first column (rounded multipliers and
    Schur complement), solve the reduced system recursively, then
    back-substitute the head unknown by a Chapter 8 rounded subtraction fold
    and a rounded division.  This is the kernel used by the quasi-quasi
    Bartels-Stewart substitution (16.6) for the diagonal blocks of order
    up to 4; at size 2 it performs exactly the Wave-15 `fl_solve2x2`
    elimination schedule. -/
noncomputable def flGESolve (fp : FPModel) :
    (N : Nat) → (Fin (N + 1) → Fin (N + 1) → Real) →
      (Fin (N + 1) → Real) → Fin (N + 1) → Real
  | 0, M, b => fun _ => fp.fl_div (b 0) (M 0 0)
  | N + 1, M, b =>
      Fin.cons
        (fp.fl_div
          (Fin.foldl (N + 1)
            (fun acc t =>
              fp.fl_sub acc
                (fp.fl_mul (M 0 t.succ)
                  (flGESolve fp N (flGESchur fp M) (flGERhs fp M b) t)))
            (b 0))
          (M 0 0))
        (flGESolve fp N (flGESchur fp M) (flGERhs fp M b))

/-- Size-one unfolding of the kernel. -/
theorem flGESolve_zero (fp : FPModel) (M : Fin 1 → Fin 1 → Real)
    (b : Fin 1 → Real) (j : Fin 1) :
    flGESolve fp 0 M b j = fp.fl_div (b 0) (M 0 0) := rfl

/-- One-stage unfolding of the kernel. -/
theorem flGESolve_succ (fp : FPModel) (N : Nat)
    (M : Fin (N + 2) → Fin (N + 2) → Real) (b : Fin (N + 2) → Real) :
    flGESolve fp (N + 1) M b =
      Fin.cons
        (fp.fl_div
          (Fin.foldl (N + 1)
            (fun acc t =>
              fp.fl_sub acc
                (fp.fl_mul (M 0 t.succ)
                  (flGESolve fp N (flGESchur fp M) (flGERhs fp M b) t)))
            (b 0))
          (M 0 0))
        (flGESolve fp N (flGESchur fp M) (flGERhs fp M b)) := rfl

/-- Higham, 2nd ed., Chapter 9.3, Theorems 9.3-9.4 convention, as required
    by Chapter 16.2, p. 308: the completion certificate of the rounded
    Gaussian elimination without pivoting — every COMPUTED pivot (the head
    entry of every rounded Schur complement stage) is nonzero.  At size 2
    this is exactly the Wave-15 pair "`M 0 0 /= 0` and the computed second
    pivot `flSolve2x2SecondPivot /= 0`". -/
def flGEPivots (fp : FPModel) :
    (N : Nat) → (Fin (N + 1) → Fin (N + 1) → Real) → Prop
  | 0, M => M 0 0 ≠ 0
  | N + 1, M => M 0 0 ≠ 0 ∧ flGEPivots fp N (flGESchur fp M)

/-- Higham, 2nd ed., Chapter 9.3, Theorem 9.3, specialized as required by
    Chapter 16.2, p. 308: the explicit entrywise elimination budget of the
    rounded Gaussian elimination — the `|L^||U^|`-shaped backward-error
    budget of Theorem 9.3 read on the COMPUTED quantities: on the head row
    and first column it is `|M i j|` (those perturbations are purely
    relative), and on the interior it accumulates the multiplier fill-in
    `|l^_i| |M_{0,j}|` plus the budget of the computed Schur complement. -/
noncomputable def flGEBudget (fp : FPModel) :
    (N : Nat) → (Fin (N + 1) → Fin (N + 1) → Real) →
      Fin (N + 1) → Fin (N + 1) → Real
  | 0, M => fun i j => |M i j|
  | N + 1, M => fun i j =>
      if hi : i.val = 0 then |M i j|
      else if hj : j.val = 0 then |M i j|
      else
        |M i j| + |fp.fl_div (M i 0) (M 0 0)| * |M 0 j| +
          flGEBudget fp N (flGESchur fp M)
            ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩

/-- Size-one value of the elimination budget. -/
theorem flGEBudget_zero (fp : FPModel) (M : Fin 1 → Fin 1 → Real)
    (i j : Fin 1) : flGEBudget fp 0 M i j = |M i j| := rfl

/-- Head-row value of the elimination budget. -/
theorem flGEBudget_succ_head (fp : FPModel) (N : Nat)
    (M : Fin (N + 2) → Fin (N + 2) → Real) (j : Fin (N + 2)) :
    flGEBudget fp (N + 1) M 0 j = |M 0 j| := by
  simp only [flGEBudget]
  rw [dif_pos (show ((0 : Fin (N + 2)).val = 0) by simp)]

/-- First-column value of the elimination budget. -/
theorem flGEBudget_succ_col (fp : FPModel) (N : Nat)
    (M : Fin (N + 2) → Fin (N + 2) → Real) (i : Fin (N + 1)) :
    flGEBudget fp (N + 1) M i.succ 0 = |M i.succ 0| := by
  simp only [flGEBudget]
  rw [dif_neg (by simp : ¬((i.succ : Fin (N + 2)).val = 0)),
    dif_pos (show ((0 : Fin (N + 2)).val = 0) by simp)]

/-- Interior value of the elimination budget: the entry, the multiplier
    fill-in, and the recursive Schur-complement budget. -/
theorem flGEBudget_succ_succ (fp : FPModel) (N : Nat)
    (M : Fin (N + 2) → Fin (N + 2) → Real) (i j : Fin (N + 1)) :
    flGEBudget fp (N + 1) M i.succ j.succ =
      |M i.succ j.succ| +
        |fp.fl_div (M i.succ 0) (M 0 0)| * |M 0 j.succ| +
        flGEBudget fp N (flGESchur fp M) i j := by
  simp only [flGEBudget]
  rw [dif_neg (by simp : ¬((i.succ : Fin (N + 2)).val = 0)),
    dif_neg (by simp : ¬((j.succ : Fin (N + 2)).val = 0))]
  have h1 : (⟨(i.succ : Fin (N + 2)).val - 1, by omega⟩ : Fin (N + 1)) = i :=
    Fin.ext (by simp)
  have h2 : (⟨(j.succ : Fin (N + 2)).val - 1, by omega⟩ : Fin (N + 1)) = j :=
    Fin.ext (by simp)
  rw [h1, h2]

/-- The elimination budget is nonnegative. -/
theorem flGEBudget_nonneg (fp : FPModel) (N : Nat) :
    ∀ (M : Fin (N + 1) → Fin (N + 1) → Real) (i j : Fin (N + 1)),
      0 ≤ flGEBudget fp N M i j := by
  induction N with
  | zero => intro M i j; exact abs_nonneg _
  | succ N ih =>
    intro M i j
    simp only [flGEBudget]
    split
    · exact abs_nonneg _
    · split
      · exact abs_nonneg _
      · exact add_nonneg
          (add_nonneg (abs_nonneg _)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
          (ih _ _ _)

/-- The elimination budget dominates the entry: `|M i j| <= flGEBudget`. -/
theorem abs_le_flGEBudget (fp : FPModel) (N : Nat) :
    ∀ (M : Fin (N + 1) → Fin (N + 1) → Real) (i j : Fin (N + 1)),
      |M i j| ≤ flGEBudget fp N M i j := by
  induction N with
  | zero => intro M i j; exact le_refl _
  | succ N ih =>
    intro M i j
    simp only [flGEBudget]
    split
    · exact le_refl _
    · split
      · exact le_refl _
      · have h1 : 0 ≤ |fp.fl_div (M i 0) (M 0 0)| * |M 0 j| :=
          mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have h2 := flGEBudget_nonneg fp N (flGESchur fp M)
          ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
        linarith

/-- Transport of the pivot certificate across a propositional size equality
    (bookkeeping for the block partition, where block sizes are `Nat`
    expressions). -/
theorem flGEPivots_congr (fp : FPModel) {N1 N2 : Nat} (h : N1 = N2)
    (M1 : Fin (N1 + 1) → Fin (N1 + 1) → Real)
    (M2 : Fin (N2 + 1) → Fin (N2 + 1) → Real)
    (hM : ∀ u v : Fin (N1 + 1),
      M1 u v = M2 ⟨u.val, by omega⟩ ⟨v.val, by omega⟩)
    (h2 : flGEPivots fp N2 M2) : flGEPivots fp N1 M1 := by
  subst h
  have hMe : M1 = M2 := by
    funext u v
    rw [hM u v]
  rw [hMe]
  exact h2

/-- Transport of the elimination budget across a propositional size
    equality. -/
theorem flGEBudget_congr (fp : FPModel) {N1 N2 : Nat} (h : N1 = N2)
    (M1 : Fin (N1 + 1) → Fin (N1 + 1) → Real)
    (M2 : Fin (N2 + 1) → Fin (N2 + 1) → Real)
    (hM : ∀ u v : Fin (N1 + 1),
      M1 u v = M2 ⟨u.val, by omega⟩ ⟨v.val, by omega⟩)
    (u v : Fin (N1 + 1)) :
    flGEBudget fp N1 M1 u v =
      flGEBudget fp N2 M2 ⟨u.val, by omega⟩ ⟨v.val, by omega⟩ := by
  subst h
  have hMe : M1 = M2 := by
    funext a b
    rw [hM a b]
  rw [hMe]

-- ============================================================
-- Tight analysis of the dense head-row fold
-- ============================================================

/-- **Higham, 2nd ed., Chapter 8.1, Lemma 8.2 fold analysis** (tight form,
    dense head row of the elimination kernel).  The rounded subtraction fold
    of the head row over all `N + 1` off-diagonal terms equals
    `(c - sum_t w_t x_t (1 + phi_t)) * P` for a positive accumulated product
    `P` with exact inverse `1 + beta`, `|beta| <= gamma_{N+1}`, and per-term
    factors `|phi_t| <= gamma_{N+1}`. -/
theorem flGE_dense_fold_tight (fp : FPModel) (N : Nat)
    (w x : Fin (N + 1) → Real) (c : Real)
    (hu : fp.u < 1) (hgv : gammaValid fp (N + 1)) :
    ∃ (P β : Real) (φ : Fin (N + 1) → Real),
      0 < P ∧ (1 + β) * P = 1 ∧ |β| ≤ gamma fp (N + 1) ∧
      (∀ t, |φ t| ≤ gamma fp (N + 1)) ∧
      Fin.foldl (N + 1)
          (fun acc t => fp.fl_sub acc (fp.fl_mul (w t) (x t))) c =
        (c - ∑ t, w t * x t * (1 + φ t)) * P := by
  let a_vals : Fin (N + 1) → Real := fun t => fp.fl_mul (w t) (x t)
  obtain ⟨σ, hσ, hfold⟩ := fl_sub_fold_unroll fp (N + 1) a_vals c
  have hmul : ∀ t : Fin (N + 1), ∃ ε : Real, |ε| ≤ fp.u ∧
      a_vals t = w t * x t * (1 + ε) :=
    fun t => fp.model_mul _ _
  choose ε hε_bd hε_eq using hmul
  set P := ∏ k : Fin (N + 1), (1 + σ k) with hP_def
  have hP_pos : (0 : Real) < P := prod_pos_of_u_bound fp (N + 1) σ hσ hu
  obtain ⟨β, hβ, hβ_eq⟩ := inv_prod_error_bound fp (N + 1) σ hσ hu hgv
  have hβP : (1 + β) * P = 1 := by
    rw [← hβ_eq, hP_def, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro k _
    have hk_pos : (0 : Real) < 1 + σ k := by
      linarith [neg_abs_le (σ k), hσ k]
    field_simp
  have hP_split : ∀ t : Fin (N + 1),
      P = (∏ k : Fin (N + 1), if k.val < t.val then (1 + σ k) else 1) *
          (∏ k : Fin (N + 1), if t.val ≤ k.val then (1 + σ k) else 1) := by
    intro t
    rw [hP_def, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    by_cases h : k.val < t.val
    · simp [h, show ¬(t.val ≤ k.val) from by omega]
    · simp [h, show t.val ≤ k.val from by omega]
  have hoff : ∀ t : Fin (N + 1),
      ∃ η : Real, |η| ≤ gamma fp (t.val + 1) ∧
        a_vals t *
            (∏ k : Fin (N + 1), if t.val ≤ k.val then (1 + σ k) else 1) =
        w t * x t * (1 + η) * P := by
    intro t
    let σ_head : Fin t.val → Real := fun j => σ ⟨j.val, by omega⟩
    have hσ_head : ∀ k, |σ_head k| ≤ fp.u := fun k => hσ ⟨k.val, by omega⟩
    have ht_valid : gammaValid fp t.val :=
      gammaValid_mono fp (by have := t.isLt; omega) hgv
    obtain ⟨α, hα, hα_eq⟩ :=
      inv_prod_error_bound fp t.val σ_head hσ_head hu ht_valid
    have hHP_eq : (∏ k : Fin (N + 1),
          if k.val < t.val then (1 + σ k) else 1) =
        ∏ j : Fin t.val, (1 + σ_head j) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun k : Fin (N + 1) => k.val < t.val)]
      have hrest : ∏ k ∈ Finset.filter
          (fun k : Fin (N + 1) => ¬(k.val < t.val)) Finset.univ,
          (if k.val < t.val then (1 + σ k) else 1) = 1 := by
        apply Finset.prod_eq_one
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp [hk]
      rw [hrest, mul_one]
      have hS_eq : ∏ k ∈ Finset.filter
          (fun k : Fin (N + 1) => k.val < t.val) Finset.univ,
          (if k.val < t.val then (1 + σ k) else 1) =
        ∏ k ∈ Finset.filter
            (fun k : Fin (N + 1) => k.val < t.val) Finset.univ,
          (1 + σ k) := by
        apply Finset.prod_congr rfl
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp [hk]
      rw [hS_eq]
      symm
      apply Finset.prod_nbij (fun j => ⟨j.val, by omega⟩)
      · intro j _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · intro j₁ _ j₂ _ h
        exact Fin.ext (Fin.mk.inj h)
      · intro k hk
        simp only [Finset.coe_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] at hk
        exact ⟨⟨k.val, hk⟩, Finset.mem_univ _, Fin.ext rfl⟩
      · intro j _
        simp only [σ_head]
    have hα_cancel : (1 + α) *
        (∏ k : Fin (N + 1), if k.val < t.val then (1 + σ k) else 1) = 1 := by
      rw [hHP_eq, ← hα_eq, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro k _
      have hk_pos : (0 : Real) < 1 + σ_head k := by
        linarith [neg_abs_le (σ_head k), hσ_head k]
      field_simp
    have hε_γ1 : |ε t| ≤ gamma fp 1 :=
      le_trans (hε_bd t)
        (u_le_gamma fp one_pos (gammaValid_mono fp (by omega) hgv))
    obtain ⟨η, hη, hη_eq⟩ := gamma_mul fp 1 t.val (ε t) α hε_γ1 hα
      (gammaValid_mono fp (by have := t.isLt; omega) hgv)
    have hη_exact : |η| ≤ gamma fp (t.val + 1) := by
      simpa [Nat.add_comm] using hη
    refine ⟨η, hη_exact, ?_⟩
    have hTP_eq : (1 + α) * P =
        ∏ k : Fin (N + 1), if t.val ≤ k.val then (1 + σ k) else 1 := by
      calc (1 + α) * P
          = (1 + α) *
              ((∏ k : Fin (N + 1), if k.val < t.val then (1 + σ k) else 1) *
                (∏ k : Fin (N + 1),
                  if t.val ≤ k.val then (1 + σ k) else 1)) := by
            rw [← hP_split t]
        _ = ((1 + α) *
              (∏ k : Fin (N + 1), if k.val < t.val then (1 + σ k) else 1)) *
              (∏ k : Fin (N + 1),
                if t.val ≤ k.val then (1 + σ k) else 1) := by
            ring
        _ = 1 * (∏ k : Fin (N + 1),
              if t.val ≤ k.val then (1 + σ k) else 1) := by
            rw [hα_cancel]
        _ = ∏ k : Fin (N + 1), if t.val ≤ k.val then (1 + σ k) else 1 :=
            one_mul _
    rw [hε_eq t, ← hTP_eq, ← hη_eq]
    ring
  choose η_vals hη_bd hη_eq using hoff
  refine ⟨P, β, η_vals, hP_pos, hβP, hβ, ?_, ?_⟩
  · intro t
    exact le_trans (hη_bd t)
      (gamma_mono fp (by have := t.isLt; omega) hgv)
  · have hqf : Fin.foldl (N + 1)
        (fun acc t => fp.fl_sub acc (fp.fl_mul (w t) (x t))) c =
        Fin.foldl (N + 1) (fun acc t => fp.fl_sub acc (a_vals t)) c := rfl
    rw [hqf, hfold]
    have hsum_rw : (∑ t : Fin (N + 1), a_vals t *
        ∏ k : Fin (N + 1), if t.val ≤ k.val then (1 + σ k) else 1) =
        (∑ t : Fin (N + 1), w t * x t * (1 + η_vals t)) * P := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      rw [hη_eq t]
    rw [hsum_rw]
    ring

-- ============================================================
-- Backward error of the elimination kernel (Theorems 9.3-9.4, small n)
-- ============================================================

/-- **Higham, 2nd ed., Chapter 9.3, Theorems 9.3-9.4 for the small systems
    required by Chapter 16.2, p. 308** (componentwise backward error of the
    rounded Gaussian-elimination solve, parametric in the size).  If every
    computed pivot is nonzero — the honest certificate that the elimination
    without pivoting runs to completion — then the computed solution
    `x^ = flGESolve` solves an exactly perturbed system

    `sum_j (M i j + DeltaM i j) x^_j = b i` with
    `|DeltaM i j| <= gamma_{5N+5} * flGEBudget i j`,

    where `flGEBudget` is the explicit Theorem 9.3 `|L^||U^|`-shaped
    elimination budget in computed quantities.  The envelope `gamma_{5N+5}`
    counts the elimination, substitution and scaling operations of the
    kernel in one gamma class (size 1: `gamma_5`; size 2: `gamma_10`;
    size 4: `gamma_20`); we do not claim the printed letter constants. -/
theorem flGESolve_backward_error (fp : FPModel) :
    ∀ (N : Nat) (M : Fin (N + 1) → Fin (N + 1) → Real)
      (b : Fin (N + 1) → Real),
      flGEPivots fp N M → gammaValid fp (5 * N + 5) →
      ∃ ΔM : Fin (N + 1) → Fin (N + 1) → Real,
        (∀ i j, |ΔM i j| ≤
          gamma fp (5 * N + 5) * flGEBudget fp N M i j) ∧
        (∀ i, (∑ j, (M i j + ΔM i j) * flGESolve fp N M b j) = b i) := by
  intro N
  induction N with
  | zero =>
    intro M b hpiv hgv
    have hM00 : M 0 0 ≠ 0 := hpiv
    have hu1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hgv
    have hu : fp.u < 1 := by
      have h := hu1
      unfold gammaValid at h
      simpa using h
    obtain ⟨δ, hδ, hx⟩ := fp.model_div (b 0) (M 0 0) hM00
    have hδpos : (0 : Real) < 1 + δ := by linarith [neg_abs_le δ]
    obtain ⟨δ', hδ', hδ'eq⟩ := gamma_inv fp 1 δ
      (le_trans hδ (u_le_gamma fp one_pos hu1)) hδpos
      (gammaValid_mono fp (by omega) hgv)
    have hcancel : (1 + δ') * (1 + δ) = 1 := by
      rw [← hδ'eq]
      field_simp
    refine ⟨fun i j => M i j * δ', ?_, ?_⟩
    · intro i j
      rw [flGEBudget_zero, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (le_trans hδ' (gamma_mono fp (by omega) hgv)) (abs_nonneg _)
    · intro i
      have hi : i = 0 := Fin.ext (by omega)
      subst hi
      rw [Fin.sum_univ_one, flGESolve_zero, hx]
      have hexp : (M 0 0 + M 0 0 * δ') * (b 0 / M 0 0 * (1 + δ)) =
          b 0 * ((1 + δ') * (1 + δ)) := by
        field_simp
      rw [hexp, hcancel, mul_one]
  | succ N ih =>
    intro M b hpiv hgv
    have hgv' : gammaValid fp (5 * N + 5) := gammaValid_mono fp (by omega) hgv
    have hu1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hgv
    have hu : fp.u < 1 := by
      have h := hu1
      unfold gammaValid at h
      simpa using h
    have hM00 : M 0 0 ≠ 0 := hpiv.1
    -- Rounding models for the multipliers.
    choose δl hδl hleq using
      (fun i : Fin (N + 1) => fp.model_div (M i.succ 0) (M 0 0) hM00)
    have hlM : ∀ i : Fin (N + 1),
        fp.fl_div (M i.succ 0) (M 0 0) * M 0 0 =
          M i.succ 0 * (1 + δl i) := by
      intro i
      rw [hleq i]
      field_simp
    -- Rounding models for the Schur complement and updated rhs.
    choose δm hδm hmeq using
      (fun (i j : Fin (N + 1)) =>
        fp.model_mul (fp.fl_div (M i.succ 0) (M 0 0)) (M 0 j.succ))
    choose δs hδs hseq using
      (fun (i j : Fin (N + 1)) =>
        fp.model_sub (M i.succ j.succ)
          (fp.fl_mul (fp.fl_div (M i.succ 0) (M 0 0)) (M 0 j.succ)))
    have hSc : ∀ i j : Fin (N + 1), flGESchur fp M i j =
        (M i.succ j.succ -
            fp.fl_div (M i.succ 0) (M 0 0) * M 0 j.succ * (1 + δm i j)) *
          (1 + δs i j) := by
      intro i j
      show fp.fl_sub _ _ = _
      rw [hseq i j, hmeq i j]
    choose δp hδp hpeq using
      (fun i : Fin (N + 1) =>
        fp.model_mul (fp.fl_div (M i.succ 0) (M 0 0)) (b 0))
    choose δq hδq hqeq using
      (fun i : Fin (N + 1) =>
        fp.model_sub (b i.succ)
          (fp.fl_mul (fp.fl_div (M i.succ 0) (M 0 0)) (b 0)))
    have hcrhs : ∀ i : Fin (N + 1), flGERhs fp M b i =
        (b i.succ -
            fp.fl_div (M i.succ 0) (M 0 0) * b 0 * (1 + δp i)) *
          (1 + δq i) := by
      intro i
      show fp.fl_sub _ _ = _
      rw [hqeq i, hpeq i]
    -- Exact inverses of the rhs scalings.
    have hq'ex : ∀ i : Fin (N + 1), ∃ θ : Real, |θ| ≤ gamma fp 2 ∧
        1 / (1 + δq i) = 1 + θ := by
      intro i
      exact gamma_inv fp 1 (δq i)
        (le_trans (hδq i) (u_le_gamma fp one_pos hu1))
        (by linarith [neg_abs_le (δq i), hδq i])
        (gammaValid_mono fp (by omega) hgv)
    choose δq' hδq' hq'eq using hq'ex
    have hq'cancel : ∀ i : Fin (N + 1),
        (1 + δq' i) * (1 + δq i) = 1 := by
      intro i
      have hpos : (0 : Real) < 1 + δq i := by
        linarith [neg_abs_le (δq i), hδq i]
      rw [← hq'eq i]
      field_simp
    -- Induction hypothesis on the rounded Schur system.
    obtain ⟨ΔS, hΔSb, hΔSeq⟩ :=
      ih (flGESchur fp M) (flGERhs fp M b) hpiv.2 hgv'
    set xr : Fin (N + 1) → Real :=
      flGESolve fp N (flGESchur fp M) (flGERhs fp M b) with hxr_def
    -- Head-row fold analysis and division.
    obtain ⟨P, β, φ, hPpos, hβP, hβ, hφ, hfold⟩ :=
      flGE_dense_fold_tight fp N (fun t => M 0 t.succ) xr (b 0) hu
        (gammaValid_mono fp (by omega) hgv)
    obtain ⟨δd, hδd, hdiv⟩ := fp.model_div
      (Fin.foldl (N + 1)
        (fun acc t => fp.fl_sub acc (fp.fl_mul (M 0 t.succ) (xr t)))
        (b 0)) (M 0 0) hM00
    have hδd_pos : (0 : Real) < 1 + δd := by linarith [neg_abs_le δd]
    have hx0 : flGESolve fp (N + 1) M b 0 =
        fp.fl_div
          (Fin.foldl (N + 1)
            (fun acc t => fp.fl_sub acc (fp.fl_mul (M 0 t.succ) (xr t)))
            (b 0)) (M 0 0) := by
      rw [flGESolve_succ]
      exact Fin.cons_zero _ _
    have hxsucc : ∀ j : Fin (N + 1),
        flGESolve fp (N + 1) M b j.succ = xr j := by
      intro j
      rw [flGESolve_succ]
      exact Fin.cons_succ _ _ j
    -- The exactly scaled head-row equation.
    have hM00x0 : M 0 0 * flGESolve fp (N + 1) M b 0 =
        (b 0 - ∑ t, M 0 t.succ * xr t * (1 + φ t)) * (P * (1 + δd)) := by
      rw [hx0, hdiv, hfold]
      field_simp
    obtain ⟨φd, hφd, hφd_eq⟩ := gamma_div fp (N + 1) 1 β δd hβ
      (le_trans hδd (u_le_gamma fp one_pos hu1)) hδd_pos
      (gammaValid_mono fp (by omega) hgv)
    have hφd_mul : (1 : Real) + β = (1 + φd) * (1 + δd) := by
      have h := hφd_eq
      rw [div_eq_iff (ne_of_gt hδd_pos)] at h
      exact h
    have hcancel_head : (1 + φd) * (P * (1 + δd)) = 1 := by
      calc (1 + φd) * (P * (1 + δd)) = ((1 + φd) * (1 + δd)) * P := by ring
        _ = (1 + β) * P := by rw [← hφd_mul]
        _ = 1 := hβP
    have hhead : b 0 =
        M 0 0 * (1 + φd) * flGESolve fp (N + 1) M b 0 +
          ∑ t, M 0 t.succ * xr t * (1 + φ t) := by
      have h3 : b 0 - (∑ t, M 0 t.succ * xr t * (1 + φ t)) =
          M 0 0 * flGESolve fp (N + 1) M b 0 * (1 + φd) := by
        calc b 0 - (∑ t, M 0 t.succ * xr t * (1 + φ t))
            = (b 0 - ∑ t, M 0 t.succ * xr t * (1 + φ t)) *
                ((1 + φd) * (P * (1 + δd))) := by
              rw [hcancel_head, mul_one]
          _ = ((b 0 - ∑ t, M 0 t.succ * xr t * (1 + φ t)) *
                (P * (1 + δd))) * (1 + φd) := by ring
          _ = M 0 0 * flGESolve fp (N + 1) M b 0 * (1 + φd) := by
              rw [← hM00x0]
      linarith [h3]
    -- The exactly scaled tail-row equations.
    have htail : ∀ i : Fin (N + 1),
        (∑ j, (flGESchur fp M i j + ΔS i j) * xr j) * (1 + δq' i) =
          b i.succ -
            fp.fl_div (M i.succ 0) (M 0 0) * b 0 * (1 + δp i) := by
      intro i
      have h1 := hΔSeq i
      rw [hcrhs i] at h1
      calc (∑ j, (flGESchur fp M i j + ΔS i j) * xr j) * (1 + δq' i)
          = ((b i.succ -
                fp.fl_div (M i.succ 0) (M 0 0) * b 0 * (1 + δp i)) *
              (1 + δq i)) * (1 + δq' i) := by rw [h1]
        _ = (b i.succ -
              fp.fl_div (M i.succ 0) (M 0 0) * b 0 * (1 + δp i)) *
              ((1 + δq' i) * (1 + δq i)) := by ring
        _ = b i.succ -
              fp.fl_div (M i.succ 0) (M 0 0) * b 0 * (1 + δp i) := by
            rw [hq'cancel i, mul_one]
    -- The assembled perturbation.
    refine ⟨fun i j =>
      Fin.cases
        (Fin.cases (M 0 0 * φd) (fun j' => M 0 j'.succ * φ j') j)
        (fun i' =>
          Fin.cases
            (fp.fl_div (M i'.succ 0) (M 0 0) * (1 + δp i') *
                (M 0 0 * (1 + φd)) - M i'.succ 0)
            (fun j' =>
              (flGESchur fp M i' j' + ΔS i' j') * (1 + δq' i') +
                fp.fl_div (M i'.succ 0) (M 0 0) * (1 + δp i') *
                  (M 0 j'.succ * (1 + φ j')) -
                M i'.succ j'.succ) j) i, ?_, ?_⟩
    · -- Componentwise bounds.
      intro i j
      have hγnn : 0 ≤ gamma fp (5 * (N + 1) + 5) := gamma_nonneg fp hgv
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero]
          rw [flGEBudget_succ_head, abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right
            (le_trans hφd (gamma_mono fp (by omega) hgv)) (abs_nonneg _)
        | succ j' =>
          simp only [Fin.cases_zero, Fin.cases_succ]
          rw [flGEBudget_succ_head, abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right
            (le_trans (hφ j') (gamma_mono fp (by omega) hgv)) (abs_nonneg _)
      | succ i' =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cases_succ, Fin.cases_zero]
          rw [flGEBudget_succ_col]
          -- Rewrite through the multiplier identity.
          have hrew : fp.fl_div (M i'.succ 0) (M 0 0) * (1 + δp i') *
              (M 0 0 * (1 + φd)) - M i'.succ 0 =
              M i'.succ 0 *
                ((1 + δl i') * (1 + δp i') * (1 + φd) - 1) := by
            have h := hlM i'
            linear_combination ((1 + δp i') * (1 + φd)) * h
          rw [hrew]
          obtain ⟨θlp, hθlp, hθlp_eq⟩ := gamma_mul fp 1 1 (δl i') (δp i')
            (le_trans (hδl i') (u_le_gamma fp one_pos hu1))
            (le_trans (hδp i') (u_le_gamma fp one_pos hu1))
            (gammaValid_mono fp (by omega) hgv)
          obtain ⟨θ0, hθ0, hθ0_eq⟩ := gamma_mul fp 2 (N + 3) θlp φd hθlp hφd
            (gammaValid_mono fp (by omega) hgv)
          have hexp : (1 + δl i') * (1 + δp i') * (1 + φd) - 1 = θ0 := by
            rw [hθlp_eq, hθ0_eq]
            ring
          rw [hexp, abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right
            (le_trans hθ0 (gamma_mono fp (by omega) hgv)) (abs_nonneg _)
        | succ j' =>
          simp only [Fin.cases_succ]
          rw [flGEBudget_succ_succ]
          -- Decompose the interior perturbation.
          have hrew : (flGESchur fp M i' j' + ΔS i' j') * (1 + δq' i') +
              fp.fl_div (M i'.succ 0) (M 0 0) * (1 + δp i') *
                (M 0 j'.succ * (1 + φ j')) -
              M i'.succ j'.succ =
              M i'.succ j'.succ * ((1 + δs i' j') * (1 + δq' i') - 1) +
                fp.fl_div (M i'.succ 0) (M 0 0) * M 0 j'.succ *
                  ((1 + δp i') * (1 + φ j') -
                    (1 + δm i' j') * (1 + δs i' j') * (1 + δq' i')) +
                ΔS i' j' * (1 + δq' i') := by
            rw [hSc i' j']
            ring
          rw [hrew]
          -- Bound the three pieces.
          obtain ⟨θ1, hθ1, hθ1_eq⟩ := gamma_mul fp 1 2 (δs i' j') (δq' i')
            (le_trans (hδs i' j') (u_le_gamma fp one_pos hu1)) (hδq' i')
            (gammaValid_mono fp (by omega) hgv)
          obtain ⟨θa, hθa, hθa_eq⟩ := gamma_mul fp 1 (N + 1)
            (δp i') (φ j')
            (le_trans (hδp i') (u_le_gamma fp one_pos hu1)) (hφ j')
            (gammaValid_mono fp (by omega) hgv)
          obtain ⟨θms, hθms, hθms_eq⟩ := gamma_mul fp 1 1
            (δm i' j') (δs i' j')
            (le_trans (hδm i' j') (u_le_gamma fp one_pos hu1))
            (le_trans (hδs i' j') (u_le_gamma fp one_pos hu1))
            (gammaValid_mono fp (by omega) hgv)
          obtain ⟨θb, hθb, hθb_eq⟩ := gamma_mul fp 2 2 θms (δq' i')
            hθms (hδq' i')
            (gammaValid_mono fp (by omega) hgv)
          have hp1 : |M i'.succ j'.succ *
              ((1 + δs i' j') * (1 + δq' i') - 1)| ≤
              gamma fp (5 * (N + 1) + 5) * |M i'.succ j'.succ| := by
            have h : (1 + δs i' j') * (1 + δq' i') - 1 = θ1 := by
              rw [hθ1_eq]
              ring
            rw [h, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right
              (le_trans hθ1 (gamma_mono fp (by omega) hgv)) (abs_nonneg _)
          have hp2 : |fp.fl_div (M i'.succ 0) (M 0 0) * M 0 j'.succ *
              ((1 + δp i') * (1 + φ j') -
                (1 + δm i' j') * (1 + δs i' j') * (1 + δq' i'))| ≤
              gamma fp (5 * (N + 1) + 5) *
                (|fp.fl_div (M i'.succ 0) (M 0 0)| * |M 0 j'.succ|) := by
            have hθ2 : |(1 + δp i') * (1 + φ j') -
                (1 + δm i' j') * (1 + δs i' j') * (1 + δq' i')| ≤
                gamma fp (N + 6) := by
              have hA : (1 + δp i') * (1 + φ j') -
                  (1 + δm i' j') * (1 + δs i' j') * (1 + δq' i') =
                  θa - θb := by
                rw [hθa_eq, hθms_eq, hθb_eq]
                ring
              rw [hA]
              have habs : |θa - θb| ≤ |θa| + |θb| := by
                have h := abs_add_le θa (-θb)
                rw [abs_neg] at h
                have h2 : θa + -θb = θa - θb := by ring
                rw [h2] at h
                exact h
              have hθa' : |θa| ≤ gamma fp (N + 2) := by
                rwa [show (1 : Nat) + (N + 1) = N + 2 from by omega] at hθa
              have hθb' : |θb| ≤ gamma fp 4 := by
                rwa [show (2 : Nat) + 2 = 4 from by omega] at hθb
              have hsum : gamma fp (N + 2) + gamma fp 4 ≤
                  gamma fp (N + 6) := by
                have h := gamma_add_le fp (N + 2) 4
                  (gammaValid_mono fp (by omega) hgv)
                rwa [show N + 2 + 4 = N + 6 from by omega] at h
              linarith
            rw [abs_mul, abs_mul]
            calc |fp.fl_div (M i'.succ 0) (M 0 0)| * |M 0 j'.succ| *
                |(1 + δp i') * (1 + φ j') -
                  (1 + δm i' j') * (1 + δs i' j') * (1 + δq' i')|
                ≤ |fp.fl_div (M i'.succ 0) (M 0 0)| * |M 0 j'.succ| *
                  gamma fp (N + 6) := by
                  exact mul_le_mul_of_nonneg_left hθ2
                    (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              _ ≤ |fp.fl_div (M i'.succ 0) (M 0 0)| * |M 0 j'.succ| *
                  gamma fp (5 * (N + 1) + 5) := by
                  exact mul_le_mul_of_nonneg_left
                    (gamma_mono fp (by omega) hgv)
                    (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              _ = gamma fp (5 * (N + 1) + 5) *
                  (|fp.fl_div (M i'.succ 0) (M 0 0)| * |M 0 j'.succ|) := by
                  ring
          have hp3 : |ΔS i' j' * (1 + δq' i')| ≤
              gamma fp (5 * (N + 1) + 5) *
                flGEBudget fp N (flGESchur fp M) i' j' := by
            rw [abs_mul]
            have h1 : |1 + δq' i'| ≤ 1 + gamma fp 2 := by
              calc |1 + δq' i'| ≤ |(1 : Real)| + |δq' i'| := abs_add_le _ _
                _ = 1 + |δq' i'| := by rw [abs_one]
                _ ≤ 1 + gamma fp 2 := by linarith [hδq' i']
            have hBnn := flGEBudget_nonneg fp N (flGESchur fp M) i' j'
            have hglue : (1 + gamma fp 2) * gamma fp (5 * N + 5) ≤
                gamma fp (5 * N + 7) := by
              have h := one_add_gamma_mul_gamma_le fp 2 (5 * N + 5)
                (gammaValid_mono fp (by omega) hgv)
              rwa [show 2 + (5 * N + 5) = 5 * N + 7 from by omega] at h
            calc |ΔS i' j'| * |1 + δq' i'|
                ≤ (gamma fp (5 * N + 5) *
                    flGEBudget fp N (flGESchur fp M) i' j') *
                  (1 + gamma fp 2) := by
                  apply mul_le_mul (hΔSb i' j') h1 (abs_nonneg _)
                  exact mul_nonneg (gamma_nonneg fp hgv') hBnn
              _ = ((1 + gamma fp 2) * gamma fp (5 * N + 5)) *
                  flGEBudget fp N (flGESchur fp M) i' j' := by ring
              _ ≤ gamma fp (5 * N + 7) *
                  flGEBudget fp N (flGESchur fp M) i' j' :=
                  mul_le_mul_of_nonneg_right hglue hBnn
              _ ≤ gamma fp (5 * (N + 1) + 5) *
                  flGEBudget fp N (flGESchur fp M) i' j' :=
                  mul_le_mul_of_nonneg_right
                    (gamma_mono fp (by omega) hgv) hBnn
          calc |M i'.succ j'.succ * ((1 + δs i' j') * (1 + δq' i') - 1) +
              fp.fl_div (M i'.succ 0) (M 0 0) * M 0 j'.succ *
                ((1 + δp i') * (1 + φ j') -
                  (1 + δm i' j') * (1 + δs i' j') * (1 + δq' i')) +
              ΔS i' j' * (1 + δq' i')|
              ≤ |M i'.succ j'.succ * ((1 + δs i' j') * (1 + δq' i') - 1) +
                  fp.fl_div (M i'.succ 0) (M 0 0) * M 0 j'.succ *
                    ((1 + δp i') * (1 + φ j') -
                      (1 + δm i' j') * (1 + δs i' j') * (1 + δq' i'))| +
                |ΔS i' j' * (1 + δq' i')| := abs_add_le _ _
            _ ≤ (|M i'.succ j'.succ *
                  ((1 + δs i' j') * (1 + δq' i') - 1)| +
                |fp.fl_div (M i'.succ 0) (M 0 0) * M 0 j'.succ *
                  ((1 + δp i') * (1 + φ j') -
                    (1 + δm i' j') * (1 + δs i' j') * (1 + δq' i'))|) +
                |ΔS i' j' * (1 + δq' i')| := by
                have := abs_add_le
                  (M i'.succ j'.succ * ((1 + δs i' j') * (1 + δq' i') - 1))
                  (fp.fl_div (M i'.succ 0) (M 0 0) * M 0 j'.succ *
                    ((1 + δp i') * (1 + φ j') -
                      (1 + δm i' j') * (1 + δs i' j') * (1 + δq' i')))
                linarith
            _ ≤ gamma fp (5 * (N + 1) + 5) *
                (|M i'.succ j'.succ| +
                  |fp.fl_div (M i'.succ 0) (M 0 0)| * |M 0 j'.succ| +
                  flGEBudget fp N (flGESchur fp M) i' j') := by
                linarith [hp1, hp2, hp3]
    · -- Row equations.
      intro i
      induction i using Fin.cases with
      | zero =>
        rw [Fin.sum_univ_succ]
        simp only [Fin.cases_zero, Fin.cases_succ]
        have hterm : ∀ j' : Fin (N + 1),
            (M 0 j'.succ + M 0 j'.succ * φ j') *
              flGESolve fp (N + 1) M b j'.succ =
            M 0 j'.succ * xr j' * (1 + φ j') := by
          intro j'
          rw [hxsucc j']
          ring
        rw [Finset.sum_congr rfl (fun j' _ => hterm j')]
        linear_combination -hhead
      | succ i' =>
        rw [Fin.sum_univ_succ]
        simp only [Fin.cases_succ, Fin.cases_zero]
        have hterm : ∀ j' : Fin (N + 1),
            (M i'.succ j'.succ +
              ((flGESchur fp M i' j' + ΔS i' j') * (1 + δq' i') +
                fp.fl_div (M i'.succ 0) (M 0 0) * (1 + δp i') *
                  (M 0 j'.succ * (1 + φ j')) -
                M i'.succ j'.succ)) *
              flGESolve fp (N + 1) M b j'.succ =
            (flGESchur fp M i' j' + ΔS i' j') * xr j' * (1 + δq' i') +
              fp.fl_div (M i'.succ 0) (M 0 0) * (1 + δp i') *
                (M 0 j'.succ * xr j' * (1 + φ j')) := by
          intro j'
          rw [hxsucc j']
          ring
        rw [Finset.sum_congr rfl (fun j' _ => hterm j')]
        rw [Finset.sum_add_distrib]
        have hs1 : (∑ j', (flGESchur fp M i' j' + ΔS i' j') * xr j' *
            (1 + δq' i')) =
            (∑ j', (flGESchur fp M i' j' + ΔS i' j') * xr j') *
              (1 + δq' i') := by
          rw [Finset.sum_mul]
        have hs2 : (∑ j', fp.fl_div (M i'.succ 0) (M 0 0) * (1 + δp i') *
            (M 0 j'.succ * xr j' * (1 + φ j'))) =
            fp.fl_div (M i'.succ 0) (M 0 0) * (1 + δp i') *
              (∑ j', M 0 j'.succ * xr j' * (1 + φ j')) := by
          rw [Finset.mul_sum]
        rw [hs1, hs2]
        have ht := htail i'
        linear_combination ht -
          (fp.fl_div (M i'.succ 0) (M 0 0) * (1 + δp i')) * hhead

/-- **Higham, 2nd ed., Chapter 9.3, Theorems 9.3-9.4 with the growth
    certificate, as required by Chapter 16.2, p. 308** (fully componentwise
    form of the kernel backward error).  Under the additional standard
    componentwise budget-domination certificate
    `flGEBudget <= (1 + rho) |M|` — the componentwise growth-factor
    condition controlling the GE fill-in — the budget of
    `flGESolve_backward_error` collapses to the fully componentwise shape
    `|DeltaM| <= (1 + rho) gamma_{5N+5} |M|`. -/
theorem flGESolve_backward_error_componentwise (fp : FPModel) (N : Nat)
    (M : Fin (N + 1) → Fin (N + 1) → Real) (b : Fin (N + 1) → Real)
    (ρ : Real) (hpiv : flGEPivots fp N M) (_hρ : 0 ≤ ρ)
    (hgrow : ∀ i j, flGEBudget fp N M i j ≤ (1 + ρ) * |M i j|)
    (hgv : gammaValid fp (5 * N + 5)) :
    ∃ ΔM : Fin (N + 1) → Fin (N + 1) → Real,
      (∀ i j, |ΔM i j| ≤ (1 + ρ) * gamma fp (5 * N + 5) * |M i j|) ∧
      (∀ i, (∑ j, (M i j + ΔM i j) * flGESolve fp N M b j) = b i) := by
  obtain ⟨ΔM, hb, heq⟩ := flGESolve_backward_error fp N M b hpiv hgv
  refine ⟨ΔM, ?_, heq⟩
  intro i j
  calc |ΔM i j| ≤ gamma fp (5 * N + 5) * flGEBudget fp N M i j := hb i j
    _ ≤ gamma fp (5 * N + 5) * ((1 + ρ) * |M i j|) :=
        mul_le_mul_of_nonneg_left (hgrow i j) (gamma_nonneg fp hgv)
    _ = (1 + ρ) * gamma fp (5 * N + 5) * |M i j| := by ring

-- ============================================================
-- (2) Rounded block back substitution over an interval partition
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, p. 308: well-formed interval block
    partition of the row index range.  `bs r` / `be r` give the start and
    one-past-the-end of the diagonal block containing row `r`; rows inside
    one block interval share the same interval, so the intervals tile
    `[0, N)`.  This generalizes the Wave-15 adjacent-pair marking to the
    mixed 1/2/4 diagonal-block structure of the quasi-quasi Bartels-Stewart
    substitution. -/
def IsBlockPartitionFn (N : Nat) (bs be : Fin N → Nat) : Prop :=
  (∀ r : Fin N, bs r ≤ r.val ∧ r.val < be r ∧ be r ≤ N) ∧
    (∀ r s : Fin N, bs r ≤ s.val → s.val < be r →
      bs s = bs r ∧ be s = be r)

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6): the diagonal
    block coefficient of one partition block `[K, E)`, read as a small
    square array for the elimination kernel. -/
noncomputable def blockSubCoeff (N : Nat) (T : Fin N → Fin N → Real)
    (K E : Nat) : Fin (E - K - 1 + 1) → Fin (E - K - 1 + 1) → Real :=
  fun u v =>
    if h : K + u.val < N ∧ K + v.val < N then
      T ⟨K + u.val, h.1⟩ ⟨K + v.val, h.2⟩
    else 0

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6): the diagonal
    block right-hand side of one partition block `[K, E)` — each block row's
    Chapter 8 rounded subtraction fold over the already-computed entries in
    the columns beyond the block. -/
noncomputable def blockSubRhs (fp : FPModel) (N : Nat)
    (T : Fin N → Fin N → Real) (bb : Fin N → Real) (x : Fin N → Real)
    (K E : Nat) : Fin (E - K - 1 + 1) → Real :=
  fun u =>
    if h : K + u.val < N then
      quasiRowFold fp N T bb x ⟨K + u.val, h⟩ (E - 1)
    else 0

/-- **Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), quasi-quasi
    block form**: the rounded block back substitution over an interval block
    partition.  Blocks are processed from the bottom up; each row of a block
    accumulates its right-hand side by the Chapter 8 rounded subtraction
    fold over the already-computed entries beyond the block, and the block
    unknowns are solved simultaneously by the `flGESolve` Gaussian
    elimination kernel, each row taking its component of the shared kernel
    value — exactly the printed Bartels-Stewart processing of the systems
    of order up to 4. -/
noncomputable def flPartitionBackSub (fp : FPModel) (N : Nat)
    (bs be : Fin N → Nat) (T : Fin N → Fin N → Real) (bb : Fin N → Real)
    (r : Fin N) : Real :=
  if hgate : bs r ≤ r.val ∧ r.val < be r ∧ be r ≤ N then
    flGESolve fp (be r - bs r - 1)
      (fun u v =>
        if h : bs r + u.val < N ∧ bs r + v.val < N then
          T ⟨bs r + u.val, h.1⟩ ⟨bs r + v.val, h.2⟩
        else 0)
      (fun u =>
        if h : bs r + u.val < N then
          Fin.foldl (N - (be r - 1) - 1)
            (fun acc t =>
              fp.fl_sub acc
                (fp.fl_mul
                  (T ⟨bs r + u.val, h⟩ ⟨be r - 1 + 1 + t.val, by omega⟩)
                  (flPartitionBackSub fp N bs be T bb
                    ⟨be r - 1 + 1 + t.val, by omega⟩)))
            (bb ⟨bs r + u.val, h⟩)
        else 0)
      ⟨r.val - bs r, by omega⟩
  else fp.fl_div (bb r) (T r r)
termination_by N - r.val
decreasing_by all_goals omega

/-- Each row of a gated block is the corresponding component of the shared
    `flGESolve` kernel value of its block (Higham, 2nd ed., Chapter 16.2,
    p. 308, equation (16.6)). -/
theorem flPartitionBackSub_eq_blockSolve (fp : FPModel) (N : Nat)
    (bs be : Fin N → Nat) (T : Fin N → Fin N → Real) (bb : Fin N → Real)
    (r : Fin N) (hgate : bs r ≤ r.val ∧ r.val < be r ∧ be r ≤ N) :
    flPartitionBackSub fp N bs be T bb r =
      flGESolve fp (be r - bs r - 1)
        (blockSubCoeff N T (bs r) (be r))
        (blockSubRhs fp N T bb (flPartitionBackSub fp N bs be T bb)
          (bs r) (be r))
        ⟨r.val - bs r, by omega⟩ := by
  rw [flPartitionBackSub, dif_pos hgate]
  rfl

/-- Kernel-component identification for every row of one block: for a
    well-formed partition, the computed entry of any row `⟨K + v, _⟩` of the
    block of `r` is component `v` of the block's shared kernel value. -/
theorem flPartitionBackSub_mem_block (fp : FPModel) (N : Nat)
    (bs be : Fin N → Nat) (T : Fin N → Fin N → Real) (bb : Fin N → Real)
    (hpart : IsBlockPartitionFn N bs be) (r : Fin N)
    (v : Fin (be r - bs r - 1 + 1))
    (hv : bs r + v.val < N) :
    flPartitionBackSub fp N bs be T bb ⟨bs r + v.val, hv⟩ =
      flGESolve fp (be r - bs r - 1)
        (blockSubCoeff N T (bs r) (be r))
        (blockSubRhs fp N T bb (flPartitionBackSub fp N bs be T bb)
          (bs r) (be r)) v := by
  obtain ⟨hg1, hg2, hg3⟩ := hpart.1 r
  set s : Fin N := ⟨bs r + v.val, hv⟩ with hs_def
  have hsv : s.val = bs r + v.val := rfl
  have hsin1 : bs r ≤ s.val := by omega
  have hsin2 : s.val < be r := by
    have := v.isLt
    omega
  obtain ⟨hbs, hbe⟩ := hpart.2 r s hsin1 hsin2
  have hgs : bs s ≤ s.val ∧ s.val < be s ∧ be s ≤ N := by
    rw [hbs, hbe]
    exact ⟨hsin1, hsin2, hg3⟩
  have h := flPartitionBackSub_eq_blockSolve fp N bs be T bb s hgs
  rw [h]
  have hidx : (⟨s.val - bs s, by omega⟩ :
      Fin (be s - bs s - 1 + 1)) =
      (⟨v.val, by rw [hbs, hbe]; exact v.isLt⟩ :
        Fin (be s - bs s - 1 + 1)) := by
    apply Fin.ext
    show s.val - bs s = v.val
    rw [hbs]
    omega
  rw [hidx]
  -- transport the block data from `s` to `r`
  have hcongr : ∀ (K1 K2 E1 E2 : Nat) (hK : K1 = K2) (hE : E1 = E2)
      (w : Fin (E1 - K1 - 1 + 1)),
      flGESolve fp (E1 - K1 - 1) (blockSubCoeff N T K1 E1)
        (blockSubRhs fp N T bb (flPartitionBackSub fp N bs be T bb) K1 E1)
        w =
      flGESolve fp (E2 - K2 - 1) (blockSubCoeff N T K2 E2)
        (blockSubRhs fp N T bb (flPartitionBackSub fp N bs be T bb) K2 E2)
        ⟨w.val, by rw [← hK, ← hE]; exact w.isLt⟩ := by
    intro K1 K2 E1 E2 hK hE w
    subst hK
    subst hE
    rfl
  have hfin := hcongr (bs s) (bs r) (be s) (be r) hbs hbe
    ⟨v.val, by rw [hbs, hbe]; exact v.isLt⟩
  rw [hfin]

/-- Higham, 2nd ed., Chapter 9.3, Theorem 9.3, transported to the partition:
    the per-entry elimination budget of the partitioned block back
    substitution.  Inside the diagonal block of row `r` it is the
    `flGEBudget` of that block; outside it is `|T r c|` (those
    perturbations are purely relative). -/
noncomputable def partitionBudget (fp : FPModel) (N : Nat)
    (bs be : Fin N → Nat) (T : Fin N → Fin N → Real) (r c : Fin N) :
    Real :=
  if h : bs r ≤ c.val ∧ c.val < be r ∧
      bs r ≤ r.val ∧ r.val < be r ∧ be r ≤ N then
    flGEBudget fp (be r - bs r - 1) (blockSubCoeff N T (bs r) (be r))
      ⟨r.val - bs r, by omega⟩ ⟨c.val - bs r, by omega⟩
  else |T r c|

/-- The partition budget is nonnegative. -/
theorem partitionBudget_nonneg (fp : FPModel) (N : Nat)
    (bs be : Fin N → Nat) (T : Fin N → Fin N → Real) (r c : Fin N) :
    0 ≤ partitionBudget fp N bs be T r c := by
  unfold partitionBudget
  split
  · exact flGEBudget_nonneg fp _ _ _ _
  · exact abs_nonneg _

/-- The partition budget dominates the entry: `|T r c| <= partitionBudget`
    (Higham, 2nd ed., Chapter 9.3, Theorem 9.3 budget shape). -/
theorem abs_le_partitionBudget (fp : FPModel) (N : Nat)
    (bs be : Fin N → Nat) (T : Fin N → Fin N → Real) (r c : Fin N) :
    |T r c| ≤ partitionBudget fp N bs be T r c := by
  unfold partitionBudget
  split
  · rename_i h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hTc : blockSubCoeff N T (bs r) (be r)
        ⟨r.val - bs r, by omega⟩ ⟨c.val - bs r, by omega⟩ = T r c := by
      unfold blockSubCoeff
      rw [dif_pos ⟨by omega, by omega⟩]
      have hr' : (⟨bs r + (r.val - bs r), by omega⟩ : Fin N) = r :=
        Fin.ext (show bs r + (r.val - bs r) = r.val by omega)
      have hc' : (⟨bs r + (c.val - bs r), by omega⟩ : Fin N) = c :=
        Fin.ext (show bs r + (c.val - bs r) = c.val by omega)
      rw [hr', hc']
    rw [← hTc]
    exact abs_le_flGEBudget fp _ _ _ _
  · exact le_refl _

/-- Three-way interval split of a full-row sum at one partition block
    (Chapter 16.2 block-substitution bookkeeping). -/
theorem sum_split_block_interval {N : Nat} (f : Fin N → Real) (K E : Nat)
    (hKE : K < E) (hEN : E ≤ N) :
    (∑ c : Fin N, f c) =
      (∑ c ∈ Finset.filter (fun c : Fin N => c.val < K) Finset.univ, f c) +
      (∑ v : Fin (E - K - 1 + 1), f ⟨K + v.val, by omega⟩) +
      (∑ c ∈ Finset.filter (fun c : Fin N => E ≤ c.val) Finset.univ,
        f c) := by
  have hinj : ∀ a : Fin (E - K - 1 + 1), a ∈ Finset.univ →
      ∀ b : Fin (E - K - 1 + 1), b ∈ Finset.univ →
      (⟨K + a.val, by omega⟩ : Fin N) = ⟨K + b.val, by omega⟩ → a = b :=
    fun a _ b _ hab => Fin.ext (by
      have := Fin.mk.inj hab
      omega)
  have himg : Finset.image
      (fun v : Fin (E - K - 1 + 1) => (⟨K + v.val, by omega⟩ : Fin N))
      Finset.univ =
      Finset.filter (fun c : Fin N => K ≤ c.val ∧ c.val < E)
        Finset.univ := by
    ext c
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_filter]
    constructor
    · rintro ⟨v, rfl⟩
      have := v.isLt
      constructor
      · simp
      · simp
        omega
    · intro hc
      exact ⟨⟨c.val - K, by omega⟩, Fin.ext (by simp; omega)⟩
  have hmid : (∑ v : Fin (E - K - 1 + 1), f ⟨K + v.val, by omega⟩) =
      ∑ c ∈ Finset.filter (fun c : Fin N => K ≤ c.val ∧ c.val < E)
        Finset.univ, f c := by
    rw [← himg, Finset.sum_image hinj]
  rw [hmid]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun c : Fin N => c.val < K)]
  have h2 : (∑ c ∈ Finset.filter (fun c : Fin N => ¬(c.val < K))
      Finset.univ, f c) =
      (∑ c ∈ Finset.filter (fun c : Fin N => K ≤ c.val ∧ c.val < E)
        Finset.univ, f c) +
      (∑ c ∈ Finset.filter (fun c : Fin N => E ≤ c.val) Finset.univ,
        f c) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.filter (fun c : Fin N => ¬(c.val < K)) Finset.univ)
      (fun c : Fin N => c.val < E)]
    congr 1
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  rw [h2]
  ring

/-- **Higham, 2nd ed., Chapter 8.1, Theorem 8.5 row analysis, as used by
    Chapter 16.2, equation (16.7), quasi-quasi block form** (uniform block
    row).  Every row `r` of the computed partitioned block back substitution
    satisfies the exactly perturbed row equation
    `sum_c (T r c + E c) x^_c = bb r` with
    `|E c| <= gamma_{N + 5B} * partitionBudget r c`, under the block
    upper-triangular zero pattern, the block pivot certificate, and a block
    size bound `be r - bs r <= B`. -/
theorem flPartitionBackSub_row (fp : FPModel) (N B : Nat)
    (bs be : Fin N → Nat) (T : Fin N → Fin N → Real) (bb : Fin N → Real)
    (hpart : IsBlockPartitionFn N bs be)
    (hz : ∀ a c : Fin N, c.val < bs a → T a c = 0)
    (r : Fin N)
    (hpiv : flGEPivots fp (be r - bs r - 1)
      (blockSubCoeff N T (bs r) (be r)))
    (hB : be r - bs r ≤ B)
    (hgv : gammaValid fp (N + 5 * B)) :
    ∃ E : Fin N → Real,
      (∀ c : Fin N, |E c| ≤ gamma fp (N + 5 * B) *
        partitionBudget fp N bs be T r c) ∧
      (∑ c : Fin N,
        (T r c + E c) * flPartitionBackSub fp N bs be T bb c) = bb r := by
  obtain ⟨hg1, hg2, hg3⟩ := hpart.1 r
  have hu1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hgv
  have hu : fp.u < 1 := by
    have h := hu1
    unfold gammaValid at h
    simpa using h
  have hγnn : 0 ≤ gamma fp (N + 5 * B) := gamma_nonneg fp hgv
  -- Kernel backward error on the diagonal block of `r`.
  obtain ⟨ΔM, hΔMb, hΔMeq⟩ := flGESolve_backward_error fp
    (be r - bs r - 1)
    (blockSubCoeff N T (bs r) (be r))
    (blockSubRhs fp N T bb (flPartitionBackSub fp N bs be T bb)
      (bs r) (be r))
    hpiv (gammaValid_mono fp (by omega) hgv)
  set u0 : Fin (be r - bs r - 1 + 1) := ⟨r.val - bs r, by omega⟩
    with hu0_def
  have hrowk := hΔMeq u0
  -- Identify the kernel values with the engine values on block columns.
  have hxblk : ∀ v : Fin (be r - bs r - 1 + 1),
      flGESolve fp (be r - bs r - 1)
        (blockSubCoeff N T (bs r) (be r))
        (blockSubRhs fp N T bb (flPartitionBackSub fp N bs be T bb)
          (bs r) (be r)) v =
      flPartitionBackSub fp N bs be T bb
        ⟨bs r + v.val, by have := v.isLt; omega⟩ :=
    fun v => (flPartitionBackSub_mem_block fp N bs be T bb hpart r v
      (by have := v.isLt; omega)).symm
  -- The block coefficient row is the `T` row.
  have hcoeff : ∀ v : Fin (be r - bs r - 1 + 1),
      blockSubCoeff N T (bs r) (be r) u0 v =
        T r ⟨bs r + v.val, by have := v.isLt; omega⟩ := by
    intro v
    have hval : u0.val = r.val - bs r := rfl
    unfold blockSubCoeff
    rw [dif_pos ⟨by omega, by have := v.isLt; omega⟩]
    congr 1
    apply Fin.ext
    show bs r + u0.val = r.val
    omega
  -- The block right-hand side of the `r` row is the row fold.
  have hrhs : blockSubRhs fp N T bb
      (flPartitionBackSub fp N bs be T bb) (bs r) (be r) u0 =
      quasiRowFold fp N T bb (flPartitionBackSub fp N bs be T bb) r
        (be r - 1) := by
    have hval : u0.val = r.val - bs r := rfl
    unfold blockSubRhs
    rw [dif_pos (by omega : bs r + u0.val < N)]
    have hidx : (⟨bs r + u0.val, by omega⟩ : Fin N) = r := by
      apply Fin.ext
      show bs r + u0.val = r.val
      omega
    rw [hidx]
  -- Tight fold analysis of the `r` row.
  obtain ⟨P, β, φ, hPpos, hβP, hβ, hφ, hfold⟩ := quasiRowFold_tight fp N
    T bb (flPartitionBackSub fp N bs be T bb) r (be r - 1) (by omega) hu
    (gammaValid_mono fp (by omega) hgv)
  have hsetEq : Finset.filter (fun j : Fin N => be r - 1 < j.val)
      Finset.univ =
      Finset.filter (fun j : Fin N => be r ≤ j.val) Finset.univ := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hsetEq] at hfold
  -- The master row equation.
  have hEq : (∑ v, (blockSubCoeff N T (bs r) (be r) u0 v + ΔM u0 v) *
      flPartitionBackSub fp N bs be T bb
        ⟨bs r + v.val, by have := v.isLt; omega⟩) =
      (bb r - ∑ j ∈ Finset.filter (fun j : Fin N => be r ≤ j.val)
          Finset.univ,
          T r j * flPartitionBackSub fp N bs be T bb j * (1 + φ j)) *
        P := by
    rw [← hfold, ← hrhs, ← hrowk]
    apply Finset.sum_congr rfl
    intro v _
    rw [hxblk v]
  -- The row perturbation.
  refine ⟨fun c =>
    if hc : bs r ≤ c.val ∧ c.val < be r then
      (T r c + ΔM u0 ⟨c.val - bs r, by omega⟩) * (1 + β) - T r c
    else if be r - 1 < c.val then T r c * φ c
    else 0, ?_, ?_⟩
  · -- Componentwise bounds.
    intro c
    simp only []
    by_cases hc : bs r ≤ c.val ∧ c.val < be r
    · rw [dif_pos hc]
      set v : Fin (be r - bs r - 1 + 1) := ⟨c.val - bs r, by omega⟩
        with hv_def
      have hval : v.val = c.val - bs r := rfl
      have hcv : (⟨bs r + v.val, by have := v.isLt; omega⟩ : Fin N) = c := by
        apply Fin.ext
        show bs r + v.val = c.val
        omega
      have hTc : blockSubCoeff N T (bs r) (be r) u0 v = T r c := by
        rw [hcoeff v, hcv]
      have hbase : |T r c| ≤
          flGEBudget fp (be r - bs r - 1)
            (blockSubCoeff N T (bs r) (be r)) u0 v := by
        rw [← hTc]
        exact abs_le_flGEBudget fp _ _ _ _
      have hbound := abs_perturb_scale_sub_le fp
        (5 * (be r - bs r - 1) + 5) (N - (be r - 1) - 1)
        (T r c) (ΔM u0 v) β
        (flGEBudget fp (be r - bs r - 1)
          (blockSubCoeff N T (bs r) (be r)) u0 v)
        (hΔMb u0 v) hbase hβ
        (gammaValid_mono fp (by omega) hgv)
      have hpb : partitionBudget fp N bs be T r c =
          flGEBudget fp (be r - bs r - 1)
            (blockSubCoeff N T (bs r) (be r)) u0 v := by
        unfold partitionBudget
        rw [dif_pos ⟨hc.1, hc.2, hg1, hg2, hg3⟩]
      rw [hpb]
      calc |(T r c + ΔM u0 v) * (1 + β) - T r c|
          ≤ gamma fp (5 * (be r - bs r - 1) + 5 + (N - (be r - 1) - 1)) *
            flGEBudget fp (be r - bs r - 1)
              (blockSubCoeff N T (bs r) (be r)) u0 v := hbound
        _ ≤ gamma fp (N + 5 * B) *
            flGEBudget fp (be r - bs r - 1)
              (blockSubCoeff N T (bs r) (be r)) u0 v :=
            mul_le_mul_of_nonneg_right
              (gamma_mono fp (by omega) hgv)
              (flGEBudget_nonneg fp _ _ _ _)
    · rw [dif_neg hc]
      by_cases hc2 : be r - 1 < c.val
      · rw [if_pos hc2]
        have hpb : partitionBudget fp N bs be T r c = |T r c| := by
          unfold partitionBudget
          rw [dif_neg (by
            intro hcon
            exact hc ⟨hcon.1, hcon.2.1⟩)]
        rw [hpb, abs_mul]
        calc |T r c| * |φ c|
            ≤ |T r c| * gamma fp (c.val - (be r - 1)) :=
              mul_le_mul_of_nonneg_left (hφ c hc2) (abs_nonneg _)
          _ ≤ |T r c| * gamma fp (N + 5 * B) :=
              mul_le_mul_of_nonneg_left
                (gamma_mono fp (by omega) hgv) (abs_nonneg _)
          _ = gamma fp (N + 5 * B) * |T r c| := by ring
      · rw [if_neg hc2, abs_zero]
        exact mul_nonneg hγnn (partitionBudget_nonneg fp N bs be T r c)
  · -- The row equation.
    simp only []
    rw [sum_split_block_interval _ (bs r) (be r) (by omega) hg3]
    have hfirst : (∑ c ∈ Finset.filter (fun c : Fin N => c.val < bs r)
        Finset.univ,
        (T r c + (if hc : bs r ≤ c.val ∧ c.val < be r then
          (T r c + ΔM u0 ⟨c.val - bs r, by omega⟩) * (1 + β) - T r c
        else if be r - 1 < c.val then T r c * φ c else 0)) *
          flPartitionBackSub fp N bs be T bb c) = 0 := by
      apply Finset.sum_eq_zero
      intro c hcm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcm
      have hTz : T r c = 0 := hz r c hcm
      rw [dif_neg (by omega : ¬(bs r ≤ c.val ∧ c.val < be r)),
        if_neg (by omega : ¬(be r - 1 < c.val)), hTz]
      ring
    have hmid : (∑ v : Fin (be r - bs r - 1 + 1),
        (T r ⟨bs r + v.val, by have := v.isLt; omega⟩ +
          (if hc : bs r ≤ (⟨bs r + v.val, by have := v.isLt; omega⟩ :
              Fin N).val ∧
              (⟨bs r + v.val, by have := v.isLt; omega⟩ : Fin N).val <
                be r then
            (T r ⟨bs r + v.val, by have := v.isLt; omega⟩ +
              ΔM u0 ⟨(⟨bs r + v.val, by have := v.isLt; omega⟩ :
                Fin N).val - bs r, by
                  show bs r + v.val - bs r < be r - bs r - 1 + 1
                  have := v.isLt
                  omega⟩) * (1 + β) -
              T r ⟨bs r + v.val, by have := v.isLt; omega⟩
          else if be r - 1 <
              (⟨bs r + v.val, by have := v.isLt; omega⟩ : Fin N).val then
            T r ⟨bs r + v.val, by have := v.isLt; omega⟩ *
              φ ⟨bs r + v.val, by have := v.isLt; omega⟩
          else 0)) *
          flPartitionBackSub fp N bs be T bb
            ⟨bs r + v.val, by have := v.isLt; omega⟩) =
        (∑ v, (blockSubCoeff N T (bs r) (be r) u0 v + ΔM u0 v) *
          flPartitionBackSub fp N bs be T bb
            ⟨bs r + v.val, by have := v.isLt; omega⟩) * (1 + β) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v _
      have hvlt := v.isLt
      rw [dif_pos ⟨by show bs r ≤ bs r + v.val; omega,
        by show bs r + v.val < be r; omega⟩]
      have hidx2 : (⟨(⟨bs r + v.val, by omega⟩ : Fin N).val - bs r,
          by
            show bs r + v.val - bs r < be r - bs r - 1 + 1
            omega⟩ : Fin (be r - bs r - 1 + 1)) = v := by
        apply Fin.ext
        show bs r + v.val - bs r = v.val
        omega
      have hTc : blockSubCoeff N T (bs r) (be r) u0 v =
          T r ⟨bs r + v.val, by omega⟩ := hcoeff v
      rw [hidx2, ← hTc]
      ring
    have hlast : (∑ c ∈ Finset.filter (fun c : Fin N => be r ≤ c.val)
        Finset.univ,
        (T r c + (if hc : bs r ≤ c.val ∧ c.val < be r then
          (T r c + ΔM u0 ⟨c.val - bs r, by omega⟩) * (1 + β) - T r c
        else if be r - 1 < c.val then T r c * φ c else 0)) *
          flPartitionBackSub fp N bs be T bb c) =
        ∑ c ∈ Finset.filter (fun c : Fin N => be r ≤ c.val) Finset.univ,
          T r c * flPartitionBackSub fp N bs be T bb c * (1 + φ c) := by
      apply Finset.sum_congr rfl
      intro c hcm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcm
      rw [dif_neg (by omega : ¬(bs r ≤ c.val ∧ c.val < be r)),
        if_pos (by omega : be r - 1 < c.val)]
      ring
    rw [hfirst, hmid, hlast]
    linear_combination (1 + β) * hEq +
      (bb r - ∑ j ∈ Finset.filter (fun j : Fin N => be r ≤ j.val)
        Finset.univ,
        T r j * flPartitionBackSub fp N bs be T bb j * (1 + φ j)) * hβP

/-- **Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.7) (quasi-quasi
    block form); block analogue of Chapter 8.1, Theorem 8.5.**  Let `T` be
    block upper triangular for the interval partition `bs`/`be` (entries
    left of the row's block vanish).  Under the per-block completion
    certificates (every computed pivot of every diagonal-block elimination
    nonzero) and a uniform block-size bound `B`, the computed partitioned
    block back substitution satisfies the exactly perturbed system

    `(T + DeltaT) x^ = bb` with
    `|DeltaT r c| <= gamma_{N + 5B} * partitionBudget r c`,

    the elimination budget being `flGEBudget` on the diagonal blocks and
    `|T r c|` elsewhere.  The uniform envelope `gamma_{N + 5B}` is the
    same-gamma-class realization of the printed unspecified constant: at
    most `N` fold operations composed with the size-`<= B` kernel
    envelope. -/
theorem flPartitionBackSub_backward_error (fp : FPModel) (N B : Nat)
    (bs be : Fin N → Nat) (T : Fin N → Fin N → Real) (bb : Fin N → Real)
    (hpart : IsBlockPartitionFn N bs be)
    (hz : ∀ a c : Fin N, c.val < bs a → T a c = 0)
    (hpiv : ∀ r : Fin N, flGEPivots fp (be r - bs r - 1)
      (blockSubCoeff N T (bs r) (be r)))
    (hB : ∀ r : Fin N, be r - bs r ≤ B)
    (hgv : gammaValid fp (N + 5 * B)) :
    ∃ ΔT : Fin N → Fin N → Real,
      (∀ r c : Fin N, |ΔT r c| ≤ gamma fp (N + 5 * B) *
        partitionBudget fp N bs be T r c) ∧
      ∀ r : Fin N, (∑ c : Fin N,
        (T r c + ΔT r c) * flPartitionBackSub fp N bs be T bb c) = bb r := by
  have hrow := fun r : Fin N =>
    flPartitionBackSub_row fp N B bs be T bb hpart hz r (hpiv r) (hB r) hgv
  choose Efun hEb hEeq using hrow
  exact ⟨fun r c => Efun r c, fun r c => hEb r c, fun r => hEeq r⟩

/-- **Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.7) (quasi-quasi
    block form, fully componentwise).**  Under the additional per-block
    budget-domination certificates `partitionBudget <= (1 + rho) |T|` — the
    standard componentwise control of the per-block GE fill-in — the mixed
    budget of `flPartitionBackSub_backward_error` collapses to the printed
    fully componentwise shape `|DeltaT| <= (1 + rho) gamma_{N + 5B} |T|`. -/
theorem flPartitionBackSub_backward_error_componentwise (fp : FPModel)
    (N B : Nat) (bs be : Fin N → Nat) (T : Fin N → Fin N → Real)
    (bb : Fin N → Real) (ρ : Real)
    (hpart : IsBlockPartitionFn N bs be)
    (hz : ∀ a c : Fin N, c.val < bs a → T a c = 0)
    (hpiv : ∀ r : Fin N, flGEPivots fp (be r - bs r - 1)
      (blockSubCoeff N T (bs r) (be r)))
    (hB : ∀ r : Fin N, be r - bs r ≤ B)
    (hgrow : ∀ r c : Fin N, partitionBudget fp N bs be T r c ≤
      (1 + ρ) * |T r c|)
    (hgv : gammaValid fp (N + 5 * B)) :
    ∃ ΔT : Fin N → Fin N → Real,
      (∀ r c : Fin N, |ΔT r c| ≤ (1 + ρ) * gamma fp (N + 5 * B) *
        |T r c|) ∧
      ∀ r : Fin N, (∑ c : Fin N,
        (T r c + ΔT r c) * flPartitionBackSub fp N bs be T bb c) = bb r := by
  obtain ⟨ΔT, hΔT, hEq⟩ := flPartitionBackSub_backward_error fp N B bs be
    T bb hpart hz hpiv hB hgv
  refine ⟨ΔT, ?_, hEq⟩
  intro r c
  calc |ΔT r c| ≤ gamma fp (N + 5 * B) *
      partitionBudget fp N bs be T r c := hΔT r c
    _ ≤ gamma fp (N + 5 * B) * ((1 + ρ) * |T r c|) :=
        mul_le_mul_of_nonneg_left (hgrow r c) (gamma_nonneg fp hgv)
    _ = (1 + ρ) * gamma fp (N + 5 * B) * |T r c| := by ring

/-- **Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.8) (quasi-quasi
    block form, engine level).**  The componentwise residual consequence of
    the block (16.7) model: each row residual of the computed partitioned
    block back substitution is bounded by `(1 + rho) gamma_{N + 5B}` times
    the absolute row action. -/
theorem flPartitionBackSub_componentwise_residual (fp : FPModel)
    (N B : Nat) (bs be : Fin N → Nat) (T : Fin N → Fin N → Real)
    (bb : Fin N → Real) (ρ : Real)
    (hpart : IsBlockPartitionFn N bs be)
    (hz : ∀ a c : Fin N, c.val < bs a → T a c = 0)
    (hpiv : ∀ r : Fin N, flGEPivots fp (be r - bs r - 1)
      (blockSubCoeff N T (bs r) (be r)))
    (hB : ∀ r : Fin N, be r - bs r ≤ B)
    (hgrow : ∀ r c : Fin N, partitionBudget fp N bs be T r c ≤
      (1 + ρ) * |T r c|)
    (hgv : gammaValid fp (N + 5 * B)) (r : Fin N) :
    |bb r - ∑ c : Fin N,
        T r c * flPartitionBackSub fp N bs be T bb c| ≤
      (1 + ρ) * gamma fp (N + 5 * B) *
        ∑ c : Fin N, |T r c| * |flPartitionBackSub fp N bs be T bb c| := by
  obtain ⟨ΔT, hΔT, hEq⟩ := flPartitionBackSub_backward_error_componentwise
    fp N B bs be T bb ρ hpart hz hpiv hB hgrow hgv
  have hdiff : bb r - (∑ c : Fin N,
      T r c * flPartitionBackSub fp N bs be T bb c) =
      ∑ c : Fin N, ΔT r c * flPartitionBackSub fp N bs be T bb c := by
    have h := hEq r
    rw [← h, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  rw [abs_mul]
  calc |ΔT r c| * |flPartitionBackSub fp N bs be T bb c|
      ≤ ((1 + ρ) * gamma fp (N + 5 * B) * |T r c|) *
        |flPartitionBackSub fp N bs be T bb c| :=
        mul_le_mul_of_nonneg_right (hΔT r c) (abs_nonneg _)
    _ = (1 + ρ) * gamma fp (N + 5 * B) *
        (|T r c| * |flPartitionBackSub fp N bs be T bb c|) := by ring

-- ============================================================
-- (3a) The interleaved two-column Bartels-Stewart ranking
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.4)-(16.6):
    the start of the diagonal-block group of a marked index (generic in the
    marking; used for the 2 x 2 row blocks of `R` and the 2 x 2 column
    blocks of `S`).  A second member of a marked adjacent pair points back
    to its top; every other index starts its own group. -/
def qqGrpStart (n : Nat) (dbl : Fin n → Bool) (k : Fin n) : Nat :=
  if 0 < k.val ∧ dbl ⟨k.val - 1, by omega⟩ = true then k.val - 1 else k.val

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.4)-(16.6):
    one past the end of the diagonal-block group of a marked index. -/
def qqGrpEnd (n : Nat) (dbl : Fin n → Bool) (k : Fin n) : Nat :=
  if 0 < k.val ∧ dbl ⟨k.val - 1, by omega⟩ = true then k.val + 1
  else if dbl k = true ∧ k.val + 1 < n then k.val + 2
  else k.val + 1

/-- Structural bounds of a group: it contains its index, ends within range,
    and has width 1 or 2. -/
theorem qqGrp_bounds (n : Nat) (dbl : Fin n → Bool) (k : Fin n) :
    qqGrpStart n dbl k ≤ k.val ∧ k.val < qqGrpEnd n dbl k ∧
      qqGrpEnd n dbl k ≤ n ∧
      1 ≤ qqGrpEnd n dbl k - qqGrpStart n dbl k ∧
      qqGrpEnd n dbl k - qqGrpStart n dbl k ≤ 2 := by
  have hk := k.isLt
  unfold qqGrpStart qqGrpEnd
  by_cases h1 : 0 < k.val ∧ dbl ⟨k.val - 1, by omega⟩ = true
  · rw [if_pos h1, if_pos h1]
    obtain ⟨h1a, -⟩ := h1
    omega
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : dbl k = true ∧ k.val + 1 < n
    · rw [if_pos h2]
      obtain ⟨-, h2b⟩ := h2
      omega
    · rw [if_neg h2]
      omega

/-- Under a well-formed pairing, every index lying inside a group carries
    the same group data (the groups partition the index range into
    intervals). -/
theorem qqGrp_mem_eq (n : Nat) (dbl : Fin n → Bool)
    (hp : IsQuasiBlockPairing n dbl) (k k' : Fin n)
    (h1 : qqGrpStart n dbl k ≤ k'.val) (h2 : k'.val < qqGrpEnd n dbl k) :
    qqGrpStart n dbl k' = qqGrpStart n dbl k ∧
      qqGrpEnd n dbl k' = qqGrpEnd n dbl k := by
  obtain ⟨-, hpk2⟩ := hp
  have hk := k.isLt
  have hk' := k'.isLt
  by_cases hks : 0 < k.val ∧ dbl ⟨k.val - 1, by omega⟩ = true
  · -- `k` is the second column of the marked pair `(k-1, k)`.
    have hgs : qqGrpStart n dbl k = k.val - 1 := by
      unfold qqGrpStart
      rw [if_pos hks]
    have hge : qqGrpEnd n dbl k = k.val + 1 := by
      unfold qqGrpEnd
      rw [if_pos hks]
    rw [hgs] at h1
    rw [hge] at h2
    rcases (by omega : k'.val = k.val - 1 ∨ k'.val = k.val) with hv | hv
    · -- `k'` is the top of the pair.
      have hdblk' : dbl k' = true := by
        have hk'eq : k' = ⟨k.val - 1, by omega⟩ := Fin.ext hv
        rw [hk'eq]
        exact hks.2
      have hk'1 : k'.val + 1 < n := by omega
      have hnots : ¬(0 < k'.val ∧ dbl ⟨k'.val - 1, by omega⟩ = true) := by
        rintro ⟨ha, hb⟩
        have hfalse := hpk2 ⟨k'.val - 1, by omega⟩ k'
          (show k'.val = k'.val - 1 + 1 by omega) hb
        rw [hdblk'] at hfalse
        exact Bool.noConfusion hfalse
      refine ⟨?_, ?_⟩
      · rw [hgs]
        unfold qqGrpStart
        rw [if_neg hnots]
        omega
      · rw [hge]
        unfold qqGrpEnd
        rw [if_neg hnots, if_pos ⟨hdblk', hk'1⟩]
        omega
    · have hk'eq : k' = k := Fin.ext hv
      rw [hk'eq]
      exact ⟨rfl, rfl⟩
  · by_cases hkt : dbl k = true ∧ k.val + 1 < n
    · -- `k` is the top of the marked pair `(k, k+1)`.
      have hgs : qqGrpStart n dbl k = k.val := by
        unfold qqGrpStart
        rw [if_neg hks]
      have hge : qqGrpEnd n dbl k = k.val + 2 := by
        unfold qqGrpEnd
        rw [if_neg hks, if_pos hkt]
      rw [hgs] at h1
      rw [hge] at h2
      rcases (by omega : k'.val = k.val ∨ k'.val = k.val + 1) with hv | hv
      · have hk'eq : k' = k := Fin.ext hv
        rw [hk'eq]
        exact ⟨rfl, rfl⟩
      · -- `k'` is the second column of the pair.
        have hsec : 0 < k'.val ∧ dbl ⟨k'.val - 1, by omega⟩ = true := by
          refine ⟨by omega, ?_⟩
          have hkeq : (⟨k'.val - 1, by omega⟩ : Fin n) = k :=
            Fin.ext (show k'.val - 1 = k.val by omega)
          rw [hkeq]
          exact hkt.1
        refine ⟨?_, ?_⟩
        · rw [hgs]
          unfold qqGrpStart
          rw [if_pos hsec]
          omega
        · rw [hge]
          unfold qqGrpEnd
          rw [if_pos hsec]
          omega
    · -- `k` is a singleton group.
      have hgs : qqGrpStart n dbl k = k.val := by
        unfold qqGrpStart
        rw [if_neg hks]
      have hge : qqGrpEnd n dbl k = k.val + 1 := by
        unfold qqGrpEnd
        rw [if_neg hks, if_neg hkt]
      rw [hgs] at h1
      rw [hge] at h2
      have hk'eq : k' = k := Fin.ext (by omega)
      rw [hk'eq]
      exact ⟨rfl, rfl⟩

/-- Two groups that overlap as intervals are equal (equal-or-disjoint). -/
theorem qqGrp_overlap_eq (n : Nat) (dbl : Fin n → Bool)
    (hp : IsQuasiBlockPairing n dbl) (k k' : Fin n)
    (h1 : qqGrpStart n dbl k' < qqGrpEnd n dbl k)
    (h2 : qqGrpStart n dbl k < qqGrpEnd n dbl k') :
    qqGrpStart n dbl k' = qqGrpStart n dbl k ∧
      qqGrpEnd n dbl k' = qqGrpEnd n dbl k := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := qqGrp_bounds n dbl k
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := qqGrp_bounds n dbl k'
  have htn : max (qqGrpStart n dbl k) (qqGrpStart n dbl k') < n := by
    omega
  have hm1 := qqGrp_mem_eq n dbl hp k
    ⟨max (qqGrpStart n dbl k) (qqGrpStart n dbl k'), htn⟩
    (by
      show qqGrpStart n dbl k ≤
        max (qqGrpStart n dbl k) (qqGrpStart n dbl k')
      omega)
    (by
      show max (qqGrpStart n dbl k) (qqGrpStart n dbl k') <
        qqGrpEnd n dbl k
      omega)
  have hm2 := qqGrp_mem_eq n dbl hp k'
    ⟨max (qqGrpStart n dbl k) (qqGrpStart n dbl k'), htn⟩
    (by
      show qqGrpStart n dbl k' ≤
        max (qqGrpStart n dbl k) (qqGrpStart n dbl k')
      omega)
    (by
      show max (qqGrpStart n dbl k) (qqGrpStart n dbl k') <
        qqGrpEnd n dbl k'
      omega)
  obtain ⟨hm1a, hm1b⟩ := hm1
  obtain ⟨hm2a, hm2b⟩ := hm2
  omega

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.6)-(16.7),
    quasi-quasi variant**: the interleaved two-column Bartels-Stewart
    elimination rank.  Column groups of the unknown (the singleton columns
    and the coupled column pairs of the quasi-triangular right factor `S`)
    are processed left to right; within one group the rows are processed
    bottom-up with the group's columns INTERLEAVED row by row, so that a
    2 x 2 block of `S` couples ADJACENT ranks.  Under this ranking the
    reordered (16.2) coefficient is block upper triangular with diagonal
    blocks of size `<= 4`. -/
def sylvesterQQRank (m n : Nat) (dblS : Fin n → Bool)
    (p : Prod (Fin n) (Fin m)) : Nat :=
  m * (n - qqGrpEnd n dblS p.1) +
    (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) * p.2.val +
    (p.1.val - qqGrpStart n dblS p.1)

/-- The interleaved rank lies in its group's rank range. -/
theorem sylvesterQQRank_range (m n : Nat) (dblS : Fin n → Bool)
    (p : Prod (Fin n) (Fin m)) :
    m * (n - qqGrpEnd n dblS p.1) ≤ sylvesterQQRank m n dblS p ∧
      sylvesterQQRank m n dblS p < m * (n - qqGrpStart n dblS p.1) ∧
      m * (n - qqGrpStart n dblS p.1) ≤ n * m := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := qqGrp_bounds n dblS p.1
  have hi := p.2.isLt
  have hkey : m * (n - qqGrpStart n dblS p.1) =
      m * (n - qqGrpEnd n dblS p.1) +
        (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) * m := by
    rw [Nat.mul_comm (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) m,
      ← Nat.mul_add]
    congr 1
    omega
  have hle : m * (n - qqGrpStart n dblS p.1) ≤ m * n :=
    Nat.mul_le_mul_left m (by omega)
  have hnm : m * n = n * m := Nat.mul_comm m n
  unfold sylvesterQQRank
  have hw : qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 1 ∨
      qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 2 := by omega
  rcases hw with hw | hw <;> rw [hw] at hkey ⊢ <;> omega

/-- The interleaved rank is a valid `Fin (n * m)` index. -/
theorem sylvesterQQRank_lt (m n : Nat) (dblS : Fin n → Bool)
    (p : Prod (Fin n) (Fin m)) : sylvesterQQRank m n dblS p < n * m := by
  have h := sylvesterQQRank_range m n dblS p
  omega

/-- The interleaved rank is injective under a well-formed pairing. -/
theorem sylvesterQQRank_injective (m n : Nat) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (p q : Prod (Fin n) (Fin m))
    (h : sylvesterQQRank m n dblS p = sylvesterQQRank m n dblS q) :
    p = q := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := qqGrp_bounds n dblS p.1
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := qqGrp_bounds n dblS q.1
  obtain ⟨hp1, hp2, -⟩ := sylvesterQQRank_range m n dblS p
  obtain ⟨hq1, hq2, -⟩ := sylvesterQQRank_range m n dblS q
  rcases Nat.lt_or_ge (qqGrpStart n dblS q.1) (qqGrpEnd n dblS p.1) with
    hd1 | hd1
  · rcases Nat.lt_or_ge (qqGrpStart n dblS p.1) (qqGrpEnd n dblS q.1) with
      hd2 | hd2
    · obtain ⟨hgs, hge⟩ := qqGrp_overlap_eq n dblS hSp p.1 q.1 hd1 hd2
      have h' := h
      unfold sylvesterQQRank at h'
      rw [hgs, hge] at h'
      rw [hgs] at hc1
      rw [hge] at hc2
      have hw : qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 1 ∨
          qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 2 := by omega
      have hvals : p.1.val = q.1.val ∧ p.2.val = q.2.val := by
        have him := p.2.isLt
        have hiq := q.2.isLt
        rcases hw with hw | hw <;> rw [hw] at h' <;> omega
      exact Prod.ext (Fin.ext hvals.1) (Fin.ext hvals.2)
    · exfalso
      have hmul : m * (n - qqGrpStart n dblS p.1) ≤
          m * (n - qqGrpEnd n dblS q.1) := Nat.mul_le_mul_left m (by omega)
      omega
  · exfalso
    have hmul : m * (n - qqGrpStart n dblS q.1) ≤
        m * (n - qqGrpEnd n dblS p.1) := Nat.mul_le_mul_left m (by omega)
    omega

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.6)-(16.7),
    quasi-quasi variant**: the interleaved two-column Bartels-Stewart index
    equivalence.  Well-formedness of the column pairing (`hSp`) makes the
    interleaved rank a bijection onto `Fin (n * m)`. -/
noncomputable def sylvesterQQIndexEquiv (m n : Nat) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) :
    Prod (Fin n) (Fin m) ≃ Fin (n * m) :=
  Equiv.ofBijective
    (fun p => ⟨sylvesterQQRank m n dblS p, sylvesterQQRank_lt m n dblS p⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun p q hpq => sylvesterQQRank_injective m n dblS hSp p q
        (by
          have hval := congrArg Fin.val hpq
          simpa using hval),
        by simp⟩)

/-- Rank formula of the interleaved index equivalence. -/
theorem sylvesterQQIndexEquiv_val (m n : Nat) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (p : Prod (Fin n) (Fin m)) :
    ((sylvesterQQIndexEquiv m n dblS hSp) p).val =
      sylvesterQQRank m n dblS p := rfl

/-- Decoding characterization: a product index whose rank matches decodes
    the given rank. -/
theorem sylvesterQQIndexEquiv_symm_eq (m n : Nat) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (a : Fin (n * m))
    (p : Prod (Fin n) (Fin m))
    (h : sylvesterQQRank m n dblS p = a.val) :
    (sylvesterQQIndexEquiv m n dblS hSp).symm a = p := by
  rw [Equiv.symm_apply_eq]
  exact Fin.ext h.symm

/-- The rank of the decoded product index recovers the rank position. -/
theorem sylvesterQQRank_symm (m n : Nat) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (a : Fin (n * m)) :
    sylvesterQQRank m n dblS
      ((sylvesterQQIndexEquiv m n dblS hSp).symm a) = a.val := by
  rw [← sylvesterQQIndexEquiv_val m n dblS hSp
    ((sylvesterQQIndexEquiv m n dblS hSp).symm a),
    Equiv.apply_symm_apply]

-- ============================================================
-- (3b) The reordered quasi-quasi system and its 1/2/4 partition
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.7), quasi-quasi
    variant: the reordered `nm x nm` coefficient array of the vectorized
    Schur-form Sylvester system, read at the interleaved two-column
    elimination ranks. -/
noncomputable def sylvesterQQBackSubCoeff (m n : Nat) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (R : RMatFn m m) (S : RMatFn n n) :
    Fin (n * m) → Fin (n * m) → Real :=
  fun a b =>
    sylvesterVecCoeff m n R S
      ((sylvesterQQIndexEquiv m n dblS hSp).symm a)
      ((sylvesterQQIndexEquiv m n dblS hSp).symm b)

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.7), quasi-quasi
    variant: the reordered right-hand side `vec(C~)` at the interleaved
    elimination ranks. -/
noncomputable def sylvesterQQBackSubRhs (m n : Nat) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (Ct : RMatFn m n) :
    Fin (n * m) → Real :=
  fun a => Matrix.vec Ct ((sylvesterQQIndexEquiv m n dblS hSp).symm a)

/-- Reading the reordered coefficient at the images of two product indices
    recovers the vec/Kronecker coefficient entry. -/
theorem sylvesterQQBackSubCoeff_reindex (m n : Nat) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (R : RMatFn m m) (S : RMatFn n n)
    (p q : Prod (Fin n) (Fin m)) :
    sylvesterQQBackSubCoeff m n dblS hSp R S
        (sylvesterQQIndexEquiv m n dblS hSp p)
        (sylvesterQQIndexEquiv m n dblS hSp q) =
      sylvesterVecCoeff m n R S p q := by
  unfold sylvesterQQBackSubCoeff
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Reading the reordered right-hand side at the image of a product index
    recovers the entry of `vec(C~)`. -/
theorem sylvesterQQBackSubRhs_reindex (m n : Nat) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (Ct : RMatFn m n)
    (p : Prod (Fin n) (Fin m)) :
    sylvesterQQBackSubRhs m n dblS hSp Ct
        (sylvesterQQIndexEquiv m n dblS hSp p) = Matrix.vec Ct p := by
  unfold sylvesterQQBackSubRhs
  rw [Equiv.symm_apply_apply]

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.6)-(16.7),
    quasi-quasi variant: the block START of the diagonal block containing a
    rank position — the rank of (top row of the `R` block, left column of
    the `S` group). -/
noncomputable def sylvesterQQBs (m n : Nat) (dblR : Fin m → Bool)
    (dblS : Fin n → Bool) (hSp : IsQuasiBlockPairing n dblS) :
    Fin (n * m) → Nat :=
  fun a =>
    m * (n - qqGrpEnd n dblS
        ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) +
      (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
          qqGrpStart n dblS
            ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) *
        qqGrpStart m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.6)-(16.7),
    quasi-quasi variant: one past the END of the diagonal block containing
    a rank position. -/
noncomputable def sylvesterQQBe (m n : Nat) (dblR : Fin m → Bool)
    (dblS : Fin n → Bool) (hSp : IsQuasiBlockPairing n dblS) :
    Fin (n * m) → Nat :=
  fun a =>
    m * (n - qqGrpEnd n dblS
        ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) +
      (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
          qqGrpStart n dblS
            ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) *
        qqGrpEnd m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2

/-- The interleaved 1/2/4 block structure is a well-formed interval
    partition (Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.7)). -/
theorem sylvesterQQPartition_valid (m n : Nat) (dblR : Fin m → Bool)
    (dblS : Fin n → Bool) (hRp : IsQuasiBlockPairing m dblR)
    (hSp : IsQuasiBlockPairing n dblS) :
    IsBlockPartitionFn (n * m) (sylvesterQQBs m n dblR dblS hSp)
      (sylvesterQQBe m n dblR dblS hSp) := by
  constructor
  · intro a
    set p := (sylvesterQQIndexEquiv m n dblS hSp).symm a with hp_def
    have hval : sylvesterQQRank m n dblS p = a.val :=
      sylvesterQQRank_symm m n dblS hSp a
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := qqGrp_bounds n dblS p.1
    obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := qqGrp_bounds m dblR p.2
    have hi := p.2.isLt
    unfold sylvesterQQRank at hval
    have hkey : m * (n - qqGrpStart n dblS p.1) =
        m * (n - qqGrpEnd n dblS p.1) +
          (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) * m := by
      rw [Nat.mul_comm (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) m,
        ← Nat.mul_add]
      congr 1
      omega
    have hle : m * (n - qqGrpStart n dblS p.1) ≤ m * n :=
      Nat.mul_le_mul_left m (by omega)
    have hnm : m * n = n * m := Nat.mul_comm m n
    show m * (n - qqGrpEnd n dblS p.1) +
        (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
          qqGrpStart m dblR p.2 ≤ a.val ∧
      a.val < m * (n - qqGrpEnd n dblS p.1) +
        (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
          qqGrpEnd m dblR p.2 ∧
      m * (n - qqGrpEnd n dblS p.1) +
        (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
          qqGrpEnd m dblR p.2 ≤ n * m
    have hw : qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 1 ∨
        qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 2 := by omega
    rcases hw with hw | hw <;> rw [hw] at hval hkey ⊢ <;> omega
  · intro a s h1 h2
    set p := (sylvesterQQIndexEquiv m n dblS hSp).symm a with hp_def
    set q := (sylvesterQQIndexEquiv m n dblS hSp).symm s with hq_def
    have hvala : sylvesterQQRank m n dblS p = a.val :=
      sylvesterQQRank_symm m n dblS hSp a
    have hvals : sylvesterQQRank m n dblS q = s.val :=
      sylvesterQQRank_symm m n dblS hSp s
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := qqGrp_bounds n dblS p.1
    obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := qqGrp_bounds n dblS q.1
    obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := qqGrp_bounds m dblR p.2
    have hi := p.2.isLt
    have hiq := q.2.isLt
    obtain ⟨hq1, hq2, -⟩ := sylvesterQQRank_range m n dblS q
    have h1' : m * (n - qqGrpEnd n dblS p.1) +
        (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
          qqGrpStart m dblR p.2 ≤ s.val := h1
    have h2' : s.val < m * (n - qqGrpEnd n dblS p.1) +
        (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
          qqGrpEnd m dblR p.2 := h2
    have hkey : m * (n - qqGrpStart n dblS p.1) =
        m * (n - qqGrpEnd n dblS p.1) +
          (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) * m := by
      rw [Nat.mul_comm (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) m,
        ← Nat.mul_add]
      congr 1
      omega
    have hwre : (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
        qqGrpEnd m dblR p.2 ≤
        (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) * m :=
      Nat.mul_le_mul_left _ hr3
    -- the S-groups of `p` and `q` coincide
    have hd1 : qqGrpStart n dblS q.1 < qqGrpEnd n dblS p.1 := by
      by_contra hcon
      push_neg at hcon
      have hmul : m * (n - qqGrpStart n dblS q.1) ≤
          m * (n - qqGrpEnd n dblS p.1) := Nat.mul_le_mul_left m (by omega)
      omega
    have hd2 : qqGrpStart n dblS p.1 < qqGrpEnd n dblS q.1 := by
      by_contra hcon
      push_neg at hcon
      have hmul : m * (n - qqGrpStart n dblS p.1) ≤
          m * (n - qqGrpEnd n dblS q.1) := Nat.mul_le_mul_left m (by omega)
      omega
    obtain ⟨hgs, hge⟩ := qqGrp_overlap_eq n dblS hSp p.1 q.1 hd1 hd2
    -- the R-blocks of `p` and `q` coincide
    unfold sylvesterQQRank at hvals
    rw [hgs] at hc1
    rw [hge] at hc2
    rw [hgs, hge] at hvals
    have hiq2 : qqGrpStart m dblR p.2 ≤ q.2.val ∧
        q.2.val < qqGrpEnd m dblR p.2 := by
      have hw : qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 1 ∨
          qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 2 := by omega
      rcases hw with hw | hw <;> rw [hw] at hvals h1' h2' <;> omega
    obtain ⟨hrq1, hrq2⟩ := qqGrp_mem_eq m dblR hRp p.2 q.2 hiq2.1 hiq2.2
    constructor
    · show m * (n - qqGrpEnd n dblS q.1) +
        (qqGrpEnd n dblS q.1 - qqGrpStart n dblS q.1) *
          qqGrpStart m dblR q.2 =
        m * (n - qqGrpEnd n dblS p.1) +
          (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
            qqGrpStart m dblR p.2
      rw [hgs, hge, hrq1]
    · show m * (n - qqGrpEnd n dblS q.1) +
        (qqGrpEnd n dblS q.1 - qqGrpStart n dblS q.1) *
          qqGrpEnd m dblR q.2 =
        m * (n - qqGrpEnd n dblS p.1) +
          (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
            qqGrpEnd m dblR p.2
      rw [hgs, hge, hrq2]

/-- The block width of the diagonal block of a rank position is the product
    of the column-group width and the row-block width (1, 2, or 4). -/
theorem sylvesterQQBlockSize (m n : Nat) (dblR : Fin m → Bool)
    (dblS : Fin n → Bool) (hSp : IsQuasiBlockPairing n dblS)
    (a : Fin (n * m)) :
    sylvesterQQBe m n dblR dblS hSp a - sylvesterQQBs m n dblR dblS hSp a =
      (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
          qqGrpStart n dblS
            ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) *
        (qqGrpEnd m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2 -
          qqGrpStart m dblR
            ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2) := by
  set p := (sylvesterQQIndexEquiv m n dblS hSp).symm a with hp_def
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := qqGrp_bounds n dblS p.1
  show (m * (n - qqGrpEnd n dblS p.1) +
      (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
        qqGrpEnd m dblR p.2) -
      (m * (n - qqGrpEnd n dblS p.1) +
        (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
          qqGrpStart m dblR p.2) =
    (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
      (qqGrpEnd m dblR p.2 - qqGrpStart m dblR p.2)
  have hw : qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 1 ∨
      qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 2 := by omega
  rcases hw with hw | hw <;> rw [hw] <;> omega

/-- Every diagonal block of the interleaved partition has size at most 4
    (Higham, 2nd ed., Chapter 16.2, p. 308: the printed algorithm solves
    systems of order at most 4). -/
theorem sylvesterQQBlockSize_le (m n : Nat) (dblR : Fin m → Bool)
    (dblS : Fin n → Bool) (hSp : IsQuasiBlockPairing n dblS)
    (a : Fin (n * m)) :
    sylvesterQQBe m n dblR dblS hSp a -
      sylvesterQQBs m n dblR dblS hSp a ≤ 4 := by
  rw [sylvesterQQBlockSize m n dblR dblS hSp a]
  set p := (sylvesterQQIndexEquiv m n dblS hSp).symm a with hp_def
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := qqGrp_bounds n dblS p.1
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := qqGrp_bounds m dblR p.2
  have hw : qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 1 ∨
      qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 2 := by omega
  rcases hw with hw | hw <;> rw [hw] <;> omega

/-- **Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), quasi-quasi
    variant**: the explicit diagonal-block coefficient of the interleaved
    substitution, in factor entries.  For a block anchored at the left
    column `k0` of an `S` group of width `w` and the top row `i0` of an `R`
    block, the entry at interleaved offsets `(uo, vo)` is

    `(if uo % w = vo % w then R_{i0+uo/w, i0+vo/w} else 0) -
     (if uo / w = vo / w then S_{k0+vo%w, k0+uo%w} else 0)`,

    the shifted 2 x 2 / 4 x 4 systems of the printed algorithm.  (At
    `w = 1`, block width 1 or 2, this is the Wave-15 shifted block
    `[[R_ii - S_kk, R_ii'], [R_i'i, R_i'i' - S_kk]]`; at `w = 2` it is the
    two-coupled-columns block with the `-S_{k+1,k}` / `-S_{k,k+1}`
    couplings.) -/
noncomputable def sylvesterQQBlockEntry (m n : Nat) (R : RMatFn m m)
    (S : RMatFn n n) (k0 : Fin n) (i0 : Fin m) (w : Nat)
    (uo vo : Nat) : Real :=
  (if h : uo % w = vo % w ∧ i0.val + uo / w < m ∧ i0.val + vo / w < m then
    R ⟨i0.val + uo / w, h.2.1⟩ ⟨i0.val + vo / w, h.2.2⟩
  else 0) -
  (if h : uo / w = vo / w ∧ k0.val + uo % w < n ∧ k0.val + vo % w < n then
    S ⟨k0.val + vo % w, h.2.2⟩ ⟨k0.val + uo % w, h.2.1⟩
  else 0)

/-- Decode of a rank position inside a diagonal block: block offset `o`
    addresses column `gs + o % w` of the `S` group and row `rs + o / w` of
    the `R` block (the interleaved ordering). -/
theorem sylvesterQQ_symm_block_offset (m n : Nat) (dblR : Fin m → Bool)
    (dblS : Fin n → Bool) (hSp : IsQuasiBlockPairing n dblS)
    (a : Fin (n * m)) (o : Nat)
    (ho : o < (qqGrpEnd n dblS
          ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) *
      (qqGrpEnd m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2 -
        qqGrpStart m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2))
    (hlt : sylvesterQQBs m n dblR dblS hSp a + o < n * m)
    (hn1 : qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 +
      o % (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS
          ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) < n)
    (hm1 : qqGrpStart m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2 +
      o / (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS
          ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) < m) :
    (sylvesterQQIndexEquiv m n dblS hSp).symm
        ⟨sylvesterQQBs m n dblR dblS hSp a + o, hlt⟩ =
      (⟨qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 +
          o % (qqGrpEnd n dblS
              ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
            qqGrpStart n dblS
              ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1), hn1⟩,
        ⟨qqGrpStart m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2 +
          o / (qqGrpEnd n dblS
              ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
            qqGrpStart n dblS
              ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1), hm1⟩) := by
  set p := (sylvesterQQIndexEquiv m n dblS hSp).symm a with hp_def
  set w := qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 with hw_def
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := qqGrp_bounds n dblS p.1
  have hw0 : 0 < w := by omega
  have hmod : o % w < w := Nat.mod_lt o hw0
  obtain ⟨hga, hgb⟩ := qqGrp_mem_eq n dblS hSp p.1
    ⟨qqGrpStart n dblS p.1 +
      o % (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1), hn1⟩
    (by
      show qqGrpStart n dblS p.1 ≤ qqGrpStart n dblS p.1 +
        o % (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1)
      omega)
    (by
      show qqGrpStart n dblS p.1 +
        o % (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) <
        qqGrpEnd n dblS p.1
      rw [← hw_def]
      omega)
  apply sylvesterQQIndexEquiv_symm_eq
  show sylvesterQQRank m n dblS _ = sylvesterQQBs m n dblR dblS hSp a + o
  unfold sylvesterQQRank
  show m * (n - qqGrpEnd n dblS
      (⟨qqGrpStart n dblS p.1 +
        o % (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1), hn1⟩ : Fin n)) +
    (qqGrpEnd n dblS
        (⟨qqGrpStart n dblS p.1 +
          o % (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1), hn1⟩ : Fin n) -
      qqGrpStart n dblS
        (⟨qqGrpStart n dblS p.1 +
          o % (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1), hn1⟩ : Fin n)) *
      (qqGrpStart m dblR p.2 +
        o / (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1)) +
    (qqGrpStart n dblS p.1 +
        o % (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) -
      qqGrpStart n dblS
        (⟨qqGrpStart n dblS p.1 +
          o % (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1), hn1⟩ : Fin n)) =
    sylvesterQQBs m n dblR dblS hSp a + o
  rw [hga, hgb]
  have hbs : sylvesterQQBs m n dblR dblS hSp a =
      m * (n - qqGrpEnd n dblS p.1) +
        (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
          qqGrpStart m dblR p.2 := rfl
  have hmuladd : (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
      (qqGrpStart m dblR p.2 +
        o / (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1)) =
      (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
          qqGrpStart m dblR p.2 +
        (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
          (o / (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1)) :=
    Nat.mul_add _ _ _
  have hdm : (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
      (o / (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1)) +
      o % (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) = o :=
    Nat.div_add_mod o _
  omega

/-- **Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), quasi-quasi
    variant**: identification of the reordered diagonal block with the
    explicit factor-entry block.  Every entry of the diagonal block of the
    reordered coefficient is the corresponding `sylvesterQQBlockEntry` of
    the decoded factor data. -/
theorem sylvesterQQBlockCoeff_entry (m n : Nat) (dblR : Fin m → Bool)
    (dblS : Fin n → Bool) (hRp : IsQuasiBlockPairing m dblR)
    (hSp : IsQuasiBlockPairing n dblS) (R : RMatFn m m) (S : RMatFn n n)
    (a : Fin (n * m))
    (u v : Fin (sylvesterQQBe m n dblR dblS hSp a -
      sylvesterQQBs m n dblR dblS hSp a - 1 + 1)) :
    blockSubCoeff (n * m) (sylvesterQQBackSubCoeff m n dblS hSp R S)
        (sylvesterQQBs m n dblR dblS hSp a)
        (sylvesterQQBe m n dblR dblS hSp a) u v =
      sylvesterQQBlockEntry m n R S
        ⟨qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1,
          by
            obtain ⟨h1, h2, -⟩ := qqGrp_bounds n dblS
              ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1
            have := ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1.isLt
            omega⟩
        ⟨qqGrpStart m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2,
          by
            obtain ⟨h1, h2, -⟩ := qqGrp_bounds m dblR
              ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2
            have := ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2.isLt
            omega⟩
        (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
          qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1)
        u.val v.val := by
  set p := (sylvesterQQIndexEquiv m n dblS hSp).symm a with hp_def
  set w := qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 with hw_def
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := qqGrp_bounds n dblS p.1
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := qqGrp_bounds m dblR p.2
  have hpart := sylvesterQQPartition_valid m n dblR dblS hRp hSp
  obtain ⟨hg1, hg2, hg3⟩ := hpart.1 a
  have hsz := sylvesterQQBlockSize m n dblR dblS hSp a
  have hszge : 1 ≤ sylvesterQQBe m n dblR dblS hSp a -
      sylvesterQQBs m n dblR dblS hSp a := by omega
  have huv : u.val < sylvesterQQBe m n dblR dblS hSp a -
      sylvesterQQBs m n dblR dblS hSp a := by
    have := u.isLt
    omega
  have hvv : v.val < sylvesterQQBe m n dblR dblS hSp a -
      sylvesterQQBs m n dblR dblS hSp a := by
    have := v.isLt
    omega
  have hw0 : 0 < w := by omega
  -- bounds for the decoded components
  have humod : u.val % w < w := Nat.mod_lt _ hw0
  have hvmod : v.val % w < w := Nat.mod_lt _ hw0
  rw [← hp_def, ← hw_def] at hsz
  have hudiv : u.val / w <
      qqGrpEnd m dblR p.2 - qqGrpStart m dblR p.2 := by
    rw [Nat.div_lt_iff_lt_mul hw0]
    rw [Nat.mul_comm]
    omega
  have hvdiv : v.val / w <
      qqGrpEnd m dblR p.2 - qqGrpStart m dblR p.2 := by
    rw [Nat.div_lt_iff_lt_mul hw0]
    rw [Nat.mul_comm]
    omega
  have hn1u : qqGrpStart n dblS p.1 + u.val % w < n := by omega
  have hn1v : qqGrpStart n dblS p.1 + v.val % w < n := by omega
  have hm1u : qqGrpStart m dblR p.2 + u.val / w < m := by omega
  have hm1v : qqGrpStart m dblR p.2 + v.val / w < m := by omega
  have hltu : sylvesterQQBs m n dblR dblS hSp a + u.val < n * m := by
    omega
  have hltv : sylvesterQQBs m n dblR dblS hSp a + v.val < n * m := by
    omega
  have hdecu := sylvesterQQ_symm_block_offset m n dblR dblS hSp a u.val
    (by rw [← hp_def, ← hw_def]; omega) hltu hn1u hm1u
  have hdecv := sylvesterQQ_symm_block_offset m n dblR dblS hSp a v.val
    (by rw [← hp_def, ← hw_def]; omega) hltv hn1v hm1v
  -- unfold the block coefficient
  unfold blockSubCoeff
  rw [dif_pos ⟨hltu, hltv⟩]
  show sylvesterVecCoeff m n R S
      ((sylvesterQQIndexEquiv m n dblS hSp).symm
        ⟨sylvesterQQBs m n dblR dblS hSp a + u.val, hltu⟩)
      ((sylvesterQQIndexEquiv m n dblS hSp).symm
        ⟨sylvesterQQBs m n dblR dblS hSp a + v.val, hltv⟩) = _
  rw [hdecu, hdecv, Wave14.sylvesterVecCoeff_pair_apply]
  unfold sylvesterQQBlockEntry
  -- match the four branches (RAW atoms throughout so `omega` sees h1/h2 directly)
  by_cases h1 : u.val %
      (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) =
    v.val %
      (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1)
  · by_cases h2 : u.val /
        (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
          qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) =
      v.val /
        (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
          qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1)
    · rw [if_pos (show _ = _ from Fin.ext (by
          show qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 +
              u.val % (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) =
            qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 +
              v.val % (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1)
          omega)),
        if_pos (show _ = _ from Fin.ext (by
          show qqGrpStart m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2 +
              u.val / (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) =
            qqGrpStart m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2 +
              v.val / (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1)
          omega)),
        dif_pos ⟨h1, hm1u, hm1v⟩, dif_pos ⟨h2, hn1u, hn1v⟩]
    · rw [if_pos (show _ = _ from Fin.ext (by
          show qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 +
              u.val % (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) =
            qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 +
              v.val % (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1)
          omega)),
        if_neg (show ¬(_ = _) from fun hcon => h2 (by
          have hv : qqGrpStart m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2 +
              u.val / (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) =
            qqGrpStart m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2 +
              v.val / (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) := congrArg Fin.val hcon
          omega)),
        dif_pos ⟨h1, hm1u, hm1v⟩,
        dif_neg (show ¬(_ ∧ _ ∧ _) from fun hcon => h2 hcon.1)]
  · by_cases h2 : u.val /
        (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
          qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) =
      v.val /
        (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
          qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1)
    · rw [if_neg (show ¬(_ = _) from fun hcon => h1 (by
          have hv : qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 +
              u.val % (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) =
            qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 +
              v.val % (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) := congrArg Fin.val hcon
          omega)),
        if_pos (show _ = _ from Fin.ext (by
          show qqGrpStart m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2 +
              u.val / (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) =
            qqGrpStart m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2 +
              v.val / (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1)
          omega)),
        dif_neg (show ¬(_ ∧ _ ∧ _) from fun hcon => h1 hcon.1),
        dif_pos ⟨h2, hn1u, hn1v⟩]
    · rw [if_neg (show ¬(_ = _) from fun hcon => h1 (by
          have hv : qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 +
              u.val % (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) =
            qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 +
              v.val % (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) := congrArg Fin.val hcon
          omega)),
        if_neg (show ¬(_ = _) from fun hcon => h2 (by
          have hv : qqGrpStart m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2 +
              u.val / (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) =
            qqGrpStart m dblR ((sylvesterQQIndexEquiv m n dblS hSp).symm a).2 +
              v.val / (qqGrpEnd n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1 -
        qqGrpStart n dblS ((sylvesterQQIndexEquiv m n dblS hSp).symm a).1) := congrArg Fin.val hcon
          omega)),
        dif_neg (show ¬(_ ∧ _ ∧ _) from fun hcon => h1 hcon.1),
        dif_neg (show ¬(_ ∧ _ ∧ _) from fun hcon => h2 hcon.1)]

/-- **Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.7), quasi-quasi
    variant**: block-triangular zero pattern.  For a quasi-triangular pair
    (`R` with row pairs `dblR`, `S` with column pairs `dblS`), the reordered
    coefficient vanishes strictly to the left of the diagonal block of each
    row — the structural fact that makes the interleaved reordered system
    block upper triangular with 1/2/4 diagonal blocks. -/
theorem sylvesterQQBackSubCoeff_zero (m n : Nat) (dblR : Fin m → Bool)
    (dblS : Fin n → Bool) (hRp : IsQuasiBlockPairing m dblR)
    (hSp : IsQuasiBlockPairing n dblS) (R : RMatFn m m) (S : RMatFn n n)
    (hR : IsQuasiUpperTriangularFn m R dblR)
    (hS : IsQuasiUpperTriangularFn n S dblS) :
    ∀ a c : Fin (n * m), c.val < sylvesterQQBs m n dblR dblS hSp a →
      sylvesterQQBackSubCoeff m n dblS hSp R S a c = 0 := by
  intro a c hlt
  set p := (sylvesterQQIndexEquiv m n dblS hSp).symm a with hp_def
  set q := (sylvesterQQIndexEquiv m n dblS hSp).symm c with hq_def
  have hvala : sylvesterQQRank m n dblS p = a.val :=
    sylvesterQQRank_symm m n dblS hSp a
  have hvalc : sylvesterQQRank m n dblS q = c.val :=
    sylvesterQQRank_symm m n dblS hSp c
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := qqGrp_bounds n dblS p.1
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := qqGrp_bounds n dblS q.1
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := qqGrp_bounds m dblR p.2
  have hi := p.2.isLt
  have hiq := q.2.isLt
  have hlt' : c.val < m * (n - qqGrpEnd n dblS p.1) +
      (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) *
        qqGrpStart m dblR p.2 := hlt
  have hkey : m * (n - qqGrpStart n dblS p.1) =
      m * (n - qqGrpEnd n dblS p.1) +
        (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) * m := by
    rw [Nat.mul_comm (qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1) m,
      ← Nat.mul_add]
    congr 1
    omega
  show sylvesterVecCoeff m n R S p q = 0
  rw [Wave14.sylvesterVecCoeff_pair_apply]
  by_cases hcol : p.1 = q.1
  · by_cases hrow : p.2 = q.2
    · exfalso
      have hac : a = c := by
        have hpq : p = q := Prod.ext hcol hrow
        exact (sylvesterQQIndexEquiv m n dblS hSp).symm.injective hpq
      have hbs := (sylvesterQQPartition_valid m n dblR dblS hRp hSp).1 c
      rw [hac] at hlt
      omega
    · rw [if_pos hcol, if_neg hrow, sub_zero]
      -- same column: below the R block
      unfold sylvesterQQRank at hvalc
      rw [← hcol] at hvalc
      have hiqlt : q.2.val < qqGrpStart m dblR p.2 := by
        have hw : qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 1 ∨
            qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 2 := by omega
        rcases hw with hw | hw <;> rw [hw] at hvalc hlt' <;> omega
      by_cases hadj : q.2.val + 1 = p.2.val
      · -- adjacent rows: the subdiagonal mark must be off
        have hdbl : dblR q.2 = false := by
          by_contra hcon
          have hcon' : dblR q.2 = true := by
            rcases Bool.eq_false_or_eq_true (dblR q.2) with hb | hb
            · exact hb
            · exact absurd hb hcon
          have hsec : 0 < p.2.val ∧ dblR ⟨p.2.val - 1, by omega⟩ = true := by
            refine ⟨by omega, ?_⟩
            have hkeq : (⟨p.2.val - 1, by omega⟩ : Fin m) = q.2 :=
              Fin.ext (show p.2.val - 1 = q.2.val by omega)
            rw [hkeq]
            exact hcon'
          have hrs : qqGrpStart m dblR p.2 = p.2.val - 1 := by
            unfold qqGrpStart
            rw [if_pos hsec]
          omega
        exact hR.2 p.2 q.2 hadj hdbl
      · exact hR.1 p.2 q.2 (by omega)
  · by_cases hrow : p.2 = q.2
    · rw [if_neg hcol, if_pos hrow]
      have hSz : S q.1 p.1 = 0 := by
        have hi2 : q.2.val = p.2.val := by rw [hrow]
        rcases Nat.lt_or_ge (qqGrpStart n dblS q.1) (qqGrpEnd n dblS p.1)
          with hd1 | hd1
        · rcases Nat.lt_or_ge (qqGrpStart n dblS p.1) (qqGrpEnd n dblS q.1)
            with hd2 | hd2
          · -- same S-group: contradicts `c` lying left of the block
            exfalso
            obtain ⟨hgs, hge⟩ := qqGrp_overlap_eq n dblS hSp p.1 q.1 hd1 hd2
            unfold sylvesterQQRank at hvalc
            rw [hgs] at hc1
            rw [hge] at hc2
            rw [hgs, hge] at hvalc
            have hw : qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 1 ∨
                qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 2 := by omega
            rcases hw with hw | hw <;> rw [hw] at hvalc hlt' <;> omega
          · -- `q`'s group entirely left: rank of `c` would be too large
            exfalso
            have hmul : m * (n - qqGrpStart n dblS p.1) ≤
                m * (n - qqGrpEnd n dblS q.1) :=
              Nat.mul_le_mul_left m (by omega)
            obtain ⟨hq1, -, -⟩ := sylvesterQQRank_range m n dblS q
            have hw : qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 1 ∨
                qqGrpEnd n dblS p.1 - qqGrpStart n dblS p.1 = 2 := by omega
            rcases hw with hw | hw <;> rw [hw] at hkey hlt' <;> omega
        · -- `q`'s group strictly to the right of `p`'s group
          have hpq1 : p.1.val < q.1.val := by omega
          by_cases hadj : p.1.val + 1 = q.1.val
          · have hdbl : dblS p.1 = false := by
              by_contra hcon
              have hcon' : dblS p.1 = true := by
                rcases Bool.eq_false_or_eq_true (dblS p.1) with hb | hb
                · exact hb
                · exact absurd hb hcon
              have hnots : ¬(0 < p.1.val ∧
                  dblS ⟨p.1.val - 1, by omega⟩ = true) := by
                rintro ⟨ha, hb⟩
                have hfalse := hSp.2 ⟨p.1.val - 1, by omega⟩ p.1
                  (show p.1.val = p.1.val - 1 + 1 by omega) hb
                rw [hcon'] at hfalse
                exact Bool.noConfusion hfalse
              have hgep : qqGrpEnd n dblS p.1 = p.1.val + 2 := by
                unfold qqGrpEnd
                rw [if_neg hnots, if_pos ⟨hcon', by omega⟩]
              omega
            exact hS.2 q.1 p.1 hadj hdbl
          · exact hS.1 q.1 p.1 (by omega)
      rw [hSz]
      ring
    · rw [if_neg hcol, if_neg hrow]
      ring

end Wave16

end NumStability
