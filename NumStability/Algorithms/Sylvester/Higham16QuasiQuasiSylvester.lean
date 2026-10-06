-- Algorithms/Sylvester/Higham16QuasiQuasiSylvester.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 16.2, pp. 307-308, equations (16.6)-(16.8), fully quasi-triangular
-- (real Schur) variant, Sylvester level.  Companion endpoint file to
-- `Higham16QuasiQuasiRounded`: the engine file proved the parametric rounded
-- Gaussian-elimination kernel (`flGESolve` with its Theorems 9.3-9.4
-- backward error), the rounded block back substitution over an interval
-- block partition (`flPartitionBackSub` with its Theorem 8.5-style block
-- backward error), and the quasi-quasi structural layer: the interleaved
-- two-column Bartels-Stewart ranking `sylvesterQQIndexEquiv`, under which
-- the (16.2) coefficient `P = I_n kron R - S^T kron I_m` of a
-- quasi-triangular pair (`R` with 2 x 2 diagonal ROW blocks marked by
-- `dblR`, `S` with 2 x 2 diagonal COLUMN blocks marked by `dblS`) is block
-- upper triangular for the induced 1/2/4 interval partition
-- (`sylvesterQQBs`/`sylvesterQQBe`, `sylvesterQQPartition_valid`,
-- `sylvesterQQBackSubCoeff_zero`), with diagonal blocks identified in
-- factor entries by `sylvesterQQBlockCoeff_entry`.  This file instantiates
-- that engine on the Sylvester data and delivers the printed
-- (16.7)/(16.8)-shaped statements for the fully quasi-quasi
-- Bartels-Stewart solve:
--
--   (16.7)  (P + DeltaP) vec(Z^) = vec(C~), with
--           |DeltaP| <= (1+rho) gamma_{nm+20} |P| componentwise under the
--           per-block growth certificates, and unconditionally with the
--           explicit Theorem 9.3 |L^||U^|-shaped per-block elimination
--           budget (`sylvesterQQBudget`);
--   (16.8)  |vec(C~) - P vec(Z^)| <= (1+rho) gamma_{nm+20} (|P| |vec(Z^)|)
--           componentwise, and in the printed matrix shape
--           |C~ - R Z^ + Z^ S| <= (1+rho) gamma_{nm+20} (|R||Z^| + |Z^||S|)
--           entrywise,
--
-- for `Z^ = flSylvesterQQBlockBackSubSolve`, the computed quasi-quasi block
-- Bartels-Stewart solution of the substitution (16.6) (defined here from
-- the engine's `flPartitionBackSub` on the interleaved reordered system).
--
-- Honest scope (inherited from the engine file):
-- * Schur factors are SUPPLIED (quasi-upper-triangular `R` with adjacent
--   2 x 2 diagonal row blocks marked by `dblR`, quasi-upper-triangular `S`
--   with adjacent 2 x 2 diagonal column blocks marked by `dblS`), as in the
--   printed setting; errors in computing the real Schur decompositions or
--   the transformed right-hand side belong to (16.9) and are not modeled
--   here.  `C~` is an arbitrary supplied right-hand side.
-- * The diagonal blocks of order 1, 2, 4 are solved by GE WITHOUT pivoting
--   (`flGESolve`).  The hypotheses are the honest per-block completion
--   certificates the engine takes: every COMPUTED pivot of every diagonal
--   block elimination is nonzero (`flGEPivots` on the explicit factor-entry
--   blocks `sylvesterQQDiagBlock`, which are exactly the shifted systems of
--   order <= 4 the printed algorithm solves on p. 308).  Nothing is
--   smuggled.
-- * GE is not componentwise backward stable relative to `|P|` alone: the
--   unconditional (16.7) bound carries the explicit transported Theorem 9.3
--   `|L^||U^|`-shaped budget `sylvesterQQBudget` (the engine
--   `partitionBudget`: `flGEBudget` on the diagonal blocks, `|P|` off the
--   blocks; it dominates `|P|` entrywise).  The printed fully componentwise
--   shape takes the standard per-block budget-domination certificates
--   `flGEBudget <= (1 + rho) |block|` as an explicit hypothesis and carries
--   the explicit `(1+rho)` growth factor.
-- * The printed unspecified constant `c_{m,n} u` is realized as the honest
--   same-gamma-class envelope `gamma_{nm+20}`, the engine envelope
--   `gamma_{N + 5B}` at `N = nm`, `B = 4`: Chapter 8 fold accumulation on
--   at most `nm` terms composed with the size-<=-4 kernel envelope
--   `gamma_{5*4} = gamma_20`.  We do not claim the printed letter constant.

import NumStability.Algorithms.Sylvester.Higham16QuasiQuasiRounded

namespace NumStability

namespace Wave16

open scoped BigOperators
open Wave15

-- ============================================================
-- The explicit factor-entry diagonal blocks of the substitution
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), quasi-quasi
    (real Schur) variant: the explicit factor-entry diagonal block of the
    interleaved two-column Bartels-Stewart substitution at rank position
    `a`, read as a small square array for the `flGESolve` elimination
    kernel.  Its entries are the `sylvesterQQBlockEntry` values of the
    decoded block anchors — the shifted systems of order 1, 2, or 4 in the
    entries of `R` and `S` that the printed algorithm solves by Gaussian
    elimination. -/
noncomputable def sylvesterQQDiagBlock (m n : Nat) (dblR : Fin m → Bool)
    (dblS : Fin n → Bool) (hSp : IsQuasiBlockPairing n dblS)
    (R : RMatFn m m) (S : RMatFn n n) (a : Fin (n * m))
    (u v : Fin (sylvesterQQBe m n dblR dblS hSp a -
      sylvesterQQBs m n dblR dblS hSp a - 1 + 1)) : Real :=
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
    u.val v.val

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), quasi-quasi
    variant: the engine's diagonal block of the reordered coefficient at
    rank position `a` is exactly the explicit factor-entry block
    `sylvesterQQDiagBlock` (function-level form of
    `sylvesterQQBlockCoeff_entry`). -/
theorem sylvesterQQBlockSubCoeff_eq_diagBlock (m n : Nat)
    (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (hRp : IsQuasiBlockPairing m dblR) (hSp : IsQuasiBlockPairing n dblS)
    (R : RMatFn m m) (S : RMatFn n n) (a : Fin (n * m)) :
    blockSubCoeff (n * m) (sylvesterQQBackSubCoeff m n dblS hSp R S)
        (sylvesterQQBs m n dblR dblS hSp a)
        (sylvesterQQBe m n dblR dblS hSp a) =
      sylvesterQQDiagBlock m n dblR dblS hSp R S a := by
  funext u v
  rw [sylvesterQQBlockCoeff_entry m n dblR dblS hRp hSp R S a u v]
  rfl

/-- Chapter 16.2 block-substitution bookkeeping: value of `blockSubCoeff`
    at a position inside its block interval — the corresponding entry of
    the underlying array. -/
theorem blockSubCoeff_apply_of_mem (N : Nat) (T : Fin N → Fin N → Real)
    (K E : Nat) (r c : Fin N)
    (h1 : K ≤ c.val) (h2 : c.val < E) (h3 : K ≤ r.val)
    (h4 : r.val < E) (h5 : E ≤ N) :
    blockSubCoeff N T K E ⟨r.val - K, by omega⟩ ⟨c.val - K, by omega⟩ =
      T r c := by
  unfold blockSubCoeff
  rw [dif_pos ⟨by omega, by omega⟩]
  have hr' : (⟨K + (r.val - K), by omega⟩ : Fin N) = r :=
    Fin.ext (show K + (r.val - K) = r.val by omega)
  have hc' : (⟨K + (c.val - K), by omega⟩ : Fin N) = c :=
    Fin.ext (show K + (c.val - K) = c.val by omega)
  rw [hr', hc']

-- ============================================================
-- The computed quasi-quasi Bartels-Stewart solution
-- ============================================================

/-- **Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), quasi-quasi
    (real Schur) form**: the computed vectorized solution of the Schur-form
    Sylvester system with BOTH factors quasi-triangular, modeled as the
    engine's rounded partitioned block back substitution
    (`flPartitionBackSub`) applied to the interleaved reordered `nm x nm`
    block upper-triangular system: the diagonal blocks of order 1, 2, 4
    (scalar rows, 2 x 2 row blocks of `R`, coupled column pairs of `S`, and
    their products) are solved by the `flGESolve` Gaussian-elimination
    kernel, and each row folds off the already-computed entries by the
    Chapter 8 rounded subtraction fold — exactly the printed Bartels-Stewart
    processing of the systems of order up to 4. -/
noncomputable def flSylvesterQQBlockBackSubSolveVec (fp : FPModel)
    (m n : Nat) (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (R : RMatFn m m) (S : RMatFn n n)
    (Ct : RMatFn m n) : Prod (Fin n) (Fin m) → Real :=
  fun p =>
    flPartitionBackSub fp (n * m) (sylvesterQQBs m n dblR dblS hSp)
      (sylvesterQQBe m n dblR dblS hSp)
      (sylvesterQQBackSubCoeff m n dblS hSp R S)
      (sylvesterQQBackSubRhs m n dblS hSp Ct)
      (sylvesterQQIndexEquiv m n dblS hSp p)

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), quasi-quasi
    variant: the computed Schur-coordinate solution matrix, i.e. the
    un-vectorized form of `flSylvesterQQBlockBackSubSolveVec`. -/
noncomputable def flSylvesterQQBlockBackSubSolve (fp : FPModel)
    (m n : Nat) (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (R : RMatFn m m) (S : RMatFn n n)
    (Ct : RMatFn m n) : RMatFn m n :=
  fun i k =>
    flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct (k, i)

/-- Column-stacking the computed Schur-coordinate solution matrix recovers
    the computed vectorized solution (Higham, 2nd ed., Chapter 16.2,
    equation (16.7) bookkeeping, quasi-quasi variant). -/
theorem vec_flSylvesterQQBlockBackSubSolve (fp : FPModel) (m n : Nat)
    (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (R : RMatFn m m) (S : RMatFn n n)
    (Ct : RMatFn m n) :
    Matrix.vec (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct) =
      flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct := rfl

-- ============================================================
-- The transported per-entry elimination budget
-- ============================================================

/-- Higham, 2nd ed., Chapter 9.3, Theorem 9.3, specialized as required by
    Chapter 16.2, p. 308 (quasi-quasi variant): the per-entry GE elimination
    budget of the quasi-quasi Bartels-Stewart solve, read on the
    column-stacking product index.  It is the engine budget
    `partitionBudget` of the interleaved reordered `nm x nm` system
    transported through the two-column Bartels-Stewart index equivalence:
    on the diagonal blocks it is the explicit `|L^||U^|`-shaped `flGEBudget`
    of the order-<=-4 factor-entry block, and off the blocks it is `|P|`
    itself (those perturbations are purely relative).  It dominates `|P|`
    entrywise (`abs_le_sylvesterQQBudget`); the per-block growth
    certificates collapse it into `(1 + rho) |P|`. -/
noncomputable def sylvesterQQBudget (fp : FPModel) (m n : Nat)
    (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (R : RMatFn m m) (S : RMatFn n n)
    (p q : Prod (Fin n) (Fin m)) : Real :=
  partitionBudget fp (n * m) (sylvesterQQBs m n dblR dblS hSp)
    (sylvesterQQBe m n dblR dblS hSp)
    (sylvesterQQBackSubCoeff m n dblS hSp R S)
    (sylvesterQQIndexEquiv m n dblS hSp p)
    (sylvesterQQIndexEquiv m n dblS hSp q)

/-- The transported elimination budget is nonnegative. -/
theorem sylvesterQQBudget_nonneg (fp : FPModel) (m n : Nat)
    (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (R : RMatFn m m) (S : RMatFn n n)
    (p q : Prod (Fin n) (Fin m)) :
    0 ≤ sylvesterQQBudget fp m n dblR dblS hSp R S p q :=
  partitionBudget_nonneg fp (n * m) (sylvesterQQBs m n dblR dblS hSp)
    (sylvesterQQBe m n dblR dblS hSp)
    (sylvesterQQBackSubCoeff m n dblS hSp R S)
    (sylvesterQQIndexEquiv m n dblS hSp p)
    (sylvesterQQIndexEquiv m n dblS hSp q)

/-- The transported elimination budget dominates the vec/Kronecker
    coefficient entrywise: `|P p q| <= sylvesterQQBudget p q` (Higham,
    2nd ed., Chapter 9.3, Theorem 9.3 budget shape). -/
theorem abs_le_sylvesterQQBudget (fp : FPModel) (m n : Nat)
    (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (R : RMatFn m m) (S : RMatFn n n)
    (p q : Prod (Fin n) (Fin m)) :
    |sylvesterVecCoeff m n R S p q| ≤
      sylvesterQQBudget fp m n dblR dblS hSp R S p q := by
  have h := abs_le_partitionBudget fp (n * m)
    (sylvesterQQBs m n dblR dblS hSp) (sylvesterQQBe m n dblR dblS hSp)
    (sylvesterQQBackSubCoeff m n dblS hSp R S)
    (sylvesterQQIndexEquiv m n dblS hSp p)
    (sylvesterQQIndexEquiv m n dblS hSp q)
  rw [sylvesterQQBackSubCoeff_reindex] at h
  exact h

/-- Higham, 2nd ed., Chapter 9.3, Theorem 9.3, as used by Chapter 16.2,
    p. 308 (quasi-quasi variant): the elimination FILL-IN excess of the
    transported budget over the coefficient itself,
    `sylvesterQQBudget - |P|`.  It is nonnegative, vanishes off the diagonal
    blocks, and is the part of the unconditional (16.7)/(16.8) budgets that
    the per-block growth certificates collapse into `rho |P|`. -/
noncomputable def sylvesterQQGrowthTerm (fp : FPModel) (m n : Nat)
    (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (R : RMatFn m m) (S : RMatFn n n)
    (p q : Prod (Fin n) (Fin m)) : Real :=
  sylvesterQQBudget fp m n dblR dblS hSp R S p q -
    |sylvesterVecCoeff m n R S p q|

/-- The elimination fill-in excess is nonnegative. -/
theorem sylvesterQQGrowthTerm_nonneg (fp : FPModel) (m n : Nat)
    (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (R : RMatFn m m) (S : RMatFn n n)
    (p q : Prod (Fin n) (Fin m)) :
    0 ≤ sylvesterQQGrowthTerm fp m n dblR dblS hSp R S p q := by
  have h := abs_le_sylvesterQQBudget fp m n dblR dblS hSp R S p q
  unfold sylvesterQQGrowthTerm
  linarith

/-- Split of the transported budget into the coefficient magnitude and the
    elimination fill-in excess. -/
theorem sylvesterQQBudget_split (fp : FPModel) (m n : Nat)
    (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (hSp : IsQuasiBlockPairing n dblS) (R : RMatFn m m) (S : RMatFn n n)
    (p q : Prod (Fin n) (Fin m)) :
    sylvesterQQBudget fp m n dblR dblS hSp R S p q =
      |sylvesterVecCoeff m n R S p q| +
        sylvesterQQGrowthTerm fp m n dblR dblS hSp R S p q := by
  unfold sylvesterQQGrowthTerm
  ring

-- ============================================================
-- Transport of the engine hypotheses to the factor-entry blocks
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), quasi-quasi
    variant: transport of the per-block completion certificates.  If every
    explicit factor-entry diagonal block (`sylvesterQQDiagBlock`, the
    shifted systems of order <= 4 of the printed algorithm) has all COMPUTED
    pivots nonzero, then so does every diagonal block of the interleaved
    reordered coefficient, which is the engine's pivot hypothesis for
    `flPartitionBackSub_backward_error`. -/
theorem sylvesterQQBlockPivots_transport (fp : FPModel) (m n : Nat)
    (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (hRp : IsQuasiBlockPairing m dblR) (hSp : IsQuasiBlockPairing n dblS)
    (R : RMatFn m m) (S : RMatFn n n)
    (hpiv : ∀ a : Fin (n * m),
      flGEPivots fp (sylvesterQQBe m n dblR dblS hSp a -
          sylvesterQQBs m n dblR dblS hSp a - 1)
        (sylvesterQQDiagBlock m n dblR dblS hSp R S a)) :
    ∀ r : Fin (n * m),
      flGEPivots fp (sylvesterQQBe m n dblR dblS hSp r -
          sylvesterQQBs m n dblR dblS hSp r - 1)
        (blockSubCoeff (n * m) (sylvesterQQBackSubCoeff m n dblS hSp R S)
          (sylvesterQQBs m n dblR dblS hSp r)
          (sylvesterQQBe m n dblR dblS hSp r)) := by
  intro r
  rw [sylvesterQQBlockSubCoeff_eq_diagBlock m n dblR dblS hRp hSp R S r]
  exact hpiv r

/-- Higham, 2nd ed., Chapter 9.3 and Chapter 16.2, p. 308, quasi-quasi
    variant: transport of the per-block growth certificates.  If every
    explicit factor-entry diagonal block satisfies the standard
    budget-domination certificate `flGEBudget <= (1 + rho) |block|` — the
    componentwise control of the order-<=-4 GE fill-in — then the engine's
    transported partition budget is dominated by
    `(1 + rho) |reordered coefficient|` at every position, which is the
    engine's growth hypothesis collapsing the fill-in into the fully
    componentwise `(1 + rho)` budget. -/
theorem sylvesterQQPartitionBudget_le_of_growth (fp : FPModel) (m n : Nat)
    (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (hRp : IsQuasiBlockPairing m dblR) (hSp : IsQuasiBlockPairing n dblS)
    (R : RMatFn m m) (S : RMatFn n n) (ρ : Real) (hρ : 0 ≤ ρ)
    (hgrow : ∀ (a : Fin (n * m))
      (u v : Fin (sylvesterQQBe m n dblR dblS hSp a -
        sylvesterQQBs m n dblR dblS hSp a - 1 + 1)),
      flGEBudget fp (sylvesterQQBe m n dblR dblS hSp a -
          sylvesterQQBs m n dblR dblS hSp a - 1)
        (sylvesterQQDiagBlock m n dblR dblS hSp R S a) u v ≤
      (1 + ρ) * |sylvesterQQDiagBlock m n dblR dblS hSp R S a u v|) :
    ∀ r c : Fin (n * m),
      partitionBudget fp (n * m) (sylvesterQQBs m n dblR dblS hSp)
        (sylvesterQQBe m n dblR dblS hSp)
        (sylvesterQQBackSubCoeff m n dblS hSp R S) r c ≤
      (1 + ρ) * |sylvesterQQBackSubCoeff m n dblS hSp R S r c| := by
  intro r c
  unfold partitionBudget
  split
  · rename_i h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hTc := blockSubCoeff_apply_of_mem (n * m)
      (sylvesterQQBackSubCoeff m n dblS hSp R S)
      (sylvesterQQBs m n dblR dblS hSp r)
      (sylvesterQQBe m n dblR dblS hSp r) r c h1 h2 h3 h4 h5
    have hMeq :=
      sylvesterQQBlockSubCoeff_eq_diagBlock m n dblR dblS hRp hSp R S r
    rw [hMeq] at hTc ⊢
    have hkey := hgrow r
      ⟨r.val - sylvesterQQBs m n dblR dblS hSp r, by omega⟩
      ⟨c.val - sylvesterQQBs m n dblR dblS hSp r, by omega⟩
    rw [hTc] at hkey
    exact hkey
  · have hng : 0 ≤ ρ * |sylvesterQQBackSubCoeff m n dblS hSp R S r c| :=
      mul_nonneg hρ (abs_nonneg _)
    linarith [abs_nonneg (sylvesterQQBackSubCoeff m n dblS hSp R S r c)]

-- ============================================================
-- (16.7): rounded block-substitution backward error
-- ============================================================

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.7), fully
    quasi-triangular (real Schur) variant, unconditional form** (supplied
    quasi-triangular `R` AND quasi-triangular `S`).  The computed vectorized
    solution `x^ = flSylvesterQQBlockBackSubSolveVec` of the Schur-form
    Sylvester system — the rounded interleaved two-column block back
    substitution (16.6) applied to the reordered vec/Kronecker system —
    satisfies the exactly perturbed system

    `(P + DeltaP) x^ = vec(C~)` with
    `|DeltaP| <= gamma_{nm+20} * sylvesterQQBudget`

    componentwise, where `P = I_n kron R - S^T kron I_m` is the (16.2)
    coefficient and `sylvesterQQBudget` is the explicit transported
    Theorem 9.3 `|L^||U^|`-shaped elimination budget, equal to `|P|` off
    the order-<=-4 diagonal blocks and dominating `|P|` everywhere.  This
    instantiates the engine `flPartitionBackSub_backward_error` through the
    interleaved Bartels-Stewart index equivalence.  Hypotheses are the
    honest per-block completion certificates: every computed pivot of every
    explicit factor-entry diagonal block (the shifted systems of order 1,
    2, 4 of the printed algorithm) is nonzero.  The printed unspecified
    constant `c_{m,n} u` is realized as the same-gamma-class envelope
    `gamma_{nm+20}`; errors from computing the Schur factors or the
    transformed right-hand side belong to (16.9) and are not modeled
    here. -/
theorem sylvesterVecCoeff_quasiQuasi_blockBackSub_backward_error
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n)
    (hRp : IsQuasiBlockPairing m dblR) (hSp : IsQuasiBlockPairing n dblS)
    (hR : IsQuasiUpperTriangularFn m R dblR)
    (hS : IsQuasiUpperTriangularFn n S dblS)
    (hpiv : ∀ a : Fin (n * m),
      flGEPivots fp (sylvesterQQBe m n dblR dblS hSp a -
          sylvesterQQBs m n dblR dblS hSp a - 1)
        (sylvesterQQDiagBlock m n dblR dblS hSp R S a))
    (hgv : gammaValid fp (n * m + 20)) :
    ∃ ΔP : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real,
      (∀ p q, |ΔP p q| ≤ gamma fp (n * m + 20) *
        sylvesterQQBudget fp m n dblR dblS hSp R S p q) ∧
      Matrix.mulVec (sylvesterVecCoeff m n R S + ΔP)
          (flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct) =
        Matrix.vec Ct := by
  obtain ⟨ΔT, hΔTbound, hΔTeq⟩ :=
    flPartitionBackSub_backward_error fp (n * m) 4
      (sylvesterQQBs m n dblR dblS hSp) (sylvesterQQBe m n dblR dblS hSp)
      (sylvesterQQBackSubCoeff m n dblS hSp R S)
      (sylvesterQQBackSubRhs m n dblS hSp Ct)
      (sylvesterQQPartition_valid m n dblR dblS hRp hSp)
      (sylvesterQQBackSubCoeff_zero m n dblR dblS hRp hSp R S hR hS)
      (sylvesterQQBlockPivots_transport fp m n dblR dblS hRp hSp R S hpiv)
      (fun r => sylvesterQQBlockSize_le m n dblR dblS hSp r)
      hgv
  refine ⟨fun p q =>
    ΔT (sylvesterQQIndexEquiv m n dblS hSp p)
      (sylvesterQQIndexEquiv m n dblS hSp q), ?_, ?_⟩
  · intro p q
    exact hΔTbound (sylvesterQQIndexEquiv m n dblS hSp p)
      (sylvesterQQIndexEquiv m n dblS hSp q)
  · funext p
    have hrow := hΔTeq (sylvesterQQIndexEquiv m n dblS hSp p)
    rw [sylvesterQQBackSubRhs_reindex] at hrow
    rw [← hrow]
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply]
    refine Fintype.sum_equiv (sylvesterQQIndexEquiv m n dblS hSp) _ _ ?_
    intro q
    rw [sylvesterQQBackSubCoeff_reindex]
    rfl

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.7), fully
    quasi-triangular (real Schur) variant, printed fully componentwise
    form** (supplied quasi-triangular `R` AND quasi-triangular `S`).  Under
    the additional per-block budget-domination certificates
    `flGEBudget <= (1 + rho) |block|` on the explicit factor-entry diagonal
    blocks — the standard componentwise control of the order-<=-4 GE
    fill-in — the computed vectorized solution satisfies the printed
    componentwise backward-error model

    `(P + DeltaP) x^ = vec(C~)` with
    `|DeltaP| <= (1 + rho) gamma_{nm+20} |P|`

    componentwise, with `P = I_n kron R - S^T kron I_m`.  This is the fully
    quasi-quasi analogue of the Wave-14 strictly triangular and Wave-15
    mixed (16.7) endpoints; the printed unspecified constant `c_{m,n} u` is
    realized as the same-gamma-class envelope `(1 + rho) gamma_{nm+20}`
    with the explicit growth factor documented. -/
theorem sylvesterVecCoeff_quasiQuasi_blockBackSub_backward_error_componentwise
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n) (ρ : Real)
    (hRp : IsQuasiBlockPairing m dblR) (hSp : IsQuasiBlockPairing n dblS)
    (hR : IsQuasiUpperTriangularFn m R dblR)
    (hS : IsQuasiUpperTriangularFn n S dblS)
    (hpiv : ∀ a : Fin (n * m),
      flGEPivots fp (sylvesterQQBe m n dblR dblS hSp a -
          sylvesterQQBs m n dblR dblS hSp a - 1)
        (sylvesterQQDiagBlock m n dblR dblS hSp R S a))
    (hρ : 0 ≤ ρ)
    (hgrow : ∀ (a : Fin (n * m))
      (u v : Fin (sylvesterQQBe m n dblR dblS hSp a -
        sylvesterQQBs m n dblR dblS hSp a - 1 + 1)),
      flGEBudget fp (sylvesterQQBe m n dblR dblS hSp a -
          sylvesterQQBs m n dblR dblS hSp a - 1)
        (sylvesterQQDiagBlock m n dblR dblS hSp R S a) u v ≤
      (1 + ρ) * |sylvesterQQDiagBlock m n dblR dblS hSp R S a u v|)
    (hgv : gammaValid fp (n * m + 20)) :
    ∃ ΔP : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real,
      (∀ p q, |ΔP p q| ≤ (1 + ρ) * gamma fp (n * m + 20) *
        |sylvesterVecCoeff m n R S p q|) ∧
      Matrix.mulVec (sylvesterVecCoeff m n R S + ΔP)
          (flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct) =
        Matrix.vec Ct := by
  obtain ⟨ΔT, hΔTbound, hΔTeq⟩ :=
    flPartitionBackSub_backward_error_componentwise fp (n * m) 4
      (sylvesterQQBs m n dblR dblS hSp) (sylvesterQQBe m n dblR dblS hSp)
      (sylvesterQQBackSubCoeff m n dblS hSp R S)
      (sylvesterQQBackSubRhs m n dblS hSp Ct) ρ
      (sylvesterQQPartition_valid m n dblR dblS hRp hSp)
      (sylvesterQQBackSubCoeff_zero m n dblR dblS hRp hSp R S hR hS)
      (sylvesterQQBlockPivots_transport fp m n dblR dblS hRp hSp R S hpiv)
      (fun r => sylvesterQQBlockSize_le m n dblR dblS hSp r)
      (sylvesterQQPartitionBudget_le_of_growth fp m n dblR dblS hRp hSp R S
        ρ hρ hgrow)
      hgv
  refine ⟨fun p q =>
    ΔT (sylvesterQQIndexEquiv m n dblS hSp p)
      (sylvesterQQIndexEquiv m n dblS hSp q), ?_, ?_⟩
  · intro p q
    have hb := hΔTbound (sylvesterQQIndexEquiv m n dblS hSp p)
      (sylvesterQQIndexEquiv m n dblS hSp q)
    rw [sylvesterQQBackSubCoeff_reindex] at hb
    exact hb
  · funext p
    have hrow := hΔTeq (sylvesterQQIndexEquiv m n dblS hSp p)
    rw [sylvesterQQBackSubRhs_reindex] at hrow
    rw [← hrow]
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply]
    refine Fintype.sum_equiv (sylvesterQQIndexEquiv m n dblS hSp) _ _ ?_
    intro q
    rw [sylvesterQQBackSubCoeff_reindex]
    rfl

-- ============================================================
-- (16.8): componentwise residual consequence
-- ============================================================

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8), fully
    quasi-triangular (real Schur) variant, vectorized elimination-budget
    form** (supplied quasi-triangular `R` AND quasi-triangular `S`).  The
    computed vectorized solution of the Schur-form Sylvester system
    satisfies a componentwise residual bound from the unconditional (16.7)
    model, keeping the explicit transported Theorem 9.3 elimination budget
    visible instead of assuming growth certificates that collapse it to
    `(1 + rho) |P|`. -/
theorem sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_residual_with_budget
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n)
    (hRp : IsQuasiBlockPairing m dblR) (hSp : IsQuasiBlockPairing n dblS)
    (hR : IsQuasiUpperTriangularFn m R dblR)
    (hS : IsQuasiUpperTriangularFn n S dblS)
    (hpiv : ∀ a : Fin (n * m),
      flGEPivots fp (sylvesterQQBe m n dblR dblS hSp a -
          sylvesterQQBs m n dblR dblS hSp a - 1)
        (sylvesterQQDiagBlock m n dblR dblS hSp R S a))
    (hgv : gammaValid fp (n * m + 20)) (p : Prod (Fin n) (Fin m)) :
    |Matrix.vec Ct p -
        Matrix.mulVec (sylvesterVecCoeff m n R S)
          (flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct)
          p| ≤
      gamma fp (n * m + 20) *
        ∑ q, sylvesterQQBudget fp m n dblR dblS hSp R S p q *
          |flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct
            q| := by
  obtain ⟨ΔP, hbound, heq⟩ :=
    sylvesterVecCoeff_quasiQuasi_blockBackSub_backward_error
      fp m n dblR dblS R S Ct hRp hSp hR hS hpiv hgv
  have hdiff :
      Matrix.vec Ct p -
          Matrix.mulVec (sylvesterVecCoeff m n R S)
            (flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct)
            p =
        ∑ q, ΔP p q *
          flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct
            q := by
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
  calc
    |ΔP p q| *
        |flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct q| ≤
        (gamma fp (n * m + 20) *
          sylvesterQQBudget fp m n dblR dblS hSp R S p q) *
          |flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct
            q| :=
      mul_le_mul_of_nonneg_right (hbound p q) (abs_nonneg _)
    _ = gamma fp (n * m + 20) *
        (sylvesterQQBudget fp m n dblR dblS hSp R S p q *
          |flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct
            q|) := by
      ring

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8), fully
    quasi-triangular (real Schur) variant, printed matrix elimination-budget
    form** (supplied quasi-triangular `R` AND quasi-triangular `S`).  This
    is the matrix-entry companion to the vectorized budget residual bound,
    keeping the explicit GE fill-in excess `sylvesterQQGrowthTerm` visible
    instead of assuming growth certificates that collapse it into
    `(1 + rho) |P|`; the `|P|` part of the budget is folded into the
    printed `|R||Z^| + |Z^||S|` shape by the Wave-14 row-action bridge. -/
theorem sylvesterResidualRect_quasiQuasi_blockBackSub_componentwise_le_with_budget
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n)
    (hRp : IsQuasiBlockPairing m dblR) (hSp : IsQuasiBlockPairing n dblS)
    (hR : IsQuasiUpperTriangularFn m R dblR)
    (hS : IsQuasiUpperTriangularFn n S dblS)
    (hpiv : ∀ a : Fin (n * m),
      flGEPivots fp (sylvesterQQBe m n dblR dblS hSp a -
          sylvesterQQBs m n dblR dblS hSp a - 1)
        (sylvesterQQDiagBlock m n dblR dblS hSp R S a))
    (hgv : gammaValid fp (n * m + 20)) (i : Fin m) (k : Fin n) :
    |sylvesterResidualRect m n R S Ct
        (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct) i k| ≤
      gamma fp (n * m + 20) *
        (matMulRect m m n (fun a b => |R a b|)
            (fun a b =>
              |flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct
                a b|) i k +
          matMulRect m n n
            (fun a b =>
              |flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct
                a b|)
            (fun a b => |S a b|) i k +
          ∑ q : Prod (Fin n) (Fin m),
            sylvesterQQGrowthTerm fp m n dblR dblS hSp R S (k, i) q *
              |flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct
                q|) := by
  have hvec :=
    sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_residual_with_budget
      fp m n dblR dblS R S Ct hRp hSp hR hS hpiv hgv (k, i)
  rw [← vec_flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct]
    at hvec
  rw [sylvesterVecCoeff_mulVec_vec m n R S
    (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct)] at hvec
  refine le_trans hvec ?_
  refine mul_le_mul_of_nonneg_left ?_ (gamma_nonneg fp hgv)
  have hsplit :
      (∑ q : Prod (Fin n) (Fin m),
          sylvesterQQBudget fp m n dblR dblS hSp R S (k, i) q *
            |Matrix.vec
              (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct)
              q|) =
        (∑ q : Prod (Fin n) (Fin m),
          |sylvesterVecCoeff m n R S (k, i) q| *
            |Matrix.vec
              (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct)
              q|) +
        ∑ q : Prod (Fin n) (Fin m),
          sylvesterQQGrowthTerm fp m n dblR dblS hSp R S (k, i) q *
            |Matrix.vec
              (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct)
              q| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [sylvesterQQBudget_split fp m n dblR dblS hSp R S (k, i) q]
    ring
  rw [hsplit]
  apply add_le_add
  · refine le_trans (Wave14.sylvesterVecCoeff_abs_row_action_le m n R S
      (Matrix.vec
        (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct))
      (k, i)) ?_
    refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
    · show (∑ j : Fin m, |R i j| *
          |Matrix.vec
            (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct)
            (k, j)|) =
        ∑ j : Fin m, |R i j| *
          |flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct j k|
      rfl
    · show (∑ l : Fin n, |S l k| *
          |Matrix.vec
            (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct)
            (l, i)|) =
        ∑ l : Fin n,
          |flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct i l| *
            |S l k|
      apply Finset.sum_congr rfl
      intro l _
      exact mul_comm _ _
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro q _
    rw [vec_flSylvesterQQBlockBackSubSolve]

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8), fully
    quasi-triangular (real Schur) variant, vectorized componentwise form**
    (supplied quasi-triangular `R` AND quasi-triangular `S`).  The computed
    vectorized solution of the Schur-form Sylvester system satisfies

    `|vec(C~) - P x^| <= (1 + rho) gamma_{nm+20} (|P| |x^|)`

    componentwise, the residual consequence of the quasi-quasi (16.7)
    backward-error model under the per-block pivot/growth certificates.
    The printed constant `c_{m,n} u` is realized as the same-gamma-class
    envelope `(1 + rho) gamma_{nm+20}`. -/
theorem sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_residual
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n) (ρ : Real)
    (hRp : IsQuasiBlockPairing m dblR) (hSp : IsQuasiBlockPairing n dblS)
    (hR : IsQuasiUpperTriangularFn m R dblR)
    (hS : IsQuasiUpperTriangularFn n S dblS)
    (hpiv : ∀ a : Fin (n * m),
      flGEPivots fp (sylvesterQQBe m n dblR dblS hSp a -
          sylvesterQQBs m n dblR dblS hSp a - 1)
        (sylvesterQQDiagBlock m n dblR dblS hSp R S a))
    (hρ : 0 ≤ ρ)
    (hgrow : ∀ (a : Fin (n * m))
      (u v : Fin (sylvesterQQBe m n dblR dblS hSp a -
        sylvesterQQBs m n dblR dblS hSp a - 1 + 1)),
      flGEBudget fp (sylvesterQQBe m n dblR dblS hSp a -
          sylvesterQQBs m n dblR dblS hSp a - 1)
        (sylvesterQQDiagBlock m n dblR dblS hSp R S a) u v ≤
      (1 + ρ) * |sylvesterQQDiagBlock m n dblR dblS hSp R S a u v|)
    (hgv : gammaValid fp (n * m + 20)) (p : Prod (Fin n) (Fin m)) :
    |Matrix.vec Ct p -
        Matrix.mulVec (sylvesterVecCoeff m n R S)
          (flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct)
          p| ≤
      (1 + ρ) * gamma fp (n * m + 20) *
        ∑ q, |sylvesterVecCoeff m n R S p q| *
          |flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct
            q| := by
  obtain ⟨ΔP, hbound, heq⟩ :=
    sylvesterVecCoeff_quasiQuasi_blockBackSub_backward_error_componentwise
      fp m n dblR dblS R S Ct ρ hRp hSp hR hS hpiv hρ hgrow hgv
  exact Wave14.componentwise_residual_of_perturbed_mulVec
    (sylvesterVecCoeff m n R S) ΔP
    (flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct)
    (Matrix.vec Ct) ((1 + ρ) * gamma fp (n * m + 20)) hbound heq p

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8), fully
    quasi-triangular (real Schur) variant, printed matrix form** (supplied
    quasi-triangular `R` AND quasi-triangular `S`).  The computed
    Schur-coordinate solution `Z^ = flSylvesterQQBlockBackSubSolve` of the
    quasi-quasi Bartels-Stewart substitution (16.6) satisfies the
    componentwise residual bound

    `|C~ - R Z^ + Z^ S| <= (1 + rho) gamma_{nm+20} (|R| |Z^| + |Z^| |S|)`

    entrywise, the un-vectorized form of the (16.8) consequence of the
    quasi-quasi (16.7) backward-error model, under the per-block
    pivot/growth certificates.  The printed constant `c_{m,n} u` is
    realized as the same-gamma-class envelope `(1 + rho) gamma_{nm+20}`. -/
theorem sylvesterResidualRect_quasiQuasi_blockBackSub_componentwise_le
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n) (ρ : Real)
    (hRp : IsQuasiBlockPairing m dblR) (hSp : IsQuasiBlockPairing n dblS)
    (hR : IsQuasiUpperTriangularFn m R dblR)
    (hS : IsQuasiUpperTriangularFn n S dblS)
    (hpiv : ∀ a : Fin (n * m),
      flGEPivots fp (sylvesterQQBe m n dblR dblS hSp a -
          sylvesterQQBs m n dblR dblS hSp a - 1)
        (sylvesterQQDiagBlock m n dblR dblS hSp R S a))
    (hρ : 0 ≤ ρ)
    (hgrow : ∀ (a : Fin (n * m))
      (u v : Fin (sylvesterQQBe m n dblR dblS hSp a -
        sylvesterQQBs m n dblR dblS hSp a - 1 + 1)),
      flGEBudget fp (sylvesterQQBe m n dblR dblS hSp a -
          sylvesterQQBs m n dblR dblS hSp a - 1)
        (sylvesterQQDiagBlock m n dblR dblS hSp R S a) u v ≤
      (1 + ρ) * |sylvesterQQDiagBlock m n dblR dblS hSp R S a u v|)
    (hgv : gammaValid fp (n * m + 20)) (i : Fin m) (k : Fin n) :
    |sylvesterResidualRect m n R S Ct
        (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct) i k| ≤
      (1 + ρ) * gamma fp (n * m + 20) *
        (matMulRect m m n (fun a b => |R a b|)
            (fun a b =>
              |flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct
                a b|) i k +
          matMulRect m n n
            (fun a b =>
              |flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct
                a b|)
            (fun a b => |S a b|) i k) := by
  have hvec :=
    sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_residual
      fp m n dblR dblS R S Ct ρ hRp hSp hR hS hpiv hρ hgrow hgv (k, i)
  rw [← vec_flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct]
    at hvec
  rw [sylvesterVecCoeff_mulVec_vec m n R S
    (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct)] at hvec
  refine le_trans hvec ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (by linarith : (0 : Real) ≤ 1 + ρ) (gamma_nonneg fp hgv))
  refine le_trans (Wave14.sylvesterVecCoeff_abs_row_action_le m n R S
    (Matrix.vec (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct))
    (k, i)) ?_
  refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · show (∑ j : Fin m, |R i j| *
        |Matrix.vec
          (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct)
          (k, j)|) =
      ∑ j : Fin m, |R i j| *
        |flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct j k|
    rfl
  · show (∑ l : Fin n, |S l k| *
        |Matrix.vec
          (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct)
          (l, i)|) =
      ∑ l : Fin n,
        |flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct i l| *
          |S l k|
    apply Finset.sum_congr rfl
    intro l _
    exact mul_comm _ _

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.7)-(16.8),
    fully quasi-triangular (real Schur) variant: bundled endpoint exposing
    the componentwise backward-error model, its vectorized residual
    consequence, and the printed matrix residual form under one shared
    hypothesis list. -/
theorem sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_error_and_residual
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n) (ρ : Real)
    (hRp : IsQuasiBlockPairing m dblR) (hSp : IsQuasiBlockPairing n dblS)
    (hR : IsQuasiUpperTriangularFn m R dblR)
    (hS : IsQuasiUpperTriangularFn n S dblS)
    (hpiv : ∀ a : Fin (n * m),
      flGEPivots fp (sylvesterQQBe m n dblR dblS hSp a -
          sylvesterQQBs m n dblR dblS hSp a - 1)
        (sylvesterQQDiagBlock m n dblR dblS hSp R S a))
    (hρ : 0 ≤ ρ)
    (hgrow : ∀ (a : Fin (n * m))
      (u v : Fin (sylvesterQQBe m n dblR dblS hSp a -
        sylvesterQQBs m n dblR dblS hSp a - 1 + 1)),
      flGEBudget fp (sylvesterQQBe m n dblR dblS hSp a -
          sylvesterQQBs m n dblR dblS hSp a - 1)
        (sylvesterQQDiagBlock m n dblR dblS hSp R S a) u v ≤
      (1 + ρ) * |sylvesterQQDiagBlock m n dblR dblS hSp R S a u v|)
    (hgv : gammaValid fp (n * m + 20)) :
    (∃ ΔP : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real,
      (∀ p q, |ΔP p q| ≤ (1 + ρ) * gamma fp (n * m + 20) *
        |sylvesterVecCoeff m n R S p q|) ∧
      Matrix.mulVec (sylvesterVecCoeff m n R S + ΔP)
          (flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct) =
        Matrix.vec Ct) ∧
    (∀ p : Prod (Fin n) (Fin m),
      |Matrix.vec Ct p -
          Matrix.mulVec (sylvesterVecCoeff m n R S)
            (flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct)
            p| ≤
        (1 + ρ) * gamma fp (n * m + 20) *
          ∑ q, |sylvesterVecCoeff m n R S p q| *
            |flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct
              q|) ∧
    (∀ (i : Fin m) (k : Fin n),
      |sylvesterResidualRect m n R S Ct
          (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct)
          i k| ≤
        (1 + ρ) * gamma fp (n * m + 20) *
          (matMulRect m m n (fun a b => |R a b|)
              (fun a b =>
                |flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct
                  a b|) i k +
            matMulRect m n n
              (fun a b =>
                |flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct
                  a b|)
              (fun a b => |S a b|) i k)) := by
  constructor
  · exact
      sylvesterVecCoeff_quasiQuasi_blockBackSub_backward_error_componentwise
        fp m n dblR dblS R S Ct ρ hRp hSp hR hS hpiv hρ hgrow hgv
  constructor
  · intro p
    exact
      sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_residual
        fp m n dblR dblS R S Ct ρ hRp hSp hR hS hpiv hρ hgrow hgv p
  · intro i k
    exact
      sylvesterResidualRect_quasiQuasi_blockBackSub_componentwise_le
        fp m n dblR dblS R S Ct ρ hRp hSp hR hS hpiv hρ hgrow hgv i k

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.7)-(16.8),
    fully quasi-triangular (real Schur) variant: bundled endpoint exposing
    the unconditional elimination-budget backward-error model, its
    vectorized residual consequence, and the printed matrix residual form
    (with the explicit GE fill-in excess) under one shared hypothesis
    list. -/
theorem sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_error_and_residual_with_budget
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool) (dblS : Fin n → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n)
    (hRp : IsQuasiBlockPairing m dblR) (hSp : IsQuasiBlockPairing n dblS)
    (hR : IsQuasiUpperTriangularFn m R dblR)
    (hS : IsQuasiUpperTriangularFn n S dblS)
    (hpiv : ∀ a : Fin (n * m),
      flGEPivots fp (sylvesterQQBe m n dblR dblS hSp a -
          sylvesterQQBs m n dblR dblS hSp a - 1)
        (sylvesterQQDiagBlock m n dblR dblS hSp R S a))
    (hgv : gammaValid fp (n * m + 20)) :
    (∃ ΔP : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real,
      (∀ p q, |ΔP p q| ≤ gamma fp (n * m + 20) *
        sylvesterQQBudget fp m n dblR dblS hSp R S p q) ∧
      Matrix.mulVec (sylvesterVecCoeff m n R S + ΔP)
          (flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct) =
        Matrix.vec Ct) ∧
    (∀ p : Prod (Fin n) (Fin m),
      |Matrix.vec Ct p -
          Matrix.mulVec (sylvesterVecCoeff m n R S)
            (flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct)
            p| ≤
        gamma fp (n * m + 20) *
          ∑ q, sylvesterQQBudget fp m n dblR dblS hSp R S p q *
            |flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S Ct
              q|) ∧
    (∀ (i : Fin m) (k : Fin n),
      |sylvesterResidualRect m n R S Ct
          (flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct)
          i k| ≤
        gamma fp (n * m + 20) *
          (matMulRect m m n (fun a b => |R a b|)
              (fun a b =>
                |flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct
                  a b|) i k +
            matMulRect m n n
              (fun a b =>
                |flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S Ct
                  a b|)
              (fun a b => |S a b|) i k +
            ∑ q : Prod (Fin n) (Fin m),
              sylvesterQQGrowthTerm fp m n dblR dblS hSp R S (k, i) q *
                |flSylvesterQQBlockBackSubSolveVec fp m n dblR dblS hSp R S
                  Ct q|)) := by
  constructor
  · exact
      sylvesterVecCoeff_quasiQuasi_blockBackSub_backward_error
        fp m n dblR dblS R S Ct hRp hSp hR hS hpiv hgv
  constructor
  · intro p
    exact
      sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_residual_with_budget
        fp m n dblR dblS R S Ct hRp hSp hR hS hpiv hgv p
  · intro i k
    exact
      sylvesterResidualRect_quasiQuasi_blockBackSub_componentwise_le_with_budget
        fp m n dblR dblS R S Ct hRp hSp hR hS hpiv hgv i k

-- ============================================================
-- Source-numbered aliases
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    explicit factor-entry diagonal-block identification of the interleaved
    reordered coefficient. -/
alias H16_eq16_6_quasiquasi_sylvesterQQBlockSubCoeff_eq_diagBlock :=
  sylvesterQQBlockSubCoeff_eq_diagBlock

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    vectorized/matrix bookkeeping of the computed rounded quasi-quasi
    Schur solve. -/
alias H16_eq16_6_quasiquasi_vec_flSylvesterQQBlockBackSubSolve :=
  vec_flSylvesterQQBlockBackSubSolve

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), fully
    quasi-triangular (real Schur) variant: source-numbered alias for
    transport of the per-block computed-pivot completion certificates to
    the interleaved reordered system. -/
alias H16_eq16_6_quasiquasi_sylvesterQQBlockPivots_transport :=
  sylvesterQQBlockPivots_transport

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), with Chapter 9.3
    growth control, fully quasi-triangular (real Schur) variant:
    source-numbered alias for transport of the per-block budget-domination
    certificates that collapse the explicit GE fill-in into the
    componentwise `(1 + rho)` budget. -/
alias H16_eq16_6_quasiquasi_sylvesterQQPartitionBudget_le_of_growth :=
  sylvesterQQPartitionBudget_le_of_growth

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.7), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    unconditional backward-error model with the explicit transported
    Theorem 9.3 elimination budget. -/
alias H16_eq16_7_quasiquasi_sylvesterVecCoeff_blockBackSub_backward_error :=
  sylvesterVecCoeff_quasiQuasi_blockBackSub_backward_error

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.7), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    printed fully componentwise backward-error model
    `(P + DeltaP) x^ = vec(C~)`, `|DeltaP| <= (1+rho) gamma_{nm+20} |P|`
    under the per-block pivot/growth certificates. -/
alias H16_eq16_7_quasiquasi_sylvesterVecCoeff_blockBackSub_backward_error_componentwise :=
  sylvesterVecCoeff_quasiQuasi_blockBackSub_backward_error_componentwise

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    vectorized componentwise residual consequence with the explicit
    transported elimination budget from the unconditional (16.7) model. -/
alias H16_eq16_8_quasiquasi_sylvesterVecCoeff_blockBackSub_componentwise_residual_with_budget :=
  sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_residual_with_budget

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    printed matrix residual consequence with the explicit GE fill-in
    excess from the unconditional (16.7) model. -/
alias H16_eq16_8_quasiquasi_sylvesterResidualRect_blockBackSub_componentwise_le_with_budget :=
  sylvesterResidualRect_quasiQuasi_blockBackSub_componentwise_le_with_budget

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    vectorized componentwise residual consequence
    `|vec(C~) - P x^| <= (1+rho) gamma_{nm+20} (|P| |x^|)`. -/
alias H16_eq16_8_quasiquasi_sylvesterVecCoeff_blockBackSub_componentwise_residual :=
  sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_residual

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    printed matrix form
    `|C~ - R Z^ + Z^ S| <= (1+rho) gamma_{nm+20} (|R||Z^| + |Z^||S|)`. -/
alias H16_eq16_8_quasiquasi_sylvesterResidualRect_blockBackSub_componentwise_le :=
  sylvesterResidualRect_quasiQuasi_blockBackSub_componentwise_le

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.7)-(16.8),
    fully quasi-triangular (real Schur) variant: source-numbered alias for
    the bundled componentwise backward-error and residual endpoint
    package. -/
alias H16_eq16_7_8_quasiquasi_sylvesterVecCoeff_blockBackSub_componentwise_error_and_residual :=
  sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_error_and_residual

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.7)-(16.8),
    fully quasi-triangular (real Schur) variant: source-numbered alias for
    the bundled unconditional elimination-budget backward-error and
    residual endpoint package. -/
alias H16_eq16_7_8_quasiquasi_sylvesterVecCoeff_blockBackSub_componentwise_error_and_residual_with_budget :=
  sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_error_and_residual_with_budget

end Wave16

end NumStability
