import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.BlockTraversal
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.QuasiTriangularSolve
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.TriangularBartelsStewart.RoundedSolve
import NumStability.Analysis.MatrixAlgebra
import NumStability.FloatingPoint.Model

/-!
# Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.QuasiTriangularSylvester

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16QuasiRoundedSylvester.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 16.2, pp. 307-308, equations (16.6)-(16.8), quasi-triangular
-- (real Schur) variant, Sylvester level.  Companion endpoint file to
-- `Higham16QuasiRoundedSolve`: the engine file proved the rounded
-- quasi-triangular block back-substitution model
-- (`flQuasiBlockBackSub_backward_error` and its fully componentwise and
-- residual forms) together with the structural layer identifying the
-- reordered vec/Kronecker coefficient `P = I_n kron R - S^T kron I_m` of
-- (16.2) as a block upper-triangular `nm x nm` system with the same
-- 1 x 1 / 2 x 2 diagonal-block structure as the quasi-triangular factor
-- `R`.  This file instantiates that engine on the Sylvester data and
-- delivers the printed (16.7)/(16.8)-shaped statements for the
-- quasi-triangular Bartels-Stewart solve:
--
--   (16.7)  (P + DeltaP) vec(Z^) = vec(C~), with
--           |DeltaP| <= (1+rho) gamma_{nm+9} |P| componentwise under the
--           per-block growth certificates, and unconditionally with the
--           explicit Theorem 9.3 |L||U|-shaped elimination fill-in budget
--           (`sylvesterQuasiGrowthTerm`);
--   (16.8)  |vec(C~) - P vec(Z^)| <= (1+rho) gamma_{nm+9} (|P| |vec(Z^)|)
--           componentwise, and in the printed matrix shape
--           |C~ - R Z^ + Z^ S| <= (1+rho) gamma_{nm+9} (|R||Z^| + |Z^||S|)
--           entrywise,
--
-- for `Z^ = flSylvesterQuasiSchurBlockBackSubSolve`, the computed
-- quasi-triangular block Bartels-Stewart solution of (16.6).
--
-- Honest scope (inherited from the engine file):
-- * Schur factors are SUPPLIED (quasi-upper-triangular `R` with adjacent
--   2 x 2 diagonal blocks marked by `dblR`, upper-triangular `S`), as in
--   the printed setting; errors in computing the real Schur decompositions
--   or the transformed right-hand side belong to (16.9) and are not
--   modeled here.  `C~` is an arbitrary supplied right-hand side.
-- * The 2 x 2 diagonal blocks are solved by GE WITHOUT pivoting.  The
--   hypotheses are the honest per-block completion certificates the engine
--   takes: diagonal separation `R_ii /= S_kk` on every row `i` that is not
--   the bottom row of a marked block (the scalar pivots and the block
--   first pivots), and a nonzero COMPUTED second pivot for every marked
--   shifted 2 x 2 block.  Nothing is smuggled.
-- * GE is not componentwise backward stable relative to `|P|` alone: the
--   unconditional (16.7) budget carries the explicit per-block elimination
--   fill-in (the `n = 2` instance of the printed `|L^||U^|` budget of
--   Theorem 9.3, transported to the product index as
--   `sylvesterQuasiGrowthTerm`).  The printed fully componentwise shape
--   takes the standard per-block growth certificates
--   `|R_{i,i+1}| |R_{i+1,i}| <= rho |R_ii - S_kk| |R_{i+1,i+1} - S_kk|`
--   as an explicit hypothesis and carries the explicit `(1+rho)` factor.
-- * The printed unspecified constant `c_{m,n} u` is realized as the
--   explicit same-gamma-class envelope `gamma_{nm+9}`, the engine envelope
--   `gamma_{N+9}` at `N = nm`: Chapter 8 fold accumulation on at most `nm`
--   terms composed with the 9-operation 2 x 2 kernel envelope `gamma_9`.
--   We do not claim the printed letter constant.
-- * Only the mixed case "R quasi-triangular, S strictly triangular" is
--   delivered; a 2 x 2 block of `S` couples unknown columns at rank
--   distance `m`, so the fully quasi-quasi case needs the interleaved
--   two-column ordering with diagonal blocks of size up to 4 and remains
--   open (see the engine file header).



namespace NumStability

namespace Wave15

open scoped BigOperators

-- ============================================================
-- The transported per-entry elimination fill-in budget
-- ============================================================

/-- Higham, 2nd ed., Chapter 9.3, Theorem 9.3, specialized as required by
    Chapter 16.2, p. 308: the per-entry GE elimination fill-in budget of the
    quasi-triangular Bartels-Stewart solve, read on the column-stacking
    product index.  It is the engine budget `quasiGrowthTerm` of the
    reordered `nm x nm` system transported through the Bartels-Stewart
    index equivalence: nonzero only at the bottom-right position of a
    marked shifted 2 x 2 diagonal block, where it equals the `n = 2` GE
    fill-in `|R_{i+1,i}| |R_{i,i+1}| / |R_ii - S_kk|` of that block.  This
    is the `|L^||U^|`-shaped part of the unconditional (16.7) budget; the
    per-block growth certificates collapse it into `rho |P|`. -/
noncomputable def sylvesterQuasiGrowthTerm (m n : Nat) (dblR : Fin m → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (p q : Prod (Fin n) (Fin m)) : Real :=
  quasiGrowthTerm (n * m) (sylvesterQuasiPairing m n dblR)
    (Wave14.sylvesterSchurBackSubCoeff m n R S)
    (Wave14.sylvesterBackSubIndexEquiv m n p)
    (Wave14.sylvesterBackSubIndexEquiv m n q)

-- ============================================================
-- Transport of the engine hypotheses through the index equivalence
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.7): entries of the
    reordered vec/Kronecker coefficient at least two positions below the
    diagonal vanish; this is the first engine zero pattern of the block
    upper-triangular reordered system for a quasi-triangular/triangular
    Schur pair. -/
theorem sylvesterQuasiSchurBackSubCoeff_below_subdiag_zero (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (dblR : Fin m → Bool)
    (hR : IsQuasiUpperTriangularFn m R dblR) (hS : IsUpperTriangularFn n S) :
    ∀ a c : Fin (n * m), c.val + 1 < a.val →
      Wave14.sylvesterSchurBackSubCoeff m n R S a c = 0 := by
  intro a c hlt
  exact sylvesterQuasiSchurBackSubCoeff_eq_zero m n R S dblR hR hS a c
    (by omega) (fun h => absurd h (by omega))

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.7): first
    subdiagonal entries of the reordered vec/Kronecker coefficient vanish
    off the marked 2 x 2 blocks; this is the second engine zero pattern of
    the block upper-triangular reordered system. -/
theorem sylvesterQuasiSchurBackSubCoeff_subdiag_zero (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (dblR : Fin m → Bool)
    (hR : IsQuasiUpperTriangularFn m R dblR) (hS : IsUpperTriangularFn n S) :
    ∀ a c : Fin (n * m), c.val + 1 = a.val →
      sylvesterQuasiPairing m n dblR c = false →
      Wave14.sylvesterSchurBackSubCoeff m n R S a c = 0 := by
  intro a c heq hdbl
  exact sylvesterQuasiSchurBackSubCoeff_eq_zero m n R S dblR hR hS a c
    (by omega) (fun _ => hdbl)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.7): combined
    marked-block zero pattern for the reordered vec/Kronecker coefficient.
    Entries strictly below the marked `1 x 1`/`2 x 2` block diagonal vanish. -/
theorem sylvesterQuasiSchurBackSubCoeff_below_markedBlock_zero (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (dblR : Fin m → Bool)
    (hR : IsQuasiUpperTriangularFn m R dblR) (hS : IsUpperTriangularFn n S) :
    ∀ a c : Fin (n * m),
      c.val + 1 < a.val ∨
        (c.val + 1 = a.val ∧ sylvesterQuasiPairing m n dblR c = false) →
      Wave14.sylvesterSchurBackSubCoeff m n R S a c = 0 := by
  intro a c h
  rcases h with hfar | ⟨hadj, hpair⟩
  · exact sylvesterQuasiSchurBackSubCoeff_below_subdiag_zero
      m n R S dblR hR hS a c hfar
  · exact sylvesterQuasiSchurBackSubCoeff_subdiag_zero
      m n R S dblR hR hS a c hadj hpair

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3), (16.6)-(16.7):
    transport of the diagonal-separation certificate.  If `R_ii ≠ S_kk` on
    every row `i` of `R` that is not the bottom row of a marked 2 x 2 block
    — the scalar pivots and the block first pivots of the quasi-triangular
    substitution (16.6) — then every non-bottom-row diagonal entry
    `R_ii - S_kk` of the reordered coefficient is nonzero, which is the
    engine's pivot hypothesis. -/
theorem sylvesterQuasiSchurBackSubCoeff_pivot_ne_zero (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (dblR : Fin m → Bool)
    (hsep : ∀ (i : Fin m) (k : Fin n),
      ¬(0 < i.val ∧ dblR ⟨i.val - 1, by omega⟩ = true) → R i i ≠ S k k) :
    ∀ a : Fin (n * m),
      ¬(0 < a.val ∧
        sylvesterQuasiPairing m n dblR ⟨a.val - 1, by omega⟩ = true) →
      Wave14.sylvesterSchurBackSubCoeff m n R S a a ≠ 0 := by
  intro a hnot
  have hfac := sylvesterQuasiPairing_notSecond_decode m n dblR a hnot
  rw [Wave14.sylvesterSchurBackSubCoeff_diag]
  exact sub_ne_zero_of_ne (hsep _ _ hfac)

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6): transport of
    the per-block computed-second-pivot certificate.  If every marked
    shifted 2 x 2 block `[[R_ii - S_kk, R_{i,i+1}], [R_{i+1,i},
    R_{i+1,i+1} - S_kk]]` of the substitution (16.6) has nonzero computed
    second pivot, then so does every marked 2 x 2 diagonal block of the
    reordered coefficient, which is the engine's completion certificate for
    the `fl_solve2x2` kernel. -/
theorem sylvesterQuasiSchurBackSubCoeff_secondPivot_ne_zero (fp : FPModel)
    (m n : Nat) (R : RMatFn m m) (S : RMatFn n n) (dblR : Fin m → Bool)
    (hpiv : ∀ (i i' : Fin m) (k : Fin n), i'.val = i.val + 1 →
      dblR i = true →
      flSolve2x2SecondPivot fp (R i i - S k k) (R i i') (R i' i)
        (R i' i' - S k k) ≠ 0) :
    ∀ a b' : Fin (n * m), b'.val = a.val + 1 →
      sylvesterQuasiPairing m n dblR a = true →
      flSolve2x2SecondPivot fp
        (Wave14.sylvesterSchurBackSubCoeff m n R S a a)
        (Wave14.sylvesterSchurBackSubCoeff m n R S a b')
        (Wave14.sylvesterSchurBackSubCoeff m n R S b' a)
        (Wave14.sylvesterSchurBackSubCoeff m n R S b' b') ≠ 0 := by
  intro a b' hb' hd
  obtain ⟨k, i, i', hii', hdbl, h11, h12, h21, h22⟩ :=
    sylvesterQuasiPairing_block_decode m n dblR R S a b' hb' hd
  rw [h11, h12, h21, h22]
  exact hpiv i i' k hii' hdbl

/-- Higham, 2nd ed., Chapter 9.3 and Chapter 16.2, p. 308: transport of the
    per-block growth certificate.  If every marked shifted 2 x 2 block of
    the substitution (16.6) satisfies the componentwise growth condition
    `|R_{i,i+1}| |R_{i+1,i}| <= rho |R_ii - S_kk| |R_{i+1,i+1} - S_kk|`,
    then every marked 2 x 2 diagonal block of the reordered coefficient
    satisfies the engine's growth hypothesis, which collapses the GE
    fill-in into the fully componentwise `(1+rho)` budget. -/
theorem sylvesterQuasiSchurBackSubCoeff_growth (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (dblR : Fin m → Bool) (ρ : Real)
    (hgrow : ∀ (i i' : Fin m) (k : Fin n), i'.val = i.val + 1 →
      dblR i = true →
      |R i i'| * |R i' i| ≤ ρ * (|R i i - S k k| * |R i' i' - S k k|)) :
    ∀ a b' : Fin (n * m), b'.val = a.val + 1 →
      sylvesterQuasiPairing m n dblR a = true →
      |Wave14.sylvesterSchurBackSubCoeff m n R S a b'| *
          |Wave14.sylvesterSchurBackSubCoeff m n R S b' a| ≤
        ρ * (|Wave14.sylvesterSchurBackSubCoeff m n R S a a| *
          |Wave14.sylvesterSchurBackSubCoeff m n R S b' b'|) := by
  intro a b' hb' hd
  obtain ⟨k, i, i', hii', hdbl, h11, h12, h21, h22⟩ :=
    sylvesterQuasiPairing_block_decode m n dblR R S a b' hb' hd
  rw [h11, h12, h21, h22]
  exact hgrow i i' k hii' hdbl

-- ============================================================
-- (16.7): rounded block-substitution backward error
-- ============================================================

















































































































































-- ============================================================
-- (16.8): componentwise residual consequence
-- ============================================================

























































































































































































































































































































































































-- ============================================================
-- Source-numbered aliases
-- ============================================================













































































































































end Wave15

end NumStability
