import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.QuasiTriangularSylvester
import NumStability.Source.Higham.Chapter16.QuasiRounded.Solve
import NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.QuasiRoundedSylvester

/-!
# Algorithms.Sylvester.Higham16QuasiRoundedSylvester

Historical declaration-bearing facade. Genuine-private and ambient-context retention closure remains here with its original identity.
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


















-- ============================================================
-- Transport of the engine hypotheses through the index equivalence
-- ============================================================




















































































































-- ============================================================
-- (16.7): rounded block-substitution backward error
-- ============================================================

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.7),
    quasi-triangular (real Schur) variant, unconditional form** (supplied
    quasi-triangular `R`, triangular `S`).  The computed vectorized
    solution `x^ = flSylvesterQuasiSchurBlockBackSubSolveVec` of the
    Schur-form Sylvester system — rounded quasi-triangular block back
    substitution (16.6) applied to the reordered vec/Kronecker system —
    satisfies the exactly perturbed system

    `(P + DeltaP) x^ = vec(C~)` with
    `|DeltaP| <= gamma_{nm+9} (|P| + fill-in)`

    componentwise, where `P = I_n kron R - S^T kron I_m` is the (16.2)
    coefficient and the fill-in is the explicit Theorem 9.3 `|L^||U^|`
    elimination budget `sylvesterQuasiGrowthTerm`, supported only on the
    bottom-right entries of the marked shifted 2 x 2 blocks.  This
    instantiates the engine `flQuasiBlockBackSub_backward_error` through
    the Bartels-Stewart index equivalence.  Hypotheses are the honest
    per-block completion certificates: diagonal separation `R_ii ≠ S_kk`
    on non-bottom rows (scalar and block first pivots) and nonzero
    computed second pivots on the marked shifted blocks.  The printed
    unspecified constant `c_{m,n} u` is realized as the same-gamma-class
    envelope `gamma_{nm+9}`; errors from computing the Schur factors or
    the transformed right-hand side belong to (16.9) and are not modeled
    here. -/
theorem sylvesterVecCoeff_quasiTriangular_blockBackSub_backward_error
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n)
    (hRp : IsQuasiBlockPairing m dblR)
    (hR : IsQuasiUpperTriangularFn m R dblR) (hS : IsUpperTriangularFn n S)
    (hsep : ∀ (i : Fin m) (k : Fin n),
      ¬(0 < i.val ∧ dblR ⟨i.val - 1, by omega⟩ = true) → R i i ≠ S k k)
    (hpiv : ∀ (i i' : Fin m) (k : Fin n), i'.val = i.val + 1 →
      dblR i = true →
      flSolve2x2SecondPivot fp (R i i - S k k) (R i i') (R i' i)
        (R i' i' - S k k) ≠ 0)
    (hgv : gammaValid fp (n * m + 9)) :
    ∃ ΔP : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real,
      (∀ p q, |ΔP p q| ≤ gamma fp (n * m + 9) *
        (|sylvesterVecCoeff m n R S p q| +
          sylvesterQuasiGrowthTerm m n dblR R S p q)) ∧
      Matrix.mulVec (sylvesterVecCoeff m n R S + ΔP)
          (flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct) =
        Matrix.vec Ct := by
  obtain ⟨ΔT, hΔTbound, hΔTeq⟩ :=
    flQuasiBlockBackSub_backward_error fp (n * m)
      (sylvesterQuasiPairing m n dblR)
      (Wave14.sylvesterSchurBackSubCoeff m n R S)
      (Wave14.sylvesterSchurBackSubRhs m n Ct)
      (sylvesterQuasiPairing_isQuasiBlockPairing m n dblR hRp)
      (sylvesterQuasiSchurBackSubCoeff_below_subdiag_zero m n R S dblR hR hS)
      (sylvesterQuasiSchurBackSubCoeff_subdiag_zero m n R S dblR hR hS)
      (sylvesterQuasiSchurBackSubCoeff_pivot_ne_zero m n R S dblR hsep)
      (sylvesterQuasiSchurBackSubCoeff_secondPivot_ne_zero fp m n R S dblR
        hpiv)
      hgv
  refine ⟨fun p q =>
    ΔT (Wave14.sylvesterBackSubIndexEquiv m n p)
      (Wave14.sylvesterBackSubIndexEquiv m n q), ?_, ?_⟩
  · intro p q
    have hb := hΔTbound (Wave14.sylvesterBackSubIndexEquiv m n p)
      (Wave14.sylvesterBackSubIndexEquiv m n q)
    rw [Wave14.sylvesterSchurBackSubCoeff_reindex] at hb
    exact hb
  · funext p
    have hrow := hΔTeq (Wave14.sylvesterBackSubIndexEquiv m n p)
    rw [Wave14.sylvesterSchurBackSubRhs_reindex] at hrow
    rw [← hrow]
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply]
    refine Fintype.sum_equiv (Wave14.sylvesterBackSubIndexEquiv m n) _ _ ?_
    intro q
    rw [Wave14.sylvesterSchurBackSubCoeff_reindex]
    rfl

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.7),
    quasi-triangular (real Schur) variant, printed fully componentwise
    form** (supplied quasi-triangular `R`, triangular `S`).  Under the
    additional per-block growth certificates
    `|R_{i,i+1}| |R_{i+1,i}| <= rho |R_ii - S_kk| |R_{i+1,i+1} - S_kk|`
    on the marked shifted 2 x 2 blocks — the standard componentwise
    control of the 2 x 2 GE fill-in — the computed vectorized solution
    satisfies the printed componentwise backward-error model

    `(P + DeltaP) x^ = vec(C~)` with
    `|DeltaP| <= (1 + rho) gamma_{nm+9} |P|`

    componentwise, with `P = I_n kron R - S^T kron I_m`.  This is the
    quasi-triangular analogue of the Wave-14 strictly triangular (16.7)
    endpoint; the printed unspecified constant `c_{m,n} u` is realized as
    the same-gamma-class envelope `(1 + rho) gamma_{nm+9}` with the
    explicit growth factor documented. -/
theorem sylvesterVecCoeff_quasiTriangular_blockBackSub_backward_error_componentwise
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n) (ρ : Real)
    (hRp : IsQuasiBlockPairing m dblR)
    (hR : IsQuasiUpperTriangularFn m R dblR) (hS : IsUpperTriangularFn n S)
    (hsep : ∀ (i : Fin m) (k : Fin n),
      ¬(0 < i.val ∧ dblR ⟨i.val - 1, by omega⟩ = true) → R i i ≠ S k k)
    (hpiv : ∀ (i i' : Fin m) (k : Fin n), i'.val = i.val + 1 →
      dblR i = true →
      flSolve2x2SecondPivot fp (R i i - S k k) (R i i') (R i' i)
        (R i' i' - S k k) ≠ 0)
    (hρ : 0 ≤ ρ)
    (hgrow : ∀ (i i' : Fin m) (k : Fin n), i'.val = i.val + 1 →
      dblR i = true →
      |R i i'| * |R i' i| ≤ ρ * (|R i i - S k k| * |R i' i' - S k k|))
    (hgv : gammaValid fp (n * m + 9)) :
    ∃ ΔP : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real,
      (∀ p q, |ΔP p q| ≤ (1 + ρ) * gamma fp (n * m + 9) *
        |sylvesterVecCoeff m n R S p q|) ∧
      Matrix.mulVec (sylvesterVecCoeff m n R S + ΔP)
          (flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct) =
        Matrix.vec Ct := by
  obtain ⟨ΔT, hΔTbound, hΔTeq⟩ :=
    flQuasiBlockBackSub_backward_error_componentwise fp (n * m)
      (sylvesterQuasiPairing m n dblR)
      (Wave14.sylvesterSchurBackSubCoeff m n R S)
      (Wave14.sylvesterSchurBackSubRhs m n Ct) ρ
      (sylvesterQuasiPairing_isQuasiBlockPairing m n dblR hRp)
      (sylvesterQuasiSchurBackSubCoeff_below_subdiag_zero m n R S dblR hR hS)
      (sylvesterQuasiSchurBackSubCoeff_subdiag_zero m n R S dblR hR hS)
      (sylvesterQuasiSchurBackSubCoeff_pivot_ne_zero m n R S dblR hsep)
      (sylvesterQuasiSchurBackSubCoeff_secondPivot_ne_zero fp m n R S dblR
        hpiv)
      hρ
      (sylvesterQuasiSchurBackSubCoeff_growth m n R S dblR ρ hgrow)
      hgv
  refine ⟨fun p q =>
    ΔT (Wave14.sylvesterBackSubIndexEquiv m n p)
      (Wave14.sylvesterBackSubIndexEquiv m n q), ?_, ?_⟩
  · intro p q
    have hb := hΔTbound (Wave14.sylvesterBackSubIndexEquiv m n p)
      (Wave14.sylvesterBackSubIndexEquiv m n q)
    rw [Wave14.sylvesterSchurBackSubCoeff_reindex] at hb
    exact hb
  · funext p
    have hrow := hΔTeq (Wave14.sylvesterBackSubIndexEquiv m n p)
    rw [Wave14.sylvesterSchurBackSubRhs_reindex] at hrow
    rw [← hrow]
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply]
    refine Fintype.sum_equiv (Wave14.sylvesterBackSubIndexEquiv m n) _ _ ?_
    intro q
    rw [Wave14.sylvesterSchurBackSubCoeff_reindex]
    rfl

-- ============================================================
-- (16.8): componentwise residual consequence
-- ============================================================

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8),
    quasi-triangular (real Schur) variant, vectorized fill-in-budget form**
    (supplied quasi-triangular `R`, triangular `S`).  The computed
    vectorized solution of the Schur-form Sylvester system satisfies a
    componentwise residual bound from the unconditional (16.7) model, keeping
    the explicit Theorem 9.3 elimination fill-in budget visible instead of
    assuming growth certificates that collapse it to `(1 + rho) |P|`. -/
theorem sylvesterVecCoeff_quasiTriangular_blockBackSub_componentwise_residual_with_growthTerm
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n)
    (hRp : IsQuasiBlockPairing m dblR)
    (hR : IsQuasiUpperTriangularFn m R dblR) (hS : IsUpperTriangularFn n S)
    (hsep : ∀ (i : Fin m) (k : Fin n),
      ¬(0 < i.val ∧ dblR ⟨i.val - 1, by omega⟩ = true) → R i i ≠ S k k)
    (hpiv : ∀ (i i' : Fin m) (k : Fin n), i'.val = i.val + 1 →
      dblR i = true →
      flSolve2x2SecondPivot fp (R i i - S k k) (R i i') (R i' i)
        (R i' i' - S k k) ≠ 0)
    (hgv : gammaValid fp (n * m + 9)) (p : Prod (Fin n) (Fin m)) :
    |Matrix.vec Ct p -
        Matrix.mulVec (sylvesterVecCoeff m n R S)
          (flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct) p| ≤
      gamma fp (n * m + 9) *
        ∑ q, (|sylvesterVecCoeff m n R S p q| +
          sylvesterQuasiGrowthTerm m n dblR R S p q) *
          |flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct q| := by
  obtain ⟨ΔP, hbound, heq⟩ :=
    sylvesterVecCoeff_quasiTriangular_blockBackSub_backward_error
      fp m n dblR R S Ct hRp hR hS hsep hpiv hgv
  have hdiff :
      Matrix.vec Ct p -
          Matrix.mulVec (sylvesterVecCoeff m n R S)
            (flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct) p =
        ∑ q, ΔP p q *
          flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct q := by
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
        |flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct q| ≤
        (gamma fp (n * m + 9) *
          (|sylvesterVecCoeff m n R S p q| +
            sylvesterQuasiGrowthTerm m n dblR R S p q)) *
          |flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct q| :=
      mul_le_mul_of_nonneg_right (hbound p q) (abs_nonneg _)
    _ = gamma fp (n * m + 9) *
        ((|sylvesterVecCoeff m n R S p q| +
            sylvesterQuasiGrowthTerm m n dblR R S p q) *
          |flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct q|) := by
      ring

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8),
    quasi-triangular (real Schur) variant, printed matrix fill-in-budget
    form** (supplied quasi-triangular `R`, triangular `S`).  This is the
    matrix-entry companion to the vectorized fill-in residual bound, keeping
    the explicit GE fill-in row budget instead of assuming growth certificates
    that collapse it into `(1 + rho) |P|`. -/
theorem sylvesterResidualRect_quasiTriangular_blockBackSub_componentwise_le_with_growthTerm
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n)
    (hRp : IsQuasiBlockPairing m dblR)
    (hR : IsQuasiUpperTriangularFn m R dblR) (hS : IsUpperTriangularFn n S)
    (hsep : ∀ (i : Fin m) (k : Fin n),
      ¬(0 < i.val ∧ dblR ⟨i.val - 1, by omega⟩ = true) → R i i ≠ S k k)
    (hpiv : ∀ (i i' : Fin m) (k : Fin n), i'.val = i.val + 1 →
      dblR i = true →
      flSolve2x2SecondPivot fp (R i i - S k k) (R i i') (R i' i)
        (R i' i' - S k k) ≠ 0)
    (hgv : gammaValid fp (n * m + 9)) (i : Fin m) (k : Fin n) :
    |sylvesterResidualRect m n R S Ct
        (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct) i k| ≤
      gamma fp (n * m + 9) *
        (matMulRect m m n (fun a b => |R a b|)
            (fun a b =>
              |flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct a b|)
            i k +
          matMulRect m n n
            (fun a b =>
              |flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct a b|)
            (fun a b => |S a b|) i k +
          ∑ q : Prod (Fin n) (Fin m),
            sylvesterQuasiGrowthTerm m n dblR R S (k, i) q *
              |flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct q|) := by
  have hvec :=
    sylvesterVecCoeff_quasiTriangular_blockBackSub_componentwise_residual_with_growthTerm
      fp m n dblR R S Ct hRp hR hS hsep hpiv hgv (k, i)
  rw [← vec_flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct] at hvec
  rw [sylvesterVecCoeff_mulVec_vec m n R S
    (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct)] at hvec
  refine le_trans hvec ?_
  refine mul_le_mul_of_nonneg_left ?_ (gamma_nonneg fp hgv)
  have hsplit :
      (∑ q : Prod (Fin n) (Fin m),
          (|sylvesterVecCoeff m n R S (k, i) q| +
              sylvesterQuasiGrowthTerm m n dblR R S (k, i) q) *
            |Matrix.vec (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct)
              q|) =
        (∑ q : Prod (Fin n) (Fin m),
          |sylvesterVecCoeff m n R S (k, i) q| *
            |Matrix.vec (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct)
              q|) +
        ∑ q : Prod (Fin n) (Fin m),
          sylvesterQuasiGrowthTerm m n dblR R S (k, i) q *
            |Matrix.vec (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct)
              q| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hsplit]
  apply add_le_add
  · refine le_trans (Wave14.sylvesterVecCoeff_abs_row_action_le m n R S
      (Matrix.vec (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct))
      (k, i)) ?_
    refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
    · show (∑ j : Fin m, |R i j| *
          |Matrix.vec (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct)
            (k, j)|) =
        ∑ j : Fin m, |R i j| *
          |flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct j k|
      rfl
    · show (∑ l : Fin n, |S l k| *
          |Matrix.vec (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct)
            (l, i)|) =
        ∑ l : Fin n,
          |flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct i l| *
            |S l k|
      apply Finset.sum_congr rfl
      intro l _
      exact mul_comm _ _
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro q _
    rw [vec_flSylvesterQuasiSchurBlockBackSubSolve]

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8),
    quasi-triangular (real Schur) variant, vectorized componentwise form**
    (supplied quasi-triangular `R`, triangular `S`).  The computed
    vectorized solution of the Schur-form Sylvester system satisfies

    `|vec(C~) - P x^| <= (1 + rho) gamma_{nm+9} (|P| |x^|)`

    componentwise, the residual consequence of the quasi-triangular (16.7)
    backward-error model under the per-block pivot/growth certificates.
    The printed constant `c_{m,n} u` is realized as the same-gamma-class
    envelope `(1 + rho) gamma_{nm+9}`. -/
theorem sylvesterVecCoeff_quasiTriangular_blockBackSub_componentwise_residual
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n) (ρ : Real)
    (hRp : IsQuasiBlockPairing m dblR)
    (hR : IsQuasiUpperTriangularFn m R dblR) (hS : IsUpperTriangularFn n S)
    (hsep : ∀ (i : Fin m) (k : Fin n),
      ¬(0 < i.val ∧ dblR ⟨i.val - 1, by omega⟩ = true) → R i i ≠ S k k)
    (hpiv : ∀ (i i' : Fin m) (k : Fin n), i'.val = i.val + 1 →
      dblR i = true →
      flSolve2x2SecondPivot fp (R i i - S k k) (R i i') (R i' i)
        (R i' i' - S k k) ≠ 0)
    (hρ : 0 ≤ ρ)
    (hgrow : ∀ (i i' : Fin m) (k : Fin n), i'.val = i.val + 1 →
      dblR i = true →
      |R i i'| * |R i' i| ≤ ρ * (|R i i - S k k| * |R i' i' - S k k|))
    (hgv : gammaValid fp (n * m + 9)) (p : Prod (Fin n) (Fin m)) :
    |Matrix.vec Ct p -
        Matrix.mulVec (sylvesterVecCoeff m n R S)
          (flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct) p| ≤
      (1 + ρ) * gamma fp (n * m + 9) *
        ∑ q, |sylvesterVecCoeff m n R S p q| *
          |flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct q| := by
  obtain ⟨ΔP, hbound, heq⟩ :=
    sylvesterVecCoeff_quasiTriangular_blockBackSub_backward_error_componentwise
      fp m n dblR R S Ct ρ hRp hR hS hsep hpiv hρ hgrow hgv
  exact Wave14.componentwise_residual_of_perturbed_mulVec
    (sylvesterVecCoeff m n R S) ΔP
    (flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct)
    (Matrix.vec Ct) ((1 + ρ) * gamma fp (n * m + 9)) hbound heq p

/-- **Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8),
    quasi-triangular (real Schur) variant, printed matrix form** (supplied
    quasi-triangular `R`, triangular `S`).  The computed Schur-coordinate
    solution `Z^ = flSylvesterQuasiSchurBlockBackSubSolve` of the
    quasi-triangular Bartels-Stewart substitution (16.6) satisfies the
    componentwise residual bound

    `|C~ - R Z^ + Z^ S| <= (1 + rho) gamma_{nm+9} (|R| |Z^| + |Z^| |S|)`

    entrywise, the un-vectorized form of the (16.8) consequence of the
    quasi-triangular (16.7) backward-error model, under the per-block
    pivot/growth certificates.  The printed constant `c_{m,n} u` is
    realized as the same-gamma-class envelope `(1 + rho) gamma_{nm+9}`. -/
theorem sylvesterResidualRect_quasiTriangular_blockBackSub_componentwise_le
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n) (ρ : Real)
    (hRp : IsQuasiBlockPairing m dblR)
    (hR : IsQuasiUpperTriangularFn m R dblR) (hS : IsUpperTriangularFn n S)
    (hsep : ∀ (i : Fin m) (k : Fin n),
      ¬(0 < i.val ∧ dblR ⟨i.val - 1, by omega⟩ = true) → R i i ≠ S k k)
    (hpiv : ∀ (i i' : Fin m) (k : Fin n), i'.val = i.val + 1 →
      dblR i = true →
      flSolve2x2SecondPivot fp (R i i - S k k) (R i i') (R i' i)
        (R i' i' - S k k) ≠ 0)
    (hρ : 0 ≤ ρ)
    (hgrow : ∀ (i i' : Fin m) (k : Fin n), i'.val = i.val + 1 →
      dblR i = true →
      |R i i'| * |R i' i| ≤ ρ * (|R i i - S k k| * |R i' i' - S k k|))
    (hgv : gammaValid fp (n * m + 9)) (i : Fin m) (k : Fin n) :
    |sylvesterResidualRect m n R S Ct
        (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct) i k| ≤
      (1 + ρ) * gamma fp (n * m + 9) *
        (matMulRect m m n (fun a b => |R a b|)
            (fun a b =>
              |flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct a b|)
            i k +
          matMulRect m n n
            (fun a b =>
              |flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct a b|)
            (fun a b => |S a b|) i k) := by
  have hvec :=
    sylvesterVecCoeff_quasiTriangular_blockBackSub_componentwise_residual
      fp m n dblR R S Ct ρ hRp hR hS hsep hpiv hρ hgrow hgv (k, i)
  rw [← vec_flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct] at hvec
  rw [sylvesterVecCoeff_mulVec_vec m n R S
    (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct)] at hvec
  refine le_trans hvec ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (by linarith : (0 : Real) ≤ 1 + ρ) (gamma_nonneg fp hgv))
  refine le_trans (Wave14.sylvesterVecCoeff_abs_row_action_le m n R S
    (Matrix.vec (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct))
    (k, i)) ?_
  refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · show (∑ j : Fin m, |R i j| *
        |Matrix.vec (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct)
          (k, j)|) =
      ∑ j : Fin m, |R i j| *
        |flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct j k|
    rfl
  · show (∑ l : Fin n, |S l k| *
        |Matrix.vec (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct)
          (l, i)|) =
      ∑ l : Fin n,
        |flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct i l| *
          |S l k|
    apply Finset.sum_congr rfl
    intro l _
    exact mul_comm _ _

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.7)-(16.8),
    quasi-triangular (real Schur) variant: bundled endpoint exposing the
    componentwise backward-error model, its vectorized residual consequence,
    and the printed matrix residual form under one shared hypothesis list. -/
theorem sylvesterVecCoeff_quasiTriangular_blockBackSub_componentwise_error_and_residual
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n) (ρ : Real)
    (hRp : IsQuasiBlockPairing m dblR)
    (hR : IsQuasiUpperTriangularFn m R dblR) (hS : IsUpperTriangularFn n S)
    (hsep : ∀ (i : Fin m) (k : Fin n),
      ¬(0 < i.val ∧ dblR ⟨i.val - 1, by omega⟩ = true) → R i i ≠ S k k)
    (hpiv : ∀ (i i' : Fin m) (k : Fin n), i'.val = i.val + 1 →
      dblR i = true →
      flSolve2x2SecondPivot fp (R i i - S k k) (R i i') (R i' i)
        (R i' i' - S k k) ≠ 0)
    (hρ : 0 ≤ ρ)
    (hgrow : ∀ (i i' : Fin m) (k : Fin n), i'.val = i.val + 1 →
      dblR i = true →
      |R i i'| * |R i' i| ≤ ρ * (|R i i - S k k| * |R i' i' - S k k|))
    (hgv : gammaValid fp (n * m + 9)) :
    (∃ ΔP : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real,
      (∀ p q, |ΔP p q| ≤ (1 + ρ) * gamma fp (n * m + 9) *
        |sylvesterVecCoeff m n R S p q|) ∧
      Matrix.mulVec (sylvesterVecCoeff m n R S + ΔP)
          (flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct) =
        Matrix.vec Ct) ∧
    (∀ p : Prod (Fin n) (Fin m),
      |Matrix.vec Ct p -
          Matrix.mulVec (sylvesterVecCoeff m n R S)
            (flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct) p| ≤
        (1 + ρ) * gamma fp (n * m + 9) *
          ∑ q, |sylvesterVecCoeff m n R S p q| *
            |flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct q|) ∧
    (∀ (i : Fin m) (k : Fin n),
      |sylvesterResidualRect m n R S Ct
          (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct) i k| ≤
        (1 + ρ) * gamma fp (n * m + 9) *
          (matMulRect m m n (fun a b => |R a b|)
              (fun a b =>
                |flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct a b|)
              i k +
            matMulRect m n n
              (fun a b =>
                |flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct a b|)
              (fun a b => |S a b|) i k)) := by
  constructor
  · exact
      sylvesterVecCoeff_quasiTriangular_blockBackSub_backward_error_componentwise
        fp m n dblR R S Ct ρ hRp hR hS hsep hpiv hρ hgrow hgv
  constructor
  · intro p
    exact
      sylvesterVecCoeff_quasiTriangular_blockBackSub_componentwise_residual
        fp m n dblR R S Ct ρ hRp hR hS hsep hpiv hρ hgrow hgv p
  · intro i k
    exact
      sylvesterResidualRect_quasiTriangular_blockBackSub_componentwise_le
        fp m n dblR R S Ct ρ hRp hR hS hsep hpiv hρ hgrow hgv i k

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.7)-(16.8),
    quasi-triangular (real Schur) variant: bundled endpoint exposing the
    unconditional fill-in-budget backward-error model, its vectorized residual
    consequence, and the printed matrix residual form under one shared
    hypothesis list. -/
theorem sylvesterVecCoeff_quasiTriangular_blockBackSub_componentwise_error_and_residual_with_growthTerm
    (fp : FPModel) (m n : Nat) (dblR : Fin m → Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n)
    (hRp : IsQuasiBlockPairing m dblR)
    (hR : IsQuasiUpperTriangularFn m R dblR) (hS : IsUpperTriangularFn n S)
    (hsep : ∀ (i : Fin m) (k : Fin n),
      ¬(0 < i.val ∧ dblR ⟨i.val - 1, by omega⟩ = true) → R i i ≠ S k k)
    (hpiv : ∀ (i i' : Fin m) (k : Fin n), i'.val = i.val + 1 →
      dblR i = true →
      flSolve2x2SecondPivot fp (R i i - S k k) (R i i') (R i' i)
        (R i' i' - S k k) ≠ 0)
    (hgv : gammaValid fp (n * m + 9)) :
    (∃ ΔP : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real,
      (∀ p q, |ΔP p q| ≤ gamma fp (n * m + 9) *
        (|sylvesterVecCoeff m n R S p q| +
          sylvesterQuasiGrowthTerm m n dblR R S p q)) ∧
      Matrix.mulVec (sylvesterVecCoeff m n R S + ΔP)
          (flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct) =
        Matrix.vec Ct) ∧
    (∀ p : Prod (Fin n) (Fin m),
      |Matrix.vec Ct p -
          Matrix.mulVec (sylvesterVecCoeff m n R S)
            (flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct) p| ≤
        gamma fp (n * m + 9) *
          ∑ q, (|sylvesterVecCoeff m n R S p q| +
            sylvesterQuasiGrowthTerm m n dblR R S p q) *
            |flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct q|) ∧
    (∀ (i : Fin m) (k : Fin n),
      |sylvesterResidualRect m n R S Ct
          (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct) i k| ≤
        gamma fp (n * m + 9) *
          (matMulRect m m n (fun a b => |R a b|)
              (fun a b =>
                |flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct a b|)
              i k +
            matMulRect m n n
              (fun a b =>
                |flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct a b|)
              (fun a b => |S a b|) i k +
            ∑ q : Prod (Fin n) (Fin m),
              sylvesterQuasiGrowthTerm m n dblR R S (k, i) q *
                |flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct q|)) := by
  constructor
  · exact
      sylvesterVecCoeff_quasiTriangular_blockBackSub_backward_error
        fp m n dblR R S Ct hRp hR hS hsep hpiv hgv
  constructor
  · intro p
    exact
      sylvesterVecCoeff_quasiTriangular_blockBackSub_componentwise_residual_with_growthTerm
        fp m n dblR R S Ct hRp hR hS hsep hpiv hgv p
  · intro i k
    exact
      sylvesterResidualRect_quasiTriangular_blockBackSub_componentwise_le_with_growthTerm
        fp m n dblR R S Ct hRp hR hS hsep hpiv hgv i k

-- ============================================================
-- Source-numbered aliases
-- ============================================================





















































































/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.7),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    unconditional backward-error model with the explicit Theorem 9.3
    elimination fill-in budget. -/
alias H16_eq16_7_quasi_sylvesterVecCoeff_blockBackSub_backward_error :=
  sylvesterVecCoeff_quasiTriangular_blockBackSub_backward_error

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.7),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    printed fully componentwise backward-error model
    `(P + DeltaP) x^ = vec(C~)`, `|DeltaP| <= (1+rho) gamma_{nm+9} |P|`
    under the per-block pivot/growth certificates. -/
alias H16_eq16_7_quasi_sylvesterVecCoeff_blockBackSub_backward_error_componentwise :=
  sylvesterVecCoeff_quasiTriangular_blockBackSub_backward_error_componentwise

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    vectorized componentwise residual consequence with the explicit GE fill-in
    budget from the unconditional (16.7) model. -/
alias H16_eq16_8_quasi_sylvesterVecCoeff_blockBackSub_componentwise_residual_with_growthTerm :=
  sylvesterVecCoeff_quasiTriangular_blockBackSub_componentwise_residual_with_growthTerm

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    printed matrix residual consequence with the explicit GE fill-in row
    budget from the unconditional (16.7) model. -/
alias H16_eq16_8_quasi_sylvesterResidualRect_blockBackSub_componentwise_le_with_growthTerm :=
  sylvesterResidualRect_quasiTriangular_blockBackSub_componentwise_le_with_growthTerm

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.7)-(16.8),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    bundled unconditional fill-in-budget backward-error and residual endpoint
    package. -/
alias H16_eq16_7_8_quasi_sylvesterVecCoeff_blockBackSub_componentwise_error_and_residual_with_growthTerm :=
  sylvesterVecCoeff_quasiTriangular_blockBackSub_componentwise_error_and_residual_with_growthTerm

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    vectorized componentwise residual consequence
    `|vec(C~) - P x^| <= (1+rho) gamma_{nm+9} (|P| |x^|)`. -/
alias H16_eq16_8_quasi_sylvesterVecCoeff_blockBackSub_componentwise_residual :=
  sylvesterVecCoeff_quasiTriangular_blockBackSub_componentwise_residual

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    printed matrix form
    `|C~ - R Z^ + Z^ S| <= (1+rho) gamma_{nm+9} (|R||Z^| + |Z^||S|)`. -/
alias H16_eq16_8_quasi_sylvesterResidualRect_blockBackSub_componentwise_le :=
  sylvesterResidualRect_quasiTriangular_blockBackSub_componentwise_le

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.7)-(16.8),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    bundled componentwise backward-error and residual endpoint package. -/
alias H16_eq16_7_8_quasi_sylvesterVecCoeff_blockBackSub_componentwise_error_and_residual :=
  sylvesterVecCoeff_quasiTriangular_blockBackSub_componentwise_error_and_residual

end Wave15

end NumStability
