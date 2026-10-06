import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.BlockTraversal
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.TriangularBartelsStewart.RoundedSolve
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.FloatingPoint.Model

/-!
# Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.QuasiTriangularSolve

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16QuasiRoundedSolve.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 16.2, pp. 307-308, equations (16.6)-(16.8), quasi-triangular
-- (real Schur) variant: the rounded block-substitution backward-error model
-- for the vectorized Schur-form Sylvester system when the left Schur factor
-- is quasi-upper-triangular with 2 x 2 diagonal blocks (complex-conjugate
-- eigenpairs) and the right Schur factor is upper triangular.
--
-- Setting.  Wave 14 (`Higham16RoundedTriangular`) proved the printed rounded
-- substitution model (16.7) and its residual consequence (16.8) for the
-- strictly triangular Schur case: both factors upper triangular, every
-- Bartels-Stewart step a scalar division.  Higham's own algorithmic setting
-- (p. 308) is the REAL Schur decomposition, where the factors are merely
-- quasi-triangular and the substitution (16.6) must solve 2 x 2 linear
-- systems for the 2 x 2 diagonal blocks.  This file supplies the missing
-- rounded block-substitution model in three layers:
--
-- * `fl_solve2x2` is the rounded 2 x 2 linear-system kernel: two-step
--   Gaussian elimination without pivoting built from the `FPModel`
--   primitives, exactly the Chapter 9 elimination specialized to `n = 2`.
--   `fl_solve2x2_backward_error` is its componentwise backward error, the
--   2 x 2 analogue of the Chapter 8/9 substitution endpoints: the computed
--   solution solves an exactly perturbed system whose perturbation is
--   bounded entrywise by `gamma_9` times the explicit GE budget
--   `|L||U|`-shaped matrix (the (2,2) entry carries the elimination
--   fill-in `|c||b|/|a|`).  Under the usual growth certificate
--   `|c||b| <= rho |a||d|` the budget collapses to `(1+rho)|M|`, giving the
--   fully componentwise `|DeltaM| <= (1+rho) gamma_9 |M|` shape.
-- * `flQuasiBlockBackSub` is the rounded quasi-triangular block back
--   substitution on an `N x N` system whose diagonal blocks (marked by an
--   adjacent-pair map `dbl`) have size 1 or 2: scalar rows are solved by
--   `fl_div` exactly as in Chapter 8 Algorithm 8.1, and marked 2 x 2
--   diagonal blocks by the `fl_solve2x2` kernel, processing rows bottom-up
--   in the Bartels-Stewart elimination order.
--   `flQuasiBlockBackSub_backward_error` is the block analogue of
--   Theorem 8.5: `(T + DeltaT) x^ = b` with `|DeltaT|` bounded entrywise by
--   `gamma_{N+9}` times `|T|` plus the per-block elimination fill-in, and
--   `flQuasiBlockBackSub_backward_error_componentwise` restores the printed
--   fully componentwise shape under the per-block growth certificates.
-- * The Sylvester instantiation transports the engine through the Wave-14
--   Bartels-Stewart index equivalence: for a supplied quasi-triangular `R`
--   (adjacent 2 x 2 blocks marked by `dblR`) and upper-triangular `S`, the
--   reordered vec/Kronecker coefficient `P = I_n kron R - S^T kron I_m` of
--   (16.2) is block upper triangular with the same 1 x 1 / 2 x 2 diagonal
--   block structure, and the computed block-substitution solution satisfies
--   the (16.7)-shaped backward error
--   `(P + DeltaP) x^ = vec(C~), |DeltaP| <= (1+rho) gamma_{nm+9} |P|`
--   under the per-block pivot/growth certificates, together with the
--   (16.8)-shaped componentwise residual in vectorized and printed matrix
--   form `|C~ - R Z^ + Z^ S| <= (1+rho) gamma_{nm+9} (|R||Z^| + |Z^||S|)`.
--
-- Honest scope:
-- * Schur factors are SUPPLIED, as in the printed setting and in Wave 14;
--   errors in computing the real Schur decompositions or the transformed
--   right-hand side belong to (16.9) and are not modeled here.
-- * The 2 x 2 blocks are solved by GE WITHOUT pivoting.  The hypotheses are
--   the honest certificates that this elimination runs to completion: the
--   block's (1,1) entry (first pivot) is nonzero and the COMPUTED second
--   pivot is nonzero.  This matches the Chapter 9 convention (Theorems
--   9.3-9.4 assume the elimination produces nonzero computed pivots).  A
--   partial-pivoting kernel is not modeled.
-- * GE is not componentwise backward stable relative to `|M|` alone: the
--   unconditional bound carries the explicit elimination fill-in
--   `|c||b|/|a|` in the (2,2) block position (the `|L||U|` budget of
--   Theorem 9.3).  The fully componentwise `(16.7)`-shaped statements
--   therefore take the standard per-block growth certificate
--   `|c||b| <= rho |a||d|` as an explicit hypothesis; nothing is smuggled.
-- * The printed unspecified constant `c_{m,n} u` is realized as the
--   explicit same-gamma-class envelope `gamma_{nm+9}` (Chapter 8 fold
--   accumulation on at most `nm` terms composed with the 9-operation
--   2 x 2 kernel envelope `gamma_9`).  We do not claim the printed letter
--   constant.
-- * Only the mixed case "R quasi-triangular, S strictly triangular" is
--   instantiated: under the Wave-14 column-major elimination order the
--   2 x 2 blocks of `R` couple ADJACENT ranks inside one column of the
--   unknown, which is exactly the engine's adjacent-block shape.  A 2 x 2
--   block of `S` couples the two unknown COLUMNS k, k+1 at rank distance
--   `m` (non-adjacent), so the fully quasi-quasi case needs the interleaved
--   two-column ordering with diagonal blocks of size up to 4 (the exact
--   two-column block algebra is `sylvesterTwoColumnBlockCoeff` in
--   `Higham16Spectrum`); no rounded kernel for those blocks exists yet, and
--   that remaining case is documented as open, not asserted.



namespace NumStability

namespace Wave15

open scoped BigOperators

-- ============================================================
-- Gamma-arithmetic helpers (Higham Lemma 3.3 consequences)
-- ============================================================

/-- Higham, 2nd ed., Chapter 3.4, Lemma 3.3: subadditivity consequence
    `gamma_j + gamma_k <= gamma_{j+k}` of the gamma-term product rule.  This
    is the additive part of the identity
    `gamma_j + gamma_k + gamma_j gamma_k <= gamma_{j+k}` underlying
    Lemma 3.3. -/
theorem gamma_add_le (fp : FPModel) (j k : Nat)
    (hval : gammaValid fp (j + k)) :
    gamma fp j + gamma fp k ≤ gamma fp (j + k) := by
  have hj : gammaValid fp j := gammaValid_mono fp (Nat.le_add_right j k) hval
  have hk : gammaValid fp k := gammaValid_mono fp (Nat.le_add_left k j) hval
  have hjnn := gamma_nonneg fp hj
  have hknn := gamma_nonneg fp hk
  obtain ⟨θ, hθ, heq⟩ := gamma_mul fp j k (gamma fp j) (gamma fp k)
    (by rw [abs_of_nonneg hjnn]) (by rw [abs_of_nonneg hknn]) hval
  have hθval : θ = gamma fp j + gamma fp k + gamma fp j * gamma fp k := by
    nlinarith [heq]
  have hle := le_abs_self θ
  nlinarith [mul_nonneg hjnn hknn]

/-- Higham, 2nd ed., Chapter 3.4, Lemma 3.3: one-sided product absorption
    `(1 + gamma_j) * gamma_k <= gamma_{j+k}`. -/
theorem one_add_gamma_mul_gamma_le (fp : FPModel) (j k : Nat)
    (hval : gammaValid fp (j + k)) :
    (1 + gamma fp j) * gamma fp k ≤ gamma fp (j + k) := by
  have hj : gammaValid fp j := gammaValid_mono fp (Nat.le_add_right j k) hval
  have hk : gammaValid fp k := gammaValid_mono fp (Nat.le_add_left k j) hval
  have hjnn := gamma_nonneg fp hj
  have hknn := gamma_nonneg fp hk
  obtain ⟨θ, hθ, heq⟩ := gamma_mul fp j k (gamma fp j) (gamma fp k)
    (by rw [abs_of_nonneg hjnn]) (by rw [abs_of_nonneg hknn]) hval
  have hθval : θ = gamma fp j + gamma fp k + gamma fp j * gamma fp k := by
    nlinarith [heq]
  have hle := le_abs_self θ
  nlinarith

/-- Higham, 2nd ed., Chapter 3.4, Lemma 3.3: relative-perturbation
    composition.  If `|Delta| <= gamma_j * B`, `|base| <= B` and
    `|beta| <= gamma_k`, then `|(base + Delta)(1 + beta) - base|` is bounded
    by `gamma_{j+k} * B`.  This composes a local backward-error perturbation
    with the accumulated row-scaling factor of a substitution fold. -/
theorem abs_perturb_scale_sub_le (fp : FPModel) (j k : Nat)
    (base Δ β B : Real)
    (hΔ : |Δ| ≤ gamma fp j * B) (hbase : |base| ≤ B)
    (hβ : |β| ≤ gamma fp k)
    (hval : gammaValid fp (j + k)) :
    |(base + Δ) * (1 + β) - base| ≤ gamma fp (j + k) * B := by
  have hj : gammaValid fp j := gammaValid_mono fp (Nat.le_add_right j k) hval
  have hk : gammaValid fp k := gammaValid_mono fp (Nat.le_add_left k j) hval
  have hjnn := gamma_nonneg fp hj
  have hknn := gamma_nonneg fp hk
  have hBnn : 0 ≤ B := le_trans (abs_nonneg base) hbase
  have hexpand : (base + Δ) * (1 + β) - base = base * β + Δ * (1 + β) := by
    ring
  rw [hexpand]
  have h1 : |base * β| ≤ B * gamma fp k := by
    rw [abs_mul]
    exact mul_le_mul hbase hβ (abs_nonneg β) hBnn
  have h2 : |Δ * (1 + β)| ≤ gamma fp j * B * (1 + gamma fp k) := by
    rw [abs_mul]
    have hb1 : |1 + β| ≤ 1 + gamma fp k := by
      calc |1 + β| ≤ |(1 : Real)| + |β| := abs_add_le 1 β
        _ = 1 + |β| := by rw [abs_one]
        _ ≤ 1 + gamma fp k := by linarith
    exact mul_le_mul hΔ hb1 (abs_nonneg _) (mul_nonneg hjnn hBnn)
  have hsum : gamma fp j + gamma fp k + gamma fp j * gamma fp k ≤
      gamma fp (j + k) := by
    obtain ⟨θ, hθ, heq⟩ := gamma_mul fp j k (gamma fp j) (gamma fp k)
      (by rw [abs_of_nonneg hjnn]) (by rw [abs_of_nonneg hknn]) hval
    have hθval : θ = gamma fp j + gamma fp k + gamma fp j * gamma fp k := by
      nlinarith [heq]
    have hle := le_abs_self θ
    linarith
  calc |base * β + Δ * (1 + β)| ≤ |base * β| + |Δ * (1 + β)| :=
        abs_add_le _ _
    _ ≤ B * gamma fp k + gamma fp j * B * (1 + gamma fp k) := by linarith
    _ = (gamma fp k + gamma fp j + gamma fp j * gamma fp k) * B := by ring
    _ ≤ gamma fp (j + k) * B := by
        apply mul_le_mul_of_nonneg_right _ hBnn
        linarith

-- ============================================================
-- (a) The rounded 2 x 2 linear-system kernel
-- ============================================================

/-- Higham, 2nd ed., Chapter 9.1 and Chapter 16.2, p. 308: the second
    (computed) pivot of two-step Gaussian elimination without pivoting on the
    2 x 2 system `[[a, b], [c, d]]`, namely `fl(d - fl(fl(c/a) * b))`.  The
    quasi-triangular Bartels-Stewart substitution (16.6) requires this
    quantity to be nonzero for the 2 x 2 diagonal-block solves to run to
    completion; this is the computed-pivot certificate in the sense of the
    Chapter 9 backward-error theorems, which assume the elimination
    completes. -/
noncomputable def flSolve2x2SecondPivot (fp : FPModel) (a b c d : Real) :
    Real :=
  fp.fl_sub d (fp.fl_mul (fp.fl_div c a) b)

/-- Higham, 2nd ed., Chapter 9.1 and Chapter 16.2, p. 308: the rounded
    2 x 2 linear-system solve `[[a, b], [c, d]] (x, y) = (p, q)` by two-step
    Gaussian elimination without pivoting, built from the `FPModel`
    primitives: multiplier `l = fl(c/a)`, eliminated pivot
    `w = fl(d - fl(l b))`, transformed right-hand side `t = fl(q - fl(l p))`,
    then back substitution `y = fl(t / w)`, `x = fl(fl(p - fl(b y)) / a)`.
    This is the kernel used by the quasi-triangular Bartels-Stewart
    substitution (16.6) for the 2 x 2 diagonal blocks of the real Schur
    form. -/
noncomputable def fl_solve2x2 (fp : FPModel) (a b c d p q : Real) :
    Real × Real :=
  (fp.fl_div
      (fp.fl_sub p (fp.fl_mul b
        (fp.fl_div (fp.fl_sub q (fp.fl_mul (fp.fl_div c a) p))
          (fp.fl_sub d (fp.fl_mul (fp.fl_div c a) b))))) a,
    fp.fl_div (fp.fl_sub q (fp.fl_mul (fp.fl_div c a) p))
      (fp.fl_sub d (fp.fl_mul (fp.fl_div c a) b)))

































































































































































































































































































































































-- ============================================================
-- (b) The rounded quasi-triangular block back substitution
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, p. 308: well-formed adjacent-pair marking
    of the 1 x 1 / 2 x 2 diagonal-block structure of a quasi-triangular
    system.  `dbl r = true` marks row `r` as the TOP row of a 2 x 2 diagonal
    block occupying rows `r, r+1`; well-formedness demands that the partner
    row exists and that blocks do not overlap. -/
def IsQuasiBlockPairing (N : Nat) (dbl : Fin N → Bool) : Prop :=
  (∀ r : Fin N, dbl r = true → r.val + 1 < N) ∧
    (∀ r s : Fin N, s.val = r.val + 1 → dbl r = true → dbl s = false)

/-- Higham, 2nd ed., Chapter 8.1 and Chapter 16.2, equation (16.6): the
    inner subtraction fold of one substitution row.  Starting from the
    right-hand side `bb r`, the already-computed entries `x j` for columns
    `j > e` (where `e` is the last column of row `r`'s diagonal block) are
    folded off with rounded multiply and subtract, exactly as in Chapter 8
    Algorithm 8.1. -/
noncomputable def quasiRowFold (fp : FPModel) (N : Nat)
    (T : Fin N → Fin N → Real) (bb : Fin N → Real)
    (x : Fin N → Real) (r : Fin N) (e : Nat) : Real :=
  Fin.foldl (N - e - 1)
    (fun acc t => fp.fl_sub acc
      (fp.fl_mul (T r ⟨e + 1 + t.val, by omega⟩) (x ⟨e + 1 + t.val, by omega⟩)))
    (bb r)

/-- **Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), quasi-
    triangular block form**: the rounded block back substitution.  Rows are
    processed from the bottom up; a row marked as the bottom (resp. top) row
    of an adjacent 2 x 2 diagonal block is solved as the second (resp.
    first) component of the `fl_solve2x2` kernel applied to that block, with
    both block right-hand sides accumulated by the Chapter 8 rounded
    subtraction fold over the already-computed entries; an unmarked row is
    solved by a rounded division exactly as in Chapter 8 Algorithm 8.1
    (the Wave-14 strictly triangular model).  Both members of a 2 x 2 block
    invoke the same kernel value, so the pair is solved simultaneously, as
    in the printed Bartels-Stewart algorithm. -/
noncomputable def flQuasiBlockBackSub (fp : FPModel) (N : Nat)
    (dbl : Fin N → Bool) (T : Fin N → Fin N → Real) (bb : Fin N → Real)
    (r : Fin N) : Real :=
  if h2 : 0 < r.val ∧ dbl ⟨r.val - 1, by omega⟩ = true then
    (fl_solve2x2 fp
      (T ⟨r.val - 1, by omega⟩ ⟨r.val - 1, by omega⟩)
      (T ⟨r.val - 1, by omega⟩ r)
      (T r ⟨r.val - 1, by omega⟩) (T r r)
      (Fin.foldl (N - r.val - 1)
        (fun acc t => fp.fl_sub acc
          (fp.fl_mul (T ⟨r.val - 1, by omega⟩ ⟨r.val + 1 + t.val, by omega⟩)
            (flQuasiBlockBackSub fp N dbl T bb ⟨r.val + 1 + t.val, by omega⟩)))
        (bb ⟨r.val - 1, by omega⟩))
      (Fin.foldl (N - r.val - 1)
        (fun acc t => fp.fl_sub acc
          (fp.fl_mul (T r ⟨r.val + 1 + t.val, by omega⟩)
            (flQuasiBlockBackSub fp N dbl T bb ⟨r.val + 1 + t.val, by omega⟩)))
        (bb r))).2
  else if h1 : dbl r = true ∧ r.val + 1 < N then
    (fl_solve2x2 fp
      (T r r) (T r ⟨r.val + 1, h1.2⟩)
      (T ⟨r.val + 1, h1.2⟩ r) (T ⟨r.val + 1, h1.2⟩ ⟨r.val + 1, h1.2⟩)
      (Fin.foldl (N - (r.val + 1) - 1)
        (fun acc t => fp.fl_sub acc
          (fp.fl_mul (T r ⟨r.val + 1 + 1 + t.val, by omega⟩)
            (flQuasiBlockBackSub fp N dbl T bb ⟨r.val + 1 + 1 + t.val, by omega⟩)))
        (bb r))
      (Fin.foldl (N - (r.val + 1) - 1)
        (fun acc t => fp.fl_sub acc
          (fp.fl_mul (T ⟨r.val + 1, h1.2⟩ ⟨r.val + 1 + 1 + t.val, by omega⟩)
            (flQuasiBlockBackSub fp N dbl T bb ⟨r.val + 1 + 1 + t.val, by omega⟩)))
        (bb ⟨r.val + 1, h1.2⟩))).1
  else
    fp.fl_div
      (Fin.foldl (N - r.val - 1)
        (fun acc t => fp.fl_sub acc
          (fp.fl_mul (T r ⟨r.val + 1 + t.val, by omega⟩)
            (flQuasiBlockBackSub fp N dbl T bb ⟨r.val + 1 + t.val, by omega⟩)))
        (bb r))
      (T r r)
termination_by N - r.val
decreasing_by all_goals omega

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6): the shared
    `fl_solve2x2` kernel value of one marked 2 x 2 diagonal block with rows
    `K, K1` (where `K1.val = K.val + 1`): the coefficient block is the
    2 x 2 diagonal block of `T`, and the two right-hand sides are the
    Chapter 8 rounded subtraction folds of the two block rows over the
    already-computed entries in columns `> K1`. -/
noncomputable def flQuasiBlockKernel (fp : FPModel) (N : Nat)
    (dbl : Fin N → Bool) (T : Fin N → Fin N → Real) (bb : Fin N → Real)
    (K K1 : Fin N) : Real × Real :=
  fl_solve2x2 fp (T K K) (T K K1) (T K1 K) (T K1 K1)
    (quasiRowFold fp N T bb (flQuasiBlockBackSub fp N dbl T bb) K K1.val)
    (quasiRowFold fp N T bb (flQuasiBlockBackSub fp N dbl T bb) K1 K1.val)

/-- Unmarked (scalar) row: the computed entry is the Chapter 8 rounded
    division of the row fold by the diagonal entry, exactly the Wave-14 /
    Algorithm 8.1 step (Higham, 2nd ed., Chapter 16.2, equation (16.6)). -/
theorem flQuasiBlockBackSub_singleton (fp : FPModel) (N : Nat)
    (dbl : Fin N → Bool) (T : Fin N → Fin N → Real) (bb : Fin N → Real)
    (r : Fin N)
    (h2 : ¬(0 < r.val ∧ dbl ⟨r.val - 1, by omega⟩ = true))
    (h1 : ¬(dbl r = true ∧ r.val + 1 < N)) :
    flQuasiBlockBackSub fp N dbl T bb r =
      fp.fl_div
        (quasiRowFold fp N T bb (flQuasiBlockBackSub fp N dbl T bb) r r.val)
        (T r r) := by
  rw [flQuasiBlockBackSub]
  rw [dif_neg h2, dif_neg h1]
  rfl

/-- Top row of a marked 2 x 2 block: the computed entry is the first
    component of the shared block kernel (Higham, 2nd ed., Chapter 16.2,
    p. 308, equation (16.6)). -/
theorem flQuasiBlockBackSub_blockTop (fp : FPModel) (N : Nat)
    (dbl : Fin N → Bool) (T : Fin N → Fin N → Real) (bb : Fin N → Real)
    (r : Fin N)
    (h2 : ¬(0 < r.val ∧ dbl ⟨r.val - 1, by omega⟩ = true))
    (h1 : dbl r = true ∧ r.val + 1 < N) :
    flQuasiBlockBackSub fp N dbl T bb r =
      (flQuasiBlockKernel fp N dbl T bb r ⟨r.val + 1, h1.2⟩).1 := by
  rw [flQuasiBlockBackSub]
  rw [dif_neg h2, dif_pos h1]
  rfl

/-- Bottom row of a marked 2 x 2 block: the computed entry is the second
    component of the shared block kernel (Higham, 2nd ed., Chapter 16.2,
    p. 308, equation (16.6)). -/
theorem flQuasiBlockBackSub_blockBottom (fp : FPModel) (N : Nat)
    (dbl : Fin N → Bool) (T : Fin N → Fin N → Real) (bb : Fin N → Real)
    (r : Fin N)
    (h2 : 0 < r.val ∧ dbl ⟨r.val - 1, by omega⟩ = true) :
    flQuasiBlockBackSub fp N dbl T bb r =
      (flQuasiBlockKernel fp N dbl T bb ⟨r.val - 1, by omega⟩ r).2 := by
  rw [flQuasiBlockBackSub]
  rw [dif_pos h2]
  rfl

-- ============================================================
-- Tight analysis of one substitution row fold
-- ============================================================

/-- Reindexing bridge between the offset-`Fin` fold enumeration of the
    columns strictly beyond a block and the corresponding filtered sum over
    the ambient index type (Higham, 2nd ed., Chapter 8.1, Algorithm 8.1
    bookkeeping). -/
theorem sum_offset_eq_sum_filter {N : Nat} (e : Nat) (heN : e < N)
    (f : Fin N → Real) :
    (∑ t : Fin (N - e - 1), f ⟨e + 1 + t.val, by omega⟩) =
      ∑ j ∈ Finset.filter (fun j : Fin N => e < j.val) Finset.univ, f j := by
  have hinj : ∀ a : Fin (N - e - 1), a ∈ Finset.univ →
      ∀ b : Fin (N - e - 1), b ∈ Finset.univ →
      (⟨e + 1 + a.val, by omega⟩ : Fin N) = ⟨e + 1 + b.val, by omega⟩ →
        a = b :=
    fun a _ b _ hab => Fin.ext (by simp only [Fin.mk.injEq] at hab; omega)
  have himg : Finset.image
      (fun (t : Fin (N - e - 1)) => (⟨e + 1 + t.val, by omega⟩ : Fin N))
      Finset.univ = Finset.filter (fun j : Fin N => e < j.val) Finset.univ := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩
      simp
      omega
    · intro hj
      exact ⟨⟨j.val - (e + 1), by omega⟩, Fin.ext (by simp; omega)⟩
  rw [← himg, Finset.sum_image hinj]

/-- **Higham, 2nd ed., Chapter 8.1, Lemma 8.2 fold analysis** (tight form,
    one substitution row of the quasi-triangular sweep).  The rounded
    subtraction fold of row `r` over the columns strictly beyond position
    `e` equals

    `(bb r - sum_{j > e} T r j * x j * (1 + φ_j)) * P`

    for a positive accumulated product `P` with exact inverse `1 + β`,
    `|β| <= gamma_{N-e-1}`, and per-column factors
    `|φ_j| <= gamma_{j-e}`.  This is the Wave-14 / Chapter 8 row analysis
    with the row-scaling product exposed, so that the perturbations can be
    pushed onto the coefficients of a subsequent scalar OR 2 x 2 block
    solve. -/
theorem quasiRowFold_tight (fp : FPModel) (N : Nat)
    (T : Fin N → Fin N → Real) (bb : Fin N → Real) (x : Fin N → Real)
    (r : Fin N) (e : Nat) (heN : e < N)
    (hu : fp.u < 1) (hgv : gammaValid fp (N - e - 1)) :
    ∃ (P β : Real) (φ : Fin N → Real),
      0 < P ∧ (1 + β) * P = 1 ∧ |β| ≤ gamma fp (N - e - 1) ∧
      (∀ j : Fin N, e < j.val → |φ j| ≤ gamma fp (j.val - e)) ∧
      quasiRowFold fp N T bb x r e =
        (bb r - ∑ j ∈ Finset.filter (fun j : Fin N => e < j.val) Finset.univ,
            T r j * x j * (1 + φ j)) * P := by
  set M := N - e - 1 with hM
  let idx : Fin M → Fin N := fun t => ⟨e + 1 + t.val, by omega⟩
  let a_vals : Fin M → Real := fun t => fp.fl_mul (T r (idx t)) (x (idx t))
  have hqf : quasiRowFold fp N T bb x r e =
      Fin.foldl M (fun acc t => fp.fl_sub acc (a_vals t)) (bb r) := rfl
  -- Unroll the fold with individual error tracking.
  obtain ⟨σ, hσ, hfold⟩ := fl_sub_fold_unroll fp M a_vals (bb r)
  -- Expand each rounded product.
  have hmul : ∀ t : Fin M, ∃ ε : Real, |ε| ≤ fp.u ∧
      a_vals t = T r (idx t) * x (idx t) * (1 + ε) :=
    fun t => fp.model_mul _ _
  let ε : Fin M → Real := fun t => Classical.choose (hmul t)
  have hε_bd : ∀ t, |ε t| ≤ fp.u := fun t => (Classical.choose_spec (hmul t)).1
  have hε_eq : ∀ t, a_vals t = T r (idx t) * x (idx t) * (1 + ε t) :=
    fun t => (Classical.choose_spec (hmul t)).2
  -- The accumulated product and its exact inverse.
  set P := ∏ k : Fin M, (1 + σ k) with hP_def
  have hP_pos : (0 : Real) < P := prod_pos_of_u_bound fp M σ hσ hu
  obtain ⟨β, hβ, hβ_eq⟩ := inv_prod_error_bound fp M σ hσ hu hgv
  have hβP : (1 + β) * P = 1 := by
    rw [← hβ_eq, hP_def, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro k _
    have hk_pos : (0 : Real) < 1 + σ k := by
      linarith [neg_abs_le (σ k), hσ k]
    field_simp
  -- Product split into head and tail at position t.
  have hP_split : ∀ t : Fin M,
      P = (∏ k : Fin M, if k.val < t.val then (1 + σ k) else 1) *
          (∏ k : Fin M, if t.val ≤ k.val then (1 + σ k) else 1) := by
    intro t
    rw [hP_def, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    by_cases h : k.val < t.val
    · simp [h, show ¬(t.val ≤ k.val) from by omega]
    · simp [h, show t.val ≤ k.val from by omega]
  -- Per-term coefficient factor.
  have hoff : ∀ t : Fin M,
      ∃ η : Real, |η| ≤ gamma fp (t.val + 1) ∧
        a_vals t * (∏ k : Fin M, if t.val ≤ k.val then (1 + σ k) else 1) =
        T r (idx t) * x (idx t) * (1 + η) * P := by
    intro t
    let σ_head : Fin t.val → Real := fun j => σ ⟨j.val, by omega⟩
    have hσ_head : ∀ k, |σ_head k| ≤ fp.u := fun k => hσ ⟨k.val, by omega⟩
    have ht_valid : gammaValid fp t.val :=
      gammaValid_mono fp (by omega) hgv
    obtain ⟨α, hα, hα_eq⟩ :=
      inv_prod_error_bound fp t.val σ_head hσ_head hu ht_valid
    have hHP_eq : (∏ k : Fin M, if k.val < t.val then (1 + σ k) else 1) =
        ∏ j : Fin t.val, (1 + σ_head j) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun k : Fin M => k.val < t.val)]
      have hrest : ∏ k ∈ Finset.filter
          (fun k : Fin M => ¬(k.val < t.val)) Finset.univ,
          (if k.val < t.val then (1 + σ k) else 1) = 1 := by
        apply Finset.prod_eq_one
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp [hk]
      rw [hrest, mul_one]
      have hS_eq : ∏ k ∈ Finset.filter
          (fun k : Fin M => k.val < t.val) Finset.univ,
          (if k.val < t.val then (1 + σ k) else 1) =
        ∏ k ∈ Finset.filter (fun k : Fin M => k.val < t.val) Finset.univ,
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
        (∏ k : Fin M, if k.val < t.val then (1 + σ k) else 1) = 1 := by
      rw [hHP_eq, ← hα_eq, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro k _
      have hk_pos : (0 : Real) < 1 + σ_head k := by
        linarith [neg_abs_le (σ_head k), hσ_head k]
      field_simp
    have hε_γ1 : |ε t| ≤ gamma fp 1 :=
      le_trans (hε_bd t)
        (u_le_gamma fp one_pos
          (gammaValid_mono fp (by have := t.isLt; omega) hgv))
    obtain ⟨η, hη, hη_eq⟩ := gamma_mul fp 1 t.val (ε t) α hε_γ1 hα
      (gammaValid_mono fp (by have := t.isLt; omega) hgv)
    have hη_exact : |η| ≤ gamma fp (t.val + 1) := by
      simpa [Nat.add_comm] using hη
    refine ⟨η, hη_exact, ?_⟩
    have hTP_eq : (1 + α) * P =
        ∏ k : Fin M, if t.val ≤ k.val then (1 + σ k) else 1 := by
      calc (1 + α) * P
          = (1 + α) *
              ((∏ k : Fin M, if k.val < t.val then (1 + σ k) else 1) *
                (∏ k : Fin M, if t.val ≤ k.val then (1 + σ k) else 1)) := by
            rw [← hP_split t]
        _ = ((1 + α) *
              (∏ k : Fin M, if k.val < t.val then (1 + σ k) else 1)) *
              (∏ k : Fin M, if t.val ≤ k.val then (1 + σ k) else 1) := by
            ring
        _ = 1 * (∏ k : Fin M, if t.val ≤ k.val then (1 + σ k) else 1) := by
            rw [hα_cancel]
        _ = ∏ k : Fin M, if t.val ≤ k.val then (1 + σ k) else 1 :=
            one_mul _
    rw [hε_eq t, ← hTP_eq, ← hη_eq]
    ring
  -- Extract all per-term witnesses.
  let η_vals : Fin M → Real := fun t => Classical.choose (hoff t)
  have hη_bd : ∀ t, |η_vals t| ≤ gamma fp (t.val + 1) := fun t =>
    (Classical.choose_spec (hoff t)).1
  have hη_eq : ∀ t,
      a_vals t * (∏ k : Fin M, if t.val ≤ k.val then (1 + σ k) else 1) =
      T r (idx t) * x (idx t) * (1 + η_vals t) * P := fun t =>
    (Classical.choose_spec (hoff t)).2
  -- Assemble the column-factor function.
  let φ : Fin N → Real := fun j =>
    if h : e < j.val then η_vals ⟨j.val - (e + 1), by omega⟩ else 0
  refine ⟨P, β, φ, hP_pos, hβP, hβ, ?_, ?_⟩
  · intro j hj
    simp only [φ, hj, dite_true]
    have ht : j.val - (e + 1) + 1 = j.val - e := by omega
    simpa [ht] using hη_bd ⟨j.val - (e + 1), by omega⟩
  · rw [hqf, hfold]
    have hsum_rw : (∑ t : Fin M, a_vals t *
        ∏ k : Fin M, if t.val ≤ k.val then (1 + σ k) else 1) =
        (∑ t : Fin M, T r (idx t) * x (idx t) * (1 + φ (idx t))) * P := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      rw [hη_eq t]
      have hφ_idx : φ (idx t) = η_vals t := by
        simp only [φ, idx]
        rw [dif_pos (by omega : e < e + 1 + t.val)]
        congr 1
        exact Fin.ext (Nat.add_sub_cancel_left (e + 1) t.val)
      rw [hφ_idx]
    rw [hsum_rw]
    have hreidx : (∑ t : Fin M, T r (idx t) * x (idx t) * (1 + φ (idx t))) =
        ∑ j ∈ Finset.filter (fun j : Fin N => e < j.val) Finset.univ,
          T r j * x j * (1 + φ j) := by
      have := sum_offset_eq_sum_filter (N := N) e heN
        (fun j => T r j * x j * (1 + φ j))
      exact this
    rw [hreidx]
    ring

-- ============================================================
-- The per-block elimination fill-in budget
-- ============================================================

/-- Higham, 2nd ed., Chapter 9.3, Theorem 9.3, specialized as required by
    Chapter 16.2, p. 308: the elimination fill-in term of the entrywise
    backward-error budget.  It is nonzero only at the bottom-right position
    `(r, r)` of a marked 2 x 2 diagonal block, where it equals the `n = 2`
    GE fill-in `|c||b|/|a|` of that block (in block coordinates
    `[[a, b], [c, a']]` with `a = T (r-1) (r-1)`, `b = T (r-1) r`,
    `c = T r (r-1)`). -/
noncomputable def quasiGrowthTerm (N : Nat) (dbl : Fin N → Bool)
    (T : Fin N → Fin N → Real) (r c : Fin N) : Real :=
  if 0 < r.val ∧ dbl ⟨r.val - 1, by omega⟩ = true ∧ c = r then
    |T r ⟨r.val - 1, by omega⟩| * |T ⟨r.val - 1, by omega⟩ r| /
      |T ⟨r.val - 1, by omega⟩ ⟨r.val - 1, by omega⟩|
  else 0

/-- The elimination fill-in budget term is nonnegative. -/
theorem quasiGrowthTerm_nonneg (N : Nat) (dbl : Fin N → Bool)
    (T : Fin N → Fin N → Real) (r c : Fin N) :
    0 ≤ quasiGrowthTerm N dbl T r c := by
  unfold quasiGrowthTerm
  split
  · exact div_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  · exact le_refl 0

/-- Value of the fill-in budget at the bottom-right position of a marked
    2 x 2 block (Higham, 2nd ed., Chapter 9.3, Theorem 9.3 for `n = 2`). -/
theorem quasiGrowthTerm_block (N : Nat) (dbl : Fin N → Bool)
    (T : Fin N → Fin N → Real) (K K1 : Fin N)
    (hK1 : K1.val = K.val + 1) (hdK : dbl K = true) :
    quasiGrowthTerm N dbl T K1 K1 =
      |T K1 K| * |T K K1| / |T K K| := by
  unfold quasiGrowthTerm
  have h0 : 0 < K1.val := by omega
  have hmk : (⟨K1.val - 1, by omega⟩ : Fin N) = K :=
    Fin.ext (show K1.val - 1 = K.val by omega)
  rw [if_pos ⟨h0, by rw [hmk]; exact hdK, rfl⟩, hmk]

-- ============================================================
-- Sum-splitting bookkeeping for the row equations
-- ============================================================

/-- Split a full-row sum at a scalar diagonal position, dropping the
    vanishing below-diagonal terms (Chapter 8 Algorithm 8.1 bookkeeping). -/
theorem sum_split_singleton {N : Nat} (f : Fin N → Real) (r : Fin N)
    (hbelow : ∀ c : Fin N, c.val < r.val → f c = 0) :
    (∑ c : Fin N, f c) =
      f r + ∑ c ∈ Finset.filter (fun c : Fin N => r.val < c.val)
        Finset.univ, f c := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun c : Fin N => r.val ≤ c.val)]
  have hnot : (∑ c ∈ Finset.filter (fun c : Fin N => ¬(r.val ≤ c.val))
      Finset.univ, f c) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hc
    exact hbelow c hc
  rw [hnot, add_zero]
  have hmem : r ∈ Finset.filter (fun c : Fin N => r.val ≤ c.val)
      Finset.univ := by
    simp
  rw [← Finset.add_sum_erase _ f hmem]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext c
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
    ne_eq]
  constructor
  · rintro ⟨hne, hle⟩
    have : c.val ≠ r.val := fun h => hne (Fin.ext h)
    omega
  · intro hlt
    exact ⟨fun h => by omega, by omega⟩

/-- Split a full-row sum at a marked 2 x 2 diagonal block, dropping the
    vanishing below-block terms (Chapter 16.2 block-substitution
    bookkeeping). -/
theorem sum_split_block {N : Nat} (f : Fin N → Real) (K K1 : Fin N)
    (hK1 : K1.val = K.val + 1)
    (hbelow : ∀ c : Fin N, c.val < K.val → f c = 0) :
    (∑ c : Fin N, f c) =
      f K + f K1 + ∑ c ∈ Finset.filter (fun c : Fin N => K1.val < c.val)
        Finset.univ, f c := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun c : Fin N => K.val ≤ c.val)]
  have hnot : (∑ c ∈ Finset.filter (fun c : Fin N => ¬(K.val ≤ c.val))
      Finset.univ, f c) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hc
    exact hbelow c hc
  rw [hnot, add_zero]
  have hmemK : K ∈ Finset.filter (fun c : Fin N => K.val ≤ c.val)
      Finset.univ := by
    simp
  rw [← Finset.add_sum_erase _ f hmemK]
  have hmemK1 : K1 ∈ (Finset.filter (fun c : Fin N => K.val ≤ c.val)
      Finset.univ).erase K := by
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
      ne_eq]
    exact ⟨fun h => by rw [h] at hK1; omega, by omega⟩
  rw [← Finset.add_sum_erase _ f hmemK1]
  have hset : ((Finset.filter (fun c : Fin N => K.val ≤ c.val)
      Finset.univ).erase K).erase K1 =
      Finset.filter (fun c : Fin N => K1.val < c.val) Finset.univ := by
    ext c
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
      ne_eq]
    constructor
    · rintro ⟨hneK1, hneK, hle⟩
      have h1 : c.val ≠ K.val := fun h => hneK (Fin.ext h)
      have h2 : c.val ≠ K1.val := fun h => hneK1 (Fin.ext h)
      omega
    · intro hlt
      exact ⟨fun h => by omega, fun h => by omega, by omega⟩
  rw [hset]
  ring

-- ============================================================
-- Per-row backward-error equations
-- ============================================================

/-- **Higham, 2nd ed., Chapter 8.1, Theorem 8.5 row analysis, as used by
    Chapter 16.2, equation (16.7)** (scalar row of the quasi-triangular
    sweep).  An unmarked row `r` of the computed block back substitution
    satisfies the exactly perturbed row equation
    `sum_c (T r c + E c) x^_c = bb r` with
    `|E c| <= gamma_{N+9} (|T r c| + fill-in)`, the fill-in term being zero
    on scalar rows.  Below-block coefficients are zero by the quasi-
    triangular zero pattern, so the whole row participates. -/
theorem flQuasiBlockBackSub_row_singleton (fp : FPModel) (N : Nat)
    (dbl : Fin N → Bool) (T : Fin N → Fin N → Real) (bb : Fin N → Real)
    (r : Fin N)
    (h2 : ¬(0 < r.val ∧ dbl ⟨r.val - 1, by omega⟩ = true))
    (h1 : ¬(dbl r = true ∧ r.val + 1 < N))
    (hz2 : ∀ a c : Fin N, c.val + 1 < a.val → T a c = 0)
    (hz1 : ∀ a c : Fin N, c.val + 1 = a.val → dbl c = false → T a c = 0)
    (hTrr : T r r ≠ 0) (hgv : gammaValid fp (N + 9)) :
    ∃ E : Fin N → Real,
      (∀ c : Fin N, |E c| ≤ gamma fp (N + 9) *
        (|T r c| + quasiGrowthTerm N dbl T r c)) ∧
      (∑ c : Fin N,
        (T r c + E c) * flQuasiBlockBackSub fp N dbl T bb c) = bb r := by
  have hu1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hgv
  have hu : fp.u < 1 := by
    have h := hu1
    unfold gammaValid at h
    simpa using h
  have hγnn : 0 ≤ gamma fp (N + 9) := gamma_nonneg fp hgv
  have heN : r.val < N := r.isLt
  obtain ⟨P, β, φ, hP_pos, hβP, hβ, hφ, hfold⟩ :=
    quasiRowFold_tight fp N T bb (flQuasiBlockBackSub fp N dbl T bb) r r.val
      heN hu (gammaValid_mono fp (by omega) hgv)
  have hx := flQuasiBlockBackSub_singleton fp N dbl T bb r h2 h1
  obtain ⟨δd, hδd, hdiv⟩ := fp.model_div
    (quasiRowFold fp N T bb (flQuasiBlockBackSub fp N dbl T bb) r r.val)
    (T r r) hTrr
  have hδd_pos : (0 : Real) < 1 + δd := by linarith [neg_abs_le δd]
  have hTx : T r r * flQuasiBlockBackSub fp N dbl T bb r =
      quasiRowFold fp N T bb (flQuasiBlockBackSub fp N dbl T bb) r r.val *
        (1 + δd) := by
    rw [hx, hdiv]
    field_simp
  obtain ⟨φd, hφd, hφd_eq⟩ := gamma_div fp (N - r.val - 1) 1 β δd hβ
    (le_trans hδd (u_le_gamma fp one_pos hu1)) hδd_pos
    (gammaValid_mono fp (by omega) hgv)
  have hTeq : T r r * flQuasiBlockBackSub fp N dbl T bb r =
      (bb r - ∑ c ∈ Finset.filter (fun c : Fin N => r.val < c.val)
          Finset.univ,
          T r c * flQuasiBlockBackSub fp N dbl T bb c * (1 + φ c)) *
        (P * (1 + δd)) := by
    rw [hTx, hfold]
    ring
  have hφd_mul : (1 : Real) + β = (1 + φd) * (1 + δd) := by
    have h := hφd_eq
    rw [div_eq_iff (ne_of_gt hδd_pos)] at h
    exact h
  have hcancel : (1 + φd) * (P * (1 + δd)) = 1 := by
    calc (1 + φd) * (P * (1 + δd)) = ((1 + φd) * (1 + δd)) * P := by ring
      _ = (1 + β) * P := by rw [← hφd_mul]
      _ = 1 := hβP
  have hmain : bb r =
      T r r * (1 + φd) * flQuasiBlockBackSub fp N dbl T bb r +
        ∑ c ∈ Finset.filter (fun c : Fin N => r.val < c.val) Finset.univ,
          T r c * flQuasiBlockBackSub fp N dbl T bb c * (1 + φ c) := by
    have h3 : bb r -
        (∑ c ∈ Finset.filter (fun c : Fin N => r.val < c.val) Finset.univ,
          T r c * flQuasiBlockBackSub fp N dbl T bb c * (1 + φ c)) =
        T r r * flQuasiBlockBackSub fp N dbl T bb r * (1 + φd) := by
      calc bb r - (∑ c ∈ Finset.filter (fun c : Fin N => r.val < c.val)
              Finset.univ,
              T r c * flQuasiBlockBackSub fp N dbl T bb c * (1 + φ c))
          = (bb r - ∑ c ∈ Finset.filter (fun c : Fin N => r.val < c.val)
              Finset.univ,
              T r c * flQuasiBlockBackSub fp N dbl T bb c * (1 + φ c)) *
              ((1 + φd) * (P * (1 + δd))) := by
            rw [hcancel, mul_one]
        _ = ((bb r - ∑ c ∈ Finset.filter (fun c : Fin N => r.val < c.val)
              Finset.univ,
              T r c * flQuasiBlockBackSub fp N dbl T bb c * (1 + φ c)) *
              (P * (1 + δd))) * (1 + φd) := by
            ring
        _ = T r r * flQuasiBlockBackSub fp N dbl T bb r * (1 + φd) := by
            rw [← hTeq]
    linear_combination h3
  -- The row perturbation.
  refine ⟨fun c =>
    if c = r then T r r * φd
    else if r.val < c.val then T r c * φ c else 0, ?_, ?_⟩
  · intro c
    simp only []
    by_cases hc : c = r
    · subst hc
      rw [if_pos rfl, abs_mul]
      calc |T c c| * |φd|
          ≤ |T c c| * gamma fp (N - c.val - 1 + 2 * 1) :=
            mul_le_mul_of_nonneg_left hφd (abs_nonneg _)
        _ ≤ |T c c| * gamma fp (N + 9) :=
            mul_le_mul_of_nonneg_left
              (gamma_mono fp (by omega) hgv) (abs_nonneg _)
        _ ≤ gamma fp (N + 9) * (|T c c| + quasiGrowthTerm N dbl T c c) := by
            rw [mul_comm (|T c c|)]
            exact mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right (quasiGrowthTerm_nonneg N dbl T c c))
              hγnn
    · rw [if_neg hc]
      by_cases hc2 : r.val < c.val
      · rw [if_pos hc2, abs_mul]
        calc |T r c| * |φ c|
            ≤ |T r c| * gamma fp (c.val - r.val) :=
              mul_le_mul_of_nonneg_left (hφ c hc2) (abs_nonneg _)
          _ ≤ |T r c| * gamma fp (N + 9) :=
              mul_le_mul_of_nonneg_left
                (gamma_mono fp (by omega) hgv) (abs_nonneg _)
          _ ≤ gamma fp (N + 9) * (|T r c| + quasiGrowthTerm N dbl T r c) := by
              rw [mul_comm (|T r c|)]
              exact mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_right (quasiGrowthTerm_nonneg N dbl T r c))
                hγnn
      · rw [if_neg hc2, abs_zero]
        exact mul_nonneg hγnn
          (add_nonneg (abs_nonneg _) (quasiGrowthTerm_nonneg N dbl T r c))
  · -- The row equation.
    simp only []
    have hbelow : ∀ c : Fin N, c.val < r.val →
        (T r c + (if c = r then T r r * φd
          else if r.val < c.val then T r c * φ c else 0)) *
          flQuasiBlockBackSub fp N dbl T bb c = 0 := by
      intro c hlt
      have hTz : T r c = 0 := by
        by_cases hcc : c.val + 1 < r.val
        · exact hz2 r c hcc
        · have hceq : c.val + 1 = r.val := by omega
          apply hz1 r c hceq
          have h0 : 0 < r.val := by omega
          rcases Bool.eq_false_or_eq_true (dbl ⟨r.val - 1, by omega⟩) with
            hb | hb
          · exact absurd ⟨h0, hb⟩ h2
          · have hcr : c = ⟨r.val - 1, by omega⟩ :=
              Fin.ext (show c.val = r.val - 1 by omega)
            rw [hcr]
            exact hb
      have hne : ¬(c = r) := fun h => by
        rw [h] at hlt
        exact lt_irrefl _ hlt
      rw [hTz, if_neg hne, if_neg (by omega : ¬(r.val < c.val))]
      ring
    rw [sum_split_singleton _ r hbelow]
    have hdiag : (T r r + (if r = r then T r r * φd
        else if r.val < r.val then T r r * φ r else 0)) *
        flQuasiBlockBackSub fp N dbl T bb r =
        T r r * (1 + φd) * flQuasiBlockBackSub fp N dbl T bb r := by
      rw [if_pos rfl]
      ring
    rw [hdiag]
    have hoffsum : (∑ c ∈ Finset.filter (fun c : Fin N => r.val < c.val)
        Finset.univ,
        (T r c + (if c = r then T r r * φd
          else if r.val < c.val then T r c * φ c else 0)) *
          flQuasiBlockBackSub fp N dbl T bb c) =
        ∑ c ∈ Finset.filter (fun c : Fin N => r.val < c.val) Finset.univ,
          T r c * flQuasiBlockBackSub fp N dbl T bb c * (1 + φ c) := by
      apply Finset.sum_congr rfl
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      have hne : ¬(c = r) := fun h => by
        rw [h] at hc
        exact lt_irrefl _ hc
      rw [if_neg hne, if_pos hc]
      ring
    rw [hoffsum]
    linear_combination -hmain





























































































































































































































































































































































-- ============================================================
-- (b)/(c) Engine backward error: the block Theorem 8.5
-- ============================================================




















































































































































































































-- ============================================================
-- The Sylvester instantiation: quasi-triangular R, triangular S
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equation (16.4): the supplied
    quasi-upper-triangular zero pattern of a real Schur factor, relative to
    an adjacent-pair marking `dblR` of its 2 x 2 diagonal blocks: entries at
    least two below the diagonal vanish, and the first subdiagonal vanishes
    except inside marked blocks. -/
def IsQuasiUpperTriangularFn (m : Nat) (R : RMatFn m m)
    (dblR : Fin m → Bool) : Prop :=
  (∀ i j : Fin m, j.val + 1 < i.val → R i j = 0) ∧
    (∀ i j : Fin m, j.val + 1 = i.val → dblR j = false → R i j = 0)

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.6)-(16.7):
    the 2 x 2-block marking of the reordered vectorized system induced by
    the marking of the quasi-triangular left factor: the product index
    `(k, i)` is a block top exactly when row `i` of `R` is a marked block
    top with its partner inside the column. -/
def sylvesterQuasiPairing (m n : Nat) (dblR : Fin m → Bool) :
    Fin (n * m) → Bool :=
  fun a =>
    dblR ((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2 &&
      decide (((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2.val + 1 < m)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.7): within one
    column of the unknown, the Bartels-Stewart elimination rank of the next
    row up is the successor rank. -/
theorem sylvesterBackSubIndexEquiv_val_succ (m n : Nat) (k : Fin n)
    (i : Fin m) (h : i.val + 1 < m) :
    (Wave14.sylvesterBackSubIndexEquiv m n (k, ⟨i.val + 1, h⟩)).val =
      (Wave14.sylvesterBackSubIndexEquiv m n (k, i)).val + 1 := by
  rw [Wave14.sylvesterBackSubIndexEquiv_val,
    Wave14.sylvesterBackSubIndexEquiv_val]
  ring

/-- The induced product-index marking is a well-formed adjacent-pair
    marking whenever the factor marking is (Higham, 2nd ed., Chapter 16.2,
    equations (16.4)-(16.7)). -/
theorem sylvesterQuasiPairing_isQuasiBlockPairing (m n : Nat)
    (dblR : Fin m → Bool) (hRp : IsQuasiBlockPairing m dblR) :
    IsQuasiBlockPairing (n * m) (sylvesterQuasiPairing m n dblR) := by
  constructor
  · intro a ha
    unfold sylvesterQuasiPairing at ha
    rcases Bool.and_eq_true_iff.mp ha with ⟨_hd, hdec⟩
    have hq2 : ((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2.val + 1 <
        m := of_decide_eq_true hdec
    have hva : a.val =
        (Wave14.sylvesterBackSubIndexEquiv m n
          (((Wave14.sylvesterBackSubIndexEquiv m n).symm a).1,
            ((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2)).val := by
      rw [Prod.mk.eta, Equiv.apply_symm_apply]
    have hsucc := sylvesterBackSubIndexEquiv_val_succ m n
      ((Wave14.sylvesterBackSubIndexEquiv m n).symm a).1
      ((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2 hq2
    rw [← hva] at hsucc
    rw [← hsucc]
    exact (Wave14.sylvesterBackSubIndexEquiv m n
      (((Wave14.sylvesterBackSubIndexEquiv m n).symm a).1,
        ⟨((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2.val + 1,
          hq2⟩)).isLt
  · intro a s hs ha
    unfold sylvesterQuasiPairing at ha ⊢
    rcases Bool.and_eq_true_iff.mp ha with ⟨hd, hdec⟩
    have hq2 : ((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2.val + 1 <
        m := of_decide_eq_true hdec
    have hva : a.val =
        (Wave14.sylvesterBackSubIndexEquiv m n
          (((Wave14.sylvesterBackSubIndexEquiv m n).symm a).1,
            ((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2)).val := by
      rw [Prod.mk.eta, Equiv.apply_symm_apply]
    have hsucc := sylvesterBackSubIndexEquiv_val_succ m n
      ((Wave14.sylvesterBackSubIndexEquiv m n).symm a).1
      ((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2 hq2
    rw [← hva] at hsucc
    have hs_eq : Wave14.sylvesterBackSubIndexEquiv m n
        (((Wave14.sylvesterBackSubIndexEquiv m n).symm a).1,
          ⟨((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2.val + 1,
            hq2⟩) = s := Fin.ext (by rw [hsucc, hs])
    rw [← hs_eq, Equiv.symm_apply_apply]
    have hRfalse := hRp.2
      ((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2
      ⟨((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2.val + 1, hq2⟩
      rfl hd
    rw [hRfalse]
    rfl

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.7): the reordered
    vec/Kronecker coefficient of a quasi-triangular/triangular pair vanishes
    strictly below the marked block diagonal.  The single hypothesis on the
    excluded position carries both engine zero patterns. -/
theorem sylvesterQuasiSchurBackSubCoeff_eq_zero (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (dblR : Fin m → Bool)
    (hR : IsQuasiUpperTriangularFn m R dblR) (hS : IsUpperTriangularFn n S)
    (a b : Fin (n * m)) (hlt : b.val < a.val)
    (hexc : b.val + 1 = a.val → sylvesterQuasiPairing m n dblR b = false) :
    Wave14.sylvesterSchurBackSubCoeff m n R S a b = 0 := by
  unfold Wave14.sylvesterSchurBackSubCoeff
  rw [Wave14.sylvesterVecCoeff_pair_apply]
  have hva : a.val =
      ((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2.val +
        m * (n - (((Wave14.sylvesterBackSubIndexEquiv m n).symm a).1.val +
          1)) := by
    conv_lhs => rw [← Equiv.apply_symm_apply
      (Wave14.sylvesterBackSubIndexEquiv m n) a]
    rw [Wave14.sylvesterBackSubIndexEquiv_val]
  have hvb : b.val =
      ((Wave14.sylvesterBackSubIndexEquiv m n).symm b).2.val +
        m * (n - (((Wave14.sylvesterBackSubIndexEquiv m n).symm b).1.val +
          1)) := by
    conv_lhs => rw [← Equiv.apply_symm_apply
      (Wave14.sylvesterBackSubIndexEquiv m n) b]
    rw [Wave14.sylvesterBackSubIndexEquiv_val]
  set p := (Wave14.sylvesterBackSubIndexEquiv m n).symm a with hp_def
  set q := (Wave14.sylvesterBackSubIndexEquiv m n).symm b with hq_def
  by_cases hcol : p.1 = q.1
  · rw [if_pos hcol]
    have hprod : m * (n - (p.1.val + 1)) = m * (n - (q.1.val + 1)) := by
      rw [hcol]
    rw [hprod] at hva
    have hij : q.2.val < p.2.val := by omega
    have hne : ¬(p.2 = q.2) := fun h => by
      rw [h] at hij
      exact lt_irrefl _ hij
    rw [if_neg hne, sub_zero]
    by_cases hstep : q.2.val + 1 < p.2.val
    · exact hR.1 p.2 q.2 hstep
    · have hstep1 : q.2.val + 1 = p.2.val := by omega
      have hba : b.val + 1 = a.val := by omega
      have hdbl := hexc hba
      unfold sylvesterQuasiPairing at hdbl
      rw [← hq_def] at hdbl
      have hq2 : q.2.val + 1 < m := by
        have := p.2.isLt
        omega
      rw [decide_eq_true hq2, Bool.and_true] at hdbl
      exact hR.2 p.2 q.2 hstep1 hdbl
  · rw [if_neg hcol]
    by_cases hrow : p.2 = q.2
    · rw [if_pos hrow]
      have hval_eq : p.2.val = q.2.val := by rw [hrow]
      have hmul_lt : m * (n - (q.1.val + 1)) < m * (n - (p.1.val + 1)) := by
        omega
      have hcol_lt : n - (q.1.val + 1) < n - (p.1.val + 1) :=
        lt_of_mul_lt_mul_left hmul_lt (Nat.zero_le m)
      have hkq : p.1.val < q.1.val := by
        have h1 := p.1.isLt
        have h2 := q.1.isLt
        omega
      have hSz : S q.1 p.1 = 0 := hS q.1 p.1 (Fin.lt_def.mpr hkq)
      rw [hSz]
      ring
    · rw [if_neg hrow]
      ring

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2): same-column off-diagonal
    entry of the vec/Kronecker Sylvester coefficient. -/
theorem sylvesterVecCoeff_same_col_apply (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (k : Fin n) (i j : Fin m)
    (hne : ¬(i = j)) :
    sylvesterVecCoeff m n R S (k, i) (k, j) = R i j := by
  rw [Wave14.sylvesterVecCoeff_pair_apply]
  simp [hne]

/-- Decode a marked product-index block of the reordered system into its
    factor data: the column index, the two adjacent marked rows of `R`, and
    the four entries of the corresponding 2 x 2 diagonal block of the
    coefficient (Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.7)). -/
theorem sylvesterQuasiPairing_block_decode (m n : Nat)
    (dblR : Fin m → Bool) (R : RMatFn m m) (S : RMatFn n n)
    (a b' : Fin (n * m)) (hb' : b'.val = a.val + 1)
    (hd : sylvesterQuasiPairing m n dblR a = true) :
    ∃ (k : Fin n) (i i' : Fin m), i'.val = i.val + 1 ∧ dblR i = true ∧
      Wave14.sylvesterSchurBackSubCoeff m n R S a a = R i i - S k k ∧
      Wave14.sylvesterSchurBackSubCoeff m n R S a b' = R i i' ∧
      Wave14.sylvesterSchurBackSubCoeff m n R S b' a = R i' i ∧
      Wave14.sylvesterSchurBackSubCoeff m n R S b' b' = R i' i' - S k k := by
  unfold sylvesterQuasiPairing at hd
  rcases Bool.and_eq_true_iff.mp hd with ⟨hdR, hdec⟩
  set pa := (Wave14.sylvesterBackSubIndexEquiv m n).symm a with hpa_def
  have hq2 : pa.2.val + 1 < m := of_decide_eq_true hdec
  set isucc : Fin m := ⟨pa.2.val + 1, hq2⟩ with hisucc_def
  have hEa : Wave14.sylvesterBackSubIndexEquiv m n (pa.1, pa.2) = a := by
    rw [Prod.mk.eta]
    exact Equiv.apply_symm_apply _ a
  have hsucc := sylvesterBackSubIndexEquiv_val_succ m n pa.1 pa.2 hq2
  rw [hEa] at hsucc
  have hEb' : Wave14.sylvesterBackSubIndexEquiv m n (pa.1, isucc) = b' :=
    Fin.ext (by rw [hisucc_def, hsucc, hb'])
  have hsymmb' : (Wave14.sylvesterBackSubIndexEquiv m n).symm b' =
      (pa.1, isucc) := by
    rw [← hEb', Equiv.symm_apply_apply]
  have hne1 : ¬(pa.2 = isucc) := fun h => by
    have := congrArg Fin.val h
    rw [hisucc_def] at this
    simp at this
  have hne2 : ¬(isucc = pa.2) := fun h => hne1 h.symm
  refine ⟨pa.1, pa.2, isucc, rfl, hdR, ?_, ?_, ?_, ?_⟩
  · rw [Wave14.sylvesterSchurBackSubCoeff_diag]
  · show sylvesterVecCoeff m n R S
      ((Wave14.sylvesterBackSubIndexEquiv m n).symm a)
      ((Wave14.sylvesterBackSubIndexEquiv m n).symm b') = R pa.2 isucc
    rw [hsymmb']
    exact sylvesterVecCoeff_same_col_apply m n R S pa.1 pa.2 isucc hne1
  · show sylvesterVecCoeff m n R S
      ((Wave14.sylvesterBackSubIndexEquiv m n).symm b')
      ((Wave14.sylvesterBackSubIndexEquiv m n).symm a) = R isucc pa.2
    rw [hsymmb']
    exact sylvesterVecCoeff_same_col_apply m n R S pa.1 isucc pa.2 hne2
  · rw [Wave14.sylvesterSchurBackSubCoeff_diag, hsymmb']

/-- Transport of the non-bottom-row condition through the Bartels-Stewart
    index equivalence: if the product index is not the bottom row of a
    marked block, neither is its factor row (Higham, 2nd ed., Chapter 16.2,
    equations (16.6)-(16.7)). -/
theorem sylvesterQuasiPairing_notSecond_decode (m n : Nat)
    (dblR : Fin m → Bool) (a : Fin (n * m))
    (hnot : ¬(0 < a.val ∧
      sylvesterQuasiPairing m n dblR ⟨a.val - 1, by omega⟩ = true)) :
    ¬(0 < ((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2.val ∧
      dblR ⟨((Wave14.sylvesterBackSubIndexEquiv m n).symm a).2.val - 1,
        by omega⟩ = true) := by
  rintro ⟨h0, hd⟩
  apply hnot
  set pa := (Wave14.sylvesterBackSubIndexEquiv m n).symm a with hpa_def
  have hlt : pa.2.val - 1 < m := by
    have := pa.2.isLt
    omega
  set ipred : Fin m := ⟨pa.2.val - 1, hlt⟩ with hipred_def
  have hipredval : ipred.val = pa.2.val - 1 := rfl
  have hq2' : ipred.val + 1 < m := by
    have := pa.2.isLt
    omega
  have hsucc := sylvesterBackSubIndexEquiv_val_succ m n pa.1 ipred hq2'
  have hmk : (⟨ipred.val + 1, hq2'⟩ : Fin m) = pa.2 :=
    Fin.ext (show ipred.val + 1 = pa.2.val by omega)
  rw [hmk] at hsucc
  have hEa : Wave14.sylvesterBackSubIndexEquiv m n (pa.1, pa.2) = a := by
    rw [Prod.mk.eta]
    exact Equiv.apply_symm_apply _ a
  rw [hEa] at hsucc
  refine ⟨by omega, ?_⟩
  have hpred_eq : (⟨a.val - 1, by omega⟩ : Fin (n * m)) =
      Wave14.sylvesterBackSubIndexEquiv m n (pa.1, ipred) :=
    Fin.ext (show a.val - 1 =
      (Wave14.sylvesterBackSubIndexEquiv m n (pa.1, ipred)).val by omega)
  rw [hpred_eq]
  unfold sylvesterQuasiPairing
  rw [Equiv.symm_apply_apply]
  have hd2 : dblR ipred = true := hd
  show (dblR ipred && decide (ipred.val + 1 < m)) = true
  rw [hd2, decide_eq_true hq2']
  rfl

-- ============================================================
-- The computed quasi-triangular Bartels-Stewart solution
-- ============================================================

/-- **Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6)
    (quasi-triangular form)**: the computed vectorized solution of the
    Schur-form Sylvester system with quasi-triangular left factor, modeled
    as the rounded quasi-triangular block back substitution
    (`flQuasiBlockBackSub`) applied to the reordered `nm x nm` block
    triangular system: scalar rows by rounded division (Wave 14), marked
    2 x 2 diagonal blocks (the complex-conjugate eigenpair blocks of `R`,
    shifted by the active eigenvalue of `S`) by the `fl_solve2x2` GE
    kernel. -/
noncomputable def flSylvesterQuasiSchurBlockBackSubSolveVec (fp : FPModel)
    (m n : Nat) (dblR : Fin m → Bool) (R : RMatFn m m) (S : RMatFn n n)
    (Ct : RMatFn m n) : Prod (Fin n) (Fin m) → Real :=
  fun p =>
    flQuasiBlockBackSub fp (n * m) (sylvesterQuasiPairing m n dblR)
      (Wave14.sylvesterSchurBackSubCoeff m n R S)
      (Wave14.sylvesterSchurBackSubRhs m n Ct)
      (Wave14.sylvesterBackSubIndexEquiv m n p)

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6): the computed
    Schur-coordinate solution matrix, i.e. the un-vectorized form of
    `flSylvesterQuasiSchurBlockBackSubSolveVec`. -/
noncomputable def flSylvesterQuasiSchurBlockBackSubSolve (fp : FPModel)
    (m n : Nat) (dblR : Fin m → Bool) (R : RMatFn m m) (S : RMatFn n n)
    (Ct : RMatFn m n) : RMatFn m n :=
  fun i k => flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct
    (k, i)

/-- Column-stacking the computed Schur-coordinate solution matrix recovers
    the computed vectorized solution (Higham, 2nd ed., Chapter 16.2,
    equation (16.7) bookkeeping). -/
theorem vec_flSylvesterQuasiSchurBlockBackSubSolve (fp : FPModel)
    (m n : Nat) (dblR : Fin m → Bool) (R : RMatFn m m) (S : RMatFn n n)
    (Ct : RMatFn m n) :
    Matrix.vec (flSylvesterQuasiSchurBlockBackSubSolve fp m n dblR R S Ct) =
      flSylvesterQuasiSchurBlockBackSubSolveVec fp m n dblR R S Ct := rfl

end Wave15

end NumStability
