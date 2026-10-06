-- Analysis/SemiconvergentRealSpectrumComplete.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 17 "Stationary Iterative Methods", §17.4 "Singular Systems",
-- eq (17.22) / Householder `[106, Lem 6.9]`.
--
-- GOAL: CLOSE the fully-unconditional REAL-SPECTRUM `[106]`/(17.22) semiconvergent
-- block-form EXISTENCE from convergence of `Gᵐ` ALONE.
--
-- The prior wave (`SemiconvergentExistenceComplete.lean`) reduced the general
-- residual to exactly TWO concrete items, (3a) and (3b), and closed everything
-- downstream of them: it assembled the coordinate real primary (Fitting)
-- decomposition (`exists_real_primary_splitting_of_forall_orbit_tendsto`), the
-- adapted-basis coordinate bridge (`adaptedBasis`, `basisActionMatrix`), and the
-- master reduction
-- (`semiconvergent_block_form_exists_of_convergence_and_complement_normal_form`)
-- that CONSTRUCTS the ∞-norm contraction from a quasi-triangular block-contractive
-- complement action matrix.  Its closing STATUS block named the single remaining
-- IMPORT-level construction (NOT a mathematical gap) for the real-spectrum case:
-- the `basisActionMatrix ↔ LinearMap.toMatrix` reindex identity that lets the real
-- (quasi-)Schur reduction choose the complement basis automatically.
--
-- THIS MODULE supplies that identity and, for a real matrix `G` with real spectrum,
-- assembles the FULL `semiconvergent_block_form_exists` data package from
-- convergence of `Gᵐ` alone, with NO supplied basis / column / contraction data:
--
--   (A) `basisActionMatrix_complement_eq_toMatrix_restrict` — the reindex identity
--       (threading `repr_reindex_apply`, `prod_repr_inr`,
--       `prodEquivOfIsCompl_symm_apply_right` through the `adaptedBasis`
--       construction): the complement block of the adapted-basis action matrix is
--       exactly `LinearMap.toMatrix bW bW ((mulVecLin G).restrict hInvF)`.
--
--   (B) `orthogonalChangeOfBasisEquiv` / `orthogonalChangeOfBasis` /
--       `toMatrix_orthogonalChangeOfBasis` — the change-of-basis primitive: an
--       orthogonal `Q` turns a basis `b` of the complement into a new basis `b.map φ_Q`
--       whose matrix of any endomorphism `f` is `Qᵀ · (toMatrix b b f) · Q`.  This is
--       how the real-Schur orthogonal similarity is realised as a genuine complement
--       basis.
--
--   (C) `charpoly_restrict_dvd_of_isCompl` — the ℂ→ℝ-free descent of the real-spectrum
--       hypothesis: for a `G`-invariant splitting `⊤ = E₁ ⊕ F`, the characteristic
--       polynomial of `G|_F` divides that of `G` (via `charpoly_prodMap` +
--       `LinearEquiv.charpoly_conj`), so `G` real spectrum ⟹ `G|_F` real spectrum.
--
--   (D) `restrict_upperTri_diag_abs_lt_one` — the diagonal modulus bound: for the
--       genuinely upper-triangular (real-spectrum) complement action matrix `T`, each
--       diagonal entry `T_kk` is an eigenvalue of `G|_F` (root of its charpoly), hence
--       an eigenvalue of `G` with an eigenvector in `F`; the GAP (2) dichotomy
--       (`eigenvalue_dichotomy_of_orbit_tendsto`) forces `T_kk = 1 ∨ |T_kk| < 1`, and
--       `T_kk = 1` is excluded because a fixed vector in `F` would lie in `E₁ ⊓ F = ⊥`.
--
--   (E) `semiconvergent_block_form_exists_of_convergence_real_spectrum` and its power
--       corollary `matPow_G_tendsto_oneEigenProjector_of_convergence_real_spectrum` —
--       the payoff.  From convergence of every orbit `Gᵐ x` AND real spectrum of `G`
--       (`(mulVecLin G).charpoly.Splits`), the FULL block form of (17.22) exists and
--       `Gᵐ → I − E` entrywise, with the ∞-norm contraction CONSTRUCTED.  Real
--       spectrum makes every diagonal block `1×1` (genuinely upper-triangular
--       `real_schur_triangulation_of_splits`), so no (3b) per-`2×2`-block ∞-norm
--       reduction is needed and (3a) is discharged in full.
--
-- HONESTY.  The real-spectrum hypothesis is genuine and is NOT the conclusion in
-- disguise: the general complex case is PROVEN impossible in the repository's ∞-norm
-- (row-sum) form (`twoByTwo_max_rowSum_ge_of_trace_det` of
-- `SemiconvergentExistenceComplete.lean`; the ∞-norm infimum of a `2×2` block with
-- eigenvalues `α ± βi` is `|α| + |β|`, not the spectral radius `√(α²+β²)`), so the
-- restriction to real spectrum is the honest scope of the ∞-norm route.  No spectral,
-- structural, or contraction fact is folded into a hypothesis: convergence of `Gᵐ`
-- and real spectrum are the only inputs, and the eigenvalue-`1` semisimplicity, the
-- strict disk `|μ| < 1`, the real invariant basis, and the ∞-norm contraction are all
-- DERIVED.
--
-- IMPORT-ONLY: this module edits nothing.  No `sorry`/`admit`/`axiom`/`unsafe`/
-- `opaque`/`native_decide`/proof-disabling option is used.
--
-- Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*,
-- 2nd ed., §17.4, eq (17.22); Householder `[106, Lem 6.9]`; real Schur form
-- §16.2 (16.4).

import NumStability.Analysis.SemiconvergentExistenceComplete
import NumStability.Analysis.RealSchurTriangulation

namespace NumStability

open scoped BigOperators Topology Matrix
open Module

-- ============================================================
-- §17.4  (A) The `basisActionMatrix ↔ LinearMap.toMatrix` reindex identity
-- ============================================================

section Reindex

variable {n : ℕ}

/-- **Higham §17.4, eq (17.22) — `[106, Lem 6.9]` — the `basisActionMatrix ↔
    LinearMap.toMatrix` reindex identity (the single residual import-level bridge of
    `SemiconvergentExistenceComplete.lean`).**

    For a real invariant splitting `⊤ = E₁ ⊕ F` with the eigenvalue-`1` block `E₁`
    first and the `G`-invariant complement `F` second, the complement block of the
    adapted-basis action matrix `basisActionMatrix G (adaptedBasis …)` — read at the
    reindexed complement coordinates `adaptEquiv (inr l)`, `adaptEquiv (inr k)` — equals
    the honest matrix `LinearMap.toMatrix bW bW ((mulVecLin G).restrict hInvF)` of `G`
    restricted to `F` in the complement basis `bW`.

    This is the identity flagged (but not proved) in the closing STATUS block of
    `SemiconvergentExistenceComplete.lean`: it lets a real (quasi-)Schur reduction of
    `G|_F` (chosen on `bW`) be transported to the coordinate action matrix consumed by
    the master reduction.  Proof threads `Basis.repr_reindex_apply`,
    `Basis.prod_repr_inr`, and `Submodule.prodEquivOfIsCompl_symm_apply_right` through the
    `adaptedBasis = (adaptedSumBasis).reindex (adaptEquiv)` construction. -/
theorem basisActionMatrix_complement_eq_toMatrix_restrict {r m : ℕ} (hrm : r + m = n)
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F)
    (G : Fin n → Fin n → ℝ) (hInvF : ∀ x ∈ F, G *ᵥ x ∈ F)
    (l k : Fin m) :
    basisActionMatrix G (adaptedBasis hrm hCompl bV bW)
        (adaptEquiv hrm (Sum.inr l)) (adaptEquiv hrm (Sum.inr k))
      = LinearMap.toMatrix bW bW ((Matrix.mulVecLin G).restrict hInvF) l k := by
  -- RHS: `bW.repr ((restrict) (bW k)) l`.
  rw [LinearMap.toMatrix_apply]
  -- The vector `(restrict) (bW k)` coerces to `G *ᵥ (bW k)`.
  have hcoe : (((Matrix.mulVecLin G).restrict hInvF) (bW k) : Fin n → ℝ)
      = G *ᵥ ((bW k : Fin n → ℝ)) := by
    rw [LinearMap.restrict_coe_apply, Matrix.mulVecLin_apply]
  -- LHS: unfold `basisActionMatrix`.
  show (adaptedBasis hrm hCompl bV bW).repr
      (G *ᵥ ((adaptedBasis hrm hCompl bV bW) (adaptEquiv hrm (Sum.inr k))))
      (adaptEquiv hrm (Sum.inr l)) = _
  -- The basis vector at the `inr k` index is `bW k`.
  have hbk : (adaptedBasis hrm hCompl bV bW) (adaptEquiv hrm (Sum.inr k))
      = (bW k : Fin n → ℝ) := by
    rw [adaptedBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply, adaptedSumBasis_inr]
  rw [hbk]
  -- The repr side: reindex + map + prod.
  rw [adaptedBasis, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply]
  have hrepr : (adaptedSumBasis hCompl bV bW).repr (G *ᵥ ((bW k : Fin n → ℝ))) (Sum.inr l)
      = (bV.prod bW).repr
          ((Submodule.prodEquivOfIsCompl E₁ F hCompl).symm (G *ᵥ ((bW k : Fin n → ℝ)))) (Sum.inr l) := by
    simp only [adaptedSumBasis, Module.Basis.map_repr, LinearEquiv.trans_apply]
  rw [hrepr, Module.Basis.prod_repr_inr]
  -- The `.2` component: `G *ᵥ bW k ∈ F`, so `prodEquiv.symm` gives `(0, ⟨G *ᵥ bW k, _⟩)`.
  set y : F := ((Matrix.mulVecLin G).restrict hInvF) (bW k) with hy
  have hsnd : ((Submodule.prodEquivOfIsCompl E₁ F hCompl).symm (G *ᵥ ((bW k : Fin n → ℝ)))).2 = y := by
    have hkey : (Submodule.prodEquivOfIsCompl E₁ F hCompl).symm ((y : Fin n → ℝ)) = (0, y) :=
      Submodule.prodEquivOfIsCompl_symm_apply_right (p := E₁) (q := F) hCompl y
    rw [hcoe] at hkey
    rw [hkey]
  rw [hsnd]

end Reindex

-- ============================================================
-- §16.2 (16.4)  (B) Orthogonal change of basis on the complement
-- ============================================================

section ChangeOfBasis

variable {m : ℕ} {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- **Higham §16.2 (16.4) — orthogonal change-of-basis automorphism.**  The linear
    automorphism of the complement `F` induced by an orthogonal change-of-basis matrix
    `Q` (`Qᵀ Q = Q Qᵀ = 1`) in a basis `b`: `Matrix.toLin b b Q`, with inverse
    `Matrix.toLin b b Qᵀ`.  Used to realise the orthogonal similarity of the real Schur
    reduction as a genuine complement basis. -/
noncomputable def orthogonalChangeOfBasisEquiv (b : Basis (Fin m) ℝ F)
    {Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    F ≃ₗ[ℝ] F :=
  LinearEquiv.ofLinear (Matrix.toLin b b Q) (Matrix.toLin b b Qᵀ)
    (by
      rw [← Matrix.toLin_mul]
      rw [Matrix.mem_orthogonalGroup_iff] at hQ
      rw [hQ, Matrix.toLin_one])
    (by
      rw [← Matrix.toLin_mul]
      rw [Matrix.mem_orthogonalGroup_iff'] at hQ
      rw [hQ, Matrix.toLin_one])

/-- **Higham §16.2 (16.4) — the conjugated complement basis.**  The new basis of `F`
    obtained by applying the orthogonal change-of-basis automorphism to `b`; its columns
    are the images of `b` under `Q`. -/
noncomputable def orthogonalChangeOfBasis (b : Basis (Fin m) ℝ F)
    {Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    Basis (Fin m) ℝ F :=
  b.map (orthogonalChangeOfBasisEquiv b hQ)

/-- **Higham §16.2 (16.4) — the matrix of `f` in the conjugated basis is `Qᵀ · A · Q`.**
    For any endomorphism `f` of the complement `F` and orthogonal `Q`, the matrix of `f`
    in the conjugated basis `orthogonalChangeOfBasis b hQ` equals `Qᵀ · (toMatrix b b f) · Q`
    — the orthogonal similarity of the real Schur reduction realised in coordinates.
    Proof via `LinearMap.toMatrix_comp` and `LinearMap.toMatrix_toLin`. -/
theorem toMatrix_orthogonalChangeOfBasis (b : Basis (Fin m) ℝ F)
    {Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q ∈ Matrix.orthogonalGroup (Fin m) ℝ)
    (f : F →ₗ[ℝ] F) :
    LinearMap.toMatrix (orthogonalChangeOfBasis b hQ) (orthogonalChangeOfBasis b hQ) f
      = Qᵀ * LinearMap.toMatrix b b f * Q := by
  have hmaprepr : ∀ (y : F),
      (orthogonalChangeOfBasis b hQ).repr y = b.repr ((orthogonalChangeOfBasisEquiv b hQ).symm y) := by
    intro y
    simp only [orthogonalChangeOfBasis, Module.Basis.map_repr, LinearEquiv.trans_apply]
  ext l k
  rw [LinearMap.toMatrix_apply, hmaprepr]
  have hbk : (orthogonalChangeOfBasis b hQ) k = (orthogonalChangeOfBasisEquiv b hQ) (b k) := by
    simp only [orthogonalChangeOfBasis, Module.Basis.map_apply]
  rw [hbk]
  have hsymmlm : (orthogonalChangeOfBasisEquiv b hQ).symm.toLinearMap = Matrix.toLin b b Qᵀ :=
    LinearEquiv.ofLinear_symm_toLinearMap (Matrix.toLin b b Q) (Matrix.toLin b b Qᵀ)
  have hlm : (orthogonalChangeOfBasisEquiv b hQ).toLinearMap = Matrix.toLin b b Q :=
    LinearEquiv.ofLinear_toLinearMap (Matrix.toLin b b Q) (Matrix.toLin b b Qᵀ)
  have hcomp : LinearMap.toMatrix b b
      (((orthogonalChangeOfBasisEquiv b hQ).symm.toLinearMap).comp
        (f.comp (orthogonalChangeOfBasisEquiv b hQ).toLinearMap))
      = Qᵀ * LinearMap.toMatrix b b f * Q := by
    rw [hsymmlm, hlm, LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b,
      LinearMap.toMatrix_toLin, LinearMap.toMatrix_toLin, mul_assoc]
  rw [← hcomp, LinearMap.toMatrix_apply]
  rfl

end ChangeOfBasis

-- ============================================================
-- §17.4  (C) ℂ→ℝ-free descent of the real-spectrum hypothesis
-- ============================================================

section CharpolyDescent

variable {n : ℕ}

/-- **Higham §17.4 (17.22) — the characteristic polynomial of `G|_F` divides that of
    `G`.**  For a `G`-invariant direct-sum splitting `⊤ = E₁ ⊕ F` (both summands
    invariant), `charpoly (G|_F) ∣ charpoly G`.  Consequently, if `G` has real spectrum
    (`charpoly G` splits over `ℝ`), so does `G|_F`.

    Proof follows Mathlib's `LinearMap.charpoly_prodMap` /
    `LinearEquiv.charpoly_conj` factorization of the characteristic polynomial along an
    invariant direct-sum decomposition: `charpoly G = charpoly (G|_E₁) · charpoly (G|_F)`,
    via the isomorphism `prodEquivOfIsCompl`.  This is the honest ℂ→ℝ-descent of the
    real-spectrum hypothesis to the complement, without any complexification API. -/
theorem charpoly_restrict_dvd_of_isCompl {E₁ F : Submodule ℝ (Fin n → ℝ)}
    (hCompl : IsCompl E₁ F) {fG : Module.End ℝ (Fin n → ℝ)}
    (hE₁inv : ∀ x ∈ E₁, fG x ∈ E₁) (hInvF : ∀ x ∈ F, fG x ∈ F) :
    LinearMap.charpoly (fG.restrict hInvF) ∣ fG.charpoly := by
  classical
  set F' : Module.End ℝ E₁ := fG.restrict hE₁inv with hF'
  set G' : Module.End ℝ F := fG.restrict hInvF with hG'
  set ψ : Module.End ℝ (E₁ × F) := F'.prodMap G' with hψdef
  set e := Submodule.prodEquivOfIsCompl E₁ F hCompl with hedef
  set bV := Module.Basis.ofVectorSpace ℝ E₁ with hbV
  set bW := Module.Basis.ofVectorSpace ℝ F with hbW
  set b := bV.prod bW with hb
  have hψ : ψ = e.symm.conj fG := by
    apply b.ext
    simp only [hb, Module.Basis.prod_apply, LinearMap.coe_inl, LinearMap.coe_inr,
      LinearMap.prodMap_apply, LinearEquiv.conj_apply, LinearEquiv.symm_symm,
      Submodule.coe_prodEquivOfIsCompl, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearMap.coprod_apply, Submodule.coe_subtype, map_add, Sum.forall,
      Sum.elim_inl, map_zero, ZeroMemClass.coe_zero, add_zero, LinearEquiv.eq_symm_apply,
      and_self, Submodule.coe_prodEquivOfIsCompl', LinearMap.restrict_coe_apply, implies_true,
      Sum.elim_inr, zero_add, hedef, hF', hG', hψdef]
  have hfac : fG.charpoly = F'.charpoly * G'.charpoly := by
    rw [← e.symm.charpoly_conj fG, ← hψ, hψdef, LinearMap.charpoly_prodMap]
  rw [hfac]
  exact Dvd.intro_left _ rfl

end CharpolyDescent

-- ============================================================
-- §17.4  (D) The diagonal modulus bound for the real-spectrum complement
-- ============================================================

section DiagBound

variable {n : ℕ}

/-- **Higham §17.4 (17.22) — `[106, Lem 6.9]` — the diagonal modulus bound of the
    genuinely-upper-triangular complement action (GAP (2) on the real spectrum).**

    Let `⊤ = E₁ ⊕ F` be a `G`-invariant splitting with `E₁` the eigenvalue-`1`
    eigenspace of `mulVecLin G`, and let `T := LinearMap.toMatrix bW bW ((mulVecLin G).restrict hInvF)`
    be UPPER-TRIANGULAR (the real-spectrum Schur form of `G|_F`).  If every orbit
    `(mulVecLin G)ᵗ x` converges, then each diagonal entry satisfies `|T_kk| < 1`.

    Proof.  `T` upper-triangular ⟹ `charpoly T = ∏ (X − T_ii)`, so `T_kk` is a root of
    `charpoly T = charpoly (G|_F)`; hence `G|_F` has eigenvalue `T_kk` with an eigenvector
    `y ∈ F`, and `↑y` is an eigenvector of `mulVecLin G` for `T_kk`.  The GAP (2) dichotomy
    `eigenvalue_dichotomy_of_orbit_tendsto` (convergent orbit) gives `T_kk = 1 ∨ |T_kk| < 1`;
    and `T_kk = 1` is impossible, since then `↑y` is fixed by `G`, so `↑y ∈ E₁ ⊓ F = ⊥`,
    contradicting `y ≠ 0`.  Unconditional in the stated hypotheses. -/
theorem restrict_upperTri_diag_abs_lt_one {m : ℕ} (G : Fin n → Fin n → ℝ)
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (hE₁ : E₁ = Module.End.eigenspace (Matrix.mulVecLin G) 1)
    (hInvF : ∀ x ∈ F, G *ᵥ x ∈ F)
    (bW : Module.Basis (Fin m) ℝ F)
    (hconv : ∀ x : Fin n → ℝ, ∃ z : Fin n → ℝ,
      Filter.Tendsto (fun t : ℕ => (Matrix.mulVecLin G ^ t) x) Filter.atTop (𝓝 z))
    (hupper : ∀ i j : Fin m, j < i →
      LinearMap.toMatrix bW bW ((Matrix.mulVecLin G).restrict hInvF) i j = 0)
    (k : Fin m) :
    |LinearMap.toMatrix bW bW ((Matrix.mulVecLin G).restrict hInvF) k k| < 1 := by
  set fG : Module.End ℝ (Fin n → ℝ) := Matrix.mulVecLin G with hfG
  set fF : Module.End ℝ F := fG.restrict hInvF with hfF
  set T : Matrix (Fin m) (Fin m) ℝ := LinearMap.toMatrix bW bW fF with hT
  set μ : ℝ := T k k with hμ
  -- `T` upper-triangular ⟹ `charpoly T = ∏ (X − T_ii)`, and `μ = T_kk` is a root.
  have hbt : T.BlockTriangular id := fun i j hji => hupper i j hji
  have hcp : T.charpoly = ∏ i : Fin m, (Polynomial.X - Polynomial.C (T i i)) :=
    Matrix.charpoly_of_upperTriangular T hbt
  have hroot : T.charpoly.IsRoot μ := by
    rw [Polynomial.IsRoot, hcp, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [hμ]
  -- `charpoly T = charpoly (G|_F)`.
  have hcpeq : T.charpoly = LinearMap.charpoly fF := by rw [hT, LinearMap.charpoly_toMatrix]
  -- Hence `G|_F` has eigenvalue `μ`.
  have hev : fF.HasEigenvalue μ := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, ← hcpeq]; exact hroot
  obtain ⟨y, hy⟩ := hev.exists_hasEigenvector
  -- `↑y` is an eigenvector of `mulVecLin G` for `μ`.
  have hyev : fG.HasEigenvector μ (y : Fin n → ℝ) := by
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      have h1 : fF y = μ • y := Module.End.mem_eigenspace_iff.mp hy.1
      have h2 := congrArg (Submodule.subtype F) h1
      simpa [hfF, LinearMap.restrict_coe_apply] using h2
    · simp only [ne_eq, Submodule.coe_eq_zero]; exact hy.2
  obtain ⟨w, hw⟩ := hconv (y : Fin n → ℝ)
  have hdich : μ = 1 ∨ ‖μ‖ < 1 := eigenvalue_dichotomy_of_orbit_tendsto hyev hw
  rcases hdich with h1 | hlt
  · -- `μ = 1` is impossible: `↑y ∈ E₁ ⊓ F = ⊥` with `↑y ≠ 0`.
    exfalso
    have hmemE₁ : (y : Fin n → ℝ) ∈ E₁ := by
      rw [hE₁, Module.End.mem_eigenspace_iff]
      have hae := hyev.apply_eq_smul
      rw [h1] at hae
      exact hae
    have hmemF : (y : Fin n → ℝ) ∈ F := y.2
    have hbot : (y : Fin n → ℝ) ∈ E₁ ⊓ F := ⟨hmemE₁, hmemF⟩
    rw [hCompl.inf_eq_bot, Submodule.mem_bot] at hbot
    exact hy.2 (Submodule.coe_eq_zero.mp hbot)
  · rwa [Real.norm_eq_abs] at hlt

end DiagBound

-- ============================================================
-- §17.4  (E) Full real-spectrum block-form existence from convergence
-- ============================================================

section RealSpectrumExistence

variable {n : ℕ}

/-- Recover the `Fin m` complement-index `l` of a `Fin n` complement coordinate `i`
    (`¬(i:ℕ) < r`) under the order-compatible splitting equivalence `adaptEquiv`.
    Index bookkeeping for Higham §17.4 (17.22). -/
theorem exists_complIndex_of_not_lt {r m : ℕ} (hrm : r + m = n) (i : Fin n)
    (hi : ¬(i : ℕ) < r) :
    ∃ l : Fin m, adaptEquiv hrm (Sum.inr l) = i ∧ (l : ℕ) = (i : ℕ) - r := by
  rcases hsum : (adaptEquiv hrm).symm i with a | l
  · exfalso
    have hval : ((adaptEquiv hrm) (Sum.inl a) : ℕ) = (i : ℕ) := by
      rw [← hsum]; exact congrArg _ ((adaptEquiv hrm).apply_symm_apply i)
    rw [adaptEquiv_inl_val] at hval
    exact hi (hval ▸ a.2)
  · refine ⟨l, ?_, ?_⟩
    · rw [← hsum]; exact (adaptEquiv hrm).apply_symm_apply i
    · have hval : ((adaptEquiv hrm) (Sum.inr l) : ℕ) = (i : ℕ) := by
        rw [← hsum]; exact congrArg _ ((adaptEquiv hrm).apply_symm_apply i)
      rw [adaptEquiv_inr_val] at hval
      omega

/-- **Higham §17.4, eq (17.22) — `[106, Lem 6.9]` — FULL real-spectrum semiconvergent
    block-form EXISTENCE from convergence of `Gᵐ` alone.**

    Let `G : Fin n → Fin n → ℝ` be a real matrix such that
      * every orbit `t ↦ (mulVecLin G)ᵗ x` converges (the operator content of
        semiconvergence: `Gᵐ` converges entrywise, hence on every vector), and
      * `G` has REAL SPECTRUM: `(mulVecLin G).charpoly` splits over `ℝ`.
    Then there exist `r`, an invertible real change of basis `(X', X'⁻¹)`, a block matrix
    `Γ`, and `q < 1` giving the EXACT `semiconvergent_block_form_exists` data package of
    (17.22): `X'⁻¹ G X' = diag(I_r, Γ)`, the first `r` columns of `X'` are eigenvalue-`1`
    eigenvectors of `G`, `Γ` has ∞-norm row sums `≤ q < 1`, and the standard block-form
    conditions hold.

    NO basis, column, contraction, or spectral data is supplied: `r = dim ker(G − I)` is
    the eigenvalue-`1` multiplicity, and the entire package is DERIVED.  This closes the
    real-spectrum case of the semiconvergent existence (17.22) in full.

    Proof.  `exists_real_primary_splitting_of_forall_orbit_tendsto` produces the real
    Fitting splitting `⊤ = E₁ ⊕ F` (GAP (1) semisimple-at-`1`).  The real-spectrum
    hypothesis descends to `G|_F` (`charpoly_restrict_dvd_of_isCompl`), so
    `real_schur_triangulation_of_splits` gives an orthogonal `Q` with `Qᵀ · toMatrix(G|_F) · Q`
    GENUINELY upper-triangular (all `1×1` blocks — no (3b) `2×2` reduction needed).  The
    conjugated complement basis (`orthogonalChangeOfBasis`) realises this upper-triangular
    matrix as the coordinate complement action (`basisActionMatrix_complement_eq_toMatrix_restrict`),
    with diagonal moduli `< 1` (`restrict_upperTri_diag_abs_lt_one`, GAP (2)).  A uniform
    `ρ < 1` (`uniform_modulus_bound_lt_one`) and the singleton block structure (`pblk = Fin.val`)
    feed the master reduction
    `semiconvergent_block_form_exists_of_convergence_and_complement_normal_form`, which
    CONSTRUCTS the ∞-norm contraction and assembles the block form. -/
theorem semiconvergent_block_form_exists_of_convergence_real_spectrum
    (G : Fin n → Fin n → ℝ)
    (hconv : ∀ x : Fin n → ℝ, ∃ z : Fin n → ℝ,
      Filter.Tendsto (fun t : ℕ => (Matrix.mulVecLin G ^ t) x) Filter.atTop (𝓝 z))
    (hsplit : (Matrix.mulVecLin G).charpoly.Splits) :
    ∃ (r : ℕ) (X' X'_inv Γ : Fin n → Fin n → ℝ) (q : ℝ),
      0 ≤ q ∧ q < 1 ∧
      (∀ i : Fin n, ¬(i : ℕ) < r →
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬(j : ℕ) < r), |Γ i j|) ≤ q) ∧
      IsRightInverse n X' X'_inv ∧ IsRightInverse n X'_inv X' ∧
      (∀ (k : Fin n), (k : ℕ) < r → ∀ i : Fin n, matMul n G X' i k = X' i k) ∧
      matMul n X'_inv (matMul n G X') = blockJ n r Γ ∧
      (∀ i j : Fin n, (i : ℕ) < r → blockJ n r Γ i j = if i = j then 1 else 0) ∧
      (∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → blockJ n r Γ i j = 0) ∧
      (∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |blockJ n r Γ i j| ≤ q) := by
  classical
  set fG : Module.End ℝ (Fin n → ℝ) := Matrix.mulVecLin G with hfG
  obtain ⟨F, hCompl, hEig1, hInvF⟩ := exists_real_primary_splitting_of_forall_orbit_tendsto G hconv
  set E₁ : Submodule ℝ (Fin n → ℝ) := Module.End.eigenspace fG 1 with hE₁
  set r : ℕ := Module.finrank ℝ E₁ with hr
  set m : ℕ := Module.finrank ℝ F with hm
  have hrm : r + m = n := by
    have h := Submodule.finrank_add_eq_of_isCompl hCompl
    rw [hr, hm, h]; simp
  set bV : Module.Basis (Fin r) ℝ E₁ := Module.finBasisOfFinrankEq ℝ E₁ rfl with hbV
  set bW₀ : Module.Basis (Fin m) ℝ F := Module.finBasisOfFinrankEq ℝ F rfl with hbW₀
  -- `E₁` (an eigenspace) is `G`-invariant.
  have hE₁inv : ∀ x ∈ E₁, fG x ∈ E₁ := by
    intro x hx
    have hxx : fG x = x := by
      rw [hE₁, Module.End.mem_eigenspace_iff] at hx; rw [hx, one_smul]
    rw [hxx]; exact hx
  have hInvF' : ∀ x ∈ F, fG x ∈ F := hInvF
  set fF : Module.End ℝ F := fG.restrict hInvF' with hfF
  set A₀ : Matrix (Fin m) (Fin m) ℝ := LinearMap.toMatrix bW₀ bW₀ fF with hA₀
  -- `A₀`'s charpoly splits (dividing `charpoly G`).
  have hA₀split : A₀.charpoly.Splits := by
    have hdvd : A₀.charpoly ∣ fG.charpoly := by
      rw [hA₀, LinearMap.charpoly_toMatrix]
      exact charpoly_restrict_dvd_of_isCompl hCompl hE₁inv hInvF'
    exact Polynomial.Splits.of_dvd hsplit (LinearMap.charpoly_monic fG).ne_zero hdvd
  -- Real Schur triangularization of `A₀` (genuinely upper-triangular: real spectrum).
  obtain ⟨Q, T', hQorth, hQT, hupperT'⟩ := real_schur_triangulation_of_splits A₀ hA₀split
  -- The conjugated complement basis; its action matrix is `Qᵀ A₀ Q = T'`, upper-triangular.
  set bW : Module.Basis (Fin m) ℝ F := orthogonalChangeOfBasis bW₀ hQorth with hbW
  have hTeq : LinearMap.toMatrix bW bW fF = T' := by
    rw [hbW, toMatrix_orthogonalChangeOfBasis bW₀ hQorth fF, hA₀] at *; rw [← hQT]
  have hupper : ∀ i j : Fin m, j < i → LinearMap.toMatrix bW bW fF i j = 0 := by
    intro i j hji; rw [hTeq]; exact hupperT' i j hji
  -- Diagonal moduli `< 1` (GAP (2) on the real spectrum).
  have hdiag : ∀ l : Fin m, |LinearMap.toMatrix bW bW fF l l| < 1 :=
    fun l => restrict_upperTri_diag_abs_lt_one G hCompl hE₁ hInvF' bW hconv hupper l
  -- Block assignment `pblk = Fin.val` (every complement index its own `1×1` block).
  set pblk : Fin n → ℕ := fun i => (i : ℕ) with hpblk
  -- The reindex identity connecting the coordinate action matrix to `toMatrix bW bW fF`.
  have hbridge : ∀ l k : Fin m,
      basisActionMatrix G (adaptedBasis hrm hCompl bV bW)
        (adaptEquiv hrm (Sum.inr l)) (adaptEquiv hrm (Sum.inr k))
        = LinearMap.toMatrix bW bW fF l k :=
    fun l k => basisActionMatrix_complement_eq_toMatrix_restrict hrm hCompl bV bW G hInvF' l k
  -- Uniform modulus bound `ρ < 1` on the complement diagonal.
  obtain ⟨ρ, hρ0, hρ1, hρle⟩ :=
    uniform_modulus_bound_lt_one n r
      (fun i => |basisActionMatrix G (adaptedBasis hrm hCompl bV bW) i i|)
      (by
        intro i hi
        obtain ⟨l, hl, _⟩ := exists_complIndex_of_not_lt hrm i hi
        show |basisActionMatrix G (adaptedBasis hrm hCompl bV bW) i i| < 1
        rw [← hl, hbridge l l]; exact hdiag l)
      (fun i => abs_nonneg _)
  -- `hClower`: quasi-triangular structure (upper-triangular, transported).
  have hClower : ∀ i j : Fin n, ¬(i : ℕ) < r → ¬(j : ℕ) < r →
      pblk j < pblk i → basisActionMatrix G (adaptedBasis hrm hCompl bV bW) i j = 0 := by
    intro i j hi hj hlt
    obtain ⟨li, hli, hlival⟩ := exists_complIndex_of_not_lt hrm i hi
    obtain ⟨lj, hlj, hljval⟩ := exists_complIndex_of_not_lt hrm j hj
    rw [← hli, ← hlj, hbridge li lj]
    apply hupper li lj
    rw [hpblk] at hlt; simp only at hlt; omega
  -- `hCblock`: singleton within-block sum `= |T_ll| ≤ ρ`.
  have hCblock : ∀ i : Fin n, ¬(i : ℕ) < r →
      (∑ j ∈ Finset.univ.filter
        (fun j : Fin n => ¬(j : ℕ) < r ∧ pblk j = pblk i),
        |basisActionMatrix G (adaptedBasis hrm hCompl bV bW) i j|) ≤ ρ := by
    intro i hi
    have hfilter : (Finset.univ.filter
        (fun j : Fin n => ¬(j : ℕ) < r ∧ pblk j = pblk i)) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hpj⟩; rw [hpblk] at hpj; simp only at hpj; exact Fin.ext hpj
      · rintro rfl; exact ⟨hi, rfl⟩
    rw [hfilter, Finset.sum_singleton]; exact hρle i hi
  -- Assemble via the master reduction (the ∞-norm contraction is CONSTRUCTED there).
  obtain ⟨X', X'_inv, Γ, q, hq0, hq1, hΓrows, hX'r, hX'l, hcolTop, hsim, hJtop, hJcross, hJrows⟩ :=
    semiconvergent_block_form_exists_of_convergence_and_complement_normal_form
      hrm G hCompl bV bW hEig1 hInvF' pblk hρ0 hρ1 hClower hCblock
  exact ⟨r, X', X'_inv, Γ, q, hq0, hq1, hΓrows, hX'r, hX'l, hcolTop, hsim, hJtop, hJcross, hJrows⟩

/-- **Higham §17.4, eq (17.22)/(17.27) — `[106, Lem 6.9]` — real-spectrum
    semiconvergence `Gᵐ → I − E` from convergence of `Gᵐ` alone.**

    The power-convergence payoff of the real-spectrum existence: under the same
    hypotheses (every orbit `(mulVecLin G)ᵗ x` converges AND `G` has real spectrum
    `(mulVecLin G).charpoly.Splits`), the powers of `G` converge entrywise to the
    eigenvalue-`1` projector `oneEigenProjector n r X' X'⁻¹ = X' · diag(I_r, 0) · X'⁻¹ = I − E`,
    where `X'` is built from the adapted real Schur basis of the Fitting splitting and
    `r = dim ker(G − I)`.

    Neither a modulus bound nor an ∞-norm contraction is assumed: both are derived
    (GAP (2) dichotomy for the diagonal moduli `< 1`, then the master reduction's GAP (4)
    δ-scaling for `‖Γ‖∞ < 1`).  This is the honest "semiconvergence ⟹ convergent powers"
    conclusion for a real matrix with real spectrum, from convergence alone. -/
theorem matPow_G_tendsto_oneEigenProjector_of_convergence_real_spectrum
    (G : Fin n → Fin n → ℝ)
    (hconv : ∀ x : Fin n → ℝ, ∃ z : Fin n → ℝ,
      Filter.Tendsto (fun t : ℕ => (Matrix.mulVecLin G ^ t) x) Filter.atTop (𝓝 z))
    (hsplit : (Matrix.mulVecLin G).charpoly.Splits) :
    ∃ (r : ℕ) (X' X'_inv : Fin n → Fin n → ℝ),
      IsRightInverse n X' X'_inv ∧ IsRightInverse n X'_inv X' ∧
      (∀ i j : Fin n,
        Filter.Tendsto (fun t => matPow n G t i j) Filter.atTop
          (nhds (oneEigenProjector n r X' X'_inv i j))) := by
  classical
  set fG : Module.End ℝ (Fin n → ℝ) := Matrix.mulVecLin G with hfG
  obtain ⟨F, hCompl, hEig1, hInvF⟩ := exists_real_primary_splitting_of_forall_orbit_tendsto G hconv
  set E₁ : Submodule ℝ (Fin n → ℝ) := Module.End.eigenspace fG 1 with hE₁
  set r : ℕ := Module.finrank ℝ E₁ with hr
  set m : ℕ := Module.finrank ℝ F with hm
  have hrm : r + m = n := by
    have h := Submodule.finrank_add_eq_of_isCompl hCompl
    rw [hr, hm, h]; simp
  set bV : Module.Basis (Fin r) ℝ E₁ := Module.finBasisOfFinrankEq ℝ E₁ rfl with hbV
  set bW₀ : Module.Basis (Fin m) ℝ F := Module.finBasisOfFinrankEq ℝ F rfl with hbW₀
  have hE₁inv : ∀ x ∈ E₁, fG x ∈ E₁ := by
    intro x hx
    have hxx : fG x = x := by
      rw [hE₁, Module.End.mem_eigenspace_iff] at hx; rw [hx, one_smul]
    rw [hxx]; exact hx
  have hInvF' : ∀ x ∈ F, fG x ∈ F := hInvF
  set fF : Module.End ℝ F := fG.restrict hInvF' with hfF
  set A₀ : Matrix (Fin m) (Fin m) ℝ := LinearMap.toMatrix bW₀ bW₀ fF with hA₀
  have hA₀split : A₀.charpoly.Splits := by
    have hdvd : A₀.charpoly ∣ fG.charpoly := by
      rw [hA₀, LinearMap.charpoly_toMatrix]
      exact charpoly_restrict_dvd_of_isCompl hCompl hE₁inv hInvF'
    exact Polynomial.Splits.of_dvd hsplit (LinearMap.charpoly_monic fG).ne_zero hdvd
  obtain ⟨Q, T', hQorth, hQT, hupperT'⟩ := real_schur_triangulation_of_splits A₀ hA₀split
  set bW : Module.Basis (Fin m) ℝ F := orthogonalChangeOfBasis bW₀ hQorth with hbW
  have hTeq : LinearMap.toMatrix bW bW fF = T' := by
    rw [hbW, toMatrix_orthogonalChangeOfBasis bW₀ hQorth fF, hA₀] at *; rw [← hQT]
  have hupper : ∀ i j : Fin m, j < i → LinearMap.toMatrix bW bW fF i j = 0 := by
    intro i j hji; rw [hTeq]; exact hupperT' i j hji
  have hdiag : ∀ l : Fin m, |LinearMap.toMatrix bW bW fF l l| < 1 :=
    fun l => restrict_upperTri_diag_abs_lt_one G hCompl hE₁ hInvF' bW hconv hupper l
  set pblk : Fin n → ℕ := fun i => (i : ℕ) with hpblk
  have hbridge : ∀ l k : Fin m,
      basisActionMatrix G (adaptedBasis hrm hCompl bV bW)
        (adaptEquiv hrm (Sum.inr l)) (adaptEquiv hrm (Sum.inr k))
        = LinearMap.toMatrix bW bW fF l k :=
    fun l k => basisActionMatrix_complement_eq_toMatrix_restrict hrm hCompl bV bW G hInvF' l k
  obtain ⟨ρ, hρ0, hρ1, hρle⟩ :=
    uniform_modulus_bound_lt_one n r
      (fun i => |basisActionMatrix G (adaptedBasis hrm hCompl bV bW) i i|)
      (by
        intro i hi
        obtain ⟨l, hl, _⟩ := exists_complIndex_of_not_lt hrm i hi
        show |basisActionMatrix G (adaptedBasis hrm hCompl bV bW) i i| < 1
        rw [← hl, hbridge l l]; exact hdiag l)
      (fun i => abs_nonneg _)
  have hClower : ∀ i j : Fin n, ¬(i : ℕ) < r → ¬(j : ℕ) < r →
      pblk j < pblk i → basisActionMatrix G (adaptedBasis hrm hCompl bV bW) i j = 0 := by
    intro i j hi hj hlt
    obtain ⟨li, hli, hlival⟩ := exists_complIndex_of_not_lt hrm i hi
    obtain ⟨lj, hlj, hljval⟩ := exists_complIndex_of_not_lt hrm j hj
    rw [← hli, ← hlj, hbridge li lj]
    apply hupper li lj
    rw [hpblk] at hlt; simp only at hlt; omega
  have hCblock : ∀ i : Fin n, ¬(i : ℕ) < r →
      (∑ j ∈ Finset.univ.filter
        (fun j : Fin n => ¬(j : ℕ) < r ∧ pblk j = pblk i),
        |basisActionMatrix G (adaptedBasis hrm hCompl bV bW) i j|) ≤ ρ := by
    intro i hi
    have hfilter : (Finset.univ.filter
        (fun j : Fin n => ¬(j : ℕ) < r ∧ pblk j = pblk i)) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hpj⟩; rw [hpblk] at hpj; simp only at hpj; exact Fin.ext hpj
      · rintro rfl; exact ⟨hi, rfl⟩
    rw [hfilter, Finset.sum_singleton]; exact hρle i hi
  obtain ⟨X', X'_inv, hX'r, hX'l, hlim⟩ :=
    matPow_G_tendsto_oneEigenProjector_of_convergence_and_complement_normal_form
      hrm G hCompl bV bW hEig1 hInvF' pblk hρ0 hρ1 hClower hCblock
  exact ⟨r, X', X'_inv, hX'r, hX'l, hlim⟩

end RealSpectrumExistence

-- ============================================================
-- §17.4  STATUS: the REAL-SPECTRUM `[106, Lem 6.9]` from convergence — CLOSED.
-- ============================================================
--
-- This module CLOSES the fully-unconditional real-spectrum semiconvergent block-form
-- existence of (17.22) from convergence of `Gᵐ` alone, discharging the single residual
-- IMPORT-level construction that `SemiconvergentExistenceComplete.lean` recorded.
--
-- • `basisActionMatrix_complement_eq_toMatrix_restrict` — the reindex identity named in
--   the closing STATUS block of `SemiconvergentExistenceComplete.lean`: the complement
--   block of the adapted-basis coordinate action matrix IS the `LinearMap.toMatrix` of
--   `G|_F`.  This is exactly what lets the real Schur reduction choose the complement
--   basis automatically.
--
-- • `orthogonalChangeOfBasis` / `toMatrix_orthogonalChangeOfBasis` — realise the
--   orthogonal similarity of the real Schur form `Qᵀ A Q` as a genuine complement basis,
--   so the upper-triangular Schur matrix becomes the coordinate complement action.
--
-- • `charpoly_restrict_dvd_of_isCompl` — descend the real-spectrum hypothesis to `G|_F`
--   (charpoly divisibility along the invariant splitting), WITHOUT any complexification /
--   ℂ→ℝ API (which is what the general obstruction of the split lacked).
--
-- • `restrict_upperTri_diag_abs_lt_one` — the strict diagonal modulus bound `|T_kk| < 1`
--   for the real-spectrum (genuinely upper-triangular) complement action, via the GAP (2)
--   dichotomy and the `E₁ ⊓ F = ⊥` exclusion of eigenvalue `1`.
--
-- • `semiconvergent_block_form_exists_of_convergence_real_spectrum` and
--   `matPow_G_tendsto_oneEigenProjector_of_convergence_real_spectrum` — the headline
--   results: from convergence of `Gᵐ` and real spectrum of `G`, the FULL block form of
--   (17.22) EXISTS and `Gᵐ → I − E` entrywise, with the ∞-norm contraction CONSTRUCTED,
--   and with NO supplied basis / column / contraction / spectral data.
--
-- HONEST SCOPE.  The real-spectrum hypothesis is genuine.  The general complex case is
-- PROVEN impossible in the repository's ∞-norm (row-sum) strengthening of (17.22)
-- (`twoByTwo_max_rowSum_ge_of_trace_det` of `SemiconvergentExistenceComplete.lean`: the
-- ∞-norm infimum over real similarities of a `2×2` block with eigenvalues `α ± βi` is
-- `|α| + |β|`, strictly larger than the spectral radius `√(α²+β²)` — e.g. `0.6 ± 0.6 i`
-- has `ρ = 0.849 < 1` yet every similar block has ∞-row-sum `≥ 1.2`).  Hence the ∞-norm
-- route closes EXACTLY the real-spectrum case, which is what this module delivers in full.
--
-- No `sorry`/`admit`/`axiom`/`unsafe`/`opaque`/`native_decide`/proof-disabling option is
-- used; the two headline theorems depend only on `[propext, Classical.choice, Quot.sound]`.

end NumStability
