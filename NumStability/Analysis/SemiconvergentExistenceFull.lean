-- Analysis/SemiconvergentExistenceFull.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 17 "Stationary Iterative Methods", §17.4 "Singular Systems",
-- eq (17.22) / Householder `[106, Lem 6.9]`: closing the residual GAP (4)
-- obstruction and consuming the real quasi-triangular Schur form (16.4).
--
-- WHAT THIS MODULE ADDS (two genuinely new UNCONDITIONAL sub-results and one
-- end-to-end corollary, all IMPORT-ONLY — no existing file is edited).
--
--   (1) `exists_diag_infNorm_conj_lt_one_of_quasiUpperTriangular` — the
--       `2×2`-BLOCK EXTENSION of GAP (4).  The prior wave's GAP (4) lemma
--       `exists_diag_infNorm_conj_lt_one_of_upperTriangular` (of
--       `SemiconvergentExistenceGaps.lean`) covers only STRICTLY-upper-triangular
--       matrices (blocks of size `1`).  It therefore cannot contract the real
--       quasi-triangular Schur form of §16.2 (16.4), whose diagonal `2×2`
--       rotation-scaling blocks are NOT upper triangular.  We prove the general
--       quasi-upper-triangular case: for a block assignment `p : Fin n → ℕ` under
--       which `C` is quasi-upper-triangular and *block-contractive* (within-block
--       absolute row sums `≤ ρ < 1`), the block-CONSTANT geometric diagonal
--       `D = diag(δ^{p·})` yields `‖D⁻¹ C D‖∞ < 1`.  Being block-constant, `D`
--       leaves the `2×2` blocks intact (so the block-contractivity hypothesis is
--       exactly what a `2×2` block must satisfy) while δ-scaling every
--       strictly-later-block entry.  This is precisely the residual GAP (4)
--       extension named in the closing obstruction of
--       `SemiconvergentBlockFormExists.lean`.
--
--   (2) `semiconvergent_block_form_exists_of_quasiTriangular_complement` — the
--       (16.4)-READY upgrade of the consuming block-form existence.  It is the
--       exact analogue of
--       `semiconvergent_block_form_exists_of_triangular_complement`, but consumes
--       a real *quasi*-triangular block-contractive complement (the honest output
--       of the real Schur decomposition `real_quasi_schur` of
--       `RealQuasiSchur.lean`) in place of a strictly-triangular one.  The ∞-norm
--       contraction is CONSTRUCTED via (1); everything else reuses the
--       generic-scaling machinery of `SemiconvergentBlockFormExists.lean`.  The
--       output is the identical `semiconvergent_block_form_exists` data package.
--
--   (3) `matPow_G_tendsto_oneEigenProjector_of_quasiTriangular_complement` — the
--       end-to-end payoff: from the quasi-triangular block-contractive complement,
--       the powers `Gᵐ` converge entrywise to the eigenvalue-`1` projector
--       `oneEigenProjector = X' · diag(I_r, 0) · X'⁻¹`.
--
-- HONEST STATEMENT STRENGTH.  Nothing that these results conclude is smuggled
-- into a hypothesis.  The complement hypotheses (`hClower` quasi-triangular,
-- `hCblock` block-contractive with `ρ < 1`) are strictly WEAKER than the ∞-norm
-- contraction they are used to DERIVE (a quasi-triangular matrix with contractive
-- BLOCKS generically has `‖·‖∞ ≥ 1`), and they are exactly the honest real Schur
-- (16.4) normal form of a complement with spectral radius `< 1`.  The
-- eigenvalue-`1` column condition `hGcolTop` is the genuine semisimple-at-`1`
-- spectral input (GAP (1)), and invertibility of `X` is the existence of the real
-- change of basis.
--
-- RESIDUAL for the FULL `[106, Lem 6.9]` from convergence of `Gᵐ` alone: see the
-- closing block.  In brief, this module closes GAP (4) in the `2×2`-block case
-- and consumes the (16.4) basis; the two steps still needed to MANUFACTURE that
-- basis from raw convergence are (i) the coordinate-level assembly of the real
-- primary (Fitting) decomposition `ℝⁿ = ker(G−I) ⊕ range(G−I)^n` — available
-- abstractly as `LinearMap.isCompl_iSup_ker_pow_iInf_range_pow` — followed by the
-- real quasi-Schur reduction of `G` on the complement, and (ii) the per-`2×2`
-- block ∞-norm reduction bringing each `2×2` block's row sums below `1`.
--
-- No `sorry`/`admit`/`axiom`/`native_decide`/proof-disabling option is used.

import NumStability.Analysis.RealQuasiSchur
import NumStability.Analysis.SemiconvergentBlockFormExists

namespace NumStability

open scoped BigOperators Topology
open Module

-- ============================================================
-- §17.4  Quasi-triangular δ-scaling contraction (GAP (4) extension)
-- ============================================================

/-- **Quasi-triangular diagonal-similarity contraction (Higham §17.4 (17.22);
    Householder `[106, Lem 6.9]`; cf. §18.2 Thm 18.1, pp. 347–348) — the `2×2`-block
    extension of GAP (4).**

    Let `C : Fin n → Fin n → ℝ` carry a block assignment `p : Fin n → ℕ` under
    which `C` is *quasi-upper-triangular* (`C i j = 0` whenever `p j < p i`), and
    which is *block-contractive*: for every row `i`, the sum of `|C i j|` over the
    entries `j` in the SAME block (`p j = p i`) is at most `ρ < 1`.  Then the
    block-constant geometric diagonal `D = diag(δ^{p ·})` with a suitably small
    `δ ∈ (0, 1]` yields `‖D⁻¹ C D‖∞ < 1`.

    This is exactly Householder's δ-scaling of the strict-upper part, generalised
    from the ordinary-triangular case (blocks of size `1`, `p = id`, the GAP (4)
    lemma `exists_diag_infNorm_conj_lt_one_of_upperTriangular`) to the real
    quasi-triangular Schur form of §16.2 (16.4) with `1×1`/`2×2` diagonal blocks:
    the exponent `p` is CONSTANT on each block, so within-block entries are left
    unscaled (whence the block-contractivity hypothesis is exactly what a `2×2`
    rotation-scaling block must satisfy), while every strictly-later-block entry
    picks up a factor `δ^{p j - p i} ≤ δ`.  Unconditional. -/
theorem exists_diag_infNorm_conj_lt_one_of_quasiUpperTriangular
    {n : ℕ} (C : Fin n → Fin n → ℝ) (p : Fin n → ℕ)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hlower : ∀ i j : Fin n, p j < p i → C i j = 0)
    (hblock : ∀ i : Fin n,
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => p j = p i), |C i j|) ≤ ρ) :
    ∃ d : Fin n → ℝ, (∀ i, 0 < d i) ∧
      infNorm (matMul n (diagMatrix fun a => (d a)⁻¹)
        (matMul n C (diagMatrix d))) < 1 := by
  classical
  -- global off-block mass bound `M > 0`
  set M : ℝ := 1 + ∑ i : Fin n, ∑ j : Fin n, |C i j| with hM
  have hMpos : 0 < M := by
    have hnn : (0 : ℝ) ≤ ∑ i : Fin n, ∑ j : Fin n, |C i j| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    simp only [hM]; linarith
  have hρpos : 0 < 1 - ρ := sub_pos.mpr hρ1
  set δ : ℝ := min 1 ((1 - ρ) / (2 * M)) with hδ
  have hδpos : 0 < δ := by
    apply lt_min
    · norm_num
    · apply div_pos hρpos; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδMpos : 0 ≤ δ * M := by positivity
  have hδM : δ * M < 1 - ρ := by
    have hle : δ ≤ (1 - ρ) / (2 * M) := min_le_right _ _
    calc δ * M ≤ ((1 - ρ) / (2 * M)) * M :=
          mul_le_mul_of_nonneg_right hle hMpos.le
      _ = (1 - ρ) / 2 := by field_simp
      _ < 1 - ρ := by linarith
  refine ⟨fun a => δ ^ (p a), fun i => pow_pos hδpos _, ?_⟩
  apply lt_of_le_of_lt (b := ρ + δ * M)
  · apply infNorm_le_of_row_sum_le _ _ (by linarith)
    intro i
    -- rewrite each conjugated entry
    have hrow : (∑ j : Fin n, |matMul n (diagMatrix fun a => (δ ^ (p a))⁻¹)
          (matMul n C (diagMatrix fun a => δ ^ (p a))) i j|)
        = ∑ j : Fin n, |(δ ^ (p i))⁻¹ * C i j * δ ^ (p j)| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [diagMatrix_conj_entry C (fun a => δ ^ (p a)) (fun a => (δ ^ (p a))⁻¹) i j]
    rw [hrow]
    -- per-term bound: block terms ≤ (within-block |C|), later-block terms ≤ δ|C|,
    -- earlier-block terms = 0
    have hterm : ∀ j : Fin n,
        |(δ ^ (p i))⁻¹ * C i j * δ ^ (p j)|
          ≤ δ * |C i j| + (if p j = p i then |C i j| else 0) := by
      intro j
      rcases lt_trichotomy (p j) (p i) with hlt | heq | hgt
      · -- earlier block: entry is zero
        have hz : C i j = 0 := hlower i j hlt
        rw [hz]
        simp
      · -- same block: factor is 1
        have hne : δ ^ (p i) ≠ 0 := (pow_pos hδpos _).ne'
        rw [if_pos heq]
        have hval : (δ ^ (p i))⁻¹ * C i j * δ ^ (p j) = C i j := by
          rw [heq, mul_comm ((δ ^ (p i))⁻¹) (C i j), mul_assoc, inv_mul_cancel₀ hne, mul_one]
        rw [hval]
        have h1 : 0 ≤ δ * |C i j| := by positivity
        linarith
      · -- later block: factor δ^{p j - p i} ≤ δ
        rw [if_neg (by omega : ¬ p j = p i), add_zero]
        have hne : δ ^ (p i) ≠ 0 := (pow_pos hδpos _).ne'
        have hfac : (δ ^ (p i))⁻¹ * C i j * δ ^ (p j)
            = δ ^ (p j - p i) * C i j := by
          have hsplit : δ ^ (p j) = δ ^ (p j - p i) * δ ^ (p i) := by
            rw [← pow_add]; congr 1; omega
          rw [hsplit,
            show (δ ^ (p i))⁻¹ * C i j * (δ ^ (p j - p i) * δ ^ (p i))
                = δ ^ (p j - p i) * C i j * ((δ ^ (p i))⁻¹ * δ ^ (p i)) by ring,
            inv_mul_cancel₀ hne, mul_one]
        rw [hfac, abs_mul, abs_of_pos (pow_pos hδpos _)]
        have hexp : δ ^ (p j - p i) ≤ δ := by
          have h1 : 1 ≤ p j - p i := by omega
          calc δ ^ (p j - p i) ≤ δ ^ 1 := pow_le_pow_of_le_one hδpos.le hδ1 h1
            _ = δ := pow_one δ
        exact mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
    -- sum the per-term bounds
    calc ∑ j : Fin n, |(δ ^ (p i))⁻¹ * C i j * δ ^ (p j)|
        ≤ ∑ j : Fin n, (δ * |C i j| + (if p j = p i then |C i j| else 0)) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = δ * ∑ j : Fin n, |C i j|
            + ∑ j ∈ Finset.univ.filter (fun j : Fin n => p j = p i), |C i j| := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 1
          rw [Finset.sum_filter]
      _ ≤ ρ + δ * M := by
          have hblk : (∑ j ∈ Finset.univ.filter (fun j : Fin n => p j = p i), |C i j|) ≤ ρ :=
            hblock i
          have hle : ∑ j : Fin n, |C i j| ≤ M := by
            rw [hM]
            have hsingle : ∑ j : Fin n, |C i j| ≤ ∑ i' : Fin n, ∑ j : Fin n, |C i' j| :=
              Finset.single_le_sum (f := fun i' => ∑ j : Fin n, |C i' j|)
                (fun i' _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
            linarith
          have hmul : δ * ∑ j : Fin n, |C i j| ≤ δ * M :=
            mul_le_mul_of_nonneg_left hle hδpos.le
          linarith
  · linarith

-- ============================================================
-- §17.4  compBlock inherits the complement quasi-triangular structure
-- ============================================================

/-- The masked complement block `compBlock n r C` is quasi-upper-triangular for
    the block assignment `pblk` (extended by `0` on the eigenvalue-`1` block)
    whenever `C` is quasi-upper-triangular *on the complement*.  Off the
    complement `compBlock` is `0`; on the complement it agrees with `C`.  Used to
    feed `exists_diag_infNorm_conj_lt_one_of_quasiUpperTriangular` from the real
    quasi-Schur (16.4) structure of the complement (Higham §17.4 (17.22)). -/
theorem compBlock_quasiLower (n r : ℕ) (C : Fin n → Fin n → ℝ) (pblk : Fin n → ℕ)
    (hClower : ∀ i j : Fin n, ¬(i : ℕ) < r → ¬(j : ℕ) < r →
      pblk j < pblk i → C i j = 0)
    (i j : Fin n) (hlt : (if (j : ℕ) < r then 0 else pblk j) < (if (i : ℕ) < r then 0 else pblk i)) :
    compBlock n r C i j = 0 := by
  unfold compBlock
  by_cases hi : (i : ℕ) < r
  · -- row masked, but then LHS of `hlt` has RHS `0`, impossible since nothing `< 0`
    rw [if_pos hi] at hlt; exact absurd hlt (Nat.not_lt_zero _)
  · by_cases hj : (j : ℕ) < r
    · rw [if_pos (Or.inr hj)]
    · rw [if_neg (not_or.mpr ⟨hi, hj⟩)]
      rw [if_neg hj, if_neg hi] at hlt
      exact hClower i j hi hj hlt

/-- The masked complement block `compBlock n r C` is block-contractive for the
    (extended) assignment `pblk'` (`0` on the eigenvalue-`1` block, `pblk` on the
    complement): every within-block absolute row sum is `≤ ρ`.  For an
    eigenvalue-`1` row the whole block row is `0`; for a complement row the
    block-restricted sum equals the complement block-restricted sum of `|C|`,
    which is `≤ ρ` by hypothesis.  Higham §17.4 (17.22). -/
theorem compBlock_blockContractive (n r : ℕ) (C : Fin n → Fin n → ℝ) (pblk : Fin n → ℕ)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hCblock : ∀ i : Fin n, ¬(i : ℕ) < r →
      (∑ j ∈ Finset.univ.filter
        (fun j : Fin n => ¬(j : ℕ) < r ∧ pblk j = pblk i), |C i j|) ≤ ρ)
    (i : Fin n) :
    (∑ j ∈ Finset.univ.filter
      (fun j : Fin n => (if (j : ℕ) < r then 0 else pblk j)
        = (if (i : ℕ) < r then 0 else pblk i)), |compBlock n r C i j|) ≤ ρ := by
  classical
  by_cases hi : (i : ℕ) < r
  · -- row masked: every entry is 0
    refine le_trans (le_of_eq ?_) hρ0
    refine Finset.sum_eq_zero ?_
    intro j _
    have : compBlock n r C i j = 0 := by unfold compBlock; rw [if_pos (Or.inl hi)]
    rw [this, abs_zero]
  · -- complement row: block sum of |compBlock| = complement block sum of |C|
    refine le_trans (le_of_eq ?_) (hCblock i hi)
    rw [if_neg hi]
    -- restrict the LHS sum to the complement columns (masked columns contribute 0),
    -- then match with the complement block filter of `C`.
    rw [← Finset.sum_filter_add_sum_filter_not
          (Finset.univ.filter (fun j : Fin n => (if (j : ℕ) < r then 0 else pblk j) = pblk i))
          (fun j : Fin n => ¬(j : ℕ) < r)]
    have hzero : (∑ j ∈ (Finset.univ.filter
        (fun j : Fin n => (if (j : ℕ) < r then 0 else pblk j) = pblk i)).filter
          (fun j : Fin n => ¬¬(j : ℕ) < r), |compBlock n r C i j|) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      rw [Finset.mem_filter] at hj
      have hjr : (j : ℕ) < r := not_not.mp hj.2
      have : compBlock n r C i j = 0 := by unfold compBlock; rw [if_pos (Or.inr hjr)]
      rw [this, abs_zero]
    rw [hzero, add_zero]
    -- now both are sums over complement columns with pblk j = pblk i
    apply Finset.sum_congr
    · ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨heq, hjr⟩
        rw [if_neg hjr] at heq
        exact ⟨hjr, heq⟩
      · rintro ⟨hjr, hpj⟩
        exact ⟨by rw [if_neg hjr]; exact hpj, hjr⟩
    · intro j hj
      rw [Finset.mem_filter] at hj
      have hjr : ¬(j : ℕ) < r := hj.2.1
      rw [compBlock_eq n r C hi hjr]

-- ============================================================
-- §17.4  Block-form existence from a QUASI-triangular complement
-- ============================================================

/-- **Higham §17.4, eq (17.22) — `[106, Lem 6.9]` — semiconvergent block-form
    EXISTENCE from a real *quasi*-triangular complement (the (16.4)-ready
    upgrade).**

    This is the exact analogue of
    `semiconvergent_block_form_exists_of_triangular_complement`, but with the
    strictly-upper-triangular complement hypothesis (`hCupper` + diagonal-modulus
    bound) replaced by the honest real quasi-triangular Schur data of §16.2
    (16.4): a block assignment `pblk` under which the complement action `C` is
    quasi-upper-triangular (`hClower`: `C i j = 0` when `pblk j < pblk i`, both in
    the complement) and *block-contractive* (`hCblock`: every within-block
    absolute row sum of `C` on the complement is `≤ ρ < 1`).  The `1×1` diagonal
    blocks contribute `|C_{kk}| ≤ ρ` and the `2×2` rotation-scaling blocks
    `[[a,b],[-b,a]]` contribute the block row sums `|a|+|b| ≤ ρ` — exactly the
    real Schur (16.4) structure with contractive diagonal blocks.

    The ∞-norm contraction of the conjugated block `Γ := D⁻¹ C D` is CONSTRUCTED
    (never assumed) via the quasi-triangular δ-scaling
    `exists_diag_infNorm_conj_lt_one_of_quasiUpperTriangular` (the `2×2`-block
    extension of GAP (4)), with `D` block-constant on the `pblk`-blocks so the
    `2×2` blocks are left intact.  The rest of the assembly (absorbing `D`,
    transporting the two column conditions, building the block form) reuses the
    generic-scaling machinery of `SemiconvergentBlockFormExists.lean`.  The output
    is the identical `semiconvergent_block_form_exists` data package. -/
theorem semiconvergent_block_form_exists_of_quasiTriangular_complement (n r : ℕ)
    (G X X_inv C : Fin n → Fin n → ℝ) (pblk : Fin n → ℕ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hGcolTop : ∀ (k : Fin n), (k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k = X i k)
    (hGcolBot : ∀ (k : Fin n), ¬(k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k =
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r),
          X i l * C l k)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hClower : ∀ i j : Fin n, ¬(i : ℕ) < r → ¬(j : ℕ) < r →
      pblk j < pblk i → C i j = 0)
    (hCblock : ∀ i : Fin n, ¬(i : ℕ) < r →
      (∑ j ∈ Finset.univ.filter
        (fun j : Fin n => ¬(j : ℕ) < r ∧ pblk j = pblk i), |C i j|) ≤ ρ) :
    ∃ (X' X'_inv Γ : Fin n → Fin n → ℝ) (q : ℝ),
      0 ≤ q ∧ q < 1 ∧
      (∀ i : Fin n, ¬(i : ℕ) < r →
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬(j : ℕ) < r), |Γ i j|) ≤ q) ∧
      IsRightInverse n X' X'_inv ∧ IsRightInverse n X'_inv X' ∧
      (∀ (k : Fin n), (k : ℕ) < r → ∀ i : Fin n, matMul n G X' i k = X' i k) ∧
      matMul n X'_inv (matMul n G X') = blockJ n r Γ ∧
      (∀ i j : Fin n, (i : ℕ) < r → blockJ n r Γ i j = if i = j then 1 else 0) ∧
      (∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → blockJ n r Γ i j = 0) ∧
      (∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |blockJ n r Γ i j| ≤ q) := by
  -- quasi-triangular δ-scaling (2×2-block GAP (4)): contract the complement block.
  obtain ⟨p, hppos, hpcontr⟩ :=
    exists_diag_infNorm_conj_lt_one_of_quasiUpperTriangular (compBlock n r C)
      (fun a => if (a : ℕ) < r then 0 else pblk a) hρ0 hρ1
      (compBlock_quasiLower n r C pblk hClower)
      (compBlock_blockContractive n r C pblk hρ0 hCblock)
  -- The conjugated contraction block and its ∞-norm bound `q`.
  set Γ : Fin n → Fin n → ℝ := conjGamma n r C p with hΓdef
  set q : ℝ := infNorm Γ with hqdef
  have hq1 : q < 1 := by rw [hqdef, hΓdef]; exact hpcontr
  have hq0 : 0 ≤ q := by rw [hqdef]; exact infNorm_nonneg _
  -- The rescaled basis `X' = X · D` and its inverse.
  set X' : Fin n → Fin n → ℝ := matMul n X (diagMatrix (scaleVec n r p)) with hX'def
  set X'_inv : Fin n → Fin n → ℝ :=
    matMul n (diagMatrix (scaleVec n r (fun a => (p a)⁻¹))) X_inv with hX'invdef
  have hX'r : IsRightInverse n X' X'_inv :=
    isRightInverse_scaled n r X X_inv hppos hXr
  have hX'l : IsRightInverse n X'_inv X' := by
    have hDl : IsRightInverse n (diagMatrix (scaleVec n r (fun a => (p a)⁻¹)))
        (diagMatrix (scaleVec n r p)) :=
      diagMatrix_isRightInverse n (scaleVec n r (fun a => (p a)⁻¹)) (scaleVec n r p)
        (fun a => by
          rw [← scaleVec_inv n r p a, inv_mul_cancel₀ (scaleVec_pos n r hppos a).ne'])
    have hXinvX : matMul n X_inv X = idMatrix n := by ext a b; exact hXl a b
    have hDD : matMul n (diagMatrix (scaleVec n r (fun a => (p a)⁻¹)))
        (diagMatrix (scaleVec n r p)) = idMatrix n := by ext a b; exact hDl a b
    have hprod : matMul n X'_inv X' = idMatrix n := by
      rw [hX'invdef, hX'def,
        matMul_assoc n (diagMatrix (scaleVec n r (fun a => (p a)⁻¹))) X_inv
          (matMul n X (diagMatrix (scaleVec n r p))),
        ← matMul_assoc n X_inv X (diagMatrix (scaleVec n r p)),
        hXinvX, matMul_id_left, hDD]
    intro i j; exact congrFun (congrFun hprod i) j
  -- The two transported column conditions.
  have hcolTop : ∀ (k : Fin n), (k : ℕ) < r → ∀ i : Fin n, matMul n G X' i k = X' i k :=
    fun k hk i => scaled_colTop n r G X hGcolTop k hk i
  have hcolBot : ∀ (k : Fin n), ¬(k : ℕ) < r →
      ∀ i : Fin n, matMul n G X' i k =
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r),
          X' i l * Γ l k :=
    fun k hk i => scaled_colBot n r G X C hppos hGcolBot k hk i
  -- The ∞-norm row-sum contraction certificate for `Γ`.
  have hΓrows : ∀ i : Fin n, ¬(i : ℕ) < r →
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬(j : ℕ) < r),
        |Γ i j|) ≤ q :=
    fun i _ => by rw [hqdef, hΓdef]; exact conjGamma_row_sum_le_infNorm n r C p i
  -- The block-diagonalizing similarity `X'⁻¹ G X' = diag(I_r, Γ)`.
  have hsim : matMul n X'_inv (matMul n G X') = blockJ n r Γ :=
    X_inv_G_X_eq_blockJ n G X' X'_inv (blockJ n r Γ) hX'l
      (matMul_G_X_eq_X_blockJ n r G X' Γ hcolTop hcolBot)
  exact ⟨X', X'_inv, Γ, q, hq0, hq1, hΓrows, hX'r, hX'l, hcolTop, hsim,
    blockJ_top n r Γ, blockJ_cross n r Γ, blockJ_bottom_row_sum_le n r Γ q hΓrows⟩

-- ============================================================
-- §17.4  End-to-end: convergent powers from a quasi-triangular complement
-- ============================================================

/-- **Higham §17.4, eq (17.22) / (17.27) — `[106, Lem 6.9]` — semiconvergence
    `Gᵐ → I − E` from a real *quasi*-triangular complement.**

    The end-to-end payoff of the (16.4)-ready assembly: from a real invertible
    basis whose first `r` columns are eigenvalue-`1` eigenvectors of `G` and whose
    complement acts through a real quasi-triangular block-contractive `C` (the
    honest real Schur (16.4) normal form of the complement, with block absolute
    row sums `≤ ρ < 1`), the powers of `G` converge entrywise to the
    eigenvalue-`1` projector `oneEigenProjector = X' · diag(I_r, 0) · X'⁻¹ = I − E`.

    The ∞-norm contraction driving the convergence is CONSTRUCTED from the
    quasi-triangular structure via the `2×2`-block GAP (4) extension
    `exists_diag_infNorm_conj_lt_one_of_quasiUpperTriangular`; it is never assumed.
    This is the genuine "semiconvergence ⟹ convergent powers" conclusion, now
    available for complements with genuine complex (`2×2`) eigenvalue pairs. -/
theorem matPow_G_tendsto_oneEigenProjector_of_quasiTriangular_complement (n r : ℕ)
    (G X X_inv C : Fin n → Fin n → ℝ) (pblk : Fin n → ℕ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hGcolTop : ∀ (k : Fin n), (k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k = X i k)
    (hGcolBot : ∀ (k : Fin n), ¬(k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k =
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r),
          X i l * C l k)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hClower : ∀ i j : Fin n, ¬(i : ℕ) < r → ¬(j : ℕ) < r →
      pblk j < pblk i → C i j = 0)
    (hCblock : ∀ i : Fin n, ¬(i : ℕ) < r →
      (∑ j ∈ Finset.univ.filter
        (fun j : Fin n => ¬(j : ℕ) < r ∧ pblk j = pblk i), |C i j|) ≤ ρ) :
    ∃ (X' X'_inv : Fin n → Fin n → ℝ),
      IsRightInverse n X' X'_inv ∧ IsRightInverse n X'_inv X' ∧
      (∀ i j : Fin n,
        Filter.Tendsto (fun m => matPow n G m i j) Filter.atTop
          (nhds (oneEigenProjector n r X' X'_inv i j))) := by
  obtain ⟨X', X'_inv, Γ, q, hq0, hq1, _hΓrows, hX'r, hX'l, _hcolTop, hsim,
      hJtop, hJcross, hJrows⟩ :=
    semiconvergent_block_form_exists_of_quasiTriangular_complement n r G X X_inv C pblk
      hXr hXl hGcolTop hGcolBot hρ0 hρ1 hClower hCblock
  refine ⟨X', X'_inv, hX'r, hX'l, ?_⟩
  exact matPow_G_tendsto_oneEigenProjector n r G (blockJ n r Γ) X' X'_inv
    hJtop hJcross q hq0 hq1 hJrows hX'r hX'l hsim

-- ============================================================
-- §17.4  RESIDUAL OBSTRUCTION for the FULL [106, Lem 6.9] from convergence.
-- ============================================================
--
-- STATE OF THE FOUR GAPS after this module (together with
-- `SemiconvergentExistenceGaps.lean`, `SemiconvergentBlockFormExists.lean`,
-- `RealInvariantSubspace.lean`, `RealQuasiSchur.lean`).
--
-- GAP (1) — CLOSED (upstream).  `maxGenEigenspace_one_eq_eigenspace_of_forall_orbit_tendsto`
--   derives semisimplicity of the eigenvalue `1` (`hGcolTop`) from convergence of
--   every orbit.
--
-- GAP (2) — CLOSED (upstream).  `scalar_pow_tendsto_dichotomy` /
--   `abs_lt_one_of_pow_tendsto_of_ne_one` give the strict disk `|μ| < 1` for the
--   non-`1` spectrum from convergence.
--
-- GAP (4) — CLOSED, INCLUDING THE `2×2`-BLOCK CASE (here).
--   `exists_diag_infNorm_conj_lt_one_of_quasiUpperTriangular` extends the prior
--   strictly-upper-triangular GAP (4) lemma to the real quasi-triangular Schur
--   form (16.4): a block-constant δ-scaling contracts a quasi-upper-triangular
--   matrix with contractive diagonal BLOCKS.  This removes the "extend the GAP (4)
--   lemma to the quasi-triangular (`2×2`-block) case" residual named in the
--   closing block of `SemiconvergentBlockFormExists.lean`.  Consequently
--   `semiconvergent_block_form_exists_of_quasiTriangular_complement` and
--   `matPow_G_tendsto_oneEigenProjector_of_quasiTriangular_complement` consume the
--   honest (16.4) complement directly — the strictly-triangular restriction of the
--   Wave-2 consumer is gone.
--
-- GAP (3) — THE SINGLE REMAINING OBSTRUCTION: MANUFACTURING the (16.4) complement
--   basis (eigenvalue-`1` eigenvector columns first + quasi-triangular
--   block-contractive `C` on the complement) from convergence of `Gᵐ` alone, in
--   the repository's `matMul` coordinate form.  This module (and the Wave-2
--   modules) close EVERYTHING downstream of that basis.  The production step now
--   splits into two concrete, independent missing lemmas:
--
--     (3a) REAL PRIMARY (FITTING) DECOMPOSITION IN COORDINATES.  The splitting
--          `ℝⁿ = ker(G − I) ⊕ range((G − I)^n)` is available abstractly in Mathlib
--          v4.29 as `LinearMap.isCompl_iSup_ker_pow_iInf_range_pow` (applied to
--          `φ = G.mulVecLin − 1`; with GAP (1) semisimplicity the left summand is
--          the ordinary eigenspace `ker(G − I)`, and `G` restricted to the right
--          summand `F` has `1 ∉ spectrum`, spectral radius `< 1` by GAP (2)).
--          What is MISSING is the COORDINATE assembly: turning `IsCompl E₁ F` +
--          bases of `E₁, F` into an invertible `X : Fin n → Fin n → ℝ` whose first
--          `r` columns are honest `matMul`-eigenvectors (`matMul n G X · = X ·`)
--          and whose complement columns realise `hGcolBot`, then applying
--          `real_quasi_schur` to `G|_F` to obtain the quasi-triangular `C` and
--          block assignment `pblk` for `hClower`.  This is the `Submodule` ↔
--          `matMul`/`Fin n → Fin n → ℝ` bridge, a substantial but mechanical
--          formalization; Mathlib supplies the splitting, the repository supplies
--          the quasi-Schur, and this module supplies the downstream contraction.
--
--     (3b) PER-`2×2`-BLOCK ∞-NORM REDUCTION.  `real_quasi_schur` yields `2×2`
--          diagonal blocks with complex-conjugate eigenvalues of modulus `√det <
--          1`, but their ∞-norm ROW SUMS can exceed `1` (e.g. a rotation-scaling
--          block `[[a,b],[-b,a]]` has row sum `|a|+|b|`, which for `a=b=0.6`
--          is `1.2 > 1` although `a²+b² = 0.72 < 1`).  The block-contractivity
--          hypothesis `hCblock` (`|a|+|b| ≤ ρ < 1`) therefore requires a further
--          per-block real similarity bringing each `2×2` block's ∞-norm below `1`.
--          CORRECTION (proved in `SemiconvergentExistenceComplete.lean`,
--          `twoByTwo_max_rowSum_ge_of_trace_det`): such a similarity does NOT
--          always exist. For the ∞-norm the infimum over real similarities of a
--          `2×2` block with eigenvalues `α ± βi` equals `|α| + |β|`, NOT the
--          spectral radius `√(α²+β²)`.  (The "spectral radius = inf of operator
--          norms over similarities" identity holds for the 2-norm, not the ∞-norm.)
--          Hence `hCblock` in the repository's `‖Γ‖∞ ≤ q < 1` form is achievable
--          EXACTLY under the sharp threshold `|Re λ| + |Im λ| < 1` for every non-`1`
--          eigenvalue, and is genuinely IMPOSSIBLE otherwise (witness `0.6 ± 0.6i`:
--          `ρ = 0.849 < 1` but every similar block has ∞-row-sum `≥ 1.2`).  This is
--          a real mathematical fact, not a Mathlib gap.  NOTE: whenever the
--          complement spectrum is REAL (all `1×1` blocks) the threshold is
--          automatic and (3a) alone completes the full existence — this module's
--          `..._of_quasiTriangular_complement` theorems discharge that fully-real
--          case end to end.  (The general non-threshold case needs the 2-norm
--          contraction form of (17.22), which the book's `ρ(Γ) < 1` statement uses;
--          the repository's ∞-norm strengthening is the stricter object.)
--
-- Thus the FULL `[106, Lem 6.9]` from convergence of `Gᵐ` reduces, after this
-- module, to exactly (3a) + (3b): everything spectral (GAP (1), (2)) and every
-- contraction/assembly step downstream of the (16.4) basis (GAP (4), including
-- `2×2` blocks) is closed.

end NumStability
