-- Analysis/SemiconvergentLimitGeneral.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 17 "Stationary Iterative Methods", §17.4 "Singular Systems",
-- eq (17.22) / (17.25) / Householder `[106, Lem 6.9]`.
--
-- GOAL — the HONEST, GENERAL-COMPLEX closure of the semiconvergence LIMIT
-- `Gᵐ → I − E = X · diag(I_r, 0) · X⁻¹` for an ARBITRARY real iteration matrix
-- `G` (NO real-spectrum restriction), via the SPECTRAL-RADIUS object `ρ(Γ) < 1`
-- (Higham's printed (17.22) condition) — NOT the ∞-norm strengthening
-- `‖Γ‖∞ < 1`, which the prior wave PROVED is UNACHIEVABLE for a
-- complex-conjugate eigenpair `α ± β i` with `|α| + |β| ≥ 1`
-- (`twoByTwo_max_rowSum_ge_of_trace_det` in
-- `Analysis/SemiconvergentExistenceComplete.lean`).  The ∞-norm was only a
-- convenience for a squeeze; the honest limit needs only `ρ(Γ) < 1`.
--
-- TWO ENTRY POINTS, both honest, both handling arbitrary complex spectrum.
--
--   (A) `matPow_G_tendsto_oneEigenProjector_of_convergence` — the HEADLINE,
--       UNCONDITIONAL from convergence of every orbit `Gᵐ x`.  From convergence
--       alone (via the real primary splitting `⊤ = E₁ ⊕ F` and the block form of
--       `Analysis/SemiconvergentExistenceComplete.lean`), the complement action
--       block `C = basisActionMatrix G (adaptedBasis …)` has NO nonzero
--       eigenvalue-`1` vector supported on the complement (`compBlock_no_comp_fixed`,
--       proved here from the direct-sum splitting), which forces the entrywise
--       limit of the block-diagonal powers `diag(I_r, C)ᵐ` to be `diag(I_r, 0)`.
--       This closes the [106] LIMIT from convergence with NEITHER a spectral
--       hypothesis NOR an ∞-norm hypothesis NOR any ℂ→ℝ descent — purely at the
--       real-linear-algebra level, in FULL generality.
--
--   (B) `matPow_G_tendsto_oneEigenProjector_of_spectralRadius` — the printed
--       (17.22) route: from the block form and `ρ(Γ) < 1` (the genuine
--       `spectralRadius` of the complexified complement block, Higham's condition
--       verbatim), Gelfand's formula gives `Cᵐ → 0` and hence the same limit.
--       The `spectralRadius(complement) < 1` intermediate
--       (`matPow_blockJ_tendsto_topProjector_of_spectralRadius`) is exposed
--       separately, as requested.
--
-- Both feed the block-diagonal power split `diag(I_r, C)ᵐ = diag(I_r, Cᵐ)` and the
-- similarity transport `Gᵐ = X · diag(I_r, C)ᵐ · X⁻¹` (repository `matPow`), and
-- both conclude `Tendsto (fun m => (Gᵐ) i j) atTop (𝓝 (oneEigenProjector … i j))`.
--
-- IMPORT-ONLY: this module edits nothing.  No `sorry`/`admit`/`axiom`/`unsafe`/
-- `opaque`/`native_decide`/proof-disabling option is used.
--
-- Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*,
-- 2nd ed., §17.4, eqs (17.22)/(17.25); Householder `[106, Lem 6.9]`.

import NumStability.Analysis.SemiconvergentExistenceComplete
import NumStability.Algorithms.MatrixPowersSpectral

namespace NumStability

open scoped BigOperators Topology Matrix
open Module

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

-- ============================================================
-- §17.4  A. Gelfand: `Cᵐ → 0` from `spectralRadius(Ĉ) < 1`
-- ============================================================

/-- The complexification of a real function-matrix as a Mathlib `ℂ`-matrix.  Its
    `spectralRadius` is Higham's `ρ(Γ)` of eq (17.22) for the real block `Γ`. -/
noncomputable def complexifyMat (n : ℕ) (B : Fin n → Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.of B).map Complex.ofReal

/-- The ∞-operator-norm of the complexified `k`-th power equals the repository
    ∞-norm of the real `k`-th power.  Bridges the repository `matPow`/`infNorm`
    to the Mathlib Banach-algebra norm used by Gelfand's formula.  Higham §17.4
    (17.22). -/
theorem norm_complexifyMat_pow (n : ℕ) (B : Fin n → Fin n → ℝ) (k : ℕ) :
    ‖(complexifyMat n B) ^ k‖ = infNorm (matPow n B k) := by
  rw [complexifyMat, ← map_ofReal_pow, linfty_opNorm_map_ofReal,
    infNorm_eq_linfty_opNorm, matPow_eq_matrix_pow]

/-- Each matrix entry is bounded in absolute value by the ∞-norm (max row sum) of
    the matrix.  Auxiliary to the entrywise power decay of Higham §17.4 (17.22). -/
theorem abs_entry_le_infNorm {n : ℕ} (A : Fin n → Fin n → ℝ) (i j : Fin n) :
    |A i j| ≤ infNorm A :=
  le_trans (Finset.single_le_sum (fun k _ => abs_nonneg (A i k)) (Finset.mem_univ j))
    (row_sum_le_infNorm A i)

/-- **Gelfand extraction of a geometric power bound.**  If `spectralRadius ℂ Ĉ`
    of the complexified real matrix `B` is `< ENNReal.ofReal r` with `0 < r`, then
    eventually `‖Bᵐ‖∞ ≤ rᵐ`.  This is Gelfand's formula
    `‖Ĉᵐ‖^{1/m} → spectralRadius` transported to the repository ∞-norm via
    `norm_complexifyMat_pow`.  Higham §17.4 (17.22) — the `ρ(Γ) < 1` route. -/
theorem eventually_matPow_infNorm_le_of_spectralRadius_lt (n : ℕ)
    (B : Fin n → Fin n → ℝ) {r : ℝ} (hr0 : 0 < r)
    (hspec : spectralRadius ℂ (complexifyMat n B) < ENNReal.ofReal r) :
    ∀ᶠ k in Filter.atTop, infNorm (matPow n B k) ≤ r ^ k := by
  haveI hfd : FiniteDimensional ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.finiteDimensional
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  have hgel := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexifyMat n B)
  have hev : ∀ᶠ (k : ℕ) in Filter.atTop,
      ENNReal.ofReal (‖(complexifyMat n B) ^ k‖ ^ (1 / (k:ℝ))) < ENNReal.ofReal r :=
    hgel.eventually_lt_const hspec
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with k hk hk1
  have hklt : ‖(complexifyMat n B) ^ k‖ ^ (1 / (k:ℝ)) < r :=
    (ENNReal.ofReal_lt_ofReal_iff hr0).mp hk
  have hknorm0 : (0:ℝ) ≤ ‖(complexifyMat n B) ^ k‖ := norm_nonneg _
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
  have hroot : ‖(complexifyMat n B) ^ k‖
      = (‖(complexifyMat n B) ^ k‖ ^ (1 / (k:ℝ))) ^ (k:ℕ) := by
    rw [← Real.rpow_natCast (‖(complexifyMat n B) ^ k‖ ^ (1 / (k:ℝ))) k,
      ← Real.rpow_mul hknorm0, one_div, inv_mul_cancel₀ (ne_of_gt hkR), Real.rpow_one]
  have hle : ‖(complexifyMat n B) ^ k‖ ≤ r ^ k := by
    rw [hroot]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hknorm0 _) (le_of_lt hklt) k
  rw [norm_complexifyMat_pow] at hle
  exact hle

/-- **Entrywise `Bᵐ → 0` from `spectralRadius(B̂) < 1`** (Higham §17.4 (17.22), the
    `ρ(Γ) < 1` route).  For a real matrix `B` whose complexification has spectral
    radius `< 1`, every entry of the power `Bᵐ` tends to `0`.  Proof: pick `r`
    with `ρ < r < 1` (`ENNReal.lt_iff_exists_real_btwn`); Gelfand gives
    `‖Bᵐ‖∞ ≤ rᵐ` eventually; squeeze `|Bᵐ_{ij}| ≤ ‖Bᵐ‖∞ ≤ rᵐ → 0`. -/
theorem matPow_tendsto_zero_of_spectralRadius_lt_one (n : ℕ)
    (B : Fin n → Fin n → ℝ)
    (hspec : spectralRadius ℂ (complexifyMat n B) < 1) (i j : Fin n) :
    Filter.Tendsto (fun m => matPow n B m i j) Filter.atTop (nhds 0) := by
  obtain ⟨r, _hr0', hrspec, hr1'⟩ := ENNReal.lt_iff_exists_real_btwn.mp hspec
  have hr0 : 0 < r := by
    by_contra h
    push_neg at h
    rw [ENNReal.ofReal_of_nonpos h] at hrspec
    exact (not_lt_bot hrspec).elim
  have hr1 : r < 1 := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp] at hr1'
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mp hr1'
  have hev := eventually_matPow_infNorm_le_of_spectralRadius_lt n B hr0 hrspec
  have hbound : ∀ᶠ m in Filter.atTop, ‖matPow n B m i j‖ ≤ r ^ m := by
    filter_upwards [hev] with m hm
    rw [Real.norm_eq_abs]
    exact le_trans (abs_entry_le_infNorm (matPow n B m) i j) hm
  exact squeeze_zero_norm' hbound
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1)

-- ============================================================
-- §17.4  B. Block-diagonal power split `diag(I_r, C)ᵐ = diag(I_r, Cᵐ)`
-- ============================================================
--
-- `blockJ n r C = diag(I_r, Γ)` (the printed (17.22) `J`) decomposes as the sum
-- of the eigenvalue-`1` projector `topProjector n r` and the complement-masked
-- block `compBlock n r C`; the two blocks annihilate each other, so the powers
-- split.  `topProjector` and `compBlock` are reused verbatim from
-- `StationaryIterationSemiconvergent.lean` / `SemiconvergentBlockFormExists.lean`.

/-- `blockJ n r C = topProjector n r + compBlock n r C`, entrywise: the
    block-diagonal `diag(I_r, Γ)` is the sum of its eigenvalue-`1` identity block
    and its complement block.  Higham §17.4 (17.22). -/
theorem blockJ_eq_topProjector_add_compBlock (n r : ℕ) (C : Fin n → Fin n → ℝ) :
    blockJ n r C = fun i j => topProjector n r i j + compBlock n r C i j := by
  funext i j
  unfold blockJ topProjector compBlock
  by_cases hi : (i : ℕ) < r
  · rw [if_pos hi, if_pos (Or.inl hi)]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos ⟨hij, hi⟩, add_zero]
    · rw [if_neg hij, if_neg (fun h => hij h.1), add_zero]
  · rw [if_neg hi]
    by_cases hj : (j : ℕ) < r
    · rw [if_pos hj, if_pos (Or.inr hj), if_neg (fun h => hi h.2), zero_add]
    · rw [if_neg hj, if_neg (not_or.mpr ⟨hi, hj⟩), if_neg (fun h => hi h.2), zero_add]

/-- `topProjector · compBlock = 0`: the eigenvalue-`1` projector kills the
    complement block (its top rows pick out complement rows, which vanish).
    Higham §17.4 (17.22). -/
theorem topProjector_mul_compBlock (n r : ℕ) (C : Fin n → Fin n → ℝ) :
    matMul n (topProjector n r) (compBlock n r C) = fun _ _ => 0 := by
  funext i j
  by_cases hi : (i : ℕ) < r
  · rw [matMul_row_id n (topProjector n r) (compBlock n r C) i j
      (topProjector_apply_top hi)]
    unfold compBlock; rw [if_pos (Or.inl hi)]
  · rw [matMul_row_zero n (topProjector n r) (compBlock n r C) i j
      (topProjector_apply_bottom hi)]

/-- `compBlock · topProjector = 0`: the complement block kills the eigenvalue-`1`
    projector (its complement columns meet only complement rows of the projector,
    which vanish).  Higham §17.4 (17.22). -/
theorem compBlock_mul_topProjector (n r : ℕ) (C : Fin n → Fin n → ℝ) :
    matMul n (compBlock n r C) (topProjector n r) = fun _ _ => 0 := by
  funext i j
  show (∑ k : Fin n, compBlock n r C i k * topProjector n r k j) = 0
  refine Finset.sum_eq_zero ?_
  intro k _
  by_cases hk : (k : ℕ) < r
  · unfold compBlock; rw [if_pos (Or.inr hk), zero_mul]
  · rw [topProjector_apply_bottom hk, mul_zero]

/-- **Block-diagonal power identity** `diag(I_r, Γ)^{m+1} = diag(I_r, Γ^{m+1})`.
    Since `topProjector` and `compBlock` annihilate each other and `topProjector`
    is idempotent, `(topProjector + compBlock)^{m+1} = topProjector +
    compBlock^{m+1}` entrywise.  Higham §17.4 (17.22). -/
theorem matPow_blockJ_eq (n r : ℕ) (C : Fin n → Fin n → ℝ) (m : ℕ) :
    matPow n (blockJ n r C) (m + 1)
      = fun i j => topProjector n r i j + matPow n (compBlock n r C) (m + 1) i j := by
  set P : Fin n → Fin n → ℝ := topProjector n r with hP
  set Bm : Fin n → Fin n → ℝ := compBlock n r C with hBm
  have hPB : matMul n P Bm = fun _ _ => 0 := topProjector_mul_compBlock n r C
  have hBP : matMul n Bm P = fun _ _ => 0 := compBlock_mul_topProjector n r C
  have hPP : matMul n P P = P := topProjector_idempotent n r
  have hsum : blockJ n r C = fun i j => P i j + Bm i j :=
    blockJ_eq_topProjector_add_compBlock n r C
  induction m with
  | zero =>
      rw [matPow_one, hsum]
      funext i j
      show P i j + Bm i j = P i j + matPow n Bm 1 i j
      rw [matPow_one]
  | succ k ih =>
      rw [matPow_succ, ih, hsum]
      funext i j
      show (∑ l : Fin n, (P i l + Bm i l) * (P l j + matPow n Bm (k + 1) l j))
          = P i j + matPow n Bm (k + 1 + 1) i j
      have hexpand : (∑ l : Fin n, (P i l + Bm i l) * (P l j + matPow n Bm (k + 1) l j))
          = (∑ l : Fin n, P i l * P l j)
            + (∑ l : Fin n, P i l * matPow n Bm (k + 1) l j)
            + (∑ l : Fin n, Bm i l * P l j)
            + (∑ l : Fin n, Bm i l * matPow n Bm (k + 1) l j) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun l _ => by ring)
      rw [hexpand]
      have h1 : (∑ l : Fin n, P i l * P l j) = P i j := by
        have := congrFun (congrFun hPP i) j; rwa [matMul] at this
      have h2 : (∑ l : Fin n, P i l * matPow n Bm (k + 1) l j) = 0 := by
        have hPBm : matMul n P (matPow n Bm (k + 1)) = fun _ _ => 0 := by
          rw [matPow_succ, ← matMul_assoc, hPB]
          funext a b; show (∑ l : Fin n, (0:ℝ) * matPow n Bm k l b) = 0; simp
        have := congrFun (congrFun hPBm i) j; rwa [matMul] at this
      have h3 : (∑ l : Fin n, Bm i l * P l j) = 0 := by
        have := congrFun (congrFun hBP i) j; rwa [matMul] at this
      have h4 : (∑ l : Fin n, Bm i l * matPow n Bm (k + 1) l j)
          = matPow n Bm (k + 1 + 1) i j := by
        rw [matPow_succ]; rfl
      rw [h1, h2, h3, h4]; ring

/-- `compBlock`'s entries vanish on any top row or top column.  Higham §17.4
    (17.22). -/
theorem compBlock_top_zero (n r : ℕ) (C : Fin n → Fin n → ℝ) (i j : Fin n)
    (h : (i : ℕ) < r ∨ (j : ℕ) < r) : compBlock n r C i j = 0 := by
  unfold compBlock; rw [if_pos h]

/-- Powers of `compBlock` are complement-supported: `compBlock^{m+1} i j = 0`
    whenever `i < r` or `j < r`.  The complement block acts within the complement
    coordinates only.  Higham §17.4 (17.22). -/
theorem matPow_compBlock_top_zero (n r : ℕ) (C : Fin n → Fin n → ℝ) (m : ℕ)
    (i j : Fin n) (h : (i : ℕ) < r ∨ (j : ℕ) < r) :
    matPow n (compBlock n r C) (m + 1) i j = 0 := by
  induction m generalizing i j with
  | zero => rw [matPow_one]; exact compBlock_top_zero n r C i j h
  | succ k ih =>
      rw [matPow_succ]
      show (∑ l : Fin n, compBlock n r C i l * matPow n (compBlock n r C) (k + 1) l j) = 0
      refine Finset.sum_eq_zero ?_
      intro l _
      rcases h with hi | hj
      · rw [compBlock_top_zero n r C i l (Or.inl hi), zero_mul]
      · by_cases hl : (l : ℕ) < r
        · rw [compBlock_top_zero n r C i l (Or.inr hl), zero_mul]
        · rw [ih l j (Or.inr hj), mul_zero]

-- ============================================================
-- §17.4  C. The similarity transport of the entrywise limit
-- ============================================================

/-- Similarity powers, reverse direction: `X⁻¹ · Gᵐ · X = Jᵐ` given `X⁻¹ G X = J`
    (two-sided real inverse).  The transpose of `matPow_similarity`, used to pull
    convergence of `Gᵐ` back to convergence of `Jᵐ`.  Higham §17.4 (17.22). -/
theorem matPow_J_eq_conj (n : ℕ) (G X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) (m : ℕ) :
    matPow n J m = matMul n X_inv (matMul n (matPow n G m) X) := by
  have hXinvX : matMul n X_inv X = idMatrix n := by ext a b; exact hXl a b
  rw [matPow_similarity n G X X_inv J hXr hXl hsim m,
    ← matMul_assoc, ← matMul_assoc, hXinvX, matMul_id_left,
    matMul_assoc, hXinvX, matMul_id_right]

/-- **Similarity transport of the entrywise power limit.**  If the powers of `J`
    converge entrywise to `topProjector n r` and `X⁻¹ G X = J` (with a two-sided
    real inverse pair), then the powers of `G` converge entrywise to the
    eigenvalue-`1` projector `oneEigenProjector n r X X⁻¹ = X · diag(I_r,0) · X⁻¹`.
    Higham §17.4 (17.22)/(17.25).  Same finite-sum-of-limits assembly as
    `matPow_G_tendsto_oneEigenProjector`, with the per-summand limit driven by the
    hypothesis rather than an ∞-norm squeeze. -/
theorem matPow_G_tendsto_oneEigenProjector_of_matPow_J_tendsto (n r : ℕ)
    (G X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J)
    (hJlim : ∀ i j : Fin n,
      Filter.Tendsto (fun m => matPow n J m i j) Filter.atTop
        (nhds (topProjector n r i j))) (i j : Fin n) :
    Filter.Tendsto (fun m => matPow n G m i j) Filter.atTop
      (nhds (oneEigenProjector n r X X_inv i j)) := by
  have hGm : ∀ m, matPow n G m i j =
      ∑ k : Fin n, X i k * matMul n (matPow n J m) X_inv k j := by
    intro m; rw [matPow_similarity n G X X_inv J hXr hXl hsim m]; rfl
  have hP : oneEigenProjector n r X X_inv i j =
      ∑ k : Fin n, X i k * matMul n (topProjector n r) X_inv k j := rfl
  have hterm : ∀ k : Fin n,
      Filter.Tendsto (fun m => X i k * matMul n (matPow n J m) X_inv k j)
        Filter.atTop (nhds (X i k * matMul n (topProjector n r) X_inv k j)) := by
    intro k
    have hinner : Filter.Tendsto (fun m => matMul n (matPow n J m) X_inv k j)
        Filter.atTop (nhds (matMul n (topProjector n r) X_inv k j)) := by
      show Filter.Tendsto (fun m => ∑ l : Fin n, matPow n J m k l * X_inv l j)
        Filter.atTop (nhds (∑ l : Fin n, topProjector n r k l * X_inv l j))
      exact tendsto_finset_sum _ (fun l _ => (hJlim k l).mul_const (X_inv l j))
    exact hinner.const_mul (X i k)
  have hsum : Filter.Tendsto
      (fun m => ∑ k : Fin n, X i k * matMul n (matPow n J m) X_inv k j)
      Filter.atTop
      (nhds (∑ k : Fin n, X i k * matMul n (topProjector n r) X_inv k j)) :=
    tendsto_finset_sum _ (fun k _ => hterm k)
  rw [show (fun m => matPow n G m i j) =
      fun m => ∑ k : Fin n, X i k * matMul n (matPow n J m) X_inv k j from funext hGm, hP]
  exact hsum

-- ============================================================
-- §17.4  D. ENTRY POINT (B): the printed (17.22) `ρ(Γ) < 1` route
-- ============================================================

/-- **The `ρ(Γ) < 1` intermediate: block-diagonal powers converge to `diag(I_r,0)`.**
    If the complement block `C` has `spectralRadius ℂ Ĉ < 1` for its
    complexification (the genuine `ρ(Γ) < 1` of eq (17.22)), then the powers of
    `blockJ n r C = diag(I_r, Γ)` converge entrywise to the top-block projector
    `topProjector n r = diag(I_r, 0)`.  Higham §17.4 (17.22): the block split
    `diag(I_r, Γ)ᵐ = diag(I_r, Γᵐ)` plus `Γᵐ → 0` (Gelfand). -/
theorem matPow_blockJ_tendsto_topProjector_of_spectralRadius (n r : ℕ)
    (C : Fin n → Fin n → ℝ)
    (hspec : spectralRadius ℂ (complexifyMat n (compBlock n r C)) < 1) (i j : Fin n) :
    Filter.Tendsto (fun m => matPow n (blockJ n r C) m i j) Filter.atTop
      (nhds (topProjector n r i j)) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  rw [show (fun m => matPow n (blockJ n r C) (m + 1) i j)
      = fun m => topProjector n r i j + matPow n (compBlock n r C) (m + 1) i j from
    funext (fun m => by rw [matPow_blockJ_eq n r C m])]
  have hzero : Filter.Tendsto (fun m => matPow n (compBlock n r C) (m + 1) i j)
      Filter.atTop (nhds 0) :=
    (matPow_tendsto_zero_of_spectralRadius_lt_one n (compBlock n r C) hspec i j).comp
      (Filter.tendsto_add_atTop_nat 1)
  simpa using (tendsto_const_nhds (x := topProjector n r i j)).add hzero

/-- **Higham §17.4, eq (17.22)/(17.25) — `[106, Lem 6.9]` — the semiconvergence
    LIMIT from the block form and `ρ(Γ) < 1` (the printed spectral-radius
    condition), GENERAL COMPLEX.**

    Given the semiconvergent block form as column data — a real invertible change
    of basis `(X, X⁻¹)` whose first `r` columns are eigenvalue-`1` eigenvectors of
    `G` (`hGcolTop`) and whose complement columns span a `G`-invariant complement
    acting through the block `C` (`hGcolBot`) — together with the printed spectral
    condition `spectralRadius ℂ Ĉ_comp < 1` (the genuine `ρ(Γ) < 1`, NOT an ∞-norm
    bound), the powers of `G` converge entrywise to the eigenvalue-`1` projector
    `oneEigenProjector n r X X⁻¹ = X · diag(I_r, 0) · X⁻¹ = I − E`.

    This is the honest object the book uses.  Unlike the ∞-norm route
    (`matPow_G_tendsto_oneEigenProjector`, which needs `‖Γ‖∞ < 1` — impossible for
    a complex-conjugate eigenpair `α ± β i` with `|α| + |β| ≥ 1`), here the only
    quantitative hypothesis is the spectral radius of the complement block, and the
    power decay `Cᵐ → 0` is DERIVED via Gelfand's formula
    (`matPow_tendsto_zero_of_spectralRadius_lt_one`).  Works for arbitrary real
    `G` with complex spectrum. -/
theorem matPow_G_tendsto_oneEigenProjector_of_spectralRadius (n r : ℕ)
    (G X X_inv C : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hGcolTop : ∀ (k : Fin n), (k : ℕ) < r → ∀ i : Fin n, matMul n G X i k = X i k)
    (hGcolBot : ∀ (k : Fin n), ¬(k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k =
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r), X i l * C l k)
    (hspec : spectralRadius ℂ (complexifyMat n (compBlock n r C)) < 1) :
    ∀ i j : Fin n,
      Filter.Tendsto (fun m => matPow n G m i j) Filter.atTop
        (nhds (oneEigenProjector n r X X_inv i j)) := by
  have hsim : matMul n X_inv (matMul n G X) = blockJ n r C :=
    X_inv_G_X_eq_blockJ n G X X_inv (blockJ n r C) hXl
      (matMul_G_X_eq_X_blockJ n r G X C hGcolTop hGcolBot)
  intro i j
  exact matPow_G_tendsto_oneEigenProjector_of_matPow_J_tendsto n r G X X_inv (blockJ n r C)
    hXr hXl hsim
    (fun i' j' => matPow_blockJ_tendsto_topProjector_of_spectralRadius n r C hspec i' j') i j

-- ============================================================
-- §17.4  E. The convergence bridge: entrywise `Gᵐ` convergence from orbits
-- ============================================================

/-- `(mulVecLin M)^m = mulVecLin (M^m)`.  Auxiliary. -/
theorem mulVecLin_pow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    (Matrix.mulVecLin M) ^ m = Matrix.mulVecLin (M ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Matrix.mulVecLin_one, Module.End.one_eq_id]
  | succ k ih => rw [pow_succ, pow_succ, ih, Matrix.mulVecLin_mul]; rfl

/-- The operator orbit of the standard basis vector `e_j` reads off the `(i,j)`
    entry of the repository power:
    `((mulVecLin (of G))^m (e_j)) i = matPow n G m i j`.  Higham §17.4 (17.22). -/
theorem mulVecLin_pow_single_eq_matPow (n : ℕ) (G : Fin n → Fin n → ℝ) (m : ℕ) (i j : Fin n) :
    ((Matrix.mulVecLin (Matrix.of G)) ^ m) (Pi.single j 1) i = matPow n G m i j := by
  rw [mulVecLin_pow, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, ← matPow_eq_matrix_pow]
  show (Matrix.of (matPow n G m)).col j i = matPow n G m i j
  rfl

/-- **Entrywise convergence of `matPow n G m` from convergence of every operator
    orbit.**  If `∀ x, ∃ z, (mulVecLin G)^m x → z` (the operator content of a
    semiconvergent `G`), then each entry sequence `m ↦ matPow n G m i j` converges
    — apply the orbit hypothesis to the standard basis vector `e_j` and read off
    coordinate `i`.  Higham §17.4 (17.22). -/
theorem matPow_entry_converges_of_forall_orbit_tendsto (n : ℕ) (G : Fin n → Fin n → ℝ)
    (hconv : ∀ x : Fin n → ℝ, ∃ z : Fin n → ℝ,
      Filter.Tendsto (fun m : ℕ => (Matrix.mulVecLin (Matrix.of G) ^ m) x) Filter.atTop (𝓝 z))
    (i j : Fin n) :
    ∃ c : ℝ, Filter.Tendsto (fun m => matPow n G m i j) Filter.atTop (nhds c) := by
  obtain ⟨z, hz⟩ := hconv (Pi.single j 1)
  refine ⟨z i, ?_⟩
  have hcoord : Filter.Tendsto
      (fun m => ((Matrix.mulVecLin (Matrix.of G) ^ m) (Pi.single j 1)) i)
      Filter.atTop (nhds (z i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hz
  exact hcoord.congr (fun m => mulVecLin_pow_single_eq_matPow n G m i j)

-- ============================================================
-- §17.4  F. The complement block has no eigenvalue-`1` vector (from `⊤ = E₁ ⊕ F`)
-- ============================================================

section NoFixed
variable {n : ℕ}

/-- Vector form of the column action: `G *ᵥ (b k) = ∑_l C_{lk} • (b l)` with
    `C = basisActionMatrix G b`.  This is `Basis.sum_repr`, since
    `basisActionMatrix G b l k = b.repr (G *ᵥ b k) l` by definition.  Higham §17.4
    (17.22). -/
theorem G_mulVec_adaptedBasis {r m : ℕ} (hrm : r + m = n)
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F)
    (G : Fin n → Fin n → ℝ) (k : Fin n) :
    G *ᵥ (adaptedBasis hrm hCompl bV bW k)
      = ∑ l : Fin n, basisActionMatrix G (adaptedBasis hrm hCompl bV bW) l k •
          adaptedBasis hrm hCompl bV bW l :=
  ((adaptedBasis hrm hCompl bV bW).sum_repr _).symm

/-- **The complement action block has no nonzero fixed vector supported on the
    complement.**  If `w` vanishes on the eigenvalue-`1` block (`w l = 0` for
    `l < r`) and is fixed by the complement-masked action block
    (`∑_l compBlock n r C i l · w l = w i` for all `i`, with
    `C = basisActionMatrix G (adaptedBasis …)`), then `w = 0`.

    Higham §17.4 (17.22).  This is the crux of the general-complex LIMIT from
    convergence: a complement fixed vector `w` assembles into
    `y = ∑ w_k • (b k) ∈ F` with `G *ᵥ y = y`, hence `y ∈ E₁` (given fixed vectors
    lie in `E₁`, `hFixSub`); but `E₁ ⊓ F = ⊥`, so `y = 0`, forcing `w = 0`.  No
    spectral/∞-norm/ℂ→ℝ machinery — purely the direct-sum splitting `⊤ = E₁ ⊕ F`. -/
theorem compBlock_no_comp_fixed {r m : ℕ} (hrm : r + m = n)
    {E₁ F : Submodule ℝ (Fin n → ℝ)} (hCompl : IsCompl E₁ F)
    (bV : Module.Basis (Fin r) ℝ E₁) (bW : Module.Basis (Fin m) ℝ F)
    (G : Fin n → Fin n → ℝ)
    (hFixSub : ∀ x : Fin n → ℝ, G *ᵥ x = x → x ∈ E₁)
    (hInvF : ∀ x ∈ F, G *ᵥ x ∈ F)
    {w : Fin n → ℝ} (hwtop : ∀ l : Fin n, (l : ℕ) < r → w l = 0)
    (hfix : ∀ i : Fin n,
      (∑ l : Fin n, compBlock n r (basisActionMatrix G (adaptedBasis hrm hCompl bV bW)) i l
        * w l) = w i) :
    w = 0 := by
  set b := adaptedBasis hrm hCompl bV bW with hb
  set C := basisActionMatrix G b with hC
  -- Key: `∑_k C_lk w_k = w_l` for EVERY `l` (both blocks).
  have hCw : ∀ l : Fin n, (∑ k : Fin n, C l k * w k) = w l := by
    intro l
    by_cases hl : (l : ℕ) < r
    · -- top row: `C_lk = 0` for `k` comp (invariance), `w_k = 0` for `k < r`
      rw [hwtop l hl]
      refine Finset.sum_eq_zero ?_
      intro k _
      by_cases hk : (k : ℕ) < r
      · rw [hwtop k hk, mul_zero]
      · have hCkl : C l k = 0 := adaptedBasis_hInv hrm hCompl bV bW G hInvF k hk l hl
        rw [hCkl, zero_mul]
    · -- complement row: use `hfix`, `compBlock C l k = C l k` for `l,k` comp
      have hfl := hfix l
      have hmask : (∑ k : Fin n, compBlock n r C l k * w k) = ∑ k : Fin n, C l k * w k := by
        refine Finset.sum_congr rfl ?_
        intro k _
        by_cases hk : (k : ℕ) < r
        · rw [hwtop k hk, mul_zero, mul_zero]
        · rw [compBlock_eq n r C hl hk]
      rw [hmask] at hfl
      exact hfl
  -- The assembled vector `y = ∑ w_k • b k`.
  set y : Fin n → ℝ := ∑ k : Fin n, w k • b k with hy
  -- `y ∈ F`.
  have hyF : y ∈ F := by
    rw [hy]
    refine Submodule.sum_mem F ?_
    intro k _
    by_cases hk : (k : ℕ) < r
    · rw [hwtop k hk, zero_smul]; exact Submodule.zero_mem F
    · exact Submodule.smul_mem F _ (adaptedBasis_mem_F hrm hCompl bV bW k hk)
  -- `G *ᵥ y = y`.
  have hGy : G *ᵥ y = y := by
    have hlin : G *ᵥ y = ∑ k : Fin n, w k • (G *ᵥ (b k)) := by
      rw [hy, show (G *ᵥ ∑ k : Fin n, w k • b k)
          = Matrix.mulVecLin G (∑ k : Fin n, w k • b k) from rfl, map_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [map_smul]; rfl)
    rw [hlin]
    have hexp : ∑ k : Fin n, w k • (G *ᵥ (b k))
        = ∑ k : Fin n, w k • (∑ l : Fin n, C l k • b l) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      by_cases hk : (k : ℕ) < r
      · rw [hwtop k hk, zero_smul, zero_smul]
      · rw [G_mulVec_adaptedBasis hrm hCompl bV bW G k]
    rw [hexp]
    have hswap : ∑ k : Fin n, w k • (∑ l : Fin n, C l k • b l)
        = ∑ l : Fin n, (∑ k : Fin n, C l k * w k) • b l := by
      rw [show (∑ k : Fin n, w k • (∑ l : Fin n, C l k • b l))
          = ∑ k : Fin n, ∑ l : Fin n, (w k * C l k) • b l from
        Finset.sum_congr rfl (fun k _ => by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl (fun l _ => by rw [smul_smul]))]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl (fun k _ => by rw [mul_comm (w k) (C l k)])
    rw [hswap, hy]
    exact Finset.sum_congr rfl (fun l _ => by rw [hCw l])
  -- `y ∈ E₁ ⊓ F = ⊥ ⟹ y = 0`.
  have hyE : y ∈ E₁ := hFixSub y hGy
  have hy0 : y = 0 := by
    have hmem : y ∈ E₁ ⊓ F := Submodule.mem_inf.mpr ⟨hyE, hyF⟩
    rw [hCompl.inf_eq_bot] at hmem
    simpa using hmem
  -- `y = 0`, `b` a basis ⟹ `w = 0`.
  funext i
  have hcoord : b.repr y i = 0 := by rw [hy0]; simp
  have hwi : b.repr y i = w i := by
    rw [hy, map_sum]
    simp only [map_smul, b.repr_self]
    rw [Finset.sum_apply', Finset.sum_eq_single i]
    · simp
    · intro k _ hki; simp [hki]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [← hwi, hcoord]; rfl

end NoFixed

-- ============================================================
-- §17.4  G. ENTRY POINT (A): the general-complex LIMIT from convergence
-- ============================================================

section ConvRoute
variable {n : ℕ}

/-- If each entry of `A m` converges, so does each entry of the conjugate
    `matMul X_inv (matMul (A m) X)` (a finite sum of convergent sequences).
    Higham §17.4 (17.22). -/
theorem matMul_conj_entry_converges (X X_inv : Fin n → Fin n → ℝ)
    (A : ℕ → Fin n → Fin n → ℝ)
    (hA : ∀ a b : Fin n, ∃ c : ℝ, Filter.Tendsto (fun m => A m a b) Filter.atTop (nhds c))
    (i j : Fin n) :
    ∃ c : ℝ, Filter.Tendsto (fun m => matMul n X_inv (matMul n (A m) X) i j)
      Filter.atTop (nhds c) := by
  classical
  choose cA hcA using hA
  refine ⟨∑ a : Fin n, ∑ b : Fin n, X_inv i a * (cA a b * X b j), ?_⟩
  have hentry : ∀ m, matMul n X_inv (matMul n (A m) X) i j
      = ∑ a : Fin n, ∑ b : Fin n, X_inv i a * (A m a b * X b j) := by
    intro m
    show (∑ a : Fin n, X_inv i a * (∑ b : Fin n, A m a b * X b j))
      = ∑ a : Fin n, ∑ b : Fin n, X_inv i a * (A m a b * X b j)
    exact Finset.sum_congr rfl (fun a _ => by rw [Finset.mul_sum])
  rw [show (fun m => matMul n X_inv (matMul n (A m) X) i j)
      = fun m => ∑ a : Fin n, ∑ b : Fin n, X_inv i a * (A m a b * X b j) from funext hentry]
  refine tendsto_finset_sum _ (fun a _ => ?_)
  refine tendsto_finset_sum _ (fun b _ => ?_)
  exact ((hcA a b).mul_const (X b j)).const_mul (X_inv i a)

/-- **The general-complex `diag(I_r, C)ᵐ → diag(I_r, 0)` from convergence.**  If
    every entry sequence `matPow n G m a b` converges, `X⁻¹ G X = blockJ n r C`
    (two-sided real inverse), and the complement action block `C` has no nonzero
    complement fixed vector (`hNoFix`), then the powers of `blockJ n r C
    = diag(I_r, Γ)` converge entrywise to `topProjector n r = diag(I_r, 0)`.

    Higham §17.4 (17.22)/(17.25).  Proof: the block powers converge (finite-sum
    transport of the `G`-power convergence); the complement limit
    `K := lim Cᵐ_comp` satisfies `C · K = K` and is complement-supported, so each
    of its columns is a complement fixed vector, hence `0` by `hNoFix`; therefore
    `Cᵐ → 0` and the block powers tend to `diag(I_r, 0)`.  No spectral radius and
    no ∞-norm — the limit `0` is forced by the direct-sum splitting alone. -/
theorem matPow_blockJ_tendsto_topProjector_of_convergence (r : ℕ)
    (G X X_inv C : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = blockJ n r C)
    (hGconv : ∀ a b : Fin n,
      ∃ c : ℝ, Filter.Tendsto (fun m => matPow n G m a b) Filter.atTop (nhds c))
    (hNoFix : ∀ w : Fin n → ℝ, (∀ l : Fin n, (l : ℕ) < r → w l = 0) →
      (∀ i : Fin n, (∑ l : Fin n, compBlock n r C i l * w l) = w i) → w = 0)
    (i j : Fin n) :
    Filter.Tendsto (fun m => matPow n (blockJ n r C) m i j) Filter.atTop
      (nhds (topProjector n r i j)) := by
  classical
  -- each entry of `matPow (blockJ) m` converges (to `Jlim`)
  have hJconv : ∀ a b : Fin n, ∃ c : ℝ,
      Filter.Tendsto (fun m => matPow n (blockJ n r C) m a b) Filter.atTop (nhds c) := by
    intro a b
    obtain ⟨c, hc⟩ := matMul_conj_entry_converges X X_inv (fun m => matPow n G m) hGconv a b
    refine ⟨c, hc.congr (fun m => ?_)⟩
    exact (congrFun (congrFun (matPow_J_eq_conj n G X X_inv (blockJ n r C) hXr hXl hsim m) a) b).symm
  choose Jlim hJlim using hJconv
  set P : Fin n → Fin n → ℝ := topProjector n r with hP
  set K : Fin n → Fin n → ℝ := fun a b => Jlim a b - P a b with hK
  -- `Cᵐ_comp → K`
  have hcompconv : ∀ a b : Fin n,
      Filter.Tendsto (fun m => matPow n (compBlock n r C) (m + 1) a b) Filter.atTop
        (nhds (K a b)) := by
    intro a b
    have hsplit : (fun m => matPow n (compBlock n r C) (m + 1) a b)
        = fun m => matPow n (blockJ n r C) (m + 1) a b - P a b := by
      funext m
      have h2 := congrFun (congrFun (matPow_blockJ_eq n r C m) a) b
      rw [h2]; ring
    rw [hsplit, hK]
    exact ((hJlim a b).comp (Filter.tendsto_add_atTop_nat 1)).sub tendsto_const_nhds
  -- `K` complement-supported
  have hKtop : ∀ a b : Fin n, (a : ℕ) < r ∨ (b : ℕ) < r → K a b = 0 := by
    intro a b h
    have hz : Filter.Tendsto (fun _ : ℕ => (0:ℝ)) Filter.atTop (nhds (K a b)) :=
      (hcompconv a b).congr (fun m => matPow_compBlock_top_zero n r C m a b h)
    exact (tendsto_nhds_unique tendsto_const_nhds hz).symm
  -- `C · K = K`
  have hfixK : ∀ a b : Fin n, (∑ l : Fin n, compBlock n r C a l * K l b) = K a b := by
    intro a b
    have hlhs : Filter.Tendsto (fun m => matPow n (compBlock n r C) (m + 1 + 1) a b)
        Filter.atTop (nhds (K a b)) :=
      (hcompconv a b).comp (Filter.tendsto_add_atTop_nat 1)
    have hrhs : Filter.Tendsto
        (fun m => ∑ l : Fin n, compBlock n r C a l * matPow n (compBlock n r C) (m + 1) l b)
        Filter.atTop (nhds (∑ l : Fin n, compBlock n r C a l * K l b)) :=
      tendsto_finset_sum _ (fun l _ => (hcompconv l b).const_mul (compBlock n r C a l))
    have heq : (fun m => matPow n (compBlock n r C) (m + 1 + 1) a b)
        = fun m => ∑ l : Fin n, compBlock n r C a l * matPow n (compBlock n r C) (m + 1) l b := by
      funext m; rw [matPow_succ]; rfl
    rw [heq] at hlhs
    exact tendsto_nhds_unique hrhs hlhs
  -- `K = 0` columnwise
  have hK0 : K = fun _ _ => 0 := by
    funext a b
    exact congrFun (hNoFix (fun i => K i b)
      (fun l hl => hKtop l b (Or.inl hl)) (fun i => hfixK i b)) a
  -- assemble
  rw [← Filter.tendsto_add_atTop_iff_nat 1,
    show (fun m => matPow n (blockJ n r C) (m + 1) i j)
      = fun m => topProjector n r i j + matPow n (compBlock n r C) (m + 1) i j from
    funext (fun m => by rw [matPow_blockJ_eq n r C m])]
  have hz : Filter.Tendsto (fun m => matPow n (compBlock n r C) (m + 1) i j)
      Filter.atTop (nhds 0) := by
    have h := hcompconv i j
    rwa [show K i j = 0 from congrFun (congrFun hK0 i) j] at h
  simpa using (tendsto_const_nhds (x := topProjector n r i j)).add hz

end ConvRoute

/-- **Higham §17.4, eq (17.22)/(17.25) — `[106, Lem 6.9]` — the GENERAL-COMPLEX
    semiconvergence LIMIT `Gᵐ → I − E`, UNCONDITIONAL from convergence of every
    orbit.**

    If every orbit `m ↦ (mulVecLin G)ᵐ x` converges (the operator content of a
    semiconvergent `G` — `Gᵐ` converges entrywise, hence on every vector), then
    there is a split index `r` and a real invertible change of basis `(X, X⁻¹)`
    such that the powers of `G` converge entrywise to the eigenvalue-`1` projector
    `oneEigenProjector n r X X⁻¹ = X · diag(I_r, 0) · X⁻¹ = I − E`.

    This is the HONEST closure of the [106] limit in FULL generality (arbitrary
    real `G`, complex spectrum allowed).  It uses NEITHER the printed
    spectral-radius hypothesis `ρ(Γ) < 1` NOR the ∞-norm strengthening `‖Γ‖∞ < 1`
    (impossible for a complex eigenpair `α ± β i` with `|α| + |β| ≥ 1`) NOR any
    ℂ→ℝ descent.  The engine is entirely real-linear-algebraic:

      • the real primary splitting `⊤ = E₁ ⊕ F` from convergence
        (`exists_real_primary_splitting_of_forall_orbit_tendsto`), with the
        eigenvalue-`1` block collapsed (GAP (1)) and `F` a `G`-invariant complement;
      • the adapted-basis block form `G · X = X · diag(I_r, C)`;
      • the complement action block `C` has NO nonzero complement eigenvalue-`1`
        vector (`compBlock_no_comp_fixed`, since such a vector would lie in
        `E₁ ⊓ F = ⊥`), which forces the entrywise limit of `diag(I_r, C)ᵐ` to be
        `diag(I_r, 0)` (`matPow_blockJ_tendsto_topProjector_of_convergence`);
      • the similarity transport `Gᵐ = X · diag(I_r, C)ᵐ · X⁻¹`.

    The convergence is entrywise (equivalently, in any norm on the
    finite-dimensional space). -/
theorem matPow_G_tendsto_oneEigenProjector_of_convergence {n : ℕ} (G : Fin n → Fin n → ℝ)
    (hconv : ∀ x : Fin n → ℝ, ∃ z : Fin n → ℝ,
      Filter.Tendsto (fun m : ℕ => (Matrix.mulVecLin G ^ m) x) Filter.atTop (𝓝 z)) :
    ∃ (r : ℕ) (X X_inv : Fin n → Fin n → ℝ),
      IsRightInverse n X X_inv ∧ IsRightInverse n X_inv X ∧
      (∀ i j : Fin n,
        Filter.Tendsto (fun m => matPow n G m i j) Filter.atTop
          (nhds (oneEigenProjector n r X X_inv i j))) := by
  classical
  -- the real primary splitting `⊤ = E₁ ⊕ F` from convergence
  obtain ⟨F, hCompl, hEig1, hInvF⟩ := exists_real_primary_splitting_of_forall_orbit_tendsto G hconv
  set E₁ : Submodule ℝ (Fin n → ℝ) := Module.End.eigenspace (Matrix.mulVecLin G) 1 with hE₁
  -- dimensions of the two summands, `r + m = n`
  set r : ℕ := Module.finrank ℝ E₁ with hr
  set mm : ℕ := Module.finrank ℝ F with hmm
  have hrm : r + mm = n := by
    rw [hr, hmm, Submodule.finrank_add_eq_of_isCompl hCompl, Module.finrank_fin_fun]
  set bV : Module.Basis (Fin r) ℝ E₁ := Module.finBasis ℝ E₁ with hbV
  set bW : Module.Basis (Fin mm) ℝ F := Module.finBasis ℝ F with hbW
  set b := adaptedBasis hrm hCompl bV bW with hb
  set X : Fin n → Fin n → ℝ := basisColMatrix b with hX
  set X_inv : Fin n → Fin n → ℝ := basisRowMatrix b with hXinv
  set C : Fin n → Fin n → ℝ := basisActionMatrix G b with hC
  -- the two column conditions from the adapted basis + splitting
  have hGcolTop : ∀ (k : Fin n), (k : ℕ) < r → ∀ i : Fin n, matMul n G X i k = X i k :=
    fun k hk i => basisColMatrix_colTop G b r
      (fun k' hk' => adaptedBasis_hEig hrm hCompl bV bW G hEig1 k' hk') k hk i
  have hGcolBot : ∀ (k : Fin n), ¬(k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k =
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r), X i l * C l k :=
    fun k hk i => basisColMatrix_colBot G b r
      (fun k' hk' l hl => adaptedBasis_hInv hrm hCompl bV bW G hInvF k' hk' l hl) k hk i
  have hXr : IsRightInverse n X X_inv := basisColMatrix_isRightInverse b
  have hXl : IsRightInverse n X_inv X := basisRowMatrix_isRightInverse b
  have hsim : matMul n X_inv (matMul n G X) = blockJ n r C :=
    X_inv_G_X_eq_blockJ n G X X_inv (blockJ n r C) hXl
      (matMul_G_X_eq_X_blockJ n r G X C hGcolTop hGcolBot)
  -- entrywise convergence of `matPow n G` from the operator hypothesis
  have hGconv : ∀ a b' : Fin n,
      ∃ c : ℝ, Filter.Tendsto (fun m => matPow n G m a b') Filter.atTop (nhds c) := by
    intro a b'
    have hconv' : ∀ x : Fin n → ℝ, ∃ z : Fin n → ℝ,
        Filter.Tendsto (fun m : ℕ => (Matrix.mulVecLin (Matrix.of G) ^ m) x) Filter.atTop (𝓝 z) :=
      hconv
    exact matPow_entry_converges_of_forall_orbit_tendsto n G hconv' a b'
  -- fixed vectors lie in `E₁` (the eigenvalue-`1` eigenspace)
  have hFixSub : ∀ x : Fin n → ℝ, G *ᵥ x = x → x ∈ E₁ := by
    intro x hx
    rw [hE₁, Module.End.mem_eigenspace_iff, one_smul, Matrix.mulVecLin_apply]
    exact hx
  -- no nonzero complement eigenvalue-`1` vector
  have hNoFix : ∀ w : Fin n → ℝ, (∀ l : Fin n, (l : ℕ) < r → w l = 0) →
      (∀ i : Fin n, (∑ l : Fin n, compBlock n r C i l * w l) = w i) → w = 0 :=
    fun w hwtop hfix =>
      compBlock_no_comp_fixed hrm hCompl bV bW G hFixSub hInvF hwtop hfix
  -- the block limit, transported by the similarity
  refine ⟨r, X, X_inv, hXr, hXl, fun i j => ?_⟩
  exact matPow_G_tendsto_oneEigenProjector_of_matPow_J_tendsto n r G X X_inv (blockJ n r C)
    hXr hXl hsim
    (fun i' j' => matPow_blockJ_tendsto_topProjector_of_convergence r G X X_inv C
      hXr hXl hsim hGconv hNoFix i' j') i j

-- ============================================================
-- §17.4  STATUS of the general-complex semiconvergence LIMIT.
-- ============================================================
--
-- HEADLINE (A) — `matPow_G_tendsto_oneEigenProjector_of_convergence` — is the
--   HONEST FULL closure of the [106, Lem 6.9] / eq (17.22) LIMIT in complete
--   generality: from convergence of every orbit `Gᵐ x`, for ARBITRARY real `G`
--   (complex spectrum allowed), the powers converge entrywise to the eigenvalue-`1`
--   projector `X · diag(I_r, 0) · X⁻¹`.  It uses NO spectral hypothesis, NO ∞-norm
--   hypothesis, and NO ℂ→ℝ descent.  The key new mathematical content is
--   `compBlock_no_comp_fixed`: the complement action block has no nonzero
--   complement eigenvalue-`1` vector, because any such vector assembles into an
--   element of `E₁ ⊓ F = ⊥` (the direct-sum splitting from GAP (1) + Fitting).
--   This is strictly stronger than the printed development, which only asserts the
--   block form with `ρ(Γ) < 1`.
--
-- ENTRY POINT (B) — `matPow_G_tendsto_oneEigenProjector_of_spectralRadius` — is the
--   printed (17.22) `ρ(Γ) < 1` route: from the block form and the genuine
--   `spectralRadius` of the complexified complement block `< 1`, Gelfand's formula
--   (`matPow_tendsto_zero_of_spectralRadius_lt_one`) gives `Cᵐ → 0` and hence the
--   same limit.  This is exactly the object the book uses.  The intermediate
--   `spectralRadius(complement) < 1 ⟹ diag(I_r, Γ)ᵐ → diag(I_r, 0)` is exposed as
--   `matPow_blockJ_tendsto_topProjector_of_spectralRadius`.
--
-- WHY NOT THE ∞-NORM.  The repository's earlier semiconvergent-limit theorem
--   `matPow_G_tendsto_oneEigenProjector` (in `StationaryIterationSemiconvergent.lean`)
--   needs the ∞-norm row-sum contraction `‖Γ‖∞ < 1`, which
--   `twoByTwo_max_rowSum_ge_of_trace_det` (in
--   `Analysis/SemiconvergentExistenceComplete.lean`) PROVED is impossible for a
--   complex-conjugate eigenpair `α ± β i` with `|α| + |β| ≥ 1` (e.g. `0.6 ± 0.6 i`:
--   `ρ = 0.849 < 1` yet every similar block has ∞-row-sum `≥ 1.2`).  Both entry
--   points here avoid that strengthening entirely.
--
-- No `sorry`/`admit`/`axiom`/`unsafe`/`opaque`/`native_decide`/proof-disabling
-- option is used.

end NumStability

