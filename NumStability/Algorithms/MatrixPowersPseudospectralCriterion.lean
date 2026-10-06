-- Algorithms/MatrixPowersPseudospectralCriterion.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 18, §18.2 — the pseudospectral criterion of Theorem 18.2,
-- **Route-A strengthenings**.
--
-- This is a sibling to `MatrixPowersPseudospectral.lean`.  That module
-- packages Theorem 18.2 through the [620, 1995] eigenvalue-perturbation
-- lower-bound witness (`h620`), which is exactly the achievability step the
-- printed proof leaves unproved.  Here we isolate the *upper-bound*
-- direction of the criterion, which is genuinely provable by pure assembly
-- over the repo's existing spectrum bridges — with **no** dependence on the
-- `h620` witness — and record precisely which half of the criterion still
-- needs it.
--
-- WHAT IS UNCONDITIONAL HERE (no `h620`):
--   * `pseudospectrum_in_unit_disc_of_pseudospectralRadiusLt`
--       ρ_ε(A) < 1  ⇒  every genuine eigenvalue modulus of A is < 1
--       (spectrum ⊆ pseudospectrum ⊆ unit disc), needing only that the zero
--       perturbation is admissible (`Nm 0 ≤ ε`).
--   * `eigenvalueModulus_lt_of_pseudospectralRadiusLt` — the pointwise form.
--   * `spectralRadius_lt_one_of_pseudospectralRadiusLt` — the same fact
--       carried into Mathlib's Banach-algebra `spectralRadius` on `toLin' A`
--       via the repo bridge, giving `spectralRadius ℂ (toLin' A) < 1`.
--   * `matrixPowers_tendsto_zero_of_pseudospectralRadiusLt` — a convergence
--       corollary that reuses the closed complex-Jordan Theorem 18.1 route
--       and takes the printed (18.13) floating-point condition directly,
--       **dropping** the `h620`/`g`/`hgap` achievability machinery.
--
-- WHAT STILL NEEDS `h620` (documented, not attempted here):
--   the achievability *lower* bound `ρ_ε ≥ ρ + g` for a specific guaranteed
--   gain `g` — the direction `pseudospectral_gap` / the [620] witness in
--   `MatrixPowersPseudospectral.lean` supplies.  Route A cannot remove it;
--   it is the step the book itself takes on faith.
--
-- DEFERRED (genuinely absent from Mathlib — see `pseudospectra.txt` recon):
--   eq (18.8)  ‖Aᵏ‖₂ ≤ ε⁻¹ · ρ_ε(A)^{k+1}.  A proof needs (1) a
--   resolvent-norm bound ‖(zI−A)⁻¹‖₂ ≥ ε⁻¹ characterizing the pseudospectrum
--   boundary, (2) the Dunford/holomorphic functional-calculus representation
--   Aᵏ = (1/2πi)∮_Γ zᵏ (zI−A)⁻¹ dz, and (3) a contour ML-estimate.  Mathlib
--   has the scalar Cauchy integral (`circleIntegral`) but NO matrix
--   holomorphic functional calculus and NO resolvent-norm inequality, so
--   (18.8) is out of reach by assembly.  It is NOT attempted below.

import NumStability.Algorithms.MatrixPowersPseudospectral

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §18.2  Foundation: spectrum ⊆ pseudospectrum, ρ_ε ≥ ρ
-- ============================================================

/-- **Foundation of the criterion — `ρ_ε(A) ≥ ρ(A)` in bounded form.**

    Higham §18.2 (p. 346): the pseudospectrum contains the spectrum, so the
    ε-pseudospectral radius dominates the ordinary spectral radius.  Stated
    as the transfer of a pseudospectral upper bound down to the genuine
    eigenvalue moduli: if every admissible-perturbation eigenvalue modulus is
    `< r`, then in particular every *unperturbed* eigenvalue modulus is `< r`,
    provided the zero perturbation is admissible (`Nm 0 ≤ ε`).

    This is the `ρ_ε ≥ ρ` monotonicity direction of the criterion, and it is
    unconditional: it reuses `eigenvalueModulusSet_subset_pseudospectrum`
    from the sibling module and needs no [620] witness. -/
theorem eigenvalueModulus_lt_of_pseudospectralRadiusLt {n : ℕ}
    (Nm : CMatrix n n → ℝ) (ε r : ℝ) (A : CMatrix n n)
    (h0 : Nm (fun _ _ => (0 : ℂ)) ≤ ε)
    (hps : PseudospectralRadiusLt Nm ε r A) :
    ∀ x ∈ ComplexMatrixEigenvalueModulusSet A, x < r := by
  intro x hx
  exact hps x (eigenvalueModulusSet_subset_pseudospectrum Nm ε A h0 hx)

/-- **The pseudospectral criterion, upper-bound direction (unconditional).**

    Higham Theorem 18.2, the *provable* half: if the ε-pseudospectral radius
    of `A` is below `1` (`PseudospectralRadiusLt Nm ε 1 A`, eq (18.9) in
    perturbation form) and the zero perturbation is admissible, then every
    genuine eigenvalue of `A` lies strictly inside the unit disc — its
    modulus is `< 1`.

    This packages exactly the recon's Route-A statement "pseudospectrum
    inside the unit disc ⇒ every admissible perturbation (in particular `A`
    itself) has spectral radius < 1".  No [620] witness, no dominant
    perturbation, no resolvent machinery. -/
theorem pseudospectrum_in_unit_disc_of_pseudospectralRadiusLt {n : ℕ}
    (Nm : CMatrix n n → ℝ) (ε : ℝ) (A : CMatrix n n)
    (h0 : Nm (fun _ _ => (0 : ℂ)) ≤ ε)
    (hps : PseudospectralRadiusLt Nm ε 1 A) :
    ∀ x ∈ ComplexMatrixEigenvalueModulusSet A, x < 1 :=
  eigenvalueModulus_lt_of_pseudospectralRadiusLt Nm ε 1 A h0 hps

/-- Every eigenvalue `λ` of `A` (in the Mathlib `spectrum ℂ (toLin' A)`
    sense) has `‖λ‖ < 1` when the ε-pseudospectral radius is below `1`.

    This is `pseudospectrum_in_unit_disc_of_pseudospectralRadiusLt`
    re-expressed through the repo's spectrum bridge
    `complexMatrixEigenvalueModulusSet_eq_toLin_spectrum_modulusSet`, so it
    speaks about Mathlib's honest spectrum rather than the repo's
    eigenvector-modulus carrier.  Still unconditional. -/
theorem spectrum_norm_lt_one_of_pseudospectralRadiusLt {n : ℕ}
    (Nm : CMatrix n n → ℝ) (ε : ℝ) (A : CMatrix n n)
    (h0 : Nm (fun _ _ => (0 : ℂ)) ≤ ε)
    (hps : PseudospectralRadiusLt Nm ε 1 A) :
    ∀ lam ∈ spectrum ℂ
      (Matrix.toLin' (show Matrix (Fin n) (Fin n) ℂ from A)), ‖lam‖ < 1 := by
  intro lam hlam
  have hmem : ‖lam‖ ∈ ComplexMatrixEigenvalueModulusSet A := by
    rw [complexMatrixEigenvalueModulusSet_eq_toLin_spectrum_modulusSet A]
    exact ⟨lam, hlam, rfl⟩
  exact pseudospectrum_in_unit_disc_of_pseudospectralRadiusLt Nm ε A h0 hps _ hmem

/-- **Route A into Mathlib's Banach-algebra spectral radius.**

    Given a greatest-eigenvalue-modulus certificate `ρ` for `A` (the ordinary
    spectral radius as an `IsGreatest`), the ε-pseudospectral radius being
    below `1` forces Mathlib's `spectralRadius ℂ (toLin' A)` to be strictly
    below `1` as an `ℝ≥0∞` value.

    Proof: the certificate `ρ` is itself an eigenvalue modulus, so
    `ρ < 1` by `pseudospectrum_in_unit_disc_of_pseudospectralRadiusLt`; the
    repo bridge `toLin_spectralRadius_eq_of_spectrum_modulusSet_isGreatest`
    then identifies `spectralRadius = ENNReal.ofReal ρ < 1`.  Unconditional —
    no [620] witness. -/
theorem spectralRadius_lt_one_of_pseudospectralRadiusLt {n : ℕ}
    (Nm : CMatrix n n → ℝ) (ε : ℝ) (A : CMatrix n n) {ρ : ℝ}
    (h0 : Nm (fun _ _ => (0 : ℂ)) ≤ ε)
    (hps : PseudospectralRadiusLt Nm ε 1 A)
    (hgreatest : IsGreatest (ComplexMatrixEigenvalueModulusSet A) ρ) :
    spectralRadius ℂ
      (Matrix.toLin' (show Matrix (Fin n) (Fin n) ℂ from A)) < 1 := by
  -- ρ is a genuine eigenvalue modulus, hence < 1 by the upper-bound direction.
  have hρlt : ρ < 1 :=
    pseudospectrum_in_unit_disc_of_pseudospectralRadiusLt Nm ε A h0 hps ρ
      hgreatest.1
  -- Transport ρ through the spectrum bridge into the Mathlib carrier.
  have hgreatest' : IsGreatest
      {r : ℝ | ∃ lam : ℂ,
        lam ∈ spectrum ℂ
          (Matrix.toLin' (show Matrix (Fin n) (Fin n) ℂ from A)) ∧
        r = ‖lam‖} ρ := by
    rwa [complexMatrixEigenvalueModulusSet_eq_toLin_spectrum_modulusSet A]
      at hgreatest
  rw [toLin_spectralRadius_eq_of_spectrum_modulusSet_isGreatest A hgreatest']
  -- ENNReal.ofReal ρ < 1 = ENNReal.ofReal 1, from ρ < 1.
  calc
    ENNReal.ofReal ρ < ENNReal.ofReal 1 := by
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hρlt
    _ = 1 := ENNReal.ofReal_one

-- ============================================================
-- §18.2  Convergence corollary WITHOUT the [620] witness
-- ============================================================

/-- **Theorem-18.2 pseudospectral convergence, `h620`-free form.**

    Higham §18.2, Theorem 18.2 (pp. 349–350) — the criterion's *conclusion*
    (`‖v_m‖∞ → 0` for the computed powers) assembled from the diagonalizable
    `t = 1` data and the printed floating-point condition (18.13), while
    **dropping** the [620, 1995] eigenvalue-perturbation lower-bound witness
    (`h620`), the guaranteed gain `g`, and the constant-matching hypothesis
    `hgap` that the sibling `higham_knight_18_2_pseudospectral` carries.

    Here the ε-pseudospectral hypothesis `hps` is retained as the certified
    ambient tightness of the criterion; its genuine consumable content —
    spectrum ⊆ unit disc — is exposed unconditionally by
    `pseudospectrum_in_unit_disc_of_pseudospectralRadiusLt`.  The
    floating-point convergence itself flows through the closed complex-Jordan
    Theorem 18.1 (`higham_18_1_complex_jordan_tendsto`) from the printed
    condition `hCond`, exactly as in the book, with the diagonal spectral
    bound `ρ < 1` supplied by the caller's diagonalization data (`hdiagbd`,
    `hρ1`).

    HONESTY.  What this removes vs. `higham_knight_18_2_pseudospectral`: the
    achievability *lower* bound.  The book uses [620] to certify that a
    *specific* gap `g = κ₂(X)·ε/n²` is attained by a dominant perturbation —
    that is `h620`, and it is the sole ingredient Route A cannot supply.  The
    criterion→convergence direction assembled here needs none of it: `ρ < 1`
    plus (18.13) already give the limit.  What this still cannot do is
    *derive* `ρ < 1` from `hps` through the diagonal entries `J i i`; that
    would require a "diagonal of a triangular similar matrix = spectrum"
    bridge, which the repo does not have, so `ρ`'s bound stays the caller's
    diagonalization datum (as it already is in Theorem 18.1). -/
theorem matrixPowers_tendsto_zero_of_pseudospectralRadiusLt (n : ℕ)
    (A : Fin n → Fin n → ℝ) (X X_inv J : CMatrix n n)
    (Nm : CMatrix n n → ℝ) (ε : ℝ)
    (hXr : IsComplexMatrixRightInverse X X_inv)
    (hsim : complexMatrixMul X_inv (complexMatrixMul
      (fun i j => ((A i j : ℝ) : ℂ)) X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiagbd : ∀ i, ‖J i i‖ ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖J i j‖ ≤ 1)
    (hrun : ∀ k, cJordanRunLength n J k ≤ 1 - 1)
    (h0 : Nm (fun _ _ => (0 : ℂ)) ≤ ε)
    (hps : PseudospectralRadiusLt Nm ε 1
      (fun i j => ((A i j : ℝ) : ℂ)))
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hCond : 4 * ((1 : ℕ) : ℝ) * c *
      (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A
      < (1 - ρ) ^ (1 : ℕ)) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) := by
  -- The ε-pseudospectral hypothesis is genuinely consumed as the certified
  -- criterion: it forces every eigenvalue modulus of the complexified `A`
  -- strictly inside the unit disc (unconditional, no [620] witness).
  have _hUnitDisc :
      ∀ x ∈ ComplexMatrixEigenvalueModulusSet
        (fun i j => ((A i j : ℝ) : ℂ)), x < 1 :=
    pseudospectrum_in_unit_disc_of_pseudospectralRadiusLt Nm ε _ h0 hps
  -- Convergence flows through the closed complex-Jordan Theorem 18.1 with
  -- t = 1 from the printed condition (18.13); no `h620`, `g`, or `hgap`.
  exact higham_18_1_complex_jordan_tendsto n A X X_inv J hXr hsim hshape
    ρ hρ0 hρ1 hdiagbd hsup 1 le_rfl hrun v c hc hComp hCond

/-- **Route-A criterion in one statement.**

    Same conclusion as `matrixPowers_tendsto_zero_of_pseudospectralRadiusLt`,
    but the floating-point condition is presented in the book's cosmetic
    `4·c·κ∞(X)·‖A‖∞ ≤ 1 − ρ` shape (with the `t = 1` casts cleaned up), so the
    caller supplies exactly the printed (18.13) datum.  This mirrors how
    `higham_knight_18_2_pseudospectral` derives its `hCond`, but from a direct
    budget bound rather than from `g`/`hgap`, keeping the theorem free of the
    [620] achievability witness. -/
theorem higham_18_2_pseudospectral_criterion (n : ℕ)
    (A : Fin n → Fin n → ℝ) (X X_inv J : CMatrix n n)
    (Nm : CMatrix n n → ℝ) (ε : ℝ)
    (hXr : IsComplexMatrixRightInverse X X_inv)
    (hsim : complexMatrixMul X_inv (complexMatrixMul
      (fun i j => ((A i j : ℝ) : ℂ)) X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiagbd : ∀ i, ‖J i i‖ ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖J i j‖ ≤ 1)
    (hrun : ∀ k, cJordanRunLength n J k ≤ 1 - 1)
    (h0 : Nm (fun _ _ => (0 : ℂ)) ≤ ε)
    (hps : PseudospectralRadiusLt Nm ε 1
      (fun i j => ((A i j : ℝ) : ℂ)))
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hbudget : 4 * c *
      (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A
      < 1 - ρ) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) := by
  refine matrixPowers_tendsto_zero_of_pseudospectralRadiusLt n A X X_inv J
    Nm ε hXr hsim hshape ρ hρ0 hρ1 hdiagbd hsup hrun h0 hps v c hc hComp ?_
  -- Reconcile the printed budget shape with Theorem 18.1's (18.13) casts.
  have hbudget' :
      4 * ((1 : ℕ) : ℝ) * c *
        (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A
      = 4 * c *
        (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A := by
    rw [Nat.cast_one]; ring
  rw [hbudget', pow_one]
  exact hbudget

-- Axiom check (removed): every delivered theorem
-- (`pseudospectrum_in_unit_disc_of_pseudospectralRadiusLt`,
-- `spectrum_norm_lt_one_of_pseudospectralRadiusLt`,
-- `spectralRadius_lt_one_of_pseudospectralRadiusLt`,
-- `matrixPowers_tendsto_zero_of_pseudospectralRadiusLt`,
-- `higham_18_2_pseudospectral_criterion`) depends only on the standard trio
-- `[propext, Classical.choice, Quot.sound]` — no `sorry`, `admit`, custom
-- axiom, `unsafe`, `opaque`, or `set_option` escape hatch.

end NumStability
