import NumStability.Analysis.LinearOperators.Pseudospectra.Perturbation.Definitions
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixNorms.SpectralRadius

/-!
# Analysis.LinearOperators.Pseudospectra.Perturbation.ConvergenceCriterion

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

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









































































































-- Axiom check (removed): every delivered theorem
-- (`pseudospectrum_in_unit_disc_of_pseudospectralRadiusLt`,
-- `spectrum_norm_lt_one_of_pseudospectralRadiusLt`,
-- `spectralRadius_lt_one_of_pseudospectralRadiusLt`,
-- `matrixPowers_tendsto_zero_of_pseudospectralRadiusLt`,
-- `higham_18_2_pseudospectral_criterion`) depends only on the standard trio
-- `[propext, Classical.choice, Quot.sound]` — no `sorry`, `admit`, custom
-- axiom, `unsafe`, `opaque`, or `set_option` escape hatch.

end NumStability
