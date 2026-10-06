import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixNorms.SpectralRadius

/-!
# Analysis.LinearOperators.Pseudospectra.Perturbation.Definitions

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/MatrixPowersPseudospectral.lean
--
-- Higham Chapter 18, eq (18.9) and the Theorem 18.2 pseudospectral
-- packaging: the ε-pseudospectrum in perturbation form, the bounded form
-- of the pseudospectral radius, and the assembly that reduces Theorem 18.2
-- to the (closed) complex-Jordan Theorem 18.1 with t = 1.




namespace NumStability

open scoped BigOperators

-- ============================================================
-- §18.2  Eq (18.9): pseudospectrum and pseudospectral radius
-- ============================================================

/-- **Eq (18.9) carrier — the ε-pseudospectrum in perturbation form**
    (Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §18.2,
    p. 346): the set of eigenvalue moduli attained by any perturbation
    `A + ΔA` with `Nm ΔA ≤ ε`.  The perturbation-size functional `Nm` is a
    parameter: the book uses the 2-norm; any matrix norm instantiates it.
    (The book's Λ_ε is the set of the eigenvalues themselves; for the radius
    (18.9) only their moduli matter, and this carrier matches the repo's
    `ComplexMatrixEigenvalueModulusSet` spectral-radius vocabulary.) -/
def PseudospectrumModulusSet {n : ℕ} (Nm : CMatrix n n → ℝ) (ε : ℝ)
    (A : CMatrix n n) : Set ℝ :=
  {r | ∃ ΔA : CMatrix n n, Nm ΔA ≤ ε ∧
    r ∈ ComplexMatrixEigenvalueModulusSet (fun i j => A i j + ΔA i j)}

/-- **Eq (18.9), bounded form**: "the ε-pseudospectral radius of `A` is
    below `r`" — every eigenvalue modulus of every admissible perturbation
    is `< r`.  This is `ρ_ε(A) < r` without committing to a supremum. -/
def PseudospectralRadiusLt {n : ℕ} (Nm : CMatrix n n → ℝ) (ε r : ℝ)
    (A : CMatrix n n) : Prop :=
  ∀ x ∈ PseudospectrumModulusSet Nm ε A, x < r

/-- The unperturbed spectrum sits inside the ε-pseudospectrum whenever the
    zero perturbation is admissible (`Nm 0 ≤ ε`). -/
theorem eigenvalueModulusSet_subset_pseudospectrum {n : ℕ}
    (Nm : CMatrix n n → ℝ) (ε : ℝ) (A : CMatrix n n)
    (h0 : Nm (fun _ _ => (0:ℂ)) ≤ ε) :
    ComplexMatrixEigenvalueModulusSet A ⊆
      PseudospectrumModulusSet Nm ε A := by
  intro r hr
  refine ⟨fun _ _ => 0, h0, ?_⟩
  have hA : (fun i j => A i j + (0:ℂ)) = A := by
    funext i j
    exact add_zero _
  rw [hA]
  exact hr

/-- The pseudospectrum grows with `ε`. -/
theorem pseudospectrumModulusSet_mono {n : ℕ} (Nm : CMatrix n n → ℝ)
    {ε ε' : ℝ} (h : ε ≤ ε') (A : CMatrix n n) :
    PseudospectrumModulusSet Nm ε A ⊆ PseudospectrumModulusSet Nm ε' A := by
  rintro r ⟨ΔA, hΔ, hr⟩
  exact ⟨ΔA, hΔ.trans h, hr⟩

/-- `ρ_ε(A) < r` is antitone in the pseudospectrum: it transfers down to
    smaller `ε` and up to larger `r`. -/
theorem pseudospectralRadiusLt_mono {n : ℕ} (Nm : CMatrix n n → ℝ)
    {ε ε' r r' : ℝ} (hε : ε' ≤ ε) (hr : r ≤ r') (A : CMatrix n n)
    (h : PseudospectralRadiusLt Nm ε r A) :
    PseudospectralRadiusLt Nm ε' r' A :=
  fun x hx => lt_of_lt_of_le
    (h x (pseudospectrumModulusSet_mono Nm hε A hx)) hr

-- ============================================================
-- §18.2  Theorem 18.2: the spectral-gap bridge and the packaging
-- ============================================================


















































































end NumStability
