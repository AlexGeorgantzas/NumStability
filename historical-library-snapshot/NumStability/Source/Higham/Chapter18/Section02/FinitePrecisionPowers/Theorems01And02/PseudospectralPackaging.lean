import NumStability.Algorithms.MatrixPowers.ComputedIteration.Model
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.Complex
import NumStability.Analysis.LinearOperators.Pseudospectra.Perturbation.Definitions
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixNorms.SpectralRadius
import NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.ComplexJordan

/-!
# Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.PseudospectralPackaging

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




















































-- ============================================================
-- §18.2  Theorem 18.2: the spectral-gap bridge and the packaging
-- ============================================================

/-- **The [620]-consumption bridge in Theorem 18.2's proof** (Higham 2nd
    ed., §18.2, pp. 349–350): if the ε-pseudospectral radius of `A` is
    below 1, and some admissible ε-perturbation has an eigenvalue of modulus
    at least `ρ + g` (the dominant-perturbation witness that [620, 1995]
    provides with `g = κ₂(X)·ε/n²` up to the O(ε²) proviso), then
    `ρ + g < 1` — the spectral gap `1 − ρ` exceeds `g`. -/
theorem pseudospectral_gap {n : ℕ} (Nm : CMatrix n n → ℝ) (ε : ℝ)
    (A : CMatrix n n) (ρ g : ℝ)
    (hps : PseudospectralRadiusLt Nm ε 1 A)
    (h620 : ∃ ΔA : CMatrix n n, Nm ΔA ≤ ε ∧
      ∃ s ∈ ComplexMatrixEigenvalueModulusSet
        (fun i j => A i j + ΔA i j), ρ + g ≤ s) :
    ρ + g < 1 := by
  obtain ⟨ΔA, hΔ, s, hs, hle⟩ := h620
  exact lt_of_le_of_lt hle (hps s ⟨ΔA, hΔ, hs⟩)

/-- **Theorem 18.2 (Higham–Knight), pseudospectral packaging** (Higham,
    Accuracy and Stability of Numerical Algorithms, 2nd ed., §18.2,
    Theorem 18.2, pp. 349–350).

    Formalizes the printed proof skeleton exactly: `A` real and
    diagonalizable over ℂ (complex Jordan data with `t = 1`, i.e. diagonal
    `J`), the ε-pseudospectral radius below 1 (`hps`, eq (18.9) in
    perturbation form, perturbation size measured by any functional `Nm` —
    the book uses the 2-norm), a dominant ε-perturbation witness with
    guaranteed eigenvalue gain `g` (`h620`), and the constant-matching
    hypothesis `hgap` aligning `g` with the t = 1 Higham–Knight condition.
    Conclusion: the printed limit `‖v_m‖∞ → 0` for every computed-power
    sequence with per-step budget `c`, via the CLOSED complex-Jordan
    Theorem 18.1.

    HONESTY NOTES (what stays hypothesis, matching what the book leaves
    unproved): (a) `h620` is the eigenvalue-perturbation lower bound the
    book cites to [620, 1995] without proof, WITH the "provided the O(ε²)
    term can be ignored" proviso of the printed statement absorbed into it;
    (b) `hgap` packages the book's unspecified constant matching
    (`c_n = 4n²(n+2)` plus 2-norm/∞-norm equivalence factors the book
    absorbs into `c_n`).  Neither is derivable from the source text; both
    are exactly the steps the printed theorem takes on faith. -/
theorem higham_knight_18_2_pseudospectral (n : ℕ)
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
    (g : ℝ)
    (hps : PseudospectralRadiusLt Nm ε 1
      (fun i j => ((A i j : ℝ) : ℂ)))
    (h620 : ∃ ΔA : CMatrix n n, Nm ΔA ≤ ε ∧
      ∃ s ∈ ComplexMatrixEigenvalueModulusSet
        (fun i j => ((A i j : ℝ) : ℂ) + ΔA i j), ρ + g ≤ s)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hgap : 4 * c *
      (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A
      ≤ g) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) := by
  -- ρ + g < 1 from the pseudospectral hypothesis and the [620] witness
  have hgaplt : ρ + g < 1 :=
    pseudospectral_gap Nm ε _ ρ g hps h620
  -- the t = 1 Higham–Knight condition (18.13)
  have hCond : 4 * ((1:ℕ) : ℝ) * c *
      (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A
      < (1 - ρ) ^ (1:ℕ) := by
    rw [Nat.cast_one, pow_one]
    have h1 : 4 * (1:ℝ) * c *
        (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A
        = 4 * c *
        (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A := by
      ring
    rw [h1]
    linarith
  exact higham_18_1_complex_jordan_tendsto n A X X_inv J hXr hsim hshape
    ρ hρ0 hρ1 hdiagbd hsup 1 le_rfl hrun v c hc hComp hCond

end NumStability
