-- Analysis/SemiconvergentSpectral.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 17 "Stationary Iterative Methods", §17.4 "Singular Systems",
-- eq (17.22) / `[106, Lem 6.9]`: the SPECTRAL substance behind the existence
-- of the semiconvergent block form.
--
-- SCOPE AND HONESTY.  The companion module
-- `Algorithms/StationaryIterationSemiconvergentExistence.lean` REPACKAGES the
-- block form: given a block-diagonalizing basis `X` outright, it assembles the
-- similarity `X⁻¹GX = diag(I_r, Γ)`.  The genuine analytic gap it explicitly
-- folds into its encoding is the derivation, *from convergence of `Gᵐ`*, of the
-- spectral facts that PRODUCE that basis:
--   (1) the eigenvalue `1` of `G` is semisimple;
--   (2) every other eigenvalue `μ` of `G` has `|μ| < 1`;
--   (3) a REAL invariant basis `X` fixing the first `r` columns and giving a
--       `Γ`-block;
--   (4) the specific ∞-norm row-sum contraction `‖Γ‖∞ ≤ q < 1`.
--
-- This module contributes ONLY what is cleanly, UNCONDITIONALLY provable toward
-- that gap using Mathlib v4.29's eigenspace / primary-decomposition and
-- power-convergence API.  It does NOT close the full existence, and it does not
-- restate the companion module's repackaging.  Concretely it proves:
--
--   * A. NECESSITY of the eigenvalue-modulus bound (the honest converse of the
--     forward machinery in `MatrixPowers*`).  If `f` has an eigenvector for
--     eigenvalue `μ` and the orbit `n ↦ (f^n) v` is bounded (in particular if
--     `(f^n) v` converges, which semiconvergence of `Gᵐ` supplies), then
--     `‖μ‖ ≤ 1`; and if `‖μ‖ > 1` the orbit is genuinely unbounded.  This is
--     the rigorous, unconditional heart of constraint (2)'s *closed unit disk*
--     half — see the OBSTRUCTION note for why the strict `< 1` for `μ ≠ 1` and
--     the semisimplicity of `1` (constraint (1)) are NOT reachable from mere
--     boundedness/convergence with Mathlib as-is.
--
--   * B. The SEMISIMPLE COLLAPSE at eigenvalue `1`: for a finitely-semisimple
--     endomorphism the maximal generalized eigenspace at `1` equals the ordinary
--     eigenspace.  This is the exact algebraic upgrade that turns the
--     eigenvalue-`1` primary block into the identity block `I_r` of eq (17.22)
--     — i.e. constraint (1) DOWNSTREAM of semisimplicity, cleanly instantiated.
--
--   * C. The PRIMARY DECOMPOSITION as an internal direct sum: over an
--     algebraically closed field a finite-dimensional space is the internal
--     direct sum of the maximal generalized eigenspaces of any endomorphism.
--     This is the structural skeleton of the ℂ block splitting invoked (but not
--     built) in the companion module's header.
--
-- OBSTRUCTIONS (documented, not smuggled).  See the closing comment block for a
-- precise, itemized statement of exactly which Mathlib lemmas are missing to
-- close each of (1)-(4).  Nothing below assumes any of (1)-(4); every hypothesis
-- is either a genuine spectral input (an eigenvector, semisimplicity as a
-- hypothesis) or a boundedness/convergence input that semiconvergence supplies.
--
-- No `sorry`/`admit`/`axiom`.

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.LiminfLimsup

namespace NumStability

open scoped BigOperators Topology
open Module

-- ============================================================
-- §17.4  A. Necessity of the eigenvalue-modulus bound
--            (honest converse of the power-convergence machinery)
-- ============================================================

section ModulusNecessity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22) — necessity of `|μ| ≤ 1` for a semiconvergent iteration matrix.

    If `v` is an eigenvector of `f` for eigenvalue `μ` (so `f v = μ • v`, `v ≠ 0`)
    and the orbit `n ↦ (f^n) v = μ^n • v` is bounded above in norm, then
    `‖μ‖ ≤ 1`.

    This is the UNCONDITIONAL converse of the forward "spectral radius `< 1` ⟹
    powers decay" machinery of the `MatrixPowers*` modules: for `G` semiconvergent
    the orbit `Gᵐ v` even *converges*, which is stronger than the boundedness
    hypothesised here, so `|μ| ≤ 1` for every eigenvalue.  It is exactly the
    *closed-unit-disk* half of the printed spectral condition on `G`. -/
theorem eigenvalue_norm_le_one_of_orbit_bddAbove
    {f : End 𝕜 V} {μ : 𝕜} {v : V} (hv : f.HasEigenvector μ v)
    (hbdd : BddAbove (Set.range fun n : ℕ => ‖(f ^ n) v‖)) :
    ‖μ‖ ≤ 1 := by
  by_contra hgt
  push_neg at hgt
  -- The orbit norms are exactly `‖μ‖^n * ‖v‖`.
  have horbit : ∀ n : ℕ, ‖(f ^ n) v‖ = ‖μ‖ ^ n * ‖v‖ := by
    intro n
    rw [hv.pow_apply n, norm_smul, norm_pow]
  -- `v ≠ 0`, so `‖v‖ > 0`.
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv.2
  -- With `‖μ‖ > 1`, `‖μ‖^n → ∞`, so `‖μ‖^n * ‖v‖ → ∞`, contradicting boundedness.
  have hdiv : Filter.Tendsto (fun n : ℕ => ‖μ‖ ^ n * ‖v‖) Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hgt).atTop_mul_const hvpos
  have hdiv' : Filter.Tendsto (fun n : ℕ => ‖(f ^ n) v‖) Filter.atTop Filter.atTop := by
    simpa [horbit] using hdiv
  exact (Filter.not_bddAbove_of_tendsto_atTop hdiv') hbdd

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22) — the same modulus bound directly from CONVERGENCE of the orbit.

    If `v` is an eigenvector of `f` for eigenvalue `μ` and the orbit
    `n ↦ (f^n) v` converges to some `w`, then `‖μ‖ ≤ 1`.  This is the form that
    matches semiconvergence of `G` verbatim: `Gᵐ` converges entrywise, hence so
    does every eigenvector orbit, forcing every eigenvalue into the closed unit
    disk.  Unconditional. -/
theorem eigenvalue_norm_le_one_of_orbit_tendsto
    {f : End 𝕜 V} {μ : 𝕜} {v : V} (hv : f.HasEigenvector μ v)
    {w : V} (hw : Filter.Tendsto (fun n : ℕ => (f ^ n) v) Filter.atTop (𝓝 w)) :
    ‖μ‖ ≤ 1 := by
  refine eigenvalue_norm_le_one_of_orbit_bddAbove hv ?_
  -- A convergent sequence in norm is bounded above.
  have hnorm : Filter.Tendsto (fun n : ℕ => ‖(f ^ n) v‖) Filter.atTop (𝓝 ‖w‖) :=
    (continuous_norm.tendsto w).comp hw
  simpa using hnorm.isBoundedUnder_le.bddAbove_range

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22) — the contrapositive divergence statement.

    If `v` is an eigenvector of `f` for an eigenvalue `μ` OUTSIDE the closed unit
    disk (`‖μ‖ > 1`), then the orbit `n ↦ (f^n) v` is norm-unbounded and cannot
    converge.  This is the precise obstruction that semiconvergence rules out:
    an eigenvalue of modulus `> 1` is incompatible with convergent powers. -/
theorem orbit_norm_tendsto_atTop_of_eigenvalue_norm_gt_one
    {f : End 𝕜 V} {μ : 𝕜} {v : V} (hv : f.HasEigenvector μ v) (hμ : 1 < ‖μ‖) :
    Filter.Tendsto (fun n : ℕ => ‖(f ^ n) v‖) Filter.atTop Filter.atTop := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv.2
  have horbit : (fun n : ℕ => ‖(f ^ n) v‖) = fun n : ℕ => ‖μ‖ ^ n * ‖v‖ := by
    funext n; rw [hv.pow_apply n, norm_smul, norm_pow]
  rw [horbit]
  exact (tendsto_pow_atTop_atTop_of_one_lt hμ).atTop_mul_const hvpos

end ModulusNecessity

-- ============================================================
-- §17.4  B. The semisimple collapse at eigenvalue `1`
-- ============================================================

section SemisimpleCollapse

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22) — the semisimple collapse of the eigenvalue-`1` block.

    For a finitely-semisimple endomorphism `f`, the maximal *generalized*
    eigenspace at `1` coincides with the ordinary eigenspace at `1`:
    `maxGenEigenspace f 1 = eigenspace f 1`.  Equivalently there is no nilpotent
    part at `1`, so the eigenvalue-`1` primary block acts as the identity — this
    is precisely what turns that block into `I_r` in eq (17.22).

    This is the DOWNSTREAM half of constraint (1): given semisimplicity at `1`
    (which for a semiconvergent `G` is exactly the folded-in hypothesis), the
    generalized eigenspace collapses to eigenvectors, matching the companion
    module's `hGcolTop` condition `G · xₖ = xₖ`.  Unconditional in the semisimple
    hypothesis. -/
theorem maxGenEigenspace_one_eq_eigenspace_of_isFinitelySemisimple
    {f : End K V} (hf : f.IsFinitelySemisimple) :
    f.maxGenEigenspace 1 = f.eigenspace 1 :=
  hf.maxGenEigenspace_eq_eigenspace 1

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22) — the semisimple collapse at every eigenvalue, in particular at
    `1`.  Companion to the previous lemma: for a finitely-semisimple `f` and any
    scalar `μ`, `maxGenEigenspace f μ = eigenspace f μ`.  Applied at each of the
    eigenvalues `μ ≠ 1` this states that the `Γ`-block of eq (17.22) is itself
    diagonalizable (no Jordan blocks off `1`), which is the structural content
    that makes `Γ` behave like a genuine contraction once `|μ| < 1`. -/
theorem maxGenEigenspace_eq_eigenspace_of_isFinitelySemisimple
    {f : End K V} (hf : f.IsFinitelySemisimple) (μ : K) :
    f.maxGenEigenspace μ = f.eigenspace μ :=
  hf.maxGenEigenspace_eq_eigenspace μ

end SemisimpleCollapse

-- ============================================================
-- §17.4  C. The primary decomposition as an internal direct sum
-- ============================================================

section PrimaryDecomposition

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22) — the primary (generalized-eigenspace) decomposition as an
    INTERNAL DIRECT SUM.

    Over an algebraically closed field, a finite-dimensional space is the
    internal direct sum of the maximal generalized eigenspaces of any
    endomorphism `f`:
    `DirectSum.IsInternal (fun μ => maxGenEigenspace f μ)`.

    This is the structural skeleton of the ℂ block splitting quoted in the
    companion module's header (the combination of
    `iSup_maxGenEigenspace_eq_top` and `independent_maxGenEigenspace`).  It is
    the invariant-subspace decomposition that, after grouping the `1`-block
    against the rest and descending to `ℝ`, would supply the basis `X` of
    eq (17.22) — see the OBSTRUCTION note for why the grouping + ℂ→ℝ descent is
    not yet mechanizable.  Unconditional. -/
theorem isInternal_maxGenEigenspace (f : End K V) :
    DirectSum.IsInternal (fun μ : K => f.maxGenEigenspace μ) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace f.iSup_maxGenEigenspace_eq_top

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22) — the eigenvalue-`1` primary block of the internal direct sum.

    Specializing the internal direct sum to a finitely-semisimple `f`, the
    summand at `1` is the ordinary eigenspace `eigenspace f 1` (by the semisimple
    collapse of Part B), so the eigenvalue-`1` block of the decomposition is
    genuinely `I_r` on that eigenspace.  This packages the "identity block" of
    eq (17.22) as a single statement: the primary decomposition holds AND its
    `1`-summand is the ordinary `1`-eigenspace.  Unconditional in the semisimple
    hypothesis. -/
theorem isInternal_maxGenEigenspace_and_one_block
    {f : End K V} (hf : f.IsFinitelySemisimple) :
    DirectSum.IsInternal (fun μ : K => f.maxGenEigenspace μ) ∧
      f.maxGenEigenspace 1 = f.eigenspace 1 :=
  ⟨isInternal_maxGenEigenspace f, hf.maxGenEigenspace_eq_eigenspace 1⟩

end PrimaryDecomposition

-- ============================================================
-- §17.4  D. OBSTRUCTIONS: what remains for the full [106, Lem 6.9]
-- ============================================================
--
-- The four steps of the true existence, and the exact missing piece for each.
--
-- (1) EIGENVALUE 1 IS SEMISIMPLE, from convergence of `Gᵐ`.
--     Part B collapses `maxGenEigenspace 1` to `eigenspace 1` GIVEN
--     `f.IsFinitelySemisimple`.  What is missing is the analytic implication
--     "`Gᵐ` converges (or is bounded) ⟹ the eigenvalue-`1` generalized
--     eigenspace has no nilpotent part".  Concretely: a nontrivial Jordan block
--     at `1` makes `Gᵐ` grow like `m` (the superdiagonal contributes an entry
--     `m`), contradicting boundedness.  Mathlib has NO lemma of the form
--     "power-bounded ⟹ eigenvalue `1` semisimple" nor the block-growth estimate
--     `‖(J₁(1))^m‖ ≥ m`.  The `MatrixPowersJordan` module builds Jordan-block
--     growth in the FORWARD direction (bounding powers of a scaled Jordan form)
--     but not the reverse quantitative lower bound needed here.  MISSING:
--     `IsPowerBounded f → (f.maxGenEigenspace 1 = f.eigenspace 1)`, or the
--     Jordan-block lower bound feeding it.
--
-- (2) ALL OTHER EIGENVALUES HAVE |μ| < 1.
--     Part A proves the CLOSED-disk bound `|μ| ≤ 1` unconditionally from orbit
--     boundedness/convergence (`eigenvalue_norm_le_one_of_orbit_tendsto`).  The
--     STRICT bound `|μ| < 1` for `μ ≠ 1` needs more than convergence of `Gᵐ`:
--     an eigenvalue on the unit circle with `μ ≠ 1` (e.g. `μ = -1` or a root of
--     unity) has bounded — but NON-convergent — powers, so `μ` on the unit
--     circle is excluded only by using that `Gᵐ` CONVERGES (not merely is
--     bounded) together with `μ ≠ 1`: `μᵐ` converges iff `μ = 1` or `|μ| < 1`.
--     Mathlib lacks the scalar lemma "`Tendsto (μ^·) atTop (𝓝 c)` with `μ` on
--     the unit circle ⟹ `μ = 1`" in usable form, and the transfer from a
--     convergent operator power to a convergent scalar eigenvalue power on a
--     PARTIAL orbit is not packaged.  MISSING: the scalar dichotomy
--     `Tendsto (fun n => μ^n) atTop (𝓝 c) ↔ μ = 1 ∨ ‖μ‖ < 1` (for `‖μ‖ ≤ 1`),
--     plus its lift to `f`-eigenvectors.
--
-- (3) A REAL INVARIANT BASIS X (ℂ→ℝ descent).
--     Part C gives the internal direct sum over an algebraically closed field
--     (so over `ℂ`).  Producing a REAL basis `X` requires recombining each
--     conjugate pair of complex generalized-eigenspaces into a single real
--     invariant subspace and choosing a real basis of it — the standard
--     real-Jordan / real-primary decomposition.  Mathlib v4.29 has NO
--     real-primary-decomposition API: there is no
--     `Module.End.exists_real_invariant_complement` or real-block-diagonal
--     normal form for a real matrix with complex spectrum.  MISSING: the ℂ→ℝ
--     descent of the primary decomposition (conjugate-pair recombination) and
--     the reindexing that places the `1`-summand in coordinates `< r`.
--
-- (4) THE ∞-NORM ROW-SUM CONTRACTION ‖Γ‖∞ ≤ q < 1.
--     Even granting (2), `ρ(Γ) < 1` gives only that SOME operator norm of a
--     power `Γ^k` is `< 1`; the printed statement's repository strengthening is
--     the ∞-norm row-sum bound `‖Γ‖∞ ≤ q < 1`, which requires a DIAGONAL
--     similarity `D⁻¹ Γ D` bringing the row sums below `1` (standard: for
--     `ρ(Γ) < 1` one can choose `D` so that `‖D⁻¹ Γ D‖∞ < 1`).  This diagonal
--     re-scaling is an additional change of basis absorbed into `X`, and Mathlib
--     has no lemma delivering it.  MISSING:
--     `spectralRadius Γ < 1 → ∃ D diagonal invertible, ‖D⁻¹ Γ D‖∞ < 1`
--     (the ∞-norm realization of the spectral radius via a diagonal similarity).
--
-- CONCLUSION.  Part A closes the closed-unit-disk necessity unconditionally;
-- Parts B and C cleanly instantiate the algebraic skeleton (semisimple collapse
-- and the ℂ primary decomposition).  Constraints (1) full, (2) strict, (3), and
-- (4) each require a specific Mathlib lemma that does not yet exist, itemized
-- above.  This module therefore proves the STRONGEST honest sub-results toward
-- `[106, Lem 6.9]` without assuming any of (1)-(4).

end NumStability
