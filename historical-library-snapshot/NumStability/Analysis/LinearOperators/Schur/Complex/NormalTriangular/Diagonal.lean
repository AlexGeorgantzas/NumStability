import Mathlib.Analysis.CStarAlgebra.Matrix
import NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Schur
import NumStability.Analysis.LinearOperators.Schur.Complex.Triangulation

/-!
# Analysis.LinearOperators.Schur.Complex.NormalTriangular.Diagonal

R07 canonical `reusable` leaf. Declaration-level review groups 3 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.normal_upperTriangular_isDiag`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.MatrixPowersSchur`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


open scoped Matrix.Norms.L2Operator BigOperators Matrix

namespace NumStability

noncomputable section

variable {n : ℕ}

/-- The `(i,i)` entry of `T Tᴴ` is the sum of squared moduli of row `i` of `T`. -/
private theorem mul_conjTranspose_diag (T : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (T * Tᴴ) i i = ∑ j, (‖T i j‖ : ℂ) ^ 2 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, RCLike.mul_conj]
  norm_cast

/-- The `(i,i)` entry of `Tᴴ T` is the sum of squared moduli of column `i` of `T`. -/
private theorem conjTranspose_mul_diag (T : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (Tᴴ * T) i i = ∑ k, (‖T k i‖ : ℂ) ^ 2 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, RCLike.conj_mul]
  norm_cast

/-- **A normal upper-triangular matrix is diagonal.**  If `T` is upper triangular
(`T i j = 0` for `j < i`) and normal (`Tᴴ * T = T * Tᴴ`), then `T i j = 0` for
`i ≠ j`.  This is the Schur-form statement Higham uses on p. 342 for normal `A`
("`J` is diagonal"); it is proved here from primitives, not taken from Mathlib.

Proof by strong induction on the row index `i`: assuming every earlier row `i' <
i` is diagonal, column `i` of `T` has only the diagonal entry surviving, so
`(Tᴴ T)_{ii} = |T i i|²`; upper-triangularity gives `(T Tᴴ)_{ii} = ∑_{j≥i} |T i
j|²`; normality equates them, forcing every super-diagonal `T i j` (`j > i`) to
vanish. -/
theorem normal_upperTriangular_isDiag {T : Matrix (Fin n) (Fin n) ℂ}
    (hUpper : ∀ i j : Fin n, (j : ℕ) < (i : ℕ) → T i j = 0)
    (hNormal : Tᴴ * T = T * Tᴴ) :
    ∀ i j : Fin n, i ≠ j → T i j = 0 := by
  -- We prove, by strong induction on the natural number `N = (i : ℕ)`, that
  -- every row `i` is diagonal:  `T i j = 0` for `j ≠ i`.
  have key : ∀ N : ℕ, ∀ i : Fin n, (i : ℕ) = N → ∀ j : Fin n, i ≠ j → T i j = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
      intro i hiN j hij
      -- Column `i` of `T` has only the diagonal entry:  `T k i = 0` for `k ≠ i`.
      have hcol : ∀ k : Fin n, k ≠ i → T k i = 0 := by
        intro k hk
        rcases lt_trichotomy (k : ℕ) (i : ℕ) with hki | hki | hki
        · -- k < i: earlier row, diagonal by IH; `k ≠ i`
          exact IH (k : ℕ) (hiN ▸ hki) k rfl i hk
        · exact absurd (Fin.ext hki) hk
        · -- k > i: below diagonal, upper-triangular
          exact hUpper k i hki
      -- `(Tᴴ T)_{ii} = ∑_k |T k i|² = |T i i|²`, since off-diagonal column entries vanish.
      have hTHT : (Tᴴ * T) i i = (‖T i i‖ : ℂ) ^ 2 := by
        rw [conjTranspose_mul_diag]
        rw [Finset.sum_eq_single i]
        · rintro k _ hk; rw [hcol k hk]; simp
        · intro h; exact absurd (Finset.mem_univ i) h
      -- `(T Tᴴ)_{ii} = ∑_j |T i j|²`.
      have hTTH : (T * Tᴴ) i i = ∑ j, (‖T i j‖ : ℂ) ^ 2 := mul_conjTranspose_diag T i
      -- Normality:  ∑_j |T i j|² = |T i i|².
      have hEq : ∑ j, (‖T i j‖ : ℂ) ^ 2 = (‖T i i‖ : ℂ) ^ 2 := by
        rw [← hTTH, ← hNormal, hTHT]
      -- Move to real sums:  ∑_j |T i j|² = |T i i|²  in ℝ.
      have hEqR : ∑ j, ‖T i j‖ ^ 2 = ‖T i i‖ ^ 2 := by
        have hcast : ((∑ j, ‖T i j‖ ^ 2 : ℝ) : ℂ) = ((‖T i i‖ ^ 2 : ℝ) : ℂ) := by
          push_cast
          exact hEq
        exact_mod_cast hcast
      -- Split off the diagonal term:  ∑_{j ≠ i} |T i j|² = 0.
      have hzero : ∑ j ∈ Finset.univ.erase i, ‖T i j‖ ^ 2 = 0 := by
        have hsplit : ∑ j, ‖T i j‖ ^ 2
            = ‖T i i‖ ^ 2 + ∑ j ∈ Finset.univ.erase i, ‖T i j‖ ^ 2 := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]; ring
        rw [hsplit] at hEqR
        linarith
      -- Every off-diagonal term is `≥ 0`, so all vanish; in particular `T i j`.
      have hji_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨(Ne.symm hij), Finset.mem_univ j⟩
      have hterm : ‖T i j‖ ^ 2 = 0 := by
        by_contra hne
        have hpos : 0 < ‖T i j‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hne)
        have hle : ‖T i j‖ ^ 2 ≤ ∑ j' ∈ Finset.univ.erase i, ‖T i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖T i j'‖ ^ 2)
            (fun _ _ => by positivity) hji_mem
        rw [hzero] at hle
        linarith
      have : ‖T i j‖ = 0 := by nlinarith [norm_nonneg (T i j)]
      exact norm_eq_zero.mp this
  intro i j hij
  exact key (i : ℕ) i rfl j hij

end

end NumStability
