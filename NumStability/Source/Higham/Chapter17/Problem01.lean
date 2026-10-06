import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import NumStability.Algorithms.MatrixPowersSpectral

/-!
# Higham Chapter 17, Problem 17.1

Canonical source-correspondence owner for the Gelfand-formula argument proving entrywise and infinity-norm summability of matrix powers under a strict spectral-radius bound.
-/

namespace NumStability

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Norm of the complexified `k`-th power of an arbitrary real matrix equals
    the repository infinity norm of the real power.  Bridge lemma for the
    Gelfand extraction below (generalizing `norm_absMatrixComplexified_pow`
    from the entrywise-absolute case to arbitrary real matrices). -/
theorem norm_complexified_pow (n : ℕ) (B : Fin n → Fin n → ℝ) (k : ℕ) :
    ‖((Matrix.of B).map Complex.ofReal) ^ k‖ = infNorm (matPow n B k) := by
  rw [← map_ofReal_pow, linfty_opNorm_map_ofReal, infNorm_eq_linfty_opNorm,
    matPow_eq_matrix_pow]

/-- **Gelfand extraction for an arbitrary real matrix** (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.2, discussion around
    eq (17.9): convergence of the powers `G^k` is governed by the spectral
    radius `ρ(G) < 1`): if the genuine Mathlib `spectralRadius` of the
    complexified matrix is at most `ρ` and `ρ < r`, then eventually
    `‖B^k‖∞ ≤ r^k`.  This generalizes
    `eventually_matPow_abs_le_of_spectralRadius_le` from `|A|` to an
    arbitrary real matrix `B`; the Gelfand argument is unchanged. -/
theorem eventually_matPow_le_of_spectralRadius_le (n : ℕ)
    (B : Fin n → Fin n → ℝ) (ρ r : ℝ) (hρ0 : 0 ≤ ρ) (hρr : ρ < r)
    (hspec : spectralRadius ℂ ((Matrix.of B).map Complex.ofReal) ≤
      ENNReal.ofReal ρ) :
    ∀ᶠ k in Filter.atTop, infNorm (matPow n B k) ≤ r ^ k := by
  haveI hfd : FiniteDimensional ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.finiteDimensional
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) :=
    FiniteDimensional.complete ℂ _
  have hr0 : 0 < r := lt_of_le_of_lt hρ0 hρr
  have hgel := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius
    ((Matrix.of B).map Complex.ofReal)
  have hlt : spectralRadius ℂ ((Matrix.of B).map Complex.ofReal) <
      ENNReal.ofReal r :=
    lt_of_le_of_lt hspec (ENNReal.ofReal_lt_ofReal_iff hr0 |>.mpr hρr)
  have hev : ∀ᶠ (k : ℕ) in Filter.atTop,
      ENNReal.ofReal (‖((Matrix.of B).map Complex.ofReal) ^ k‖ ^ (1 / (k:ℝ))) <
        ENNReal.ofReal r :=
    hgel.eventually_lt_const hlt
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with k hk hk1
  have hklt : ‖((Matrix.of B).map Complex.ofReal) ^ k‖ ^ (1 / (k:ℝ)) < r :=
    (ENNReal.ofReal_lt_ofReal_iff hr0).mp hk
  have hknorm0 : (0:ℝ) ≤ ‖((Matrix.of B).map Complex.ofReal) ^ k‖ :=
    norm_nonneg _
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
  -- Undo the 1/k root: x = (x^(1/k))^k for x ≥ 0, k ≠ 0.
  have hroot : ‖((Matrix.of B).map Complex.ofReal) ^ k‖ =
      (‖((Matrix.of B).map Complex.ofReal) ^ k‖ ^ (1 / (k:ℝ))) ^ (k:ℕ) := by
    rw [← Real.rpow_natCast
      (‖((Matrix.of B).map Complex.ofReal) ^ k‖ ^ (1 / (k:ℝ))) k,
      ← Real.rpow_mul hknorm0]
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hkR), Real.rpow_one]
  have hle : ‖((Matrix.of B).map Complex.ofReal) ^ k‖ ≤ r ^ k := by
    rw [hroot]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hknorm0 _) (le_of_lt hklt) k
  rw [norm_complexified_pow] at hle
  exact hle

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eqs (17.8)/(17.9): summability of `‖G^k‖∞` from the genuine spectral
    certificate `spectralRadius(G) ≤ ρ < 1` (Mathlib `spectralRadius` of the
    complexified matrix), via Gelfand's formula.  The series is split at the
    eventual index provided by `eventually_matPow_le_of_spectralRadius_le`
    with `r := (ρ + 1)/2` strictly between `ρ` and `1`.  Scope: unlike
    `summable_infNorm_matPow` this needs no norm certificate `‖G‖∞ < 1`. -/
theorem summable_infNorm_matPow_of_spectralRadius (n : ℕ)
    (B : Fin n → Fin n → ℝ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hspec : spectralRadius ℂ ((Matrix.of B).map Complex.ofReal) ≤
      ENNReal.ofReal ρ) :
    Summable (fun k => infNorm (matPow n B k)) := by
  set r := (ρ + 1) / 2 with hr
  have hρr : ρ < r := by rw [hr]; linarith
  have hr0 : 0 ≤ r := le_of_lt (lt_of_le_of_lt hρ0 hρr)
  have hr1 : r < 1 := by rw [hr]; linarith
  have hev := eventually_matPow_le_of_spectralRadius_le n B ρ r hρ0 hρr hspec
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  have hshift : Summable (fun k => infNorm (matPow n B (k + K))) := by
    refine Summable.of_nonneg_of_le (fun _ => infNorm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (r ^ K))
    calc infNorm (matPow n B (k + K))
        ≤ r ^ (k + K) := hK (k + K) (Nat.le_add_left K k)
      _ = r ^ K * r ^ k := by rw [pow_add]; ring
  exact (summable_nat_add_iff
    (f := fun k => infNorm (matPow n B k)) K).mp hshift

/-- Higham, Problem 17.1, in the exact form consumed by (17.8), (17.11),
    and (17.29): if the spectral radius of `B` is strictly below one, then
    every entry of the matrix series `∑ |B^k|` and the scalar series
    `∑ ‖B^k‖∞` are summable.  The first conjunct is the finite-dimensional
    meaning of convergence of the entrywise-absolute matrix series; the
    second uses the repository's matrix infinity norm. -/
theorem higham17_problem17_1 (n : ℕ)
    (B : Fin n → Fin n → ℝ)
    (hspec : spectralRadius ℂ ((Matrix.of B).map Complex.ofReal) < 1) :
    (∀ i j : Fin n, Summable (fun k => |matPow n B k i j|)) ∧
      Summable (fun k => infNorm (matPow n B k)) := by
  obtain ⟨r, _hr0', hrspec, hr1'⟩ := ENNReal.lt_iff_exists_real_btwn.mp hspec
  have hr0 : 0 < r := by
    by_contra h
    push_neg at h
    rw [ENNReal.ofReal_of_nonpos h] at hrspec
    exact (not_lt_bot hrspec).elim
  have hr1 : r < 1 := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp] at hr1'
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mp hr1'
  have hnorm : Summable (fun k => infNorm (matPow n B k)) :=
    summable_infNorm_matPow_of_spectralRadius n B r hr0.le hr1
      (le_of_lt hrspec)
  refine ⟨?_, hnorm⟩
  intro i j
  exact Summable.of_nonneg_of_le
    (fun _ => abs_nonneg _)
    (fun k =>
      le_trans
        (Finset.single_le_sum
          (fun l _ => abs_nonneg (matPow n B k i l))
          (Finset.mem_univ j))
        (row_sum_le_infNorm (matPow n B k) i))
    hnorm

end NumStability
