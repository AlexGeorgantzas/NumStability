import NumStability.Algorithms.LeastSquares.LSQRSolve

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# Higham Chapter 20, Lemma 20.6

Canonical source-correspondence module for the symmetric perturbation minimizer and norm bounds.
-/

/-- Higham, 2nd ed., Chapter 20, Lemma 20.6, source-facing existential
    package.

An asymmetric perturbed augmented system with matrix perturbations `DeltaA1`
and `DeltaA2` admits a single symmetric perturbation `DeltaA` for which `y`
is an exact least-squares minimizer.  The witness is `DeltaA1` in the
zero-residual branch and the projector mixture from (20.22) in the nonzero
branch.  The same witness satisfies both printed combined bounds, for
`p = F` and for the repository's operator-2 predicate (`p = 2`). -/
theorem higham20_lemma20_6_exists_symmetric_perturbation_minimizer_and_norm_bounds
    {m n : ℕ} (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b s : Fin m → ℝ) (y : Fin n → ℝ)
    (h : LSAsymmetricPerturbedAugmentedSystem A DeltaA1 DeltaA2 b s y)
    {alpha beta : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta) :
    ∃ DeltaA : Fin m → Fin n → ℝ,
      ((s = 0 ∧ DeltaA = DeltaA1) ∨
        (s ≠ 0 ∧ DeltaA = lsLemma20_6Perturbation s DeltaA1 DeltaA2)) ∧
      IsLeastSquaresMinimizer (fun i j => A i j + DeltaA i j) b y ∧
      frobNormRect DeltaA ≤
        Real.sqrt (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2) ∧
      rectOpNorm2Le DeltaA (Real.sqrt (alpha ^ 2 + beta ^ 2)) := by
  by_cases hs : s = 0
  · refine ⟨DeltaA1, Or.inl ⟨hs, rfl⟩, ?_, ?_, ?_⟩
    · exact
        LSAugmentedSystem.isLeastSquaresMinimizer_of_zero_rhs
          (fun i j => A i j + DeltaA1 i j) b (0 : Fin m → ℝ) y
          (LSAsymmetricPerturbedAugmentedSystem.to_augmentedSystem_of_s_eq_zero
            A DeltaA1 DeltaA2 b s y h hs)
    · have hrad_nonneg :
          0 ≤ frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2 :=
        add_nonneg (sq_nonneg _) (sq_nonneg _)
      have hroot_sq :
          Real.sqrt
              (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2) ^ 2 =
            frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2 :=
        Real.sq_sqrt hrad_nonneg
      nlinarith [frobNormRect_nonneg DeltaA1,
        frobNormRect_nonneg DeltaA2,
        Real.sqrt_nonneg
          (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2)]
    · have hrad_nonneg : 0 ≤ alpha ^ 2 + beta ^ 2 :=
        add_nonneg (sq_nonneg _) (sq_nonneg _)
      have hroot_sq :
          Real.sqrt (alpha ^ 2 + beta ^ 2) ^ 2 = alpha ^ 2 + beta ^ 2 :=
        Real.sq_sqrt hrad_nonneg
      have halpha_root : alpha ≤ Real.sqrt (alpha ^ 2 + beta ^ 2) := by
        nlinarith [Real.sqrt_nonneg (alpha ^ 2 + beta ^ 2), sq_nonneg beta]
      intro x
      exact (hDeltaA1 x).trans
        (mul_le_mul_of_nonneg_right halpha_root (vecNorm2_nonneg x))
  · have hsq : vecNorm2Sq s ≠ 0 :=
      lsLemma20_6Projector_den_ne_zero_of_ne_zero hs
    let DeltaA := lsLemma20_6Perturbation s DeltaA1 DeltaA2
    let sbar : Fin m → ℝ :=
      fun i => lsLemma20_6Beta s DeltaA1 DeltaA2 y * s i
    have haug :
        LSAugmentedSystem (fun i j => A i j + DeltaA i j) b
          (0 : Fin n → ℝ) sbar y := by
      simpa [DeltaA, sbar] using
        LSAsymmetricPerturbedAugmentedSystem.to_augmentedSystem_of_s_ne_zero
          A DeltaA1 DeltaA2 b s y h hs
    refine ⟨DeltaA, Or.inr ⟨hs, rfl⟩, ?_, ?_, ?_⟩
    · exact
        LSAugmentedSystem.isLeastSquaresMinimizer_of_zero_rhs
          (fun i j => A i j + DeltaA i j) b sbar y haug
    · simpa [DeltaA] using
        lsLemma20_6Perturbation_norm_bound_two_frob
          s hsq DeltaA1 DeltaA2
    · simpa [DeltaA] using
        lsLemma20_6Perturbation_norm_bound_two_operator
          s hsq DeltaA1 DeltaA2 halpha hbeta hDeltaA1 hDeltaA2

end NumStability
