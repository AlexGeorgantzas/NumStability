import NumStability.Algorithms.TestMatrices.Higham28PascalOscillationCore
import NumStability.Algorithms.TestMatrices.Higham28PascalDualFlag

namespace NumStability

open scoped BigOperators
open Set

/-- Every zero-compatible sign completion of the rank-`i` Pascal eigenvector
has at least `i` adjacent sign changes. -/
theorem pascalSortedEigenvector_signChangeCount_ge
    {n : ℕ} (i : Fin (n + 1)) (s : Fin (n + 1) → Bool)
    (hs : IsSignCompletion (pascalSortedEigenvector (n + 1) i) s) :
    i.val ≤ boolSignChangeCount s := by
  by_cases hi : i.val = 0
  · omega
  · obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hi
    have hqn : q ≤ n := by omega
    obtain ⟨l, hn⟩ := Nat.exists_eq_add_of_le hqn
    subst n
    have hiq : i = (⟨q + 1, by omega⟩ : Fin (q + l + 1)) := by
      apply Fin.ext
      exact hq
    rw [hiq] at hs ⊢
    have hl : 0 < l := by omega
    let Q := pascalSortedEigenvectorMatrix (q + l + 1)
    have hQ : Q.transpose * Q = 1 :=
      pascalSortedEigenvectorMatrix_transpose_mul_self (q + l + 1)
    have hk : 0 < q + 1 := by omega
    have hkn : q + 1 ≤ q + l + 1 := by omega
    obtain ⟨ε, _hε, hminorLeading⟩ :=
      pascalOscillation_pascalLeadingPlucker_same_sign hk hkn
    have hlead : ∃ ε : ℝ,
        ∀ (u : Fin (q + 1) → Fin (q + l + 1)), StrictMono u →
          0 < ε * Matrix.det (fun a b : Fin (q + 1) =>
            Q (u a) (pascalOscillationLeadingColumn b)) := by
      refine ⟨ε, ?_⟩
      intro u hu
      let su : Set.powersetCard (Fin (q + l + 1)) (q + 1) :=
        Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.ofStrictMono u hu)
      have hp := hminorLeading su
      have heq : Matrix.det (fun a b : Fin (q + 1) =>
          Q (u a) (pascalOscillationLeadingColumn b)) =
          pascalLeadingPlucker (q + l + 1) (q + 1) hkn su := by
        rw [pascalLeadingPlucker, compoundMatrix_apply]
        congr 1
        funext a b
        simp [Q, su, initialPowerset, pascalOscillationLeadingColumn]
      rwa [heq]
    let B : Fin (q + l + 1) → Fin l → ℝ := fun r c =>
      (-1 : ℝ) ^ r.val * Q r (pascalOscillationTrailingColumn c)
    have hlocal : ∀ (f : Fin (l + 1) → Fin (q + l + 1)), StrictMono f →
        ∃ η : ℝ, ∀ r : Fin (l + 1),
          0 < η * Matrix.det (fun a b : Fin l =>
            B (f (r.succAbove a)) b) := by
      intro f hf
      simpa [B] using pascalOscillation_checkerTrailing_local_orientation Q hQ hlead f hf
    let c : Fin l := ⟨0, hl⟩
    have hcol : (fun r => B r c) =
        pascalOscillationCheckerVector
          (pascalSortedEigenvector (q + l + 1)
            (⟨q + 1, by omega⟩ : Fin (q + l + 1))) := by
      funext r
      simp only [B, c, pascalOscillationCheckerVector]
      change (-1 : ℝ) ^ r.val *
          pascalSortedEigenvectorMatrix (q + l + 1) r
            (pascalOscillationTrailingColumn (⟨0, hl⟩ : Fin l)) = _
      rw [pascalSortedEigenvectorMatrix_apply]
      congr 2
    have hscheck : IsSignCompletion (fun r => B r c) (pascalOscillationCheckerBool s) := by
      rw [hcol]
      exact pascalOscillationCheckerBool_isSignCompletion hs
    have hlt := pascalOscillation_tSystem_column_signChangeCount_lt_local
      B c hlocal (pascalOscillationCheckerBool s) hscheck
    have hsum := pascalOscillationCheckerBool_count_add s
    omega

/-- Higham, Section 28.4, p. 520: the eigenvector belonging to the `i`-th
strictly decreasing Pascal eigenvalue has exactly `i` sign changes, with zero
entries assigned either neighboring sign. -/
theorem pascalSortedEigenvector_hasExactlySignChanges
    {n : ℕ} (i : Fin (n + 1)) :
    HasExactlySignChanges (pascalSortedEigenvector (n + 1) i) i.val := by
  constructor
  · obtain ⟨s, hs⟩ := pascalOscillation_exists_signCompletion
      (pascalSortedEigenvector (n + 1) i)
    exact ⟨s, hs, pascalSortedEigenvector_signChangeCount_ge i s hs⟩
  · rintro ⟨s, hs, hmore⟩
    have hle := pascalSortedEigenvector_signChangeCount_le i s hs
    omega

end NumStability
