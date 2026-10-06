import NumStability.Source.Higham.Chapter04.Problem04
import NumStability.Source.Higham.Chapter28.Section06.Companion.CompanionSpectral

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28CompanionSpectral under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

open scoped BigOperators ComplexConjugate
open Matrix Module Polynomial

noncomputable section
namespace NumStability
private theorem companion_normal_higher_a0_unit (m : ℕ) (a : ℕ → ℂ)
    (h : (companionMatrix (m + 3) a).conjTranspose * companionMatrix (m + 3) a =
      companionMatrix (m + 3) a * (companionMatrix (m + 3) a).conjTranspose) :
    star (a 0) * a 0 = 1 := by
  let ell : Fin (m + 3) := Fin.last (m + 2)
  have hd := congrArg
    (fun M : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ => M ell ell) h
  rw [companion_conjTranspose_mul_self] at hd
  simp [companionGramFormula, ell, companionMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply] at hd
  let p : Fin (m + 3) := ⟨m + 1, by omega⟩
  have hp : ∀ x : Fin (m + 3), m + 1 = x.val ↔ x = p := by
    intro x
    constructor
    · intro hx
      exact Fin.ext hx.symm
    · rintro rfl
      rfl
  simp_rw [hp] at hd
  simp at hd
  exact hd

private theorem companion_normal_higher_coeff_vanish
    (m k : ℕ) (a : ℕ → ℂ) (hk0 : 0 < k) (hk : k < m + 2)
    (h : (companionMatrix (m + 3) a).conjTranspose * companionMatrix (m + 3) a =
      companionMatrix (m + 3) a * (companionMatrix (m + 3) a).conjTranspose) :
    a k = 0 := by
  let i : Fin (m + 3) := ⟨m + 2 - k, by omega⟩
  have hi0 : 0 < i.val := by simp [i]; omega
  have hicond : i.val + 1 < m + 3 := by simp [i]; omega
  have hd := congrArg
    (fun M : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ => M i i) h
  rw [companion_conjTranspose_mul_self] at hd
  simp [companionGramFormula, companionMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, hicond, hi0.ne'] at hd
  let p : Fin (m + 3) := ⟨i.val - 1, by omega⟩
  have hp : ∀ x : Fin (m + 3), i.val = x.val + 1 ↔ x = p := by
    intro x
    constructor
    · intro hx
      apply Fin.ext
      simp [p]
      omega
    · rintro rfl
      simp [p]
      omega
  simp_rw [hp] at hd
  simp at hd
  have hrev : m + 2 - i.val = k := by simp [i]; omega
  simpa [hrev] using hd

private theorem companion_normal_higher_last_coeff_vanish (m : ℕ) (a : ℕ → ℂ)
    (h : (companionMatrix (m + 3) a).conjTranspose * companionMatrix (m + 3) a =
      companionMatrix (m + 3) a * (companionMatrix (m + 3) a).conjTranspose) :
    a (m + 2) = 0 := by
  let ell : Fin (m + 3) := Fin.last (m + 2)
  let z : Fin (m + 3) := ⟨0, by omega⟩
  have ha1 : a 1 = 0 :=
    companion_normal_higher_coeff_vanish m 1 a (by omega) (by omega) h
  have he := congrArg
    (fun M : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ => M ell z) h
  rw [companion_conjTranspose_mul_self] at he
  simp [companionGramFormula, companionMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, ell, z] at he
  let p : Fin (m + 3) := ⟨m + 1, by omega⟩
  have hp : ∀ x : Fin (m + 3), m + 1 = x.val ↔ x = p := by
    intro x
    constructor
    · intro hx
      exact Fin.ext hx.symm
    · rintro rfl
      rfl
  simp_rw [hp] at he
  simp at he
  have hindex : m + 2 - p.val = 1 := by simp [p]
  rw [hindex, ha1] at he
  have ha0unit := companion_normal_higher_a0_unit m a h
  have ha0ne : star (a 0) ≠ 0 := by
    intro ha0
    rw [ha0, zero_mul] at ha0unit
    norm_num at ha0unit
  have he' : star (a 0) * a (m + 2) = 0 := by simpa using he
  exact (mul_eq_zero.mp he').resolve_left ha0ne

/-- Exact higher-order repair of the false normality statement on p. 523.
For orders at least three, a companion is normal exactly when the constant
coefficient has unit modulus and every higher coefficient vanishes. Order two
is governed separately by `companion_orderTwo_isStarNormal_iff`. -/
theorem companion_orderAtLeastThree_isStarNormal_iff
    (m : ℕ) (a : ℕ → ℂ) :
    IsStarNormal (companionMatrix (m + 3) a) ↔
      star (a 0) * a 0 = 1 ∧
        ∀ k, 0 < k → k < m + 3 → a k = 0 := by
  rw [isStarNormal_iff]
  change
    (companionMatrix (m + 3) a).conjTranspose * companionMatrix (m + 3) a =
        companionMatrix (m + 3) a *
          (companionMatrix (m + 3) a).conjTranspose ↔ _
  constructor
  · intro h
    refine ⟨companion_normal_higher_a0_unit m a h, ?_⟩
    intro k hk0 hk
    by_cases hlast : k = m + 2
    · simpa [hlast] using companion_normal_higher_last_coeff_vanish m a h
    · exact companion_normal_higher_coeff_vanish m k a hk0 (by omega) h
  · rintro ⟨ha0, ha⟩
    let ell : Fin (m + 3) := Fin.last (m + 2)
    have hcoeff : ∀ i : Fin (m + 3),
        a (m + 3 - 1 - i.val) = if i = ell then a 0 else 0 := by
      intro i
      by_cases hi : i = ell
      · subst i
        simp [ell]
      · rw [if_neg hi]
        apply ha
        · have hiv : i.val ≠ m + 2 := by
            intro hiv
            apply hi
            apply Fin.ext
            simpa [ell] using hiv
          omega
        · omega
    have hleft :
        (companionMatrix (m + 3) a).conjTranspose * companionMatrix (m + 3) a =
          (1 : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ) := by
      rw [companion_conjTranspose_mul_self]
      ext i j
      simp only [companionGramFormula, Matrix.one_apply]
      rw [hcoeff i, hcoeff j]
      have hicond : i.val + 1 < m + 3 ↔ i ≠ ell := by
        constructor
        · intro hi hlast
          subst i
          simp [ell] at hi
        · intro hine
          have hval : i.val ≠ m + 2 := by
            intro hval
            apply hine
            apply Fin.ext
            simpa [ell] using hval
          omega
      simp only [hicond]
      by_cases hi : i = ell
      · by_cases hj : j = ell
        · subst i
          subst j
          simpa using ha0
        · have hji : ell ≠ j := Ne.symm hj
          simp [hi, hj, hji]
      · by_cases hj : j = ell
        · simp [hi, hj]
        · simp [hi, hj]
    have hright :
        companionMatrix (m + 3) a *
            (companionMatrix (m + 3) a).conjTranspose =
          (1 : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ) :=
      mul_eq_one_comm.mp hleft
    rw [hleft, hright]

end NumStability
end
