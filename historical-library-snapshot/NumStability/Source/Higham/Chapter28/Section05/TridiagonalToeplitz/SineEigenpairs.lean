import NumStability.Source.Higham.Chapter28.Section05.TridiagonalToeplitz.SineEigenvectors
import NumStability.Source.Higham.Chapter28.Section05.TridiagonalToeplitz.ToeplitzGeneral
import NumStability.Upstream.Lindemann.MonoidAlgebraCompat

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28ToeplitzGeneral under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

theorem generalToeplitz_sine_eigenpair {n : ℕ}
    (c d e : ℝ) (hc : 0 < c) (he : 0 < e) (k : Fin n) :
    Matrix.mulVec (tridiagonalToeplitz n c d e)
        (generalToeplitzSineVector c e k) =
      generalToeplitzEigenvalue n c d e k •
        generalToeplitzSineVector c e k := by
  let q := Real.sqrt c / Real.sqrt e
  let s := Real.sqrt c * Real.sqrt e
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hse : 0 < Real.sqrt e := Real.sqrt_pos.2 he
  have hcSq : Real.sqrt c * Real.sqrt c = c :=
    Real.mul_self_sqrt (le_of_lt hc)
  have heSq : Real.sqrt e * Real.sqrt e = e :=
    Real.mul_self_sqrt (le_of_lt he)
  have heq : e * q = s := by
    dsimp [q, s]
    field_simp [hse.ne']
    nlinarith
  have hcq : c = q * s := by
    dsimp [q, s]
    field_simp [hse.ne']
    nlinarith
  have hsqrt : Real.sqrt (c * e) = s := by
    dsimp [s]
    rw [Real.sqrt_mul (le_of_lt hc)]
  rw [generalToeplitzSineVector]
  have hsim := tridiagonalToeplitz_mulVec_scaled_similarity
    c d e q s (toeplitzSineVector n k) heq hcq
  rw [hsim]
  have heig := symmetricToeplitz_sine_eigenpair s d k
  rw [heig]
  funext i
  simp only [toeplitzScaledVector, Pi.smul_apply, smul_eq_mul,
    generalToeplitzEigenvalue]
  rw [hsqrt]
  simp [symmetricToeplitzEigenvalue, q]
  ring

/-- The scaled sine vector is nonzero on the positive source domain, so the
preceding equality is a genuine eigenpair. -/
theorem generalToeplitzSineVector_ne_zero {n : ℕ}
    (c e : ℝ) (hc : 0 < c) (he : 0 < e) (k : Fin n) :
    generalToeplitzSineVector c e k ≠ 0 := by
  have hq : Real.sqrt c / Real.sqrt e ≠ 0 :=
    div_ne_zero (ne_of_gt (Real.sqrt_pos.2 hc))
      (ne_of_gt (Real.sqrt_pos.2 he))
  intro hzero
  apply toeplitzSineVector_ne_zero k
  funext i
  have hi := congrFun hzero i
  simp only [generalToeplitzSineVector, toeplitzScaledVector,
    Pi.zero_apply] at hi
  exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero _ hq)

/-- The complexified symmetric Toeplitz matrix has the usual sine eigenpair,
with no sign restriction on its (possibly complex) off-diagonal scalar. -/
theorem complexSymmetricToeplitz_sine_eigenpair {n : ℕ}
    (s d : ℂ) (k : Fin n) :
    Matrix.mulVec (complexTridiagonalToeplitz n s d s)
        (fun i => (toeplitzSineVector n k i : ℂ)) =
      (d + 2 * s *
          (Real.cos (((k.val + 1 : ℕ) : ℝ) * Real.pi /
            (n + 1 : ℕ)) : ℂ)) •
        (fun i => (toeplitzSineVector n k i : ℂ)) := by
  funext i
  rw [complexTridiagonalToeplitz_mulVec_apply]
  have hreal := congrFun
    (symmetricToeplitz_sine_eigenpair (c := (1 : ℝ)) (d := (0 : ℝ)) k) i
  rw [tridiagonalToeplitz_mulVec_apply] at hreal
  have hcast := congrArg Complex.ofReal hreal
  simp only [symmetricToeplitzEigenvalue, zero_mul, zero_add, one_mul,
    Pi.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat] at hcast
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs at hcast ⊢ <;>
    simp only [Complex.ofReal_zero, Complex.ofReal_one,
      add_zero, zero_add] at hcast ⊢ <;>
    ring_nf at hcast ⊢ <;> linear_combination s * hcast

/-- Higham p. 522, unrestricted nontriangular case: for every printed index,
the displayed complex eigenvalue has an explicit sine eigenvector. -/
theorem generalToeplitz_complex_sine_eigenpair_of_super_ne_zero {n : ℕ}
    (c d e : ℝ) (he : e ≠ 0) (k : Fin n) :
    let s := realProductComplexSqrt c e
    let q := s / (e : ℂ)
    Matrix.mulVec (complexTridiagonalToeplitz n c d e)
        (complexToeplitzSineVector q k) =
      generalToeplitzComplexEigenvalue n c d e k •
        complexToeplitzSineVector q k := by
  dsimp only
  let s : ℂ := realProductComplexSqrt c e
  let q : ℂ := s / (e : ℂ)
  have heC : (e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he
  have heq : (e : ℂ) * q = s := by
    dsimp [q]
    field_simp
  have hsquare : s * s = ((c * e : ℝ) : ℂ) := by
    exact realProductComplexSqrt_sq c e
  have hcq : (c : ℂ) = q * s := by
    dsimp [q]
    rw [div_mul_eq_mul_div, hsquare, Complex.ofReal_mul]
    field_simp
  rw [complexToeplitzSineVector]
  rw [complexTridiagonalToeplitz_mulVec_scaled_similarity
    (c := (c : ℂ)) (d := (d : ℂ)) (e := (e : ℂ))
    (q := q) (s := s) _ heq hcq]
  rw [complexSymmetricToeplitz_sine_eigenpair]
  funext i
  simp only [complexToeplitzScaledVector, Pi.smul_apply, smul_eq_mul,
    generalToeplitzComplexEigenvalue, s, q]
  ring

/-- Higham p. 522, without sign or nonzero restrictions: every member of the
printed list is a genuine eigenvalue of the complexified real Toeplitz matrix,
witnessed by a nonzero vector.  The zero-superdiagonal branch is triangular;
all other cases use the complex scaled-sine similarity. -/
theorem generalToeplitz_unrestricted_complex_eigenpair {n : ℕ}
    (c d e : ℝ) (k : Fin n) :
    generalToeplitzComplexEigenvector c e k ≠ 0 ∧
      Matrix.mulVec (complexTridiagonalToeplitz n c d e)
          (generalToeplitzComplexEigenvector c e k) =
        generalToeplitzComplexEigenvalue n c d e k •
          generalToeplitzComplexEigenvector c e k := by
  by_cases he : e ≠ 0
  · constructor
    · simpa [generalToeplitzComplexEigenvector, he] using
        complexToeplitzSineVector_ne_zero
          (realProductComplexSqrt c e / (e : ℂ)) k
    · simpa [generalToeplitzComplexEigenvector, he] using
        generalToeplitz_complex_sine_eigenpair_of_super_ne_zero c d e he k
  · have he0 : e = 0 := not_ne_iff.mp he
    subst e
    constructor
    · simpa [generalToeplitzComplexEigenvector] using
        complexTridiagonalToeplitz_lastVector_ne_zero k
    · have hlast := complexTridiagonalToeplitz_last_eigenpair
        (c := (c : ℂ)) (d := (d : ℂ)) k
      simpa [generalToeplitzComplexEigenvector,
        generalToeplitzComplexEigenvalue, realProductComplexSqrt] using hlast

/-- Source-facing p. 522 endpoint: the original real matrix, mapped to `ℂ`,
has every member of the displayed `k = 1:n` eigenvalue list. -/
theorem tridiagonalToeplitz_p522_unrestricted_eigenvalue {n : ℕ}
    (c d e : ℝ) (k : Fin n) :
    ∃ v : Fin n → ℂ, v ≠ 0 ∧
      Matrix.mulVec ((tridiagonalToeplitz n c d e).map Complex.ofReal) v =
        generalToeplitzComplexEigenvalue n c d e k • v := by
  have h := generalToeplitz_unrestricted_complex_eigenpair c d e k
  refine ⟨generalToeplitzComplexEigenvector c e k, h.1, ?_⟩
  rw [← complexTridiagonalToeplitz_ofReal]
  exact h.2

end NumStability
