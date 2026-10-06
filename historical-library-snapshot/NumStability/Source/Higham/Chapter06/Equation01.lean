import Mathlib.Analysis.SpecialFunctions.Sqrt
import NumStability.Analysis.VectorNorms.Basic

/-!
# Higham Chapter 6, equation (6.1): equality cases

Source correspondence for the finite Holder equality prose following equation
(6.1), including the interior power-profile/common-ray condition and endpoint
witnesses.
-/

namespace NumStability

open scoped BigOperators

/-! ### Equality cases in Hölder's inequality (6.1)

For `p,q > 1`, the book gives two sufficient equality conditions: the vectors
of powers of the magnitudes are linearly dependent, and all scalar products
`conj (x i) * y i` lie on the same complex ray.  The power-profile hypothesis
below is the standard explicit parametrization
`‖yᵢ‖ = t ‖xᵢ‖^(p-1)`.  Since `(p-1)q=p`, it implies
`‖yᵢ‖^q = t^q ‖xᵢ‖^p`, exactly the stated linear dependence.  The common-ray
hypothesis uses a unit complex direction `z`, including zero coordinates
without a special case.
-/

/-- A common unit complex ray turns the triangle inequality for the Hölder
pairing into equality. -/
lemma higham6_holder_commonRay_norm_eq {n : ℕ} (x y : CVec n) (z : ℂ)
    (hz : ‖z‖ = 1)
    (hphase : ∀ i, star (x i) * y i =
      ((‖x i‖ * ‖y i‖ : ℝ) : ℂ) * z) :
    ‖∑ i : Fin n, star (x i) * y i‖ =
      ∑ i : Fin n, ‖x i‖ * ‖y i‖ := by
  have hsum :
      (∑ i : Fin n, star (x i) * y i) =
        ((∑ i : Fin n, ‖x i‖ * ‖y i‖ : ℝ) : ℂ) * z := by
    simp_rw [hphase]
    rw [← Finset.sum_mul]
    push_cast
    rfl
  rw [hsum, norm_mul, hz, mul_one, Complex.norm_real]
  exact Real.norm_of_nonneg (Finset.sum_nonneg fun i _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The magnitude power profile from the equality paragraph after (6.1)
makes the scalar Hölder inequality an equality. -/
lemma higham6_holder_scalar_equality_of_powerProfile {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x y : CVec n) (t : ℝ) (ht : 0 ≤ t)
    (hmag : ∀ i, ‖y i‖ = t * ‖x i‖ ^ (p - 1)) :
    (∑ i : Fin n, ‖x i‖ * ‖y i‖) =
      complexVecLpNorm (ENNReal.ofReal p) x *
        complexVecLpNorm (ENNReal.ofReal q) y := by
  have hp : 0 < p := hpq.pos
  have hq : 0 < q := hpq.symm.pos
  have hp1 : 0 < p - 1 := hpq.sub_one_pos
  have hexp : (p - 1) * q = p := hpq.sub_one_mul_conj
  let S : ℝ := ∑ i : Fin n, ‖x i‖ ^ p
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (norm_nonneg _) _
  have hxterm : ∀ i : Fin n,
      ‖x i‖ * ‖x i‖ ^ (p - 1) = ‖x i‖ ^ p := by
    intro i
    rcases eq_or_lt_of_le (norm_nonneg (x i)) with hzero | hpos
    · rw [← hzero]
      simp [hp.ne', hp1.ne']
    · calc
        ‖x i‖ * ‖x i‖ ^ (p - 1) =
            ‖x i‖ ^ 1 * ‖x i‖ ^ (p - 1) := by rw [Real.rpow_one]
        _ = ‖x i‖ ^ (1 + (p - 1)) :=
          (Real.rpow_add hpos 1 (p - 1)).symm
        _ = ‖x i‖ ^ p := by ring_nf
  have hlhs : (∑ i : Fin n, ‖x i‖ * ‖y i‖) = t * S := by
    calc
      (∑ i : Fin n, ‖x i‖ * ‖y i‖) =
          ∑ i : Fin n, t * ‖x i‖ ^ p := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hmag, ← hxterm]
        ring
      _ = t * S := by rw [Finset.mul_sum]
  have hyterm : ∀ i : Fin n,
      ‖y i‖ ^ q = t ^ q * ‖x i‖ ^ p := by
    intro i
    rw [hmag, Real.mul_rpow ht (Real.rpow_nonneg (norm_nonneg _) _)]
    rw [← Real.rpow_mul (norm_nonneg _) (p - 1) q, hexp]
  have hysum : (∑ i : Fin n, ‖y i‖ ^ q) = t ^ q * S := by
    simp_rw [hyterm]
    rw [Finset.mul_sum]
  rw [complexVecLpNorm_ofReal_eq_sum_rpow hp,
    complexVecLpNorm_ofReal_eq_sum_rpow hq, hlhs, hysum]
  rw [show (∑ i : Fin n, ‖x i‖ ^ p) = S by rfl]
  by_cases hSzero : S = 0
  · simp [hSzero, hp.ne', hq.ne']
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hSzero)
  rw [Real.mul_rpow (Real.rpow_nonneg ht q) hS]
  have htq : (t ^ q) ^ q⁻¹ = t := by
    rw [← Real.rpow_mul ht]
    rw [mul_inv_cancel₀ hq.ne', Real.rpow_one]
  rw [htq]
  symm
  calc
    S ^ p⁻¹ * (t * S ^ q⁻¹) =
        t * (S ^ p⁻¹ * S ^ q⁻¹) := by ring
    _ = t * S ^ (p⁻¹ + q⁻¹) := by
      rw [Real.rpow_add hSpos]
    _ = t * S := by
      rw [hpq.inv_add_inv_eq_one, Real.rpow_one]

/-- **Hölder equality under Higham's two sufficient conditions.**  This is the
finite complex equality statement immediately following equation (6.1). -/
theorem higham6_holder_equality_of_powerProfile_sameRay {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x y : CVec n) (t : ℝ) (ht : 0 ≤ t)
    (hmag : ∀ i, ‖y i‖ = t * ‖x i‖ ^ (p - 1))
    (z : ℂ) (hz : ‖z‖ = 1)
    (hphase : ∀ i, star (x i) * y i =
      ((‖x i‖ * ‖y i‖ : ℝ) : ℂ) * z) :
    ‖∑ i : Fin n, star (x i) * y i‖ =
      complexVecLpNorm (ENNReal.ofReal p) x *
        complexVecLpNorm (ENNReal.ofReal q) y := by
  rw [higham6_holder_commonRay_norm_eq x y z hz hphase]
  exact higham6_holder_scalar_equality_of_powerProfile hpq x y t ht hmag

/-- **Endpoint equality is possible.**  The single-coordinate unit vector
attains equality for both conjugate endpoint pairs `(1,∞)` and `(∞,1)`, as
asserted after (6.1). -/
theorem higham6_holder_endpoint_equality_standardBasis :
    let e : CVec 1 := standardBasisCVec (n := 1) (0 : Fin 1)
    (‖∑ i : Fin 1, star (e i) * e i‖ =
        complexVecLpNorm 1 e * complexVecLpNorm (⊤ : ENNReal) e) ∧
      (‖∑ i : Fin 1, star (e i) * e i‖ =
        complexVecLpNorm (⊤ : ENNReal) e * complexVecLpNorm 1 e) := by
  dsimp
  rw [complexVecLpNorm_one_eq_complexVecOneNorm,
    complexVecLpNorm_infty_eq_complexVecInfNorm,
    complexVecOneNorm_standardBasisCVec,
    complexVecInfNorm_standardBasisCVec]
  simp [standardBasisCVec]

end NumStability
