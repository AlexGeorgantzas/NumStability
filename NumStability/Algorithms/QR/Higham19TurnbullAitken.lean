/-
Chapter 19, p. 374 (Notes and References): Turnbull--Aitken's rank-one
unitary map between equal-length vectors.

The source states that, when `‖x‖₂ = ‖y‖₂` and `x ≠ -y`, a unitary matrix
of the form `R = α z zᴴ - I` can be constructed so that `R x = y`.  The
construction below makes the witnesses explicit:

  z = x + y,    α = (zᴴ x)⁻¹,    R = α z zᴴ - I.

The coefficient is generally complex.  Thus this is a unitary rank-one
update, not necessarily a Hermitian Householder reflector.  A real
orthogonal specialization is provided at the end of the file.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup
import NumStability.Analysis.Norms
import NumStability.Algorithms.QR.HouseholderSpec

namespace NumStability

open scoped BigOperators Matrix

/-- The standard conjugate-linear-in-the-first-argument inner product on
finite complex coordinate vectors. -/
noncomputable def higham19TurnbullAitkenInner {n : ℕ}
    (u v : CVec n) : ℂ :=
  ∑ i : Fin n, star (u i) * v i

@[simp] private lemma higham19TurnbullAitkenInner_add_left
    {n : ℕ} (u v w : CVec n) :
    higham19TurnbullAitkenInner (u + v) w =
      higham19TurnbullAitkenInner u w +
        higham19TurnbullAitkenInner v w := by
  simp [higham19TurnbullAitkenInner, add_mul, Finset.sum_add_distrib]

@[simp] private lemma higham19TurnbullAitkenInner_add_right
    {n : ℕ} (u v w : CVec n) :
    higham19TurnbullAitkenInner u (v + w) =
      higham19TurnbullAitkenInner u v +
        higham19TurnbullAitkenInner u w := by
  simp [higham19TurnbullAitkenInner, mul_add, Finset.sum_add_distrib]

@[simp] private lemma higham19TurnbullAitkenInner_star
    {n : ℕ} (u v : CVec n) :
    star (higham19TurnbullAitkenInner u v) =
      higham19TurnbullAitkenInner v u := by
  simp [higham19TurnbullAitkenInner, star_mul, mul_comm]

/-- Turnbull--Aitken's vector `z = x + y`. -/
noncomputable def higham19TurnbullAitkenZ {n : ℕ}
    (x y : CVec n) : CVec n :=
  x + y

/-- Turnbull--Aitken's coefficient `α = (zᴴx)⁻¹`. -/
noncomputable def higham19TurnbullAitkenAlpha {n : ℕ}
    (x y : CVec n) : ℂ :=
  (higham19TurnbullAitkenInner (higham19TurnbullAitkenZ x y) x)⁻¹

/-- The source's rank-one matrix `R = α z zᴴ - I`. -/
noncomputable def higham19TurnbullAitkenMatrix {n : ℕ}
    (x y : CVec n) : Matrix (Fin n) (Fin n) ℂ :=
  higham19TurnbullAitkenAlpha x y •
      Matrix.vecMulVec (higham19TurnbullAitkenZ x y)
        (star (higham19TurnbullAitkenZ x y)) -
    1

private lemma higham19TurnbullAitkenInner_self_eq_of_twoNorm_eq
    {n : ℕ} {x y : CVec n}
    (hxy : complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) x =
      complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) y) :
    higham19TurnbullAitkenInner x x =
      higham19TurnbullAitkenInner y y := by
  have hnorm : ‖WithLp.toLp (2 : ENNReal) x‖ =
      ‖WithLp.toLp (2 : ENNReal) y‖ := by
    rw [complexVecLpNorm_two_eq_toLp, complexVecLpNorm_two_eq_toLp] at hxy
    exact hxy
  have hinner :
      inner ℂ (WithLp.toLp (2 : ENNReal) x) (WithLp.toLp (2 : ENNReal) x) =
        inner ℂ (WithLp.toLp (2 : ENNReal) y) (WithLp.toLp (2 : ENNReal) y) := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hnorm]
  change (∑ i : Fin n, inner ℂ (x i) (x i)) =
    ∑ i : Fin n, inner ℂ (y i) (y i) at hinner
  simpa only [RCLike.inner_apply'] using hinner

private lemma higham19TurnbullAitkenZ_ne_zero
    {n : ℕ} {x y : CVec n} (hopp : x ≠ -y) :
    higham19TurnbullAitkenZ x y ≠ 0 := by
  intro hz
  apply hopp
  ext i
  have hi := congrFun hz i
  simpa [higham19TurnbullAitkenZ] using eq_neg_of_add_eq_zero_left hi

private lemma higham19TurnbullAitkenInner_self_ne_zero
    {n : ℕ} {z : CVec n} (hz : z ≠ 0) :
    higham19TurnbullAitkenInner z z ≠ 0 := by
  have hzLp : WithLp.toLp (2 : ENNReal) z ≠ 0 := by
    intro hz0
    apply hz
    exact (WithLp.toLp_eq_zero (2 : ENNReal)).mp hz0
  have hinner :
      inner ℂ (WithLp.toLp (2 : ENNReal) z) (WithLp.toLp (2 : ENNReal) z) ≠ 0 :=
    inner_self_ne_zero.mpr hzLp
  change (∑ i : Fin n, inner ℂ (z i) (z i)) ≠ 0 at hinner
  simpa only [RCLike.inner_apply'] using hinner

private lemma higham19TurnbullAitken_denominator_identity
    {n : ℕ} {x y : CVec n}
    (hxy : complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) x =
      complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) y) :
    let z := higham19TurnbullAitkenZ x y
    higham19TurnbullAitkenInner z z =
      higham19TurnbullAitkenInner z x +
        star (higham19TurnbullAitkenInner z x) := by
  dsimp only
  have hself := higham19TurnbullAitkenInner_self_eq_of_twoNorm_eq hxy
  simp only [higham19TurnbullAitkenZ,
    higham19TurnbullAitkenInner_add_left,
    higham19TurnbullAitkenInner_add_right, star_add,
    higham19TurnbullAitkenInner_star] at hself ⊢
  rw [hself]
  ring

/-- The scalar `zᴴx` in the explicit construction is nonzero; no denominator
nonbreakdown premise is needed beyond the source assumptions. -/
theorem higham19TurnbullAitken_denominator_ne_zero
    {n : ℕ} {x y : CVec n}
    (hxy : complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) x =
      complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) y)
    (hopp : x ≠ -y) :
    higham19TurnbullAitkenInner (higham19TurnbullAitkenZ x y) x ≠ 0 := by
  let z := higham19TurnbullAitkenZ x y
  let s := higham19TurnbullAitkenInner z x
  have hz : z ≠ 0 := higham19TurnbullAitkenZ_ne_zero hopp
  have hzz : higham19TurnbullAitkenInner z z ≠ 0 :=
    higham19TurnbullAitkenInner_self_ne_zero hz
  have hid : higham19TurnbullAitkenInner z z = s + star s := by
    simpa [z, s] using higham19TurnbullAitken_denominator_identity hxy
  have hs : s ≠ 0 := by
    intro hs0
    apply hzz
    rw [hid, hs0]
    simp
  simpa [z, s] using hs

/-- The explicit Turnbull--Aitken rank-one update sends `x` exactly to `y`. -/
theorem higham19TurnbullAitken_mulVec_eq
    {n : ℕ} {x y : CVec n}
    (hxy : complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) x =
      complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) y)
    (hopp : x ≠ -y) :
    higham19TurnbullAitkenMatrix x y *ᵥ x = y := by
  let z := higham19TurnbullAitkenZ x y
  let s := higham19TurnbullAitkenInner z x
  have hs : s ≠ 0 := by
    simpa [z, s] using higham19TurnbullAitken_denominator_ne_zero hxy hopp
  ext i
  simp only [higham19TurnbullAitkenMatrix, higham19TurnbullAitkenAlpha,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.one_mulVec]
  change s⁻¹ * (z i * s) - x i = y i
  calc
    s⁻¹ * (z i * s) - x i = z i * (s⁻¹ * s) - x i := by ring
    _ = z i - x i := by rw [inv_mul_cancel₀ hs, mul_one]
    _ = y i := by simp [z, higham19TurnbullAitkenZ]

private lemma higham19TurnbullAitken_unitary_coefficient
    {n : ℕ} {x y : CVec n}
    (hxy : complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) x =
      complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) y)
    (hopp : x ≠ -y) :
    let z := higham19TurnbullAitkenZ x y
    let s := higham19TurnbullAitkenInner z x
    star s⁻¹ * s⁻¹ * higham19TurnbullAitkenInner z z =
      star s⁻¹ + s⁻¹ := by
  dsimp only
  let z := higham19TurnbullAitkenZ x y
  let s := higham19TurnbullAitkenInner z x
  change star s⁻¹ * s⁻¹ * higham19TurnbullAitkenInner z z =
    star s⁻¹ + s⁻¹
  have hs : s ≠ 0 := by
    simpa [z, s] using higham19TurnbullAitken_denominator_ne_zero hxy hopp
  have hstars : star s ≠ 0 := by simpa using hs
  have hid : higham19TurnbullAitkenInner z z = s + star s := by
    simpa [z, s] using higham19TurnbullAitken_denominator_identity hxy
  rw [hid, star_inv₀]
  field_simp [hs, hstars]

/-- The explicit matrix `α z zᴴ - I` is unitary. -/
theorem higham19TurnbullAitken_mem_unitaryGroup
    {n : ℕ} {x y : CVec n}
    (hxy : complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) x =
      complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) y)
    (hopp : x ≠ -y) :
    higham19TurnbullAitkenMatrix x y ∈
      Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  let z := higham19TurnbullAitkenZ x y
  let s := higham19TurnbullAitkenInner z x
  let V : Matrix (Fin n) (Fin n) ℂ := Matrix.vecMulVec z (star z)
  have hcoef : star s⁻¹ * s⁻¹ * higham19TurnbullAitkenInner z z =
      star s⁻¹ + s⁻¹ := by
    simpa [z, s] using higham19TurnbullAitken_unitary_coefficient hxy hopp
  have hVstar : star V = V := by
    rw [Matrix.star_eq_conjTranspose]
    simp [V]
  have hVV : V * V = higham19TurnbullAitkenInner z z • V := by
    ext i j
    simp only [V, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Matrix.smul_apply, higham19TurnbullAitkenInner]
    calc
      (∑ k : Fin n, (z i * star (z k)) * (z k * star (z j))) =
          z i * (∑ k : Fin n, star (z k) * z k) * star (z j) := by
            rw [Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
      _ = (∑ k : Fin n, star (z k) * z k) *
          (z i * star (z j)) := by ring
  have hcoefAssoc :
      star s⁻¹ * (s⁻¹ * higham19TurnbullAitkenInner z z) =
        star s⁻¹ + s⁻¹ := by
    rw [← mul_assoc]
    exact hcoef
  change star (s⁻¹ • V - 1) * (s⁻¹ • V - 1) = 1
  rw [star_sub, star_smul, hVstar, star_one]
  rw [Matrix.sub_mul, Matrix.mul_sub]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hVV]
  simp only [mul_one, one_mul, smul_smul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, V]
  by_cases hij : i = j
  · subst j
    rw [hcoefAssoc]
    simp
    ring
  · simp only [hij, ↓reduceIte]
    rw [hcoefAssoc]
    simp only [smul_eq_mul]
    ring

/-- **Higham Chapter 19, p. 374 (Turnbull--Aitken).**

For equal Euclidean-length complex vectors with `x ≠ -y`, the displayed
witnesses

`z = x + y`, `α = (zᴴx)⁻¹`, and `R = α z zᴴ - I`

give a unitary matrix satisfying `R x = y`.  Both the rank-one form and the
action are conclusions of the construction, not caller-supplied properties. -/
theorem higham19_turnbullAitken_equal_norm_rankOne_unitary
    {n : ℕ} (x y : CVec n)
    (hxy : complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) x =
      complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) y)
    (hopp : x ≠ -y) :
    let z := higham19TurnbullAitkenZ x y
    let α := higham19TurnbullAitkenAlpha x y
    let R := higham19TurnbullAitkenMatrix x y
    α = (higham19TurnbullAitkenInner z x)⁻¹ ∧
      R = α • Matrix.vecMulVec z (star z) - 1 ∧
      R ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      R *ᵥ x = y := by
  dsimp only
  exact ⟨rfl, rfl,
    higham19TurnbullAitken_mem_unitaryGroup hxy hopp,
    higham19TurnbullAitken_mulVec_eq hxy hopp⟩

/-! ### Real orthogonal specialization -/

/-- Real dot product used by the Turnbull--Aitken specialization. -/
noncomputable def higham19TurnbullAitkenRealInner {n : ℕ}
    (u v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, u i * v i

/-- The real specialization of `z = x + y`. -/
noncomputable def higham19TurnbullAitkenRealZ {n : ℕ}
    (x y : Fin n → ℝ) : Fin n → ℝ :=
  x + y

/-- The real coefficient `(zᵀx)⁻¹`. -/
noncomputable def higham19TurnbullAitkenRealAlpha {n : ℕ}
    (x y : Fin n → ℝ) : ℝ :=
  (higham19TurnbullAitkenRealInner
    (higham19TurnbullAitkenRealZ x y) x)⁻¹

/-- The real matrix `α z zᵀ - I`. -/
noncomputable def higham19TurnbullAitkenRealMatrix {n : ℕ}
    (x y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  higham19TurnbullAitkenRealAlpha x y •
      Matrix.vecMulVec (higham19TurnbullAitkenRealZ x y)
        (higham19TurnbullAitkenRealZ x y) -
    1

private lemma higham19TurnbullAitkenRealInner_self_eq_of_norm_eq
    {n : ℕ} {x y : Fin n → ℝ} (hxy : vecNorm2 x = vecNorm2 y) :
    higham19TurnbullAitkenRealInner x x =
      higham19TurnbullAitkenRealInner y y := by
  have hsq := congrArg (fun t : ℝ => t ^ 2) hxy
  change vecNorm2 x ^ 2 = vecNorm2 y ^ 2 at hsq
  rw [vecNorm2_sq, vecNorm2_sq] at hsq
  simpa [higham19TurnbullAitkenRealInner, vecNorm2Sq, pow_two] using hsq

private lemma higham19TurnbullAitkenRealZ_ne_zero
    {n : ℕ} {x y : Fin n → ℝ} (hopp : x ≠ -y) :
    higham19TurnbullAitkenRealZ x y ≠ 0 := by
  intro hz
  apply hopp
  ext i
  have hi := congrFun hz i
  simpa [higham19TurnbullAitkenRealZ] using eq_neg_of_add_eq_zero_left hi

private lemma higham19TurnbullAitkenRealInner_self_ne_zero
    {n : ℕ} {z : Fin n → ℝ} (hz : z ≠ 0) :
    higham19TurnbullAitkenRealInner z z ≠ 0 := by
  intro hzero
  apply hz
  have hnormSq : vecNorm2Sq z = 0 := by
    simpa [higham19TurnbullAitkenRealInner, vecNorm2Sq, pow_two] using hzero
  have hnorm : vecNorm2 z = 0 := by
    apply sq_eq_zero_iff.mp
    rw [vecNorm2_sq, hnormSq]
  exact funext ((vecNorm2_eq_zero_iff z).mp hnorm)

private lemma higham19TurnbullAitkenReal_denominator_identity
    {n : ℕ} {x y : Fin n → ℝ} (hxy : vecNorm2 x = vecNorm2 y) :
    let z := higham19TurnbullAitkenRealZ x y
    higham19TurnbullAitkenRealInner z z =
      2 * higham19TurnbullAitkenRealInner z x := by
  dsimp only
  have hself := higham19TurnbullAitkenRealInner_self_eq_of_norm_eq hxy
  simp only [higham19TurnbullAitkenRealInner,
    higham19TurnbullAitkenRealZ, Pi.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib] at hself ⊢
  rw [hself]
  have hcross : (∑ i : Fin n, x i * y i) = ∑ i : Fin n, y i * x i := by
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hcross]
  ring

/-- The real denominator `zᵀx` is nonzero under exactly the source
assumptions. -/
theorem higham19TurnbullAitkenReal_denominator_ne_zero
    {n : ℕ} {x y : Fin n → ℝ}
    (hxy : vecNorm2 x = vecNorm2 y) (hopp : x ≠ -y) :
    higham19TurnbullAitkenRealInner
      (higham19TurnbullAitkenRealZ x y) x ≠ 0 := by
  let z := higham19TurnbullAitkenRealZ x y
  let s := higham19TurnbullAitkenRealInner z x
  have hz : z ≠ 0 := higham19TurnbullAitkenRealZ_ne_zero hopp
  have hzz : higham19TurnbullAitkenRealInner z z ≠ 0 :=
    higham19TurnbullAitkenRealInner_self_ne_zero hz
  have hid : higham19TurnbullAitkenRealInner z z = 2 * s := by
    simpa [z, s] using higham19TurnbullAitkenReal_denominator_identity hxy
  have hs : s ≠ 0 := by
    intro hs0
    apply hzz
    rw [hid, hs0, mul_zero]
  simpa [z, s] using hs

private lemma higham19TurnbullAitkenReal_alpha_mul_selfInner
    {n : ℕ} {x y : Fin n → ℝ}
    (hxy : vecNorm2 x = vecNorm2 y) (hopp : x ≠ -y) :
    higham19TurnbullAitkenRealAlpha x y *
      higham19TurnbullAitkenRealInner
        (higham19TurnbullAitkenRealZ x y)
        (higham19TurnbullAitkenRealZ x y) = 2 := by
  let z := higham19TurnbullAitkenRealZ x y
  let s := higham19TurnbullAitkenRealInner z x
  have hs : s ≠ 0 := by
    simpa [z, s] using
      higham19TurnbullAitkenReal_denominator_ne_zero hxy hopp
  have hid : higham19TurnbullAitkenRealInner z z = 2 * s := by
    simpa [z, s] using higham19TurnbullAitkenReal_denominator_identity hxy
  change s⁻¹ * higham19TurnbullAitkenRealInner z z = 2
  rw [hid]
  field_simp [hs]

/-- The real rank-one update sends `x` to `y`. -/
theorem higham19TurnbullAitkenReal_mulVec_eq
    {n : ℕ} {x y : Fin n → ℝ}
    (hxy : vecNorm2 x = vecNorm2 y) (hopp : x ≠ -y) :
    higham19TurnbullAitkenRealMatrix x y *ᵥ x = y := by
  let z := higham19TurnbullAitkenRealZ x y
  let s := higham19TurnbullAitkenRealInner z x
  have hs : s ≠ 0 := by
    simpa [z, s] using
      higham19TurnbullAitkenReal_denominator_ne_zero hxy hopp
  ext i
  simp only [higham19TurnbullAitkenRealMatrix,
    higham19TurnbullAitkenRealAlpha, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, Matrix.one_mulVec]
  change s⁻¹ * (z i * s) - x i = y i
  calc
    s⁻¹ * (z i * s) - x i = z i * (s⁻¹ * s) - x i := by ring
    _ = z i - x i := by rw [inv_mul_cancel₀ hs, mul_one]
    _ = y i := by simp [z, higham19TurnbullAitkenRealZ]

private lemma higham19TurnbullAitkenRealMatrix_eq_neg_householder
    {n : ℕ} (x y : Fin n → ℝ) :
    higham19TurnbullAitkenRealMatrix x y =
      -householder n (higham19TurnbullAitkenRealZ x y)
        (higham19TurnbullAitkenRealAlpha x y) := by
  ext i j
  simp only [higham19TurnbullAitkenRealMatrix, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.one_apply,
    Pi.neg_apply, householder]
  unfold idMatrix
  by_cases hij : i = j <;> simp [hij] <;> ring

private lemma IsOrthogonal.neg {n : ℕ} {U : Fin n → Fin n → ℝ}
    (hU : IsOrthogonal n U) : IsOrthogonal n (-U) := by
  constructor
  · intro i j
    simpa [matTranspose] using hU.1 i j
  · intro i j
    simpa [matTranspose] using hU.2 i j

/-- The real specialization is orthogonal. -/
theorem higham19TurnbullAitkenReal_isOrthogonal
    {n : ℕ} {x y : Fin n → ℝ}
    (hxy : vecNorm2 x = vecNorm2 y) (hopp : x ≠ -y) :
    IsOrthogonal n (higham19TurnbullAitkenRealMatrix x y) := by
  let z := higham19TurnbullAitkenRealZ x y
  let α := higham19TurnbullAitkenRealAlpha x y
  have hα : α * (∑ k : Fin n, z k * z k) = 2 := by
    simpa [z, α, higham19TurnbullAitkenRealInner] using
      higham19TurnbullAitkenReal_alpha_mul_selfInner hxy hopp
  have hP : IsOrthogonal n (householder n z α) :=
    householder_orthogonal n z α hα
  rw [higham19TurnbullAitkenRealMatrix_eq_neg_householder]
  exact hP.neg

/-- Real orthogonal corollary of the source-facing complex construction. -/
theorem higham19_turnbullAitken_equal_norm_rankOne_orthogonal
    {n : ℕ} (x y : Fin n → ℝ)
    (hxy : vecNorm2 x = vecNorm2 y) (hopp : x ≠ -y) :
    let z := higham19TurnbullAitkenRealZ x y
    let α := higham19TurnbullAitkenRealAlpha x y
    let R := higham19TurnbullAitkenRealMatrix x y
    α = (higham19TurnbullAitkenRealInner z x)⁻¹ ∧
      R = α • Matrix.vecMulVec z z - 1 ∧
      IsOrthogonal n R ∧
      R *ᵥ x = y := by
  dsimp only
  exact ⟨rfl, rfl,
    higham19TurnbullAitkenReal_isOrthogonal hxy hopp,
    higham19TurnbullAitkenReal_mulVec_eq hxy hopp⟩

end NumStability
