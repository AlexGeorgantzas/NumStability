/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Higham Chapter 11: the scaled explicit-inverse 2 x 2 pivot solve

Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Problems 11.2 and 11.5, and Higham, "Stability of the Diagonal Pivoting Method with
Partial Pivoting", SIAM J. Matrix Anal. Appl. 18 (1997), equation (4.3),
recommend solving a selected symmetric `2 x 2` pivot through

  `s = a/b`, `t = c/b`, `mu = s*t - 1`,
  `x0 = (t*f - g)/(b*mu)`, `x1 = (s*g - f)/(b*mu)`.

The definitions below implement every displayed arithmetic operation with an
`FPModel` primitive.  The proof does not assume a residual certificate.  It
extracts the eleven local standard-model errors, eliminates the right-hand
side from the two computed numerator equations, and obtains an exactly solved
nearby system.  The case-(4) scale guard keeps the two cancellation-sensitive
"minus one" quantities uniformly separated from zero.
-/
import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanActualSelector
import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedMiddleSolve
import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGrowthSolve

open scoped BigOperators

namespace NumStability

/-! ## Concrete scaled-inverse producer and its run domain -/

/-- Rounded `a / b` used by the scaled inverse. -/
noncomputable def higham11_2_flExplicitInverseScaledA
    (fp : FPModel) (a b : Real) : Real :=
  fp.fl_div a b

/-- Rounded `c / b` used by the scaled inverse. -/
noncomputable def higham11_2_flExplicitInverseScaledC
    (fp : FPModel) (b c : Real) : Real :=
  fp.fl_div c b

/-- Rounded `mu = fl(fl(a/b) * fl(c/b) - 1)`. -/
noncomputable def higham11_2_flExplicitInverseMu
    (fp : FPModel) (a b c : Real) : Real :=
  fp.fl_sub
    (fp.fl_mul
      (higham11_2_flExplicitInverseScaledA fp a b)
      (higham11_2_flExplicitInverseScaledC fp b c)) 1

/-- Rounded common denominator `fl(b * muHat)`. -/
noncomputable def higham11_2_flExplicitInverseDen
    (fp : FPModel) (a b c : Real) : Real :=
  fp.fl_mul b (higham11_2_flExplicitInverseMu fp a b c)

/-- The overflow-avoiding explicit-inverse solve from Higham (1997), (4.3).

The two numerators are evaluated as
`fl(fl(fl(c/b) * f) - g)` and `fl(fl(fl(a/b) * g) - f)`, and the two final
quotients use the shared rounded denominator `fl(b * muHat)`. -/
noncomputable def higham11_2_flExplicitInverseSolve
    (fp : FPModel) (a b c f g : Real) : Fin 2 -> Real :=
  let s := higham11_2_flExplicitInverseScaledA fp a b
  let t := higham11_2_flExplicitInverseScaledC fp b c
  let den := higham11_2_flExplicitInverseDen fp a b c
  fun i => Fin.cases
    (fp.fl_div (fp.fl_sub (fp.fl_mul t f) g) den)
    (fun _ => fp.fl_div (fp.fl_sub (fp.fl_mul s g) f) den) i

/-- Honest execution guard for the scaled explicit-inverse kernel.

* `b ≠ 0` licenses the two scaling divisions;
* the computed scaled product is at most `3/5`, the cancellation-separation
  fact supplied by an Algorithm 11.2 case-(4) pivot at small unit roundoff;
* the computed common denominator is nonzero, licensing both final divisions.

No residual, perturbation, or desired conclusion occurs in this predicate. -/
def Higham11ExplicitInverseRunDomain (fp : FPModel) (a b c : Real) : Prop :=
  b ≠ 0 /\
    |higham11_2_flExplicitInverseScaledA fp a b *
      higham11_2_flExplicitInverseScaledC fp b c| <= (3 : Real) / 5 /\
    higham11_2_flExplicitInverseDen fp a b c ≠ 0

/-! ## Scalar perturbation estimates -/

private lemma abs_one_add_le_one_add {u d : Real}
    (hd : |d| <= u) :
    |1 + d| <= 1 + u := by
  calc
    |1 + d| <= |(1 : Real)| + |d| := abs_add_le 1 d
    _ <= 1 + u := by simpa using add_le_add_left hd 1

private lemma one_sub_le_one_add {u d : Real}
    (hd : |d| <= u) : 1 - u <= 1 + d := by
  linarith [neg_abs_le d]

/-- The cancellation-sensitive ratio in the explicit-inverse proof.

The numerator is the computed `muHat`; the denominator is the corresponding
coefficient arising after the two rounded numerator equations are eliminated.
The computed scale cap `|q| <= 3/5` keeps both away from the dangerous value
`q = 1`. -/
private lemma explicitInverse_mu_ratio_le
    (u q d3 d4 d6 d8 : Real)
    (hu0 : 0 <= u) (hu : u <= 1 / 1000)
    (hq : |q| <= 3 / 5)
    (h3 : |d3| <= u) (h4 : |d4| <= u)
    (h6 : |d6| <= u) (h8 : |d8| <= u) :
    let nu := q * (1 + d8) * (1 + d6) - 1
    nu ≠ 0 /\
      |((q * (1 + d3) - 1) * (1 + d4)) / nu - 1| <= 12 * u := by
  let nu := q * (1 + d8) * (1 + d6) - 1
  let inner := (1 + d3) * (1 + d4) - (1 + d8) * (1 + d6)
  have h1d6 := abs_one_add_le_one_add h6
  have h1d8 := abs_one_add_le_one_add h8
  have hqnu : |q * (1 + d8) * (1 + d6)| <= 2 / 3 := by
    calc
      |q * (1 + d8) * (1 + d6)| = |q| * |1 + d8| * |1 + d6| := by
        simp only [abs_mul]
      _ <= (3 / 5) * (1 + u) * (1 + u) := by
        gcongr
      _ <= 2 / 3 := by nlinarith
  have hnu_abs : 1 / 3 <= |nu| := by
    have hrev : |(1 : Real)| - |q * (1 + d8) * (1 + d6)| <=
        |(1 : Real) - q * (1 + d8) * (1 + d6)| :=
      abs_sub_abs_le_abs_sub 1 (q * (1 + d8) * (1 + d6))
    simp only [abs_mul] at hqnu
    dsimp [nu]
    rw [abs_sub_comm]
    norm_num at hrev
    linarith
  have hnu_pos : 0 < |nu| := lt_of_lt_of_le (by norm_num) hnu_abs
  have hnu_ne : nu ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hnu_pos
    exact lt_irrefl 0 hnu_pos
  have h34 : |d3 * d4| <= u * u := by
    rw [abs_mul]
    exact mul_le_mul h3 h4 (abs_nonneg _) hu0
  have h86 : |d8 * d6| <= u * u := by
    rw [abs_mul]
    exact mul_le_mul h8 h6 (abs_nonneg _) hu0
  have hinner_eq :
      inner = d3 + d4 + d3 * d4 - d8 - d6 - d8 * d6 := by
    dsimp [inner]
    ring
  have hinner : |inner| <= 5 * u := by
    rw [hinner_eq, abs_le]
    constructor <;>
      nlinarith [neg_abs_le d3, le_abs_self d3,
        neg_abs_le d4, le_abs_self d4,
        neg_abs_le d6, le_abs_self d6,
        neg_abs_le d8, le_abs_self d8,
        neg_abs_le (d3 * d4), le_abs_self (d3 * d4),
        neg_abs_le (d8 * d6), le_abs_self (d8 * d6)]
  have hqinner : |q * inner| <= 3 * u := by
    rw [abs_mul]
    calc
      |q| * |inner| <= (3 / 5) * (5 * u) :=
        mul_le_mul hq hinner (abs_nonneg _) (by norm_num)
      _ = 3 * u := by ring
  have hdiff_eq :
      (q * (1 + d3) - 1) * (1 + d4) - nu = q * inner - d4 := by
    dsimp [nu, inner]
    ring
  have hdiff :
      |(q * (1 + d3) - 1) * (1 + d4) - nu| <= 4 * u := by
    rw [hdiff_eq]
    calc
      |q * inner - d4| <= |q * inner| + |d4| := abs_sub _ _
      _ <= 3 * u + u := add_le_add hqinner h4
      _ = 4 * u := by ring
  refine ⟨hnu_ne, ?_⟩
  have hratio :
      |((q * (1 + d3) - 1) * (1 + d4)) / nu - 1| =
        |(q * (1 + d3) - 1) * (1 + d4) - nu| / |nu| := by
    rw [show ((q * (1 + d3) - 1) * (1 + d4)) / nu - 1 =
        (((q * (1 + d3) - 1) * (1 + d4)) - nu) / nu by
      field_simp [hnu_ne]]
    exact abs_div _ _
  rw [hratio, div_le_iff₀ hnu_pos]
  nlinarith [mul_nonneg hu0 (abs_nonneg nu)]

/-- Adding the denominator multiplication, numerator scaling, and final
division errors to the cancellation-sensitive ratio costs at most `20u`. -/
private lemma explicitInverse_scaled_ratio_le
    (u R d5 dp dq : Real)
    (hu0 : 0 <= u) (hu : u <= 1 / 1000)
    (hR : |R - 1| <= 12 * u)
    (h5 : |d5| <= u) (hp : |dp| <= u) (hq : |dq| <= u) :
    |R * (1 + d5) / ((1 + dp) * (1 + dq)) - 1| <= 20 * u := by
  have hp_pos : 0 < 1 + dp := by linarith [neg_abs_le dp]
  have hq_pos : 0 < 1 + dq := by linarith [neg_abs_le dq]
  have hden_pos : 0 < (1 + dp) * (1 + dq) := mul_pos hp_pos hq_pos
  have hden_lower : 9 / 10 <= (1 + dp) * (1 + dq) := by
    have hleft := one_sub_le_one_add hp
    have hright := one_sub_le_one_add hq
    have hmul : (1 - u) * (1 - u) <= (1 + dp) * (1 + dq) := by
      exact mul_le_mul hleft hright (by nlinarith) (by nlinarith)
    nlinarith
  have hRabs : |R| <= 2 := by
    have htri : |R| <= |R - 1| + 1 := by
      calc
        |R| = |(R - 1) + 1| := by ring_nf
        _ <= |R - 1| + |(1 : Real)| := abs_add_le _ _
        _ = |R - 1| + 1 := by norm_num
    linarith
  have hRd5 : |R * d5| <= 2 * u := by
    rw [abs_mul]
    exact mul_le_mul hRabs h5 (abs_nonneg _) (by norm_num)
  have hpdq : |dp * dq| <= u * u := by
    rw [abs_mul]
    exact mul_le_mul hp hq (abs_nonneg _) hu0
  have hdiff_eq :
      R * (1 + d5) - (1 + dp) * (1 + dq) =
        (R - 1) + R * d5 - dp - dq - dp * dq := by ring
  have hdiff :
      |R * (1 + d5) - (1 + dp) * (1 + dq)| <= 17 * u := by
    rw [hdiff_eq, abs_le]
    constructor <;>
      nlinarith [neg_abs_le (R - 1), le_abs_self (R - 1),
        neg_abs_le (R * d5), le_abs_self (R * d5),
        neg_abs_le dp, le_abs_self dp, neg_abs_le dq, le_abs_self dq,
        neg_abs_le (dp * dq), le_abs_self (dp * dq)]
  have hratio :
      |R * (1 + d5) / ((1 + dp) * (1 + dq)) - 1| =
        |R * (1 + d5) - (1 + dp) * (1 + dq)| /
          ((1 + dp) * (1 + dq)) := by
    rw [show R * (1 + d5) / ((1 + dp) * (1 + dq)) - 1 =
        (R * (1 + d5) - (1 + dp) * (1 + dq)) /
          ((1 + dp) * (1 + dq)) by field_simp [ne_of_gt hden_pos]]
    rw [abs_div, abs_of_pos hden_pos]
  rw [hratio, div_le_iff₀ hden_pos]
  have hden_nonneg : 0 <= (1 + dp) * (1 + dq) := le_of_lt hden_pos
  nlinarith [mul_nonneg hu0 hden_nonneg]

/-- Two additional relative factors, needed for a diagonal coefficient, turn
the `20u` scaled-ratio estimate into a still-conservative `48u` estimate. -/
private lemma explicitInverse_diagonal_ratio_le
    (u K da db : Real)
    (hu0 : 0 <= u) (hu : u <= 1 / 1000)
    (hK : |K - 1| <= 20 * u)
    (ha : |da| <= u) (hb : |db| <= u) :
    |(1 + da) * (1 + db) * K - 1| <= 48 * u := by
  have hada : |da * db| <= u * u := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hu0
  have hPdiff : |(1 + da) * (1 + db) - 1| <= 3 * u := by
    have heq : (1 + da) * (1 + db) - 1 = da + db + da * db := by ring
    rw [heq, abs_le]
    constructor <;>
      nlinarith [neg_abs_le da, le_abs_self da,
        neg_abs_le db, le_abs_self db,
        neg_abs_le (da * db), le_abs_self (da * db)]
  have hPa := abs_one_add_le_one_add ha
  have hPb := abs_one_add_le_one_add hb
  have hPabs : |(1 + da) * (1 + db)| <= 2 := by
    rw [abs_mul]
    calc
      |1 + da| * |1 + db| <= (1 + u) * (1 + u) :=
        mul_le_mul hPa hPb (abs_nonneg _) (by nlinarith)
      _ <= 2 := by nlinarith
  have hprod : |((1 + da) * (1 + db)) * (K - 1)| <= 40 * u := by
    rw [abs_mul]
    calc
      |(1 + da) * (1 + db)| * |K - 1| <= 2 * (20 * u) :=
        mul_le_mul hPabs hK (abs_nonneg _) (by norm_num)
      _ = 40 * u := by ring
  have hrearrange :
      (1 + da) * (1 + db) * K - 1 =
        ((1 + da) * (1 + db)) * (K - 1) +
          ((1 + da) * (1 + db) - 1) := by ring
  rw [hrearrange]
  calc
    |(1 + da) * (1 + db) * (K - 1) + ((1 + da) * (1 + db) - 1)|
        <= |(1 + da) * (1 + db) * (K - 1)| +
          |(1 + da) * (1 + db) - 1| := abs_add_le _ _
    _ <= 40 * u + 3 * u := add_le_add hprod hPdiff
    _ <= 48 * u := by nlinarith

/-! ## Componentwise backward error of the concrete kernel -/

/-- The actual scaled explicit-inverse kernel solves an exactly perturbed
symmetric `2 x 2` system.  The two off-diagonal perturbations are allowed to
differ, as in the usual componentwise backward-error statement.

The bound is the source-faithful `gamma_180` class from Higham (1997), p. 8.
Our local bookkeeping is sharper (`48u` on the diagonal and `20u` off the
diagonal); `gamma_180` is retained at the public boundary to match the source.
The small finite-precision guard is deliberately explicit. -/
theorem higham11_2_flExplicitInverseSolve_backward_error_gamma180
    (fp : FPModel) (hu : fp.u <= 1 / 1000)
    (a b c f g : Real) (hrun : Higham11ExplicitInverseRunDomain fp a b c) :
    exists da db01 db10 dc : Real,
      |da| <= gamma fp 180 * |a| /\
      |db01| <= gamma fp 180 * |b| /\
      |db10| <= gamma fp 180 * |b| /\
      |dc| <= gamma fp 180 * |c| /\
      (a + da) * higham11_2_flExplicitInverseSolve fp a b c f g 0 +
          (b + db01) * higham11_2_flExplicitInverseSolve fp a b c f g 1 = f /\
      (b + db10) * higham11_2_flExplicitInverseSolve fp a b c f g 0 +
          (c + dc) * higham11_2_flExplicitInverseSolve fp a b c f g 1 = g := by
  rcases hrun with ⟨hb, hq, hden_ne⟩
  have hu0 : 0 <= fp.u := fp.u_nonneg
  have hvalid180 : gammaValid fp 180 := by
    unfold gammaValid
    norm_num at hu ⊢
    nlinarith
  have hgamma48 : 48 * fp.u <= gamma fp 180 := by
    have h180 := n_mul_u_le_gamma fp 180 hvalid180
    norm_num at h180
    nlinarith
  have hgamma20 : 20 * fp.u <= gamma fp 180 := by linarith
  let s := higham11_2_flExplicitInverseScaledA fp a b
  let t := higham11_2_flExplicitInverseScaledC fp b c
  let prod := fp.fl_mul s t
  let mu := fp.fl_sub prod 1
  let den := fp.fl_mul b mu
  let n0 := fp.fl_sub (fp.fl_mul t f) g
  let n1 := fp.fl_sub (fp.fl_mul s g) f
  let x := fp.fl_div n0 den
  let y := fp.fl_div n1 den
  have hs_def : s = higham11_2_flExplicitInverseScaledA fp a b := rfl
  have ht_def : t = higham11_2_flExplicitInverseScaledC fp b c := rfl
  have hden_def : den = higham11_2_flExplicitInverseDen fp a b c := rfl
  have hden_local : den ≠ 0 := by simpa [hden_def] using hden_ne
  have hq_local : |s * t| <= 3 / 5 := by simpa [hs_def, ht_def] using hq
  obtain ⟨d1, hd1, hs⟩ := fp.model_div a b hb
  obtain ⟨d2, hd2, ht⟩ := fp.model_div c b hb
  obtain ⟨d3, hd3, hprod⟩ := fp.model_mul s t
  obtain ⟨d4, hd4, hmu⟩ := fp.model_sub prod 1
  obtain ⟨d5, hd5, hden⟩ := fp.model_mul b mu
  obtain ⟨d6, hd6, htf⟩ := fp.model_mul t f
  obtain ⟨d7, hd7, hn0⟩ :=
    fp.model_sub (fp.fl_mul t f) g
  obtain ⟨d8, hd8, hsg⟩ := fp.model_mul s g
  obtain ⟨d9, hd9, hn1⟩ :=
    fp.model_sub (fp.fl_mul s g) f
  obtain ⟨d10, hd10, hx⟩ := fp.model_div n0 den hden_local
  obtain ⟨d11, hd11, hy⟩ := fp.model_div n1 den hden_local
  let q : Real := s * t
  let nu : Real := q * (1 + d8) * (1 + d6) - 1
  let mfac : Real := (q * (1 + d3) - 1) * (1 + d4)
  let R : Real := mfac / nu
  let P0 : Real := (1 + d7) * (1 + d10)
  let P1 : Real := (1 + d9) * (1 + d11)
  let K0 : Real := R * (1 + d5) / P0
  let K1 : Real := R * (1 + d5) / P1
  obtain ⟨hnu_ne, hR⟩ :=
    explicitInverse_mu_ratio_le fp.u q d3 d4 d6 d8
      hu0 hu (by simpa [q] using hq_local) hd3 hd4 hd6 hd8
  have hnu_local : nu ≠ 0 := by simpa [nu] using hnu_ne
  have hK0 : |K0 - 1| <= 20 * fp.u := by
    apply explicitInverse_scaled_ratio_le fp.u R d5 d7 d10 hu0 hu
    · simpa [R, mfac] using hR
    · exact hd5
    · exact hd7
    · exact hd10
  have hK1 : |K1 - 1| <= 20 * fp.u := by
    apply explicitInverse_scaled_ratio_le fp.u R d5 d9 d11 hu0 hu
    · simpa [R, mfac] using hR
    · exact hd5
    · exact hd9
    · exact hd11
  have hdiag0 : |(1 + d1) * (1 + d8) * K0 - 1| <= 48 * fp.u :=
    explicitInverse_diagonal_ratio_le fp.u K0 d1 d8 hu0 hu hK0 hd1 hd8
  have hdiag1 : |(1 + d2) * (1 + d6) * K1 - 1| <= 48 * fp.u :=
    explicitInverse_diagonal_ratio_le fp.u K1 d2 d6 hu0 hu hK1 hd2 hd6
  have h7pos : 0 < 1 + d7 := by linarith [neg_abs_le d7]
  have h9pos : 0 < 1 + d9 := by linarith [neg_abs_le d9]
  have h10pos : 0 < 1 + d10 := by linarith [neg_abs_le d10]
  have h11pos : 0 < 1 + d11 := by linarith [neg_abs_le d11]
  have hP0_ne : P0 ≠ 0 := by
    exact ne_of_gt (by dsimp [P0]; positivity)
  have hP1_ne : P1 ≠ 0 := by
    exact ne_of_gt (by dsimp [P1]; positivity)
  have hmu_shape : mu = mfac := by
    calc
      mu = (prod - 1) * (1 + d4) := hmu
      _ = mfac := by
        dsimp [mfac, q, prod]
        rw [hprod]
  have hden_shape : den = b * mfac * (1 + d5) := by
    calc
      den = b * mu * (1 + d5) := hden
      _ = b * mfac * (1 + d5) := by rw [hmu_shape]
  have hn0_shape : n0 = (t * f * (1 + d6) - g) * (1 + d7) := by
    calc
      n0 = (fp.fl_mul t f - g) * (1 + d7) := hn0
      _ = (t * f * (1 + d6) - g) * (1 + d7) := by rw [htf]
  have hn1_shape : n1 = (s * g * (1 + d8) - f) * (1 + d9) := by
    calc
      n1 = (fp.fl_mul s g - f) * (1 + d9) := hn1
      _ = (s * g * (1 + d8) - f) * (1 + d9) := by rw [hsg]
  have hraw0 :
      b * mfac * (1 + d5) * x =
        (t * f * (1 + d6) - g) * P0 := by
    calc
      b * mfac * (1 + d5) * x = den * x := by rw [hden_shape]
      _ = n0 * (1 + d10) := by
        change den * fp.fl_div n0 den = n0 * (1 + d10)
        rw [hx]
        field_simp [hden_local]
      _ = (t * f * (1 + d6) - g) * P0 := by
        rw [hn0_shape]
        dsimp [P0]
        ring
  have hraw1 :
      b * mfac * (1 + d5) * y =
        (s * g * (1 + d8) - f) * P1 := by
    calc
      b * mfac * (1 + d5) * y = den * y := by rw [hden_shape]
      _ = n1 * (1 + d11) := by
        change den * fp.fl_div n1 den = n1 * (1 + d11)
        rw [hy]
        field_simp [hden_local]
      _ = (s * g * (1 + d8) - f) * P1 := by
        rw [hn1_shape]
        dsimp [P1]
        ring
  have hK0coeff : b * K0 * nu = b * mfac * (1 + d5) / P0 := by
    dsimp [K0, R]
    field_simp [hnu_local, hP0_ne]
  have hK1coeff : b * K1 * nu = b * mfac * (1 + d5) / P1 := by
    dsimp [K1, R]
    field_simp [hnu_local, hP1_ne]
  have heq0div :
      t * (1 + d6) * f - g =
        (b * mfac * (1 + d5) / P0) * x := by
    have hraw0' :
        b * mfac * (1 + d5) * x =
          (t * (1 + d6) * f - g) * P0 := by
      convert hraw0 using 1 ; ring
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff hP0_ne).2 hraw0'.symm
  have heq1div :
      s * (1 + d8) * g - f =
        (b * mfac * (1 + d5) / P1) * y := by
    have hraw1' :
        b * mfac * (1 + d5) * y =
          (s * (1 + d8) * g - f) * P1 := by
      convert hraw1 using 1 ; ring
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff hP1_ne).2 hraw1'.symm
  have heq0 :
      t * (1 + d6) * f - g = b * K0 * nu * x := by
    rw [hK0coeff]
    exact heq0div
  have heq1 :
      s * (1 + d8) * g - f = b * K1 * nu * y := by
    rw [hK1coeff]
    exact heq1div
  have hnu_coeff :
      s * (1 + d8) * (t * (1 + d6)) - 1 = nu := by
    dsimp [nu, q]
    ring
  have hrow0_scaled :
      nu * f = nu * (s * (1 + d8) * b * K0 * x + b * K1 * y) := by
    rw [← hnu_coeff]
    linear_combination (s * (1 + d8)) * heq0 + heq1
  have hrow0_coeff :
      s * (1 + d8) * b * K0 * x + b * K1 * y = f := by
    apply Eq.symm
    apply mul_left_cancel₀ hnu_local
    exact hrow0_scaled
  have hrow1_coeff :
      b * K0 * x + t * (1 + d6) * b * K1 * y = g := by
    calc
      b * K0 * x + t * (1 + d6) * b * K1 * y
          = t * (1 + d6) *
              (s * (1 + d8) * b * K0 * x + b * K1 * y) -
              b * K0 * nu * x := by
            rw [← hnu_coeff]
            ring
      _ = t * (1 + d6) * f - b * K0 * nu * x := by rw [hrow0_coeff]
      _ = g := by linear_combination heq0
  have hsb : s * b = a * (1 + d1) := by
    have hs_local : s = a / b * (1 + d1) := by
      simpa [s, higham11_2_flExplicitInverseScaledA] using hs
    rw [hs_local]
    field_simp [hb]
  have htb : t * b = c * (1 + d2) := by
    have ht_local : t = c / b * (1 + d2) := by
      simpa [t, higham11_2_flExplicitInverseScaledC] using ht
    rw [ht_local]
    field_simp [hb]
  let da : Real := a * ((1 + d1) * (1 + d8) * K0 - 1)
  let db01 : Real := b * (K1 - 1)
  let db10 : Real := b * (K0 - 1)
  let dc : Real := c * ((1 + d2) * (1 + d6) * K1 - 1)
  have hda : |da| <= gamma fp 180 * |a| := by
    dsimp [da]
    rw [abs_mul]
    calc
      |a| * |(1 + d1) * (1 + d8) * K0 - 1| <= |a| * (48 * fp.u) :=
        mul_le_mul_of_nonneg_left hdiag0 (abs_nonneg a)
      _ <= |a| * gamma fp 180 :=
        mul_le_mul_of_nonneg_left hgamma48 (abs_nonneg a)
      _ = gamma fp 180 * |a| := by ring
  have hdb01 : |db01| <= gamma fp 180 * |b| := by
    dsimp [db01]
    rw [abs_mul]
    calc
      |b| * |K1 - 1| <= |b| * (20 * fp.u) :=
        mul_le_mul_of_nonneg_left hK1 (abs_nonneg b)
      _ <= |b| * gamma fp 180 :=
        mul_le_mul_of_nonneg_left hgamma20 (abs_nonneg b)
      _ = gamma fp 180 * |b| := by ring
  have hdb10 : |db10| <= gamma fp 180 * |b| := by
    dsimp [db10]
    rw [abs_mul]
    calc
      |b| * |K0 - 1| <= |b| * (20 * fp.u) :=
        mul_le_mul_of_nonneg_left hK0 (abs_nonneg b)
      _ <= |b| * gamma fp 180 :=
        mul_le_mul_of_nonneg_left hgamma20 (abs_nonneg b)
      _ = gamma fp 180 * |b| := by ring
  have hdc : |dc| <= gamma fp 180 * |c| := by
    dsimp [dc]
    rw [abs_mul]
    calc
      |c| * |(1 + d2) * (1 + d6) * K1 - 1| <= |c| * (48 * fp.u) :=
        mul_le_mul_of_nonneg_left hdiag1 (abs_nonneg c)
      _ <= |c| * gamma fp 180 :=
        mul_le_mul_of_nonneg_left hgamma48 (abs_nonneg c)
      _ = gamma fp 180 * |c| := by ring
  have hrow0 : (a + da) * x + (b + db01) * y = f := by
    rw [← hrow0_coeff]
    dsimp [da, db01]
    calc
      (a + a * ((1 + d1) * (1 + d8) * K0 - 1)) * x +
          (b + b * (K1 - 1)) * y =
          a * (1 + d1) * (1 + d8) * K0 * x + b * K1 * y := by ring
      _ = s * (1 + d8) * b * K0 * x + b * K1 * y := by
        rw [← hsb]
        ring
  have hrow1 : (b + db10) * x + (c + dc) * y = g := by
    rw [← hrow1_coeff]
    dsimp [db10, dc]
    calc
      (b + b * (K0 - 1)) * x +
          (c + c * ((1 + d2) * (1 + d6) * K1 - 1)) * y =
          b * K0 * x + c * (1 + d2) * (1 + d6) * K1 * y := by ring
      _ = b * K0 * x + t * (1 + d6) * b * K1 * y := by
        rw [← htb]
        ring
  refine ⟨da, db01, db10, dc, hda, hdb01, hdb10, hdc, ?_, ?_⟩
  · simpa [higham11_2_flExplicitInverseSolve, x, y, s, t, den, n0, n1,
      higham11_2_flExplicitInverseDen, higham11_2_flExplicitInverseMu, prod, mu]
      using hrow0
  · simpa [higham11_2_flExplicitInverseSolve, x, y, s, t, den, n0, n1,
      higham11_2_flExplicitInverseDen, higham11_2_flExplicitInverseMu, prod, mu]
      using hrow1

/-- A source-style finite-`u` corollary of the `gamma_180` certificate.
Under the same explicit smallness guard, `gamma_180 <= 360u`. -/
theorem higham11_2_flExplicitInverseSolve_backward_error_360u
    (fp : FPModel) (hu : fp.u <= 1 / 1000)
    (a b c f g : Real) (hrun : Higham11ExplicitInverseRunDomain fp a b c) :
    exists da db01 db10 dc : Real,
      |da| <= 360 * fp.u * |a| /\
      |db01| <= 360 * fp.u * |b| /\
      |db10| <= 360 * fp.u * |b| /\
      |dc| <= 360 * fp.u * |c| /\
      (a + da) * higham11_2_flExplicitInverseSolve fp a b c f g 0 +
          (b + db01) * higham11_2_flExplicitInverseSolve fp a b c f g 1 = f /\
      (b + db10) * higham11_2_flExplicitInverseSolve fp a b c f g 0 +
          (c + dc) * higham11_2_flExplicitInverseSolve fp a b c f g 1 = g := by
  obtain ⟨da, db01, db10, dc, hda, hdb01, hdb10, hdc, hrows⟩ :=
    higham11_2_flExplicitInverseSolve_backward_error_gamma180
      fp hu a b c f g hrun
  have hsmall : (180 : Real) * fp.u <= 1 / 2 := by
    nlinarith [fp.u_nonneg]
  have hgamma := gamma_le_two_mul_n_u_of_nu_le_half fp 180 hsmall
  have hgamma360 : gamma fp 180 <= 360 * fp.u := by
    calc
      gamma fp 180 <= 2 * (180 * fp.u) := hgamma
      _ = 360 * fp.u := by ring
  refine ⟨da, db01, db10, dc, ?_, ?_, ?_, ?_, hrows⟩
  · exact hda.trans (mul_le_mul_of_nonneg_right hgamma360 (abs_nonneg a))
  · exact hdb01.trans (mul_le_mul_of_nonneg_right hgamma360 (abs_nonneg b))
  · exact hdb10.trans (mul_le_mul_of_nonneg_right hgamma360 (abs_nonneg b))
  · exact hdc.trans (mul_le_mul_of_nonneg_right hgamma360 (abs_nonneg c))

/-! ## From the actual Algorithm 11.2 case-(4) selector to the run domain -/

/-- If the exact scaled product is at most one half, the two rounded scaling
divisions satisfy the computable `3/5` scale guard at `u <= 10^-3`. -/
theorem higham11_2_flExplicitInverse_scaled_product_le_three_fifths
    (fp : FPModel) (hu : fp.u <= 1 / 1000)
    (a b c : Real) (hb : b ≠ 0)
    (hhalf : 2 * |a * c| <= |b| ^ 2) :
    |higham11_2_flExplicitInverseScaledA fp a b *
      higham11_2_flExplicitInverseScaledC fp b c| <= 3 / 5 := by
  obtain ⟨d1, hd1, hs⟩ := fp.model_div a b hb
  obtain ⟨d2, hd2, ht⟩ := fp.model_div c b hb
  have hbabs : |b| ≠ 0 := abs_ne_zero.mpr hb
  have hbabs_sq_pos : 0 < |b| ^ 2 := sq_pos_of_ne_zero hbabs
  have hratio_eq : |a / b| * |c / b| = |a * c| / |b| ^ 2 := by
    rw [abs_div, abs_div, abs_mul]
    field_simp [hbabs]
  have hratio : |a / b| * |c / b| <= 1 / 2 := by
    rw [hratio_eq, div_le_iff₀ hbabs_sq_pos]
    nlinarith
  have h1 := abs_one_add_le_one_add hd1
  have h2 := abs_one_add_le_one_add hd2
  rw [higham11_2_flExplicitInverseScaledA,
    higham11_2_flExplicitInverseScaledC, hs, ht]
  simp only [abs_mul]
  calc
    |a / b| * |1 + d1| * (|c / b| * |1 + d2|)
        = (|a / b| * |c / b|) * |1 + d1| * |1 + d2| := by ring
    _ <= (1 / 2) * (1 + fp.u) * (1 + fp.u) := by
      exact mul_le_mul
        (mul_le_mul hratio h1 (abs_nonneg _) (by norm_num)) h2
        (abs_nonneg _) (mul_nonneg (by norm_num) (by nlinarith [fp.u_nonneg]))
    _ <= 3 / 5 := by nlinarith [fp.u_nonneg]

/-- The common denominator cannot vanish once the computed scaled product is
separated from one.  Thus the denominator clause in the low-level run domain
is a proved operational invariant for a case-(4) pivot, not an additional
producer premise. -/
theorem higham11_2_flExplicitInverseDen_ne_zero_of_scaled_product
    (fp : FPModel) (hu : fp.u <= 1 / 1000)
    (a b c : Real) (hb : b ≠ 0)
    (hq : |higham11_2_flExplicitInverseScaledA fp a b *
      higham11_2_flExplicitInverseScaledC fp b c| <= 3 / 5) :
    higham11_2_flExplicitInverseDen fp a b c ≠ 0 := by
  let s := higham11_2_flExplicitInverseScaledA fp a b
  let t := higham11_2_flExplicitInverseScaledC fp b c
  let prod := fp.fl_mul s t
  let mu := fp.fl_sub prod 1
  obtain ⟨d3, hd3, hprod⟩ := fp.model_mul s t
  obtain ⟨d4, hd4, hmu⟩ := fp.model_sub prod 1
  obtain ⟨d5, hd5, hden⟩ := fp.model_mul b mu
  have hq_local : |s * t| <= 3 / 5 := by simpa [s, t] using hq
  have hprod_abs : |prod| < 1 := by
    change |fp.fl_mul s t| < 1
    rw [hprod, abs_mul]
    calc
      |s * t| * |1 + d3| <= (3 / 5) * (1 + fp.u) := by
        exact mul_le_mul hq_local
          (abs_one_add_le_one_add hd3) (abs_nonneg _) (by norm_num)
      _ < 1 := by nlinarith [fp.u_nonneg]
  have hprod_sub : prod - 1 ≠ 0 := by
    intro hzero
    have : prod = 1 := sub_eq_zero.mp hzero
    rw [this, abs_one] at hprod_abs
    exact lt_irrefl 1 hprod_abs
  have h4pos : 0 < 1 + d4 := by linarith [neg_abs_le d4, fp.u_nonneg]
  have h5pos : 0 < 1 + d5 := by linarith [neg_abs_le d5, fp.u_nonneg]
  have hmu_ne : mu ≠ 0 := by
    change fp.fl_sub prod 1 ≠ 0
    rw [hmu]
    exact mul_ne_zero hprod_sub (ne_of_gt h4pos)
  change fp.fl_mul b mu ≠ 0
  rw [hden]
  exact mul_ne_zero (mul_ne_zero hb hmu_ne) (ne_of_gt h5pos)

/-- The selected case-(4) pivot has the stronger exact product separation
`2 |a*c| <= |b|^2`.  This is the two failed diagonal tests plus
`alpha^2 < 1/2`; it is strictly stronger than the fill-only GEPP bridge. -/
theorem higham11_2_case4_selected_product_half_bound {n : Nat} (hn : 0 < n)
    (A : Fin n -> Fin n -> Real) (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch hn
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4) :
    let i0 := higham11_2_firstIndex hn
    let r := higham11_2_bunchKaufmanMaxRow hn A
    2 * |A i0 i0 * A r r| <= |A i0 r| ^ 2 := by
  let i0 := higham11_2_firstIndex hn
  let r := higham11_2_bunchKaufmanMaxRow hn A
  let omega1 := higham11_2_bunchKaufmanOmegaOne hn A
  let omegaR := higham11_2_bunchKaufmanOmegaRow hn A
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    hn higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  rcases hcase with ⟨homega_ne, _hfirst, hprod, hdiag⟩
  have halpha_pos : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  have halpha_sq_lt_half : higham11_1_bunchParlettAlpha ^ 2 < 1 / 2 := by
    have hsq : higham11_1_bunchParlettAlpha ^ 2 =
        (higham11_1_bunchParlettAlpha + 1) / 4 := by
      simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_sq
    have hlt : higham11_1_bunchParlettAlpha < 1 := by
      simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one
    nlinarith
  have hattain : |A r i0| = omega1 :=
    higham11_2_bunchKaufmanMaxRow_attains_omegaOne hn A homega_ne
  have hdiag_le : |A r r| <= higham11_1_bunchParlettAlpha * omegaR :=
    le_of_lt hdiag
  have hstep1 :
      |A i0 i0| * |A r r| <=
        |A i0 i0| * (higham11_1_bunchParlettAlpha * omegaR) :=
    mul_le_mul_of_nonneg_left hdiag_le (abs_nonneg _)
  have hstep2 :
      |A i0 i0| * (higham11_1_bunchParlettAlpha * omegaR) <
        higham11_1_bunchParlettAlpha ^ 2 * omega1 ^ 2 := by
    have hm := mul_lt_mul_of_pos_left hprod halpha_pos
    nlinarith
  have hprod_half : |A i0 i0| * |A r r| < (1 / 2) * omega1 ^ 2 :=
    lt_of_le_of_lt hstep1
      (lt_of_lt_of_le hstep2
        (mul_le_mul_of_nonneg_right (le_of_lt halpha_sq_lt_half)
          (sq_nonneg omega1)))
  dsimp only
  rw [abs_mul, hA i0 r, hattain]
  nlinarith

/-- The selected Higham (4.3) explicit-inverse producer. -/
noncomputable def higham11_2_flSelectedExplicitInverseSolve
    (fp : FPModel) {n : Nat} (hn : 0 < n)
    (A : Fin n -> Fin n -> Real) (z : Fin n -> Real) : Fin 2 -> Real :=
  let i0 := higham11_2_firstIndex hn
  let r := higham11_2_bunchKaufmanMaxRow hn A
  higham11_2_flExplicitInverseSolve fp
    (A i0 i0) (A i0 r) (A r r) (z i0) (z r)

/-- The selected producer's shared computed denominator. -/
noncomputable def higham11_2_flSelectedExplicitInverseDen
    (fp : FPModel) {n : Nat} (hn : 0 < n)
    (A : Fin n -> Fin n -> Real) : Real :=
  let i0 := higham11_2_firstIndex hn
  let r := higham11_2_bunchKaufmanMaxRow hn A
  higham11_2_flExplicitInverseDen fp (A i0 i0) (A i0 r) (A r r)

/-- An actual case-(4) decision and `u <= 10^-3` imply the complete low-level
run domain, including nonvanishing of the computed common denominator. -/
theorem higham11_2_case4_selected_explicitInverse_runDomain
    (fp : FPModel) (hu : fp.u <= 1 / 1000)
    {n : Nat} (hn : 0 < n) (A : Fin n -> Fin n -> Real)
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch hn
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4) :
    let i0 := higham11_2_firstIndex hn
    let r := higham11_2_bunchKaufmanMaxRow hn A
    Higham11ExplicitInverseRunDomain fp (A i0 i0) (A i0 r) (A r r) := by
  let i0 := higham11_2_firstIndex hn
  let r := higham11_2_bunchKaufmanMaxRow hn A
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    hn higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  have hattain := higham11_2_bunchKaufmanMaxRow_attains_omegaOne hn A hcase.1
  have hb : A i0 r ≠ 0 := by
    intro hz
    have hrz : A r i0 = 0 := by simpa [hA i0 r] using hz
    have : higham11_2_bunchKaufmanOmegaOne hn A = 0 := by
      rw [← hattain, hrz, abs_zero]
    exact hcase.1 this
  have hhalf : 2 * |A i0 i0 * A r r| <= |A i0 r| ^ 2 := by
    simpa [i0, r] using
      higham11_2_case4_selected_product_half_bound hn A hA hbranch
  have hscaled := higham11_2_flExplicitInverse_scaled_product_le_three_fifths
    fp hu (A i0 i0) (A i0 r) (A r r) hb hhalf
  refine ⟨hb, hscaled, ?_⟩
  exact higham11_2_flExplicitInverseDen_ne_zero_of_scaled_product
    fp hu (A i0 i0) (A i0 r) (A r r) hb hscaled

/-! ## Selected case-(4) matrix certificates -/

/-- **Algorithm 11.2 case (4), explicit-inverse arm.**  The actual scaled
inverse producer supplies the source's componentwise `gamma_180` certificate
for the matrix-selected pivot.  There is no data-dependent solve premise:
the case-(4) tests and the explicit smallness guard prove denominator
nonvanishing. -/
theorem higham11_2_flSelectedExplicitInverseSolve_backward_error_gamma180
    (fp : FPModel) (hu : fp.u <= 1 / 1000)
    {n : Nat} (hn : 0 < n) (A : Fin n -> Fin n -> Real)
    (hA : IsSymmetricFiniteMatrix A) (z : Fin n -> Real)
    (hbranch : higham11_2_bunchKaufmanFirstBranch hn
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4) :
    exists DeltaE : Fin 2 -> Fin 2 -> Real,
      (forall i j : Fin 2,
        |DeltaE i j| <= gamma fp 180 *
          |higham11_2_bunchKaufmanSelectedTwoBlock hn A i j|) /\
      forall p : Fin 2,
        (∑ q : Fin 2,
          (higham11_2_bunchKaufmanSelectedTwoBlock hn A p q + DeltaE p q) *
            higham11_2_flSelectedExplicitInverseSolve fp hn A z q) =
          z (Fin.cases (higham11_2_firstIndex hn)
            (fun _ => higham11_2_bunchKaufmanMaxRow hn A) p) := by
  let i0 := higham11_2_firstIndex hn
  let r := higham11_2_bunchKaufmanMaxRow hn A
  have hrun : Higham11ExplicitInverseRunDomain fp
      (A i0 i0) (A i0 r) (A r r) := by
    simpa [i0, r] using higham11_2_case4_selected_explicitInverse_runDomain
      fp hu hn A hA hbranch
  obtain ⟨da, db01, db10, dc, hda, hdb01, hdb10, hdc, hrow0, hrow1⟩ :=
    higham11_2_flExplicitInverseSolve_backward_error_gamma180 fp hu
      (A i0 i0) (A i0 r) (A r r) (z i0) (z r) hrun
  let DeltaE : Fin 2 -> Fin 2 -> Real := fun i j =>
    Fin.cases (Fin.cases da (fun _ => db01) j)
      (fun _ => Fin.cases db10 (fun _ => dc) j) i
  refine ⟨DeltaE, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · simpa [DeltaE, higham11_2_bunchKaufmanSelectedTwoBlock, i0, r] using hda
    · simpa [DeltaE, higham11_2_bunchKaufmanSelectedTwoBlock, i0, r] using hdb01
    · simpa [DeltaE, higham11_2_bunchKaufmanSelectedTwoBlock, i0, r, hA i0 r]
        using hdb10
    · simpa [DeltaE, higham11_2_bunchKaufmanSelectedTwoBlock, i0, r] using hdc
  · intro p
    fin_cases p
    · rw [Fin.sum_univ_two]
      simpa [DeltaE, higham11_2_bunchKaufmanSelectedTwoBlock,
        higham11_2_flSelectedExplicitInverseSolve, i0, r] using hrow0
    · rw [Fin.sum_univ_two]
      simpa [DeltaE, higham11_2_bunchKaufmanSelectedTwoBlock,
        higham11_2_flSelectedExplicitInverseSolve, i0, r, hA i0 r] using hrow1

/-- Linear finite-`u` form of the selected explicit-inverse certificate.
This is intentionally `360u`, obtained from `gamma_180`; it is not the
unrelated `36u` constant of the GEPP arm. -/
theorem higham11_2_flSelectedExplicitInverseSolve_higham115
    (fp : FPModel) (hu : fp.u <= 1 / 1000)
    {n : Nat} (hn : 0 < n) (A : Fin n -> Fin n -> Real)
    (hA : IsSymmetricFiniteMatrix A) (z : Fin n -> Real)
    (hbranch : higham11_2_bunchKaufmanFirstBranch hn
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4) :
    exists DeltaE : Fin 2 -> Fin 2 -> Real,
      higham11_5_twoByTwoPivotSolveStable fp.u 360
        (higham11_2_bunchKaufmanSelectedTwoBlock hn A) DeltaE /\
      forall p : Fin 2,
        (∑ q : Fin 2,
          (higham11_2_bunchKaufmanSelectedTwoBlock hn A p q + DeltaE p q) *
            higham11_2_flSelectedExplicitInverseSolve fp hn A z q) =
          z (Fin.cases (higham11_2_firstIndex hn)
            (fun _ => higham11_2_bunchKaufmanMaxRow hn A) p) := by
  obtain ⟨DeltaE, hDelta, hrows⟩ :=
    higham11_2_flSelectedExplicitInverseSolve_backward_error_gamma180
      fp hu hn A hA z hbranch
  have hsmall : (180 : Real) * fp.u <= 1 / 2 := by
    nlinarith [fp.u_nonneg]
  have hgamma := gamma_le_two_mul_n_u_of_nu_le_half fp 180 hsmall
  have hgamma360 : gamma fp 180 <= 360 * fp.u := by
    calc
      gamma fp 180 <= 2 * (180 * fp.u) := hgamma
      _ = 360 * fp.u := by ring
  refine ⟨DeltaE, ?_, hrows⟩
  intro i j
  exact (hDelta i j).trans
    (mul_le_mul_of_nonneg_right hgamma360
      (abs_nonneg (higham11_2_bunchKaufmanSelectedTwoBlock hn A i j)))

end NumStability

namespace NumStability

open Ch11Closure.Mixed
open Ch11Closure.Solve

namespace Higham11RoundedBunchKaufmanExecution

/-! ## Recursive middle solve using the explicit-inverse arm -/

/-- Recursively solve the literal block diagonal factor, choosing Higham's
scaled explicit inverse at every case-(4) node.  The existing honest
`MiddleSolveRunDomain` is sufficient: case-(4) denominator nonvanishing was
proved above, so only a terminal `noAction` scalar pivot needs a guard. -/
theorem actualExplicitInverseMiddleSolve_backward_error
    (hu : fp.u <= 1 / 1000)
    (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) :
    forall {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
      (exec : Higham11RoundedBunchKaufmanExecution fp A),
      exec.MiddleSolveRunDomain ->
      forall z : Fin n -> Real,
        exists (w : Fin n -> Real) (DeltaD : Fin n -> Fin n -> Real),
          (forall i j : Fin n,
            |DeltaD i j| <= 360 * fp.u * |exec.flatD i j|) /\
          forall p : Fin n,
            (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w q) = z p := by
  intro n A exec
  induction exec with
  | nil A =>
      intro _ z
      refine ⟨(fun i => Fin.elim0 i), (fun i _ => Fin.elim0 i), ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro p
        exact Fin.elim0 p
  | noAction A hA hbranch tail ih =>
      intro hdomain z
      rcases hdomain with ⟨hpivot, htailDomain⟩
      have hval1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hval9
      obtain ⟨Deltae, hDeltae, hheadEq⟩ :=
        fl_oneByOne_solve_backward_error fp (z 0) (A 0 0) hpivot hval1
      obtain ⟨wTail, DeltaTail, htailBound, htailEq⟩ :=
        ih htailDomain (fun i => z i.succ)
      have hgamma :=
        gamma_one_le_thirtySix_mul_u_of_gammaValid_nine hval9 hsmall9
      have hheadBound : |Deltae| <= 360 * fp.u * |A 0 0| := by
        calc
          |Deltae| <= gamma fp 1 * |A 0 0| := hDeltae
          _ <= 36 * fp.u * |A 0 0| :=
            mul_le_mul_of_nonneg_right hgamma (abs_nonneg _)
          _ <= 360 * fp.u * |A 0 0| := by
            nlinarith [mul_nonneg fp.u_nonneg (abs_nonneg (A 0 0))]
      obtain ⟨w, DeltaD, hbound, heq⟩ :=
        middleBlockDiagConsOne_solve_assemble (360 * fp.u) (A 0 0) (z 0)
          tail.flatD (fun i => z i.succ)
          (fp.fl_div (z 0) (A 0 0)) Deltae wTail DeltaTail
          hheadBound hheadEq htailBound htailEq
      refine ⟨w, DeltaD, ?_, ?_⟩
      · intro i j
        simpa [flatD, middleBlockDiagConsOne] using hbound i j
      · intro p
        have hp := heq p
        cases p using Fin.cases with
        | zero => simpa [flatD, middleBlockDiagConsOne, middleVecConsOne] using hp
        | succ i => simpa [flatD, middleBlockDiagConsOne, middleVecConsOne] using hp
  | case1 A hA hbranch tail ih =>
      intro hdomain z
      let B := higham11_2_bunchKaufmanRoundedActive A
      have hpivot : B 0 0 ≠ 0 := roundedActive_pivot_ne_zero_case1 A hbranch
      have hval1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hval9
      obtain ⟨Deltae, hDeltae, hheadEq⟩ :=
        fl_oneByOne_solve_backward_error fp (z 0) (B 0 0) hpivot hval1
      obtain ⟨wTail, DeltaTail, htailBound, htailEq⟩ :=
        ih hdomain (fun i => z i.succ)
      have hgamma :=
        gamma_one_le_thirtySix_mul_u_of_gammaValid_nine hval9 hsmall9
      have hheadBound : |Deltae| <= 360 * fp.u * |B 0 0| := by
        calc
          |Deltae| <= gamma fp 1 * |B 0 0| := hDeltae
          _ <= 36 * fp.u * |B 0 0| :=
            mul_le_mul_of_nonneg_right hgamma (abs_nonneg _)
          _ <= 360 * fp.u * |B 0 0| := by
            nlinarith [mul_nonneg fp.u_nonneg (abs_nonneg (B 0 0))]
      obtain ⟨w, DeltaD, hbound, heq⟩ :=
        middleBlockDiagConsOne_solve_assemble (360 * fp.u) (B 0 0) (z 0)
          tail.flatD (fun i => z i.succ)
          (fp.fl_div (z 0) (B 0 0)) Deltae wTail DeltaTail
          hheadBound hheadEq htailBound htailEq
      refine ⟨w, DeltaD, ?_, ?_⟩
      · intro i j
        simpa [flatD, B, middleBlockDiagConsOne] using hbound i j
      · intro p
        have hp := heq p
        cases p using Fin.cases with
        | zero => simpa [flatD, B, middleBlockDiagConsOne, middleVecConsOne] using hp
        | succ i => simpa [flatD, B, middleBlockDiagConsOne, middleVecConsOne] using hp
  | case2 A hA hbranch tail ih =>
      intro hdomain z
      let B := higham11_2_bunchKaufmanRoundedActive A
      have hpivot : B 0 0 ≠ 0 := roundedActive_pivot_ne_zero_case2 A hbranch
      have hval1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hval9
      obtain ⟨Deltae, hDeltae, hheadEq⟩ :=
        fl_oneByOne_solve_backward_error fp (z 0) (B 0 0) hpivot hval1
      obtain ⟨wTail, DeltaTail, htailBound, htailEq⟩ :=
        ih hdomain (fun i => z i.succ)
      have hgamma :=
        gamma_one_le_thirtySix_mul_u_of_gammaValid_nine hval9 hsmall9
      have hheadBound : |Deltae| <= 360 * fp.u * |B 0 0| := by
        calc
          |Deltae| <= gamma fp 1 * |B 0 0| := hDeltae
          _ <= 36 * fp.u * |B 0 0| :=
            mul_le_mul_of_nonneg_right hgamma (abs_nonneg _)
          _ <= 360 * fp.u * |B 0 0| := by
            nlinarith [mul_nonneg fp.u_nonneg (abs_nonneg (B 0 0))]
      obtain ⟨w, DeltaD, hbound, heq⟩ :=
        middleBlockDiagConsOne_solve_assemble (360 * fp.u) (B 0 0) (z 0)
          tail.flatD (fun i => z i.succ)
          (fp.fl_div (z 0) (B 0 0)) Deltae wTail DeltaTail
          hheadBound hheadEq htailBound htailEq
      refine ⟨w, DeltaD, ?_, ?_⟩
      · intro i j
        simpa [flatD, B, middleBlockDiagConsOne] using hbound i j
      · intro p
        have hp := heq p
        cases p using Fin.cases with
        | zero => simpa [flatD, B, middleBlockDiagConsOne, middleVecConsOne] using hp
        | succ i => simpa [flatD, B, middleBlockDiagConsOne, middleVecConsOne] using hp
  | case3 A hA hbranch tail ih =>
      intro hdomain z
      let B := higham11_2_bunchKaufmanRoundedActive A
      have hpivot : B 0 0 ≠ 0 := roundedActive_pivot_ne_zero_case3 A hA hbranch
      have hval1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hval9
      obtain ⟨Deltae, hDeltae, hheadEq⟩ :=
        fl_oneByOne_solve_backward_error fp (z 0) (B 0 0) hpivot hval1
      obtain ⟨wTail, DeltaTail, htailBound, htailEq⟩ :=
        ih hdomain (fun i => z i.succ)
      have hgamma :=
        gamma_one_le_thirtySix_mul_u_of_gammaValid_nine hval9 hsmall9
      have hheadBound : |Deltae| <= 360 * fp.u * |B 0 0| := by
        calc
          |Deltae| <= gamma fp 1 * |B 0 0| := hDeltae
          _ <= 36 * fp.u * |B 0 0| :=
            mul_le_mul_of_nonneg_right hgamma (abs_nonneg _)
          _ <= 360 * fp.u * |B 0 0| := by
            nlinarith [mul_nonneg fp.u_nonneg (abs_nonneg (B 0 0))]
      obtain ⟨w, DeltaD, hbound, heq⟩ :=
        middleBlockDiagConsOne_solve_assemble (360 * fp.u) (B 0 0) (z 0)
          tail.flatD (fun i => z i.succ)
          (fp.fl_div (z 0) (B 0 0)) Deltae wTail DeltaTail
          hheadBound hheadEq htailBound htailEq
      refine ⟨w, DeltaD, ?_, ?_⟩
      · intro i j
        simpa [flatD, B, middleBlockDiagConsOne] using hbound i j
      · intro p
        have hp := heq p
        cases p using Fin.cases with
        | zero => simpa [flatD, B, middleBlockDiagConsOne, middleVecConsOne] using hp
        | succ i => simpa [flatD, B, middleBlockDiagConsOne, middleVecConsOne] using hp
  | @case4 n A hA hbranch hsecond tail ih =>
      intro hdomain z
      let B := higham11_2_bunchKaufmanRoundedActive A
      let zSource : Fin (n + 2) -> Real := fun k => if k = 0 then z 0 else z 1
      obtain ⟨wTail, DeltaTail, htailBound, htailEq⟩ :=
        ih hdomain (fun i => z i.succ.succ)
      obtain ⟨DeltaE, hstable, hheadSourceEq⟩ :=
        higham11_2_flSelectedExplicitInverseSolve_higham115 fp hu
          (by omega : 0 < n + 2) A hA zSource hbranch
      have hcase := higham11_2_bunchKaufmanFirstBranch_spec
        (by omega : 0 < n + 2) higham11_1_bunchParlettAlpha A
      rw [hbranch] at hcase
      have hr0 : higham11_2_bunchKaufmanMaxRow
          (by omega : 0 < n + 2) A ≠ (0 : Fin (n + 2)) := by
        simpa [higham11_2_firstIndex] using
          (higham11_2_bunchKaufmanMaxRow_ne_first_of_omegaOne_ne_zero
            (by omega : 0 < n + 2) A hcase.1)
      have hlead := higham11_2_bunchKaufmanSelectedTwoBlock_eq_activeLeading
        A hbranch
      have hheadBound : forall p q : Fin 2,
          |DeltaE p q| <= 360 * fp.u * |B (embedTwo n p) (embedTwo n q)| := by
        intro p q
        change |DeltaE p q| <= 360 * fp.u *
          |higham11_2_bunchKaufmanExactActive A (embedTwo n p) (embedTwo n q)|
        rw [← hlead p q]
        exact hstable p q
      have hheadEq : forall p : Fin 2,
          (∑ q : Fin 2,
            (B (embedTwo n p) (embedTwo n q) + DeltaE p q) *
              higham11_2_flSelectedExplicitInverseSolve fp
                (by omega : 0 < n + 2) A zSource q) = z (embedTwo n p) := by
        intro p
        have hp := hheadSourceEq p
        change (∑ q : Fin 2,
            (higham11_2_bunchKaufmanExactActive A
              (embedTwo n p) (embedTwo n q) + DeltaE p q) *
              higham11_2_flSelectedExplicitInverseSolve fp
                (by omega : 0 < n + 2) A zSource q) = z (embedTwo n p)
        simp_rw [← hlead]
        rw [hp]
        fin_cases p
        · simp [zSource, higham11_2_firstIndex]
        · change zSource
            (higham11_2_bunchKaufmanMaxRow (by omega : 0 < n + 2) A) = z 1
          simp [zSource, hr0]
      obtain ⟨w, DeltaD, hbound, heq⟩ :=
        middleBlockDiagConsTwo_solve_assemble (360 * fp.u)
          (fun p q => B (embedTwo n p) (embedTwo n q)) tail.flatD
          (fun p => z (embedTwo n p)) (fun i => z i.succ.succ)
          (higham11_2_flSelectedExplicitInverseSolve fp
            (by omega : 0 < n + 2) A zSource)
          DeltaE wTail DeltaTail hheadBound hheadEq htailBound htailEq
      refine ⟨w, DeltaD, ?_, ?_⟩
      · intro i j
        simpa [flatD, B, middleBlockDiagConsTwo] using hbound i j
      · intro p
        cases p using Fin.cases with
        | zero =>
            simpa [flatD, B, middleBlockDiagConsTwo, middleVecConsTwo] using
              heq (0 : Fin (n + 2))
        | succ k =>
            cases k using Fin.cases with
            | zero =>
                simpa [flatD, B, middleBlockDiagConsTwo, middleVecConsTwo] using
                  heq (Fin.succ (0 : Fin (n + 1)))
            | succ i =>
                simpa [flatD, B, middleBlockDiagConsTwo, middleVecConsTwo] using
                  heq i.succ.succ
  | case4Breakdown A hA hbranch hsecond =>
      intro hdomain
      exact False.elim hdomain

/-- The unchanged middle-solve domain also implies successful completion for
the explicit-inverse recursion. -/
theorem completed_of_explicitInverseMiddleSolveRunDomain : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) ->
    exec.MiddleSolveRunDomain -> exec.Completed
  | _, _, .nil _ => by simp [MiddleSolveRunDomain, Completed]
  | _, _, .noAction _ _ _ tail => by
      intro h
      exact completed_of_explicitInverseMiddleSolveRunDomain tail h.2
  | _, _, .case1 _ _ _ tail => by
      intro h
      exact completed_of_explicitInverseMiddleSolveRunDomain tail h
  | _, _, .case2 _ _ _ tail => by
      intro h
      exact completed_of_explicitInverseMiddleSolveRunDomain tail h
  | _, _, .case3 _ _ _ tail => by
      intro h
      exact completed_of_explicitInverseMiddleSolveRunDomain tail h
  | _, _, .case4 _ _ _ _ tail => by
      intro h
      exact completed_of_explicitInverseMiddleSolveRunDomain tail h
  | _, _, .case4Breakdown _ _ _ _ => by
      intro h
      exact False.elim h

end Higham11RoundedBunchKaufmanExecution

end NumStability

namespace NumStability

namespace Higham11RoundedBunchKaufmanExecution

/-! ## Pivot- and source-coordinate terminal adapters -/

/-- Terminal rounded solve in pivot coordinates using the actual scaled
explicit-inverse middle solve at every case-(4) node.  Completion is derived
from `MiddleSolveRunDomain`; no separate `Completed` premise is exposed. -/
theorem computedSolve_backward_error_normwise_forty_actual_explicitInverse
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hmiddleDomain : exec.MiddleSolveRunDomain)
    (b : Fin n -> Real) (hvaln : gammaValid fp n) (Amax : Real)
    (hAmax : forall i j : Fin n, |exec.permutedInput i j| <= Amax)
    (hAmaxPos : 0 < Amax) :
    exists (w_hat : Fin n -> Real)
      (DeltaD DeltaA2 : Fin n -> Fin n -> Real),
      (forall i j : Fin n,
        |DeltaD i j| <= 360 * fp.u * |exec.flatD i j|) /\
      (forall p : Fin n,
        (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
          fl_forwardSub fp n exec.flatL b p) /\
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          exec.finiteResidualCoefficient *
              ((1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax) +
            solveResidualCoefficient fp n (360 * fp.u) *
              (40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax)) /\
      forall i : Fin n,
        (∑ j : Fin n,
          (exec.permutedInput i j + DeltaA2 i j) *
            fl_backSub fp n (fun r c => exec.flatL c r) w_hat j) = b i := by
  have hu : fp.u <= 1 / 1000 := by nlinarith [fp.u_nonneg]
  have hcompleted : exec.Completed :=
    completed_of_explicitInverseMiddleSolveRunDomain exec hmiddleDomain
  obtain ⟨w_hat, DeltaD, hDeltaD, hmiddle⟩ :=
    actualExplicitInverseMiddleSolve_backward_error hu hval9 hsmall9
      exec hmiddleDomain (fl_forwardSub fp n exec.flatL b)
  have hgammaMid : 0 <= 360 * fp.u :=
    mul_nonneg (by norm_num) fp.u_nonneg
  obtain ⟨DeltaA2, hDeltaA2, hsolve⟩ :=
    computedSolve_backward_error_normwise_forty
      hval3 hval9 hsmall9 huSmall exec hcompleted b hvaln
        (360 * fp.u) Amax hgammaMid hAmax hAmaxPos
        w_hat DeltaD hDeltaD hmiddle
  exact ⟨w_hat, DeltaD, DeltaA2, hDeltaD, hmiddle, hDeltaA2, hsolve⟩

/-- Source-coordinate terminal using the actual scaled explicit-inverse arm.
The pivot permutation is confined to the implementation of the solve. -/
theorem computedSolve_backward_error_normwise_forty_actual_explicitInverse_source
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hmiddleDomain : exec.MiddleSolveRunDomain)
    (b : Fin n -> Real) (hvaln : gammaValid fp n) (Amax : Real)
    (hAmax : forall i j : Fin n, |A i j| <= Amax)
    (hAmaxPos : 0 < Amax) :
    exists (w_hat : Fin n -> Real)
      (DeltaD DeltaA2 : Fin n -> Fin n -> Real),
      (forall i j : Fin n,
        |DeltaD i j| <= 360 * fp.u * |exec.flatD i j|) /\
      (forall p : Fin n,
        (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
          fl_forwardSub fp n exec.flatL
            (fun i => b (exec.permutation i)) p) /\
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          exec.finiteResidualCoefficient *
              ((1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax) +
            solveResidualCoefficient fp n (360 * fp.u) *
              (40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax)) /\
      forall i : Fin n,
        (∑ j : Fin n,
          (A i j + DeltaA2 i j) *
            exec.unpermutedVector
              (fl_backSub fp n (fun r c => exec.flatL c r) w_hat) j) = b i := by
  have hu : fp.u <= 1 / 1000 := by nlinarith [fp.u_nonneg]
  have hcompleted : exec.Completed :=
    completed_of_explicitInverseMiddleSolveRunDomain exec hmiddleDomain
  obtain ⟨w_hat, DeltaD, hDeltaD, hmiddle⟩ :=
    actualExplicitInverseMiddleSolve_backward_error hu hval9 hsmall9
      exec hmiddleDomain
        (fl_forwardSub fp n exec.flatL (fun i => b (exec.permutation i)))
  have hgammaMid : 0 <= 360 * fp.u :=
    mul_nonneg (by norm_num) fp.u_nonneg
  obtain ⟨DeltaA2, hDeltaA2, hsolve⟩ :=
    computedSolve_backward_error_normwise_forty_source
      hval3 hval9 hsmall9 huSmall exec hcompleted b hvaln
        (360 * fp.u) Amax hgammaMid hAmax hAmaxPos
        w_hat DeltaD hDeltaD hmiddle
  exact ⟨w_hat, DeltaD, DeltaA2, hDeltaD, hmiddle, hDeltaA2, hsolve⟩

end Higham11RoundedBunchKaufmanExecution

end NumStability
