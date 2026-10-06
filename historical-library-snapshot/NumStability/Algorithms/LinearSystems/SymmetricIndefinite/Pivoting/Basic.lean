import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms LinearSystems SymmetricIndefinite Pivoting Basic

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.CholeskyIndefinite` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Bunch-Parlett pivoting parameter** α = (1 + √17)/8.

    This minimizes the worst-case element growth by equating
    the growth bounds for 1×1 and 2×2 pivot steps.

    α is the positive root of 4α² − α − 1 = 0. -/
noncomputable def bunchParlettAlpha : ℝ := (1 + Real.sqrt 17) / 8

/-- **Bunch-Parlett α is a root of 4α² − α − 1 = 0**.

    This algebraic identity characterizes α = (1 + √17)/8 as the solution that
    minimizes the worst-case element growth. -/
theorem bunch_parlett_alpha_root :
    4 * bunchParlettAlpha ^ 2 - bunchParlettAlpha - 1 = 0 := by
  unfold bunchParlettAlpha
  have h17 : Real.sqrt 17 * Real.sqrt 17 = 17 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  field_simp
  nlinarith [h17]

/-- The Bunch-Parlett parameter is strictly positive. -/
theorem bunch_parlett_alpha_pos : 0 < bunchParlettAlpha := by
  unfold bunchParlettAlpha
  have : (0 : ℝ) ≤ Real.sqrt 17 := Real.sqrt_nonneg 17
  linarith

/-- The Bunch-Parlett parameter satisfies `α < 1` (since `√17 < 7`). -/
theorem bunch_parlett_alpha_lt_one : bunchParlettAlpha < 1 := by
  unfold bunchParlettAlpha
  have h : Real.sqrt 17 < 7 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- **Growth-balance identity** (Higham §11.1.1).  For any `α ≠ 0, 1` that is a
    root of `4α² − α − 1 = 0`, the worst-case growth of two `s = 1` steps equals
    that of one `s = 2` step: `(1 + 1/α)² = 1 + 2/(1 − α)`.  This is the source's
    derivation "we equate the maximum growth …, which reduces to `4α² − α − 1 = 0`". -/
theorem growth_balance_of_root (α : ℝ) (hα0 : α ≠ 0) (hα1 : α ≠ 1)
    (hroot : 4 * α ^ 2 - α - 1 = 0) :
    (1 + 1 / α) ^ 2 = 1 + 2 / (1 - α) := by
  have h1α : (1 - α) ≠ 0 := by
    intro h; apply hα1; linarith [sub_eq_zero.mp h]
  field_simp
  nlinarith [hroot]

/-- The Bunch-Parlett `α = (1+√17)/8` is exactly the value that balances the 1×1
    and 2×2 single-step growth bounds proved above (`oneByOne_schur_growth`,
    `twoByTwo_schur_growth`): `(1 + 1/α)² = 1 + 2/(1 − α)`. -/
theorem bunch_parlett_growth_balance :
    (1 + 1 / bunchParlettAlpha) ^ 2 = 1 + 2 / (1 - bunchParlettAlpha) :=
  growth_balance_of_root bunchParlettAlpha
    (ne_of_gt bunch_parlett_alpha_pos)
    (ne_of_lt bunch_parlett_alpha_lt_one)
    bunch_parlett_alpha_root

/-- `α > 1/2` (since `√17 > 3`). -/
theorem bunch_parlett_alpha_gt_half : (1 : ℝ) / 2 < bunchParlettAlpha := by
  unfold bunchParlettAlpha
  have h : (3 : ℝ) < Real.sqrt 17 :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 3)).mpr (by norm_num)
  linarith

/-- `α ≤ 5/7` (since `√17 ≤ 33/7`). -/
theorem bunch_parlett_alpha_le_5_7 : bunchParlettAlpha ≤ 5 / 7 := by
  unfold bunchParlettAlpha
  have h : Real.sqrt 17 ≤ 33 / 7 := by
    rw [show (33 : ℝ) / 7 = Real.sqrt ((33 / 7) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- From the root `4α²−α−1=0`: `α² = (α+1)/4`. -/
theorem bunch_parlett_alpha_sq :
    bunchParlettAlpha ^ 2 = (bunchParlettAlpha + 1) / 4 := by
  nlinarith [bunch_parlett_alpha_root]

/-- The 1×1-pivot multiplier constant `1/α < 2` (Higham [608, 1997], the bound
    `g_ij ≤ α⁻¹·max ≤ 2·max` for 1×1 pivots). -/
theorem bunch_kaufman_recip_alpha_lt_two : 1 / bunchParlettAlpha < 2 := by
  rw [div_lt_iff₀ bunch_parlett_alpha_pos]; nlinarith [bunch_parlett_alpha_gt_half]

/-- **Higham [608, 1997], appendix (A.3)**: `|E||E⁻¹||E| ≤ ((3+α²)/(1−α²))|E| ≤ 6|E|`
    — the scalar constant `(3+α²)/(1−α²) ≤ 6` for the Bunch–Kaufman `α`. -/
theorem bunch_kaufman_pivot_norm_const_le_six :
    (3 + bunchParlettAlpha ^ 2) / (1 - bunchParlettAlpha ^ 2) ≤ 6 := by
  have hlt : bunchParlettAlpha ^ 2 < 1 := by
    nlinarith [bunch_parlett_alpha_pos, bunch_parlett_alpha_lt_one]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [bunch_parlett_alpha_sq, bunch_parlett_alpha_le_5_7, bunch_parlett_alpha_pos]

/-- **Higham [608, 1997], eq (4.13)** — the constant behind the Theorem 11.4
    bound `‖|L̂||D̂||L̂ᵀ|‖_M ≤ 36 n ρₙ ‖A‖_M`: for a 2×2 pivot,
    `(3+α²)(3+α)/(1−α²)² ≤ 36`. -/
theorem bunch_kaufman_bound_const_le_36 :
    (3 + bunchParlettAlpha ^ 2) * (3 + bunchParlettAlpha)
      / (1 - bunchParlettAlpha ^ 2) ^ 2 ≤ 36 := by
  have hlt : bunchParlettAlpha ^ 2 < 1 := by
    nlinarith [bunch_parlett_alpha_pos, bunch_parlett_alpha_lt_one]
  have hden : 0 < (1 - bunchParlettAlpha ^ 2) ^ 2 := pow_pos (by linarith) 2
  rw [div_le_iff₀ hden]
  nlinarith [bunch_parlett_alpha_sq, bunch_parlett_alpha_le_5_7,
    bunch_parlett_alpha_pos, bunch_parlett_alpha_lt_one]

/-- **Growth-factor recursion** (Higham §11.1.1).  If the stage-maximum sequence
    `r` grows by at most the single-step factor `1 + 1/α` at each elimination
    stage (`r(k+1) ≤ (1 + 1/α)·r k`, the per-step bound proved for both 1×1 and
    2×2 pivots by `oneByOne_schur_growth` / `twoByTwo_schur_growth`), starting
    from `r 0 = ρ₀`, then after `n` stages `r n ≤ (1 + 1/α)^n · ρ₀`.  This is the
    mechanism turning the single-step element-growth bounds into the growth-factor
    bound `ρₙ ≤ (1 + α⁻¹)^{n−1}` quoted in the text (derived here, not assumed). -/
theorem geom_growth_iterate (α ρ0 : ℝ) (r : ℕ → ℝ)
    (hα : 0 < α) (h0 : r 0 = ρ0)
    (hstep : ∀ k, r (k + 1) ≤ (1 + 1 / α) * r k) :
    ∀ n, r n ≤ (1 + 1 / α) ^ n * ρ0 := by
  have hc : (0 : ℝ) ≤ 1 + 1 / α := by positivity
  intro n
  induction n with
  | zero => simp [h0]
  | succ k ih =>
      calc r (k + 1) ≤ (1 + 1 / α) * r k := hstep k
        _ ≤ (1 + 1 / α) * ((1 + 1 / α) ^ k * ρ0) :=
            mul_le_mul_of_nonneg_left ih hc
        _ = (1 + 1 / α) ^ (k + 1) * ρ0 := by ring

/-- **Abstract Bunch-Parlett growth-factor interface** (Higham §11.1.1).

    The diagonal pivoting method with complete pivoting has
    growth factor bounded by (1 + α⁻¹)^{n−1} where α = (1+√17)/8.

    Since 1 + α⁻¹ ≈ 2.57, this gives growth ≤ (2.57)^{n−1}.

    A more detailed analysis by Bunch shows that the growth factor
    is no more than 3.07(n−1)^{0.446} times the LU complete pivoting bound.
    The hypothesis `hρ` supplies the pivot-growth analysis. -/
theorem bunch_parlett_growth_bound (n : ℕ) (_hn : 0 < n)
    (ρ_n : ℝ)
    -- Growth factor hypothesis: ρ_n ≤ (1 + α⁻¹)^{n-1}
    (hρ : ρ_n ≤ (1 + bunchParlettAlpha⁻¹) ^ (n - 1)) :
    ρ_n ≤ (1 + bunchParlettAlpha⁻¹) ^ (n - 1) :=
  hρ

/-- **Abstract Bunch-Parlett L-factor bound interface** (Higham §11.1.1).

    For the complete pivoting strategy, no element of CE⁻¹ (the
    multiplier block) exceeds max{1/α, 1/(1-α)} in absolute value.
    This bounds ‖L‖ independently of A.  The entrywise multiplier bound is
    supplied as `hL`. -/
theorem bunch_parlett_L_bound (n : ℕ)
    (L : Fin n → Fin n → ℝ)
    (c_bound : ℝ)
    (_hc : c_bound = max (1 / bunchParlettAlpha) (1 / (1 - bunchParlettAlpha)))
    (hL : ∀ i j : Fin n, |L i j| ≤ c_bound) :
    ∀ i j : Fin n, |L i j| ≤ c_bound :=
  hL

/-- **Multiplier bound for a 1×1 pivot** (Higham §11.1.1–§11.1.2).

    A 1×1 pivot `e` accepted by the Bunch–Parlett / Bunch–Kaufman test
    `α·ω ≤ |e|`, where `ω` bounds the magnitude of the off-pivot column entries
    `c`, produces subdiagonal multipliers `c / e` with `|c / e| ≤ 1/α`.

    This is the elementwise fact behind "no element of `CE⁻¹` exceeds
    `max{1/α, 1/(1-α)}`", hence `‖L‖` is bounded independently of `A`.  It is a
    genuine derivation from the pivot-acceptance test, not an assumed bound. -/
theorem oneByOne_multiplier_bound (c e ω α : ℝ)
    (hα : 0 < α) (hω : 0 < ω) (hc : |c| ≤ ω) (he : α * ω ≤ |e|) :
    |c / e| ≤ 1 / α := by
  have hαω : 0 < α * ω := mul_pos hα hω
  have hepos : 0 < |e| := lt_of_lt_of_le hαω he
  have hinv : (0 : ℝ) < 1 / α := by positivity
  have hstep : ω ≤ 1 / α * |e| := by
    have h1 := mul_le_mul_of_nonneg_left he (le_of_lt hinv)
    rwa [← mul_assoc, one_div_mul_cancel (ne_of_gt hα), one_mul] at h1
  rw [abs_div, div_le_iff₀ hepos]
  linarith [hc, hstep]

/-- **Element growth for a 1×1 Schur step** (Higham §11.1.1, and §11.1.2 cases
    (1)–(3)).  With `μ₀` bounding the magnitude of every active entry
    (`|b|, |c₁|, |c₂| ≤ μ₀`) and a 1×1 pivot `e` accepted under `α·μ₀ ≤ |e|`,
    the Schur-complement entry `b − c₁·c₂/e` satisfies
    `|b − c₁·c₂/e| ≤ (1 + 1/α)·μ₀`.  Iterating this per-step bound is the
    mechanism behind the growth-factor bound `ρₙ ≤ (1 + α⁻¹)^{n−1}`. -/
theorem oneByOne_schur_growth (b c1 c2 e μ0 α : ℝ)
    (hα : 0 < α) (hμ : 0 < μ0)
    (hb : |b| ≤ μ0) (hc1 : |c1| ≤ μ0) (hc2 : |c2| ≤ μ0)
    (he : α * μ0 ≤ |e|) :
    |b - c1 * c2 / e| ≤ (1 + 1 / α) * μ0 := by
  have hmult : |c2 / e| ≤ 1 / α :=
    oneByOne_multiplier_bound c2 e μ0 α hα hμ hc2 he
  have hcorr : |c1 * c2 / e| ≤ 1 / α * μ0 := by
    rw [mul_div_assoc, abs_mul]
    calc |c1| * |c2 / e|
        ≤ μ0 * (1 / α) := mul_le_mul hc1 hmult (abs_nonneg _) (le_of_lt hμ)
      _ = 1 / α * μ0 := by ring
  have htri : |b - c1 * c2 / e| ≤ |b| + |c1 * c2 / e| := by
    have h := abs_add_le b (-(c1 * c2 / e))
    simpa [sub_eq_add_neg, abs_neg] using h
  calc |b - c1 * c2 / e|
      ≤ |b| + |c1 * c2 / e| := htri
    _ ≤ μ0 + 1 / α * μ0 := add_le_add hb hcorr
    _ = (1 + 1 / α) * μ0 := by ring

/-- **2×2 complete-pivot determinant bound** (Higham §11.1.1).

    When complete pivoting selects a 2×2 pivot block
    `E = [[e₁₁, e₂₁], [e₂₁, e₂₂]]`, the off-diagonal entry has the maximal
    magnitude `μ₀` (`e₂₁² = μ₀²`), the diagonal entries are bounded by the best
    1×1 pivot `μ₁ ≤ α·μ₀`, and the determinant satisfies
    `det E = e₁₁e₂₂ − e₂₁² ≤ (α² − 1)·μ₀²`.  This is the printed estimate
    `det(E) ≤ μ₁² − μ₀² ≤ (α² − 1)μ₀²`. -/
theorem twoByTwo_completePivot_det_bound (e11 e22 e21 μ0 μ1 α : ℝ)
    (hμ1 : 0 ≤ μ1)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0) :
    e11 * e22 - e21 ^ 2 ≤ (α ^ 2 - 1) * μ0 ^ 2 := by
  have h1 : e11 * e22 ≤ μ1 * μ1 := by
    calc e11 * e22 ≤ |e11 * e22| := le_abs_self _
      _ = |e11| * |e22| := abs_mul _ _
      _ ≤ μ1 * μ1 := mul_le_mul he11 he22 (abs_nonneg _) hμ1
  have hαμ0 : 0 ≤ α * μ0 := le_trans hμ1 hμ1α
  have h2 : μ1 * μ1 ≤ (α * μ0) * (α * μ0) :=
    mul_le_mul hμ1α hμ1α hμ1 hαμ0
  nlinarith [h1, h2, he21]

/-- **2×2 complete-pivot determinant magnitude lower bound** (Higham §11.1.1).

    For `α ∈ [0, 1)`, the 2×2 pivot chosen by complete pivoting is nonsingular
    with `|det E| ≥ (1 − α²)·μ₀²`, the printed bound used to control `E⁻¹`. -/
theorem twoByTwo_completePivot_absdet_lower (e11 e22 e21 μ0 μ1 α : ℝ)
    (hμ1 : 0 ≤ μ1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0) :
    (1 - α ^ 2) * μ0 ^ 2 ≤ |e11 * e22 - e21 ^ 2| := by
  have hdet := twoByTwo_completePivot_det_bound e11 e22 e21 μ0 μ1 α
    hμ1 he11 he22 he21 hμ1α
  have hμ0sq : 0 ≤ μ0 ^ 2 := sq_nonneg μ0
  have hα2 : (0 : ℝ) ≤ 1 - α ^ 2 := by nlinarith [hα0, hα1]
  have hneg : e11 * e22 - e21 ^ 2 ≤ 0 := by
    nlinarith [hdet, mul_nonneg hα2 hμ0sq]
  rw [abs_of_nonpos hneg]
  nlinarith [hdet]

/-- **2×2 inverse-block entrywise bounds** (Higham §11.1.1).  For the
    complete-pivoting 2×2 block `E = [[e₁₁,e₂₁],[e₂₁,e₂₂]]`
    (`|e₁₁|,|e₂₂| ≤ μ₁ ≤ αμ₀`, `e₂₁² = μ₀²`, `α ∈ [0,1)`, `μ₀ > 0`), with
    `d = det E = e₁₁e₂₂ − e₂₁²` and `K = 1/((1−α²)μ₀)`, the entries of
    `E⁻¹ = d⁻¹[[e₂₂,−e₂₁],[−e₂₁,e₁₁]]` are bounded by
    `|e₂₂/d|, |e₁₁/d| ≤ αK` and `|e₂₁/d| ≤ K`.  This is the printed
    `|E⁻¹| ≤ K·[[α,1],[1,α]]`, derived from `twoByTwo_completePivot_absdet_lower`. -/
theorem twoByTwo_inverse_entry_bounds (e11 e22 e21 μ0 μ1 α K : ℝ)
    (hμ1 : 0 ≤ μ1) (hα0 : 0 ≤ α) (hα1 : α < 1) (hμ : 0 < μ0)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0)
    (hK : (1 - α ^ 2) * μ0 * K = 1) :
    |e22 / (e11 * e22 - e21 ^ 2)| ≤ α * K
      ∧ |e11 / (e11 * e22 - e21 ^ 2)| ≤ α * K
      ∧ |e21 / (e11 * e22 - e21 ^ 2)| ≤ K := by
  have hα2 : α ^ 2 < 1 := by nlinarith [hα0, hα1]
  have hD : 0 < (1 - α ^ 2) * μ0 ^ 2 := mul_pos (by linarith [hα2]) (pow_pos hμ 2)
  have habs := twoByTwo_completePivot_absdet_lower e11 e22 e21 μ0 μ1 α
    hμ1 hα0 hα1 he11 he22 he21 hμ1α
  set d := e11 * e22 - e21 ^ 2 with hd
  have hdpos : 0 < |d| := lt_of_lt_of_le hD habs
  have hK0 : 0 ≤ K := by
    nlinarith [hK, mul_pos (by linarith [hα2] : (0 : ℝ) < 1 - α ^ 2) hμ]
  have hαK0 : 0 ≤ α * K := mul_nonneg hα0 hK0
  have hkey1 : α * μ0 ≤ α * K * |d| := by
    have hval : α * K * ((1 - α ^ 2) * μ0 ^ 2) = α * μ0 := by
      have h1 : K * ((1 - α ^ 2) * μ0) = 1 := by linarith [hK]
      nlinarith [h1]
    nlinarith [mul_le_mul_of_nonneg_left habs hαK0, hval]
  have hkey2 : μ0 ≤ K * |d| := by
    have hval : K * ((1 - α ^ 2) * μ0 ^ 2) = μ0 := by
      have h1 : K * ((1 - α ^ 2) * μ0) = 1 := by linarith [hK]
      nlinarith [h1]
    nlinarith [mul_le_mul_of_nonneg_left habs hK0, hval]
  have h21abs : |e21| = μ0 := by
    rw [← Real.sqrt_sq_eq_abs, he21, Real.sqrt_sq (le_of_lt hμ)]
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_div, div_le_iff₀ hdpos]
    calc |e22| ≤ μ1 := he22
      _ ≤ α * μ0 := hμ1α
      _ ≤ α * K * |d| := hkey1
  · rw [abs_div, div_le_iff₀ hdpos]
    calc |e11| ≤ μ1 := he11
      _ ≤ α * μ0 := hμ1α
      _ ≤ α * K * |d| := hkey1
  · rw [abs_div, div_le_iff₀ hdpos]
    calc |e21| = μ0 := h21abs
      _ ≤ K * |d| := hkey2

/-- Elementary bound `|x·y·z| ≤ p·q·r` from `|x| ≤ p`, `|y| ≤ q`, `|z| ≤ r`
    with `p, q ≥ 0`.  Used to bound the length-two inner products in the 2×2
    Schur-complement growth estimate. -/
theorem abs_triple_mul_le (x y z p q r : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hx : |x| ≤ p) (hy : |y| ≤ q) (hz : |z| ≤ r) :
    |x * y * z| ≤ p * q * r := by
  rw [abs_mul, abs_mul]
  have h1 : |x| * |y| ≤ p * q := mul_le_mul hx hy (abs_nonneg _) hp
  exact mul_le_mul h1 hz (abs_nonneg _) (mul_nonneg hp hq)

/-- **2×2 complete-pivoting element growth** (Higham §11.1.1, eq. (11.4)).

    The Schur-complement entry
    `ã = b − (c_i1(f₁₁c_j1 + f₁₂c_j2) + c_i2(f₂₁c_j1 + f₂₂c_j2))`,
    built from the inverse-block entries `f` bounded entrywise by
    `|f₁₁|, |f₂₂| ≤ αK` and `|f₁₂|, |f₂₁| ≤ K` with `K = 1/((1−α²)μ₀)`
    (`hK : (1−α²)·μ₀·K = 1`), and with every active entry bounded by `μ₀`,
    satisfies the printed bound `|ã| ≤ (1 + 2/(1−α))·μ₀`.

    Together with `oneByOne_schur_growth` (the `(1 + 1/α)μ₀` bound for a 1×1
    step) this gives both single-step growth bounds of §11.1.1, whose equality
    `(1 + 1/α)² = 1 + 2/(1−α)` fixes `α = (1+√17)/8`. -/
theorem twoByTwo_schur_growth
    (b ci1 ci2 cj1 cj2 f11 f12 f21 f22 μ0 α K : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hμ : 0 < μ0)
    (hK : (1 - α ^ 2) * μ0 * K = 1)
    (hb : |b| ≤ μ0)
    (hci1 : |ci1| ≤ μ0) (hci2 : |ci2| ≤ μ0)
    (hcj1 : |cj1| ≤ μ0) (hcj2 : |cj2| ≤ μ0)
    (hf11 : |f11| ≤ α * K) (hf12 : |f12| ≤ K)
    (hf21 : |f21| ≤ K) (hf22 : |f22| ≤ α * K) :
    |b - (ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2))|
      ≤ (1 + 2 / (1 - α)) * μ0 := by
  have hμ0 : 0 ≤ μ0 := le_of_lt hμ
  have hα2 : α ^ 2 < 1 := by nlinarith [hα0, hα1]
  have hden : 0 < (1 - α ^ 2) * μ0 := mul_pos (by linarith [hα2]) hμ
  have hK0 : 0 ≤ K := by nlinarith [hK, hden]
  have hαK : 0 ≤ α * K := mul_nonneg hα0 hK0
  have t1 : |ci1 * f11 * cj1| ≤ μ0 * (α * K) * μ0 :=
    abs_triple_mul_le ci1 f11 cj1 μ0 (α * K) μ0 hμ0 hαK hci1 hf11 hcj1
  have t2 : |ci1 * f12 * cj2| ≤ μ0 * K * μ0 :=
    abs_triple_mul_le ci1 f12 cj2 μ0 K μ0 hμ0 hK0 hci1 hf12 hcj2
  have t3 : |ci2 * f21 * cj1| ≤ μ0 * K * μ0 :=
    abs_triple_mul_le ci2 f21 cj1 μ0 K μ0 hμ0 hK0 hci2 hf21 hcj1
  have t4 : |ci2 * f22 * cj2| ≤ μ0 * (α * K) * μ0 :=
    abs_triple_mul_le ci2 f22 cj2 μ0 (α * K) μ0 hμ0 hαK hci2 hf22 hcj2
  have hexpand :
      ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2)
        = (ci1 * f11 * cj1) + (ci1 * f12 * cj2)
          + (ci2 * f21 * cj1) + (ci2 * f22 * cj2) := by ring
  have hcorr :
      |ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2)|
        ≤ 2 * μ0 ^ 2 * K * (1 + α) := by
    rw [hexpand]
    have htri :
        |(ci1 * f11 * cj1) + (ci1 * f12 * cj2)
            + (ci2 * f21 * cj1) + (ci2 * f22 * cj2)|
          ≤ |ci1 * f11 * cj1| + |ci1 * f12 * cj2|
            + |ci2 * f21 * cj1| + |ci2 * f22 * cj2| := by
      refine le_trans (abs_add_le _ _) ?_
      refine add_le_add (le_trans (abs_add_le _ _) ?_) (le_refl _)
      exact add_le_add (abs_add_le _ _) (le_refl _)
    have hsum : |ci1 * f11 * cj1| + |ci1 * f12 * cj2|
        + |ci2 * f21 * cj1| + |ci2 * f22 * cj2|
          ≤ 2 * μ0 ^ 2 * K * (1 + α) := by nlinarith [t1, t2, t3, t4]
    exact le_trans htri hsum
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have hid : 2 * μ0 ^ 2 * K * (1 + α) = 2 * μ0 / (1 - α) := by
    rw [eq_div_iff (ne_of_gt h1α)]
    nlinarith [hK]
  have hfinal :
      |b - (ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2))|
        ≤ μ0 + 2 * μ0 / (1 - α) := by
    have htri2 :
        |b - (ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2))|
          ≤ |b|
            + |ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2)| := by
      have h := abs_add_le b
        (-(ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2)))
      rwa [← sub_eq_add_neg, abs_neg] at h
    calc |b - (ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2))|
        ≤ |b|
          + |ci1 * (f11 * cj1 + f12 * cj2) + ci2 * (f21 * cj1 + f22 * cj2)| := htri2
      _ ≤ μ0 + 2 * μ0 ^ 2 * K * (1 + α) := add_le_add hb hcorr
      _ = μ0 + 2 * μ0 / (1 - α) := by rw [hid]
  have hrhs : (1 + 2 / (1 - α)) * μ0 = μ0 + 2 * μ0 / (1 - α) := by
    field_simp
  rw [hrhs]
  exact hfinal

/-- **Self-contained 2×2 complete-pivoting element growth** (Higham §11.1.1,
    eq. (11.4)).  Combining `twoByTwo_inverse_entry_bounds` with
    `twoByTwo_schur_growth`: the Schur entry formed with the *actual* inverse of
    the pivot block `E`, namely `E⁻¹ = d⁻¹[[e₂₂,−e₂₁],[−e₂₁,e₁₁]]`, is bounded by
    `(1 + 2/(1−α))·μ₀` using only the pivot-block data and the entry bound `μ₀` —
    no inverse-entry bounds are assumed. -/
theorem twoByTwo_schur_growth_of_block
    (b ci1 ci2 cj1 cj2 e11 e22 e21 μ0 μ1 α K : ℝ)
    (hμ1 : 0 ≤ μ1) (hα0 : 0 ≤ α) (hα1 : α < 1) (hμ : 0 < μ0)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0)
    (hK : (1 - α ^ 2) * μ0 * K = 1)
    (hb : |b| ≤ μ0)
    (hci1 : |ci1| ≤ μ0) (hci2 : |ci2| ≤ μ0)
    (hcj1 : |cj1| ≤ μ0) (hcj2 : |cj2| ≤ μ0) :
    |b - (ci1 * (e22 / (e11 * e22 - e21 ^ 2) * cj1
            + -(e21 / (e11 * e22 - e21 ^ 2)) * cj2)
          + ci2 * (-(e21 / (e11 * e22 - e21 ^ 2)) * cj1
            + e11 / (e11 * e22 - e21 ^ 2) * cj2))|
      ≤ (1 + 2 / (1 - α)) * μ0 := by
  obtain ⟨hInv22, hInv11, hInv21⟩ :=
    twoByTwo_inverse_entry_bounds e11 e22 e21 μ0 μ1 α K
      hμ1 hα0 hα1 hμ he11 he22 he21 hμ1α hK
  exact twoByTwo_schur_growth b ci1 ci2 cj1 cj2
    (e22 / (e11 * e22 - e21 ^ 2)) (-(e21 / (e11 * e22 - e21 ^ 2)))
    (-(e21 / (e11 * e22 - e21 ^ 2))) (e11 / (e11 * e22 - e21 ^ 2)) μ0 α K
    hα0 hα1 hμ hK hb hci1 hci2 hcj1 hcj2
    hInv22 (by rw [abs_neg]; exact hInv21) (by rw [abs_neg]; exact hInv21) hInv11

/-- **Abstract Bunch-Kaufman stability interface** (Higham §11.1.2).

    Same α = (1+√17)/8 as complete pivoting, but requires only
    O(n²) comparisons (searches at most two columns per stage).

    The growth factor is still bounded by (2.57)^{n−1},
    though no example is known where this bound is attained.

    The stability result for partial pivoting:
      ‖|L̂||D̂||L̂^T|‖_M ≤ 36n · ρ_n · ‖A‖_M

    The hypothesis `hstab` supplies the pivoting/stability analysis. -/
theorem bunch_kaufman_stability (n : ℕ)
    (A L_hat D_hat : Fin n → Fin n → ℝ)
    (ρ_n : ℝ)
    (maxNorm_A : ℝ) (_hmA : 0 ≤ maxNorm_A)
    -- Maximum entry norm bounds
    (_hA_norm : ∀ i j : Fin n, |A i j| ≤ maxNorm_A)
    -- The stability bound as hypothesis
    (hstab : ∀ i j : Fin n,
      ∑ k₁ : Fin n, ∑ k₂ : Fin n,
        |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂| ≤
      36 * ↑n * ρ_n * maxNorm_A) :
    ∀ i j : Fin n,
      ∑ k₁ : Fin n, ∑ k₂ : Fin n,
        |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂| ≤
      36 * ↑n * ρ_n * maxNorm_A :=
  hstab

/-- **Abstract Bunch-Kaufman solve backward-error interface**
    (Higham §11.1.2, Higham [559, 1995]).

    The computed solution to Ax = b via diagonal pivoting with
    partial pivoting satisfies:
      (A + ΔA) x̂ = b  with  |ΔA| ≤ p₂(n) · u · |L̂| · |D̂| · |L̂^T|

    where p₂ is a linear polynomial in n.  The hypothesis `hsolve` supplies
    the detailed solve analysis. -/
theorem bunch_kaufman_solve_backward_error (n : ℕ) (fp : FPModel)
    (A L_hat D_hat : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (b x_hat : Fin n → ℝ)
    (_hBLDLT : BlockLDLTBackwardError n A L_hat D_hat σ (gamma fp n))
    (ρ_n maxNorm_A : ℝ)
    -- Growth + stability bound
    (_hstab : ∀ i j : Fin n,
      ∑ k₁ : Fin n, ∑ k₂ : Fin n,
        |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂| ≤
      36 * ↑n * ρ_n * maxNorm_A)
    -- The solve backward error bound
    (hsolve : ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        gamma fp n * 36 * ↑n * ρ_n * maxNorm_A) ∧
      (∀ i, ∑ j : Fin n, (A (σ i) (σ j) + ΔA i j) *
        x_hat j = b (σ i))) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        gamma fp n * 36 * ↑n * ρ_n * maxNorm_A) ∧
      (∀ i, ∑ j : Fin n, (A (σ i) (σ j) + ΔA i j) *
        x_hat j = b (σ i)) :=
  hsolve

/-- **Floating-point backward error of one 1×1 Schur-complement update**
    (Higham §11.1, floating-point form of the block-LDLᵀ Schur step (11.3)).

    For a 1×1 pivot the diagonal-pivoting method updates a Schur entry by
    `s = fl(a − fl(fl(c₁/e)·c₂))` (multiplier, product, subtract — three rounded
    operations).  Under the standard model this computed value equals the exact
    Schur entry `a − c₁c₂/e` plus a genuine backward error `Δ` bounded by
    `γ₃·(|a| + |c₁c₂/e|)`.  The error is *derived* from the model laws via
    `prod_error_bound`, not assumed; it is the floating-point analogue of
    `oneByOne_schur_growth` and the atomic per-step ingredient of the
    Theorem 11.3 block-LDLᵀ backward-error bound. -/
theorem fl_oneByOne_schur_step_error (fp : FPModel) (a e c1 c2 : ℝ)
    (he : e ≠ 0) (hval : gammaValid fp 3) :
    ∃ Δ : ℝ,
      |Δ| ≤ gamma fp 3 * (|a| + |c1 * c2 / e|) ∧
      fp.fl_sub a (fp.fl_mul (fp.fl_div c1 e) c2) = (a - c1 * c2 / e) + Δ := by
  obtain ⟨δ1, hδ1, hm⟩ := fp.model_div c1 e he
  obtain ⟨δ2, hδ2, hp⟩ := fp.model_mul (fp.fl_div c1 e) c2
  obtain ⟨δ3, hδ3, hs⟩ := fp.model_sub a (fp.fl_mul (fp.fl_div c1 e) c2)
  obtain ⟨θ, hθ, hprod⟩ :=
    prod_error_bound fp 3 ![δ1, δ2, δ3]
      (by intro i; fin_cases i <;> simp_all) hval
  have hfactor : (1 + δ1) * (1 + δ2) * (1 + δ3) = 1 + θ := by
    have h := hprod
    rw [Fin.prod_univ_three] at h
    simpa using h
  have hs_eq : fp.fl_sub a (fp.fl_mul (fp.fl_div c1 e) c2)
      = a * (1 + δ3) - (c1 * c2 / e) * (1 + θ) := by
    rw [hs, hp, hm, ← hfactor]; ring
  refine ⟨a * δ3 - (c1 * c2 / e) * θ, ?_, ?_⟩
  · have hu3 : fp.u ≤ gamma fp 3 := u_le_gamma fp (by norm_num) hval
    have hγ0 : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
    have htri : |a * δ3 - (c1 * c2 / e) * θ| ≤ |a * δ3| + |(c1 * c2 / e) * θ| := by
      have h := abs_add_le (a * δ3) (-((c1 * c2 / e) * θ))
      rwa [← sub_eq_add_neg, abs_neg] at h
    have e1 : |a * δ3 - (c1 * c2 / e) * θ|
        ≤ |a| * fp.u + |c1 * c2 / e| * gamma fp 3 := by
      calc |a * δ3 - (c1 * c2 / e) * θ|
          ≤ |a * δ3| + |(c1 * c2 / e) * θ| := htri
        _ = |a| * |δ3| + |c1 * c2 / e| * |θ| := by rw [abs_mul, abs_mul]
        _ ≤ |a| * fp.u + |c1 * c2 / e| * gamma fp 3 :=
            add_le_add (mul_le_mul_of_nonneg_left hδ3 (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hθ (abs_nonneg _))
    have e2 : |a| * fp.u + |c1 * c2 / e| * gamma fp 3
        ≤ gamma fp 3 * (|a| + |c1 * c2 / e|) := by
      have hle : |a| * fp.u ≤ |a| * gamma fp 3 :=
        mul_le_mul_of_nonneg_left hu3 (abs_nonneg _)
      nlinarith [hle, abs_nonneg (c1 * c2 / e), hγ0]
    exact le_trans e1 e2
  · rw [hs_eq]; ring

/-- **Floating-point backward error of a 1×1 pivot solve** (Higham §11.1, the
    `s = 1` case of eq (11.5)).  The computed solution `x̂ = fl(b/e)` of the
    scalar system `e·x = b` satisfies `(e + Δe)·x̂ = b` with a backward error `Δe`
    in the pivot bounded by `γ₁·|e|` (constant `c = 1`, no `O(u²)` term).  Derived
    from the standard division model, not assumed; the 1×1 instance of the
    Theorem 11.3 solve-perturbation hypothesis (11.5). -/
theorem fl_oneByOne_solve_backward_error (fp : FPModel) (b e : ℝ)
    (he : e ≠ 0) (hval : gammaValid fp 1) :
    ∃ Δe : ℝ, |Δe| ≤ gamma fp 1 * |e| ∧ (e + Δe) * fp.fl_div b e = b := by
  obtain ⟨δ, hδ, hd⟩ := fp.model_div b e he
  have hu1 : fp.u < 1 := by
    have h := hval; unfold gammaValid at h; simpa using h
  have hδ1 : |δ| < 1 := lt_of_le_of_lt hδ hu1
  have hpos : 0 < 1 + δ := by
    have hlo : -1 < δ := (abs_lt.mp hδ1).1
    linarith
  have hg0 : 0 ≤ gamma fp 1 := gamma_nonneg fp hval
  have h1u : (1 : ℝ) - fp.u ≠ 0 := by linarith
  have hgeq : gamma fp 1 * (1 - fp.u) = fp.u := by
    unfold gamma; rw [Nat.cast_one, one_mul]; field_simp
  refine ⟨-e * δ / (1 + δ), ?_, ?_⟩
  · rw [abs_div, abs_mul, abs_neg, abs_of_pos hpos, div_le_iff₀ hpos]
    have key : |δ| ≤ gamma fp 1 * (1 + δ) := by
      have h1 : gamma fp 1 * (1 - fp.u) ≤ gamma fp 1 * (1 + δ) :=
        mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp hδ).1]) hg0
      calc |δ| ≤ fp.u := hδ
        _ = gamma fp 1 * (1 - fp.u) := hgeq.symm
        _ ≤ gamma fp 1 * (1 + δ) := h1
    calc |e| * |δ| ≤ |e| * (gamma fp 1 * (1 + δ)) :=
          mul_le_mul_of_nonneg_left key (abs_nonneg e)
      _ = gamma fp 1 * |e| * (1 + δ) := by ring
  · rw [hd]; field_simp; ring

/-- **Per-stage trailing floating-point backward error** for a 1×1-pivot block
    LDLᵀ step (Higham [608,1997] §4.2).  Combining the rounded multiplier product
    `l̂_i·e·l̂_j` (an entry of `L̂D̂L̂ᵀ` before the recursion) with the computed
    Schur entry `Ŝ = fl(b − fl(l̂_i·c_j))`, the total equals the original entry `b`
    plus a backward error `Δ` with `|Δ| ≤ 2·γ₃·(|b| + |c_i c_j/e|)`.  Derived from
    the standard model via `prod_error_bound`, not assumed — the atomic `(i,j)`
    ingredient of Theorem 11.3's componentwise backward-error induction. -/
theorem fl_oneByOne_stage_trailing_error (fp : FPModel) (e ci cj b : ℝ)
    (he : e ≠ 0) (hval : gammaValid fp 3) :
    ∃ Δ : ℝ, |Δ| ≤ 2 * gamma fp 3 * (|b| + |ci * cj / e|) ∧
      fp.fl_div ci e * e * fp.fl_div cj e
        + fp.fl_sub b (fp.fl_mul (fp.fl_div ci e) cj) = b + Δ := by
  obtain ⟨δi, hδi, hli⟩ := fp.model_div ci e he
  obtain ⟨δj, hδj, hlj⟩ := fp.model_div cj e he
  obtain ⟨δ1, hδ1, hpp⟩ := fp.model_mul (fp.fl_div ci e) cj
  obtain ⟨δ2, hδ2, hss⟩ := fp.model_sub b (fp.fl_mul (fp.fl_div ci e) cj)
  have hval2 : gammaValid fp 2 := gammaValid_mono fp (by norm_num) hval
  have hg2 : gamma fp 2 ≤ gamma fp 3 := gamma_mono fp (by norm_num) hval
  have hg0 : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
  obtain ⟨θa, hθa, hpa⟩ :=
    prod_error_bound fp 2 ![δi, δj] (by intro i; fin_cases i <;> simp_all) hval2
  have hfa : (1 + δi) * (1 + δj) = 1 + θa := by
    have h := hpa; rw [Fin.prod_univ_two] at h; simpa using h
  obtain ⟨θb, hθb, hpb⟩ :=
    prod_error_bound fp 3 ![δi, δ1, δ2] (by intro i; fin_cases i <;> simp_all) hval
  have hfb : (1 + δi) * (1 + δ1) * (1 + δ2) = 1 + θb := by
    have h := hpb; rw [Fin.prod_univ_three] at h; simpa using h
  have hab : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    have := abs_add_le x (-y); rwa [← sub_eq_add_neg, abs_neg] at this
  refine ⟨ci * cj / e * θa - ci * cj / e * θb + b * δ2, ?_, ?_⟩
  · have hθa3 : |θa| ≤ gamma fp 3 := le_trans hθa hg2
    have hu3 : fp.u ≤ gamma fp 3 := u_le_gamma fp (by norm_num) hval
    have hb2 : |b * δ2| ≤ |b| * gamma fp 3 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (le_trans hδ2 hu3) (abs_nonneg _)
    have hP : |ci * cj / e * θa| ≤ |ci * cj / e| * gamma fp 3 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hθa3 (abs_nonneg _)
    have hPb : |ci * cj / e * θb| ≤ |ci * cj / e| * gamma fp 3 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hθb (abs_nonneg _)
    calc |ci * cj / e * θa - ci * cj / e * θb + b * δ2|
        ≤ |ci * cj / e * θa - ci * cj / e * θb| + |b * δ2| := abs_add_le _ _
      _ ≤ (|ci * cj / e * θa| + |ci * cj / e * θb|) + |b * δ2| :=
          add_le_add (hab _ _) (le_refl _)
      _ ≤ (|ci * cj / e| * gamma fp 3 + |ci * cj / e| * gamma fp 3) + |b| * gamma fp 3 :=
          add_le_add (add_le_add hP hPb) hb2
      _ ≤ 2 * gamma fp 3 * (|b| + |ci * cj / e|) := by
          nlinarith [hg0, abs_nonneg b, abs_nonneg (ci * cj / e)]
  · have key : ci / e * (1 + δi) * e * (cj / e * (1 + δj))
        + (b - ci / e * (1 + δi) * cj * (1 + δ1)) * (1 + δ2)
        = b + (ci * cj / e * θa - ci * cj / e * θb + b * δ2) := by
      have e1 : ci / e * (1 + δi) * e * (cj / e * (1 + δj))
          = ci * cj / e * ((1 + δi) * (1 + δj)) := by field_simp
      have e2 : (b - ci / e * (1 + δi) * cj * (1 + δ1)) * (1 + δ2)
          = b * (1 + δ2) - ci * cj / e * ((1 + δi) * (1 + δ1) * (1 + δ2)) := by
        field_simp
      rw [e1, e2, hfa, hfb]; ring
    rw [hss, hpp, hli, hlj]; exact key

/-- **Trailing-block floating-point backward error of one 1×1-pivot stage**
    (Higham [608,1997] §4.2, the inductive step of Theorem 11.3).  With computed
    multipliers `l̂_i = fl(A i.succ 0 / A00)`, computed Schur entries
    `Ŝ i j = fl(A i.succ j.succ − fl(l̂_i · A 0 j.succ))`, and a recursive
    factorization `L_S,D_S` approximating `Ŝ` entrywise within `Bs` (`hIH`), the
    assembled `L̂,D̂` satisfy on the trailing block
    `|(L̂D̂L̂ᵀ)_{i+1,j+1} − A_{i+1,j+1}| ≤ 2γ₃(|A_{i+1,j+1}| + |A_{i+1,0}·A_{0,j+1}/A00|) + Bs i j`.
    Combines `fl_oneByOne_stage_trailing_error` with the recursion hypothesis. -/
theorem fl_blockLDLT_trailing_bound (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (he : A 0 0 ≠ 0) (hsym1 : ∀ i : Fin n, A 0 i.succ = A i.succ 0)
    (hval : gammaValid fp 3)
    (L_S D_S : Fin n → Fin n → ℝ) (Bs : Fin n → Fin n → ℝ)
    (hIH : ∀ i j : Fin n,
      |(∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂)
        - fp.fl_sub (A i.succ j.succ)
            (fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ))| ≤ Bs i j)
    (L D : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hLcol : ∀ i : Fin n, L i.succ 0 = fp.fl_div (A i.succ 0) (A 0 0))
    (hLtr : ∀ i j : Fin n, L i.succ j.succ = L_S i j)
    (hD00 : D 0 0 = A 0 0)
    (hD0s : ∀ j : Fin n, D 0 j.succ = 0)
    (hDs0 : ∀ i : Fin n, D i.succ 0 = 0)
    (hDtr : ∀ i j : Fin n, D i.succ j.succ = D_S i j) :
    ∀ i j : Fin n,
      |(∑ k₁, ∑ k₂, L i.succ k₁ * D k₁ k₂ * L j.succ k₂) - A i.succ j.succ|
        ≤ 2 * gamma fp 3 * (|A i.succ j.succ|
            + |A i.succ 0 * A 0 j.succ / A 0 0|) + Bs i j := by
  intro i j
  have hreduce : (∑ k₁, ∑ k₂, L i.succ k₁ * D k₁ k₂ * L j.succ k₂)
      = L i.succ 0 * (A 0 0) * L j.succ 0
        + (∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂) := by
    have inner : ∀ k₁ : Fin (n + 1),
        (∑ k₂, L i.succ k₁ * D k₁ k₂ * L j.succ k₂)
          = L i.succ k₁ * (∑ k₂, D k₁ k₂ * L j.succ k₂) := by
      intro k₁; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    rw [Fin.sum_univ_succ, inner 0]
    have c0 : (∑ k₂, D 0 k₂ * L j.succ k₂) = A 0 0 * L j.succ 0 := by
      rw [Fin.sum_univ_succ, hD00]
      have : (∑ k₂ : Fin n, D 0 k₂.succ * L j.succ k₂.succ) = 0 :=
        Finset.sum_eq_zero fun k _ => by rw [hD0s k, zero_mul]
      rw [this, add_zero]
    rw [c0]
    have csucc : (∑ k₁ : Fin n, ∑ k₂, L i.succ k₁.succ * D k₁.succ k₂ * L j.succ k₂)
        = ∑ k₁ : Fin n, ∑ k₂ : Fin n, L_S i k₁ * D_S k₁ k₂ * L_S j k₂ := by
      apply Finset.sum_congr rfl; intro k₁ _
      rw [inner k₁.succ, Fin.sum_univ_succ, hDs0 k₁, zero_mul, zero_add]
      rw [hLtr i k₁, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k₂ _
      rw [hDtr k₁ k₂, hLtr j k₂]; ring
    rw [csucc, hLcol i, hLcol j]; ring
  obtain ⟨Δ, hΔ, hstage⟩ :=
    fl_oneByOne_stage_trailing_error fp (A 0 0) (A i.succ 0) (A 0 j.succ)
      (A i.succ j.succ) he hval
  have hljeq : L j.succ 0 = fp.fl_div (A 0 j.succ) (A 0 0) := by
    rw [hLcol j, hsym1 j]
  set Ŝ := fp.fl_sub (A i.succ j.succ)
      (fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ)) with hŜ
  have hval2 : (∑ k₁, ∑ k₂, L i.succ k₁ * D k₁ k₂ * L j.succ k₂)
      = (fp.fl_div (A i.succ 0) (A 0 0) * A 0 0 * fp.fl_div (A 0 j.succ) (A 0 0) + Ŝ)
        + ((∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂) - Ŝ) := by
    rw [hreduce, hLcol i, hljeq]; ring
  rw [hval2, hstage]
  have hcancel : (A i.succ j.succ + Δ)
      + ((∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂) - Ŝ) - A i.succ j.succ
      = Δ + ((∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂) - Ŝ) := by ring
  rw [hcancel]
  calc |Δ + ((∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂) - Ŝ)|
      ≤ |Δ| + |(∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂) - Ŝ| := abs_add_le _ _
    _ ≤ 2 * gamma fp 3 * (|A i.succ j.succ| + |A i.succ 0 * A 0 j.succ / A 0 0|)
          + Bs i j := add_le_add hΔ (hIH i j)

/-- **Pivot row/column floating-point backward error of one 1×1-pivot stage.**
    The pivot entry is reproduced exactly, `(L̂D̂L̂ᵀ)_{0,0} = A 0 0`, and each
    pivot-row entry has a tiny backward error `(L̂D̂L̂ᵀ)_{0,j+1} = A 0 j.succ + Δ`
    with `|Δ| ≤ u·|A 0 j.succ|`.  Together with `fl_blockLDLT_trailing_bound` this
    is the complete 1×1-stage assemble step of Theorem 11.3's backward error. -/
theorem fl_blockLDLT_pivot_row_bound (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (he : A 0 0 ≠ 0) (hsym1 : ∀ i : Fin n, A 0 i.succ = A i.succ 0)
    (L D : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hL00 : L 0 0 = 1)
    (hLcol : ∀ i : Fin n, L i.succ 0 = fp.fl_div (A i.succ 0) (A 0 0))
    (hL0s : ∀ j : Fin n, L 0 j.succ = 0)
    (hD00 : D 0 0 = A 0 0)
    (hD0s : ∀ j : Fin n, D 0 j.succ = 0) :
    (∑ k₁, ∑ k₂, L 0 k₁ * D k₁ k₂ * L 0 k₂) = A 0 0
    ∧ ∀ j : Fin n,
        |(∑ k₁, ∑ k₂, L 0 k₁ * D k₁ k₂ * L j.succ k₂) - A 0 j.succ|
          ≤ fp.u * |A 0 j.succ| := by
  have row0 : ∀ (X : Fin (n + 1)),
      (∑ k₁, ∑ k₂, L 0 k₁ * D k₁ k₂ * L X k₂) = ∑ k₂, D 0 k₂ * L X k₂ := by
    intro X
    rw [Fin.sum_univ_succ]
    have hz : (∑ k₁ : Fin n, ∑ k₂, L 0 k₁.succ * D k₁.succ k₂ * L X k₂) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        simp only [hL0s k]
        exact Finset.sum_eq_zero fun k₂ _ => by ring
    rw [hz, add_zero, hL00]
    apply Finset.sum_congr rfl; intro k₂ _; ring
  have colpick : ∀ (X : Fin (n + 1)), (∑ k₂, D 0 k₂ * L X k₂) = A 0 0 * L X 0 := by
    intro X; rw [Fin.sum_univ_succ, hD00]
    have : (∑ k₂ : Fin n, D 0 k₂.succ * L X k₂.succ) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hD0s k, zero_mul]
    rw [this, add_zero]
  constructor
  · rw [row0 0, colpick 0, hL00, mul_one]
  · intro j
    rw [row0 j.succ, colpick j.succ, hLcol j, hsym1 j]
    obtain ⟨δ, hδ, hd⟩ := fp.model_div (A j.succ 0) (A 0 0) he
    rw [hd]
    have hrw : A 0 0 * (A j.succ 0 / A 0 0 * (1 + δ)) - A j.succ 0
        = A j.succ 0 * δ := by field_simp; ring
    rw [hrw, abs_mul]
    exact (mul_le_mul_of_nonneg_left hδ (abs_nonneg _)).trans_eq (by rw [mul_comm])

/-- **Pivot-column floating-point backward error of one 1×1-pivot stage.**
    `(L̂D̂L̂ᵀ)_{i+1,0} = l̂_i·A00 = A_{i+1,0}(1+δ)`, so
    `|(L̂D̂L̂ᵀ)_{i+1,0} − A_{i+1,0}| ≤ u·|A_{i+1,0}|` — the pivot-column companion of
    `fl_blockLDLT_pivot_row_bound`, completing all four index cases of the
    single 1×1-pivot floating-point assemble step. -/
theorem fl_blockLDLT_pivot_col_bound (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (he : A 0 0 ≠ 0)
    (L D : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hL00 : L 0 0 = 1)
    (hLcol : ∀ i : Fin n, L i.succ 0 = fp.fl_div (A i.succ 0) (A 0 0))
    (hL0s : ∀ j : Fin n, L 0 j.succ = 0)
    (hD00 : D 0 0 = A 0 0)
    (hDs0 : ∀ i : Fin n, D i.succ 0 = 0) :
    ∀ i : Fin n,
      |(∑ k₁, ∑ k₂, L i.succ k₁ * D k₁ k₂ * L 0 k₂) - A i.succ 0|
        ≤ fp.u * |A i.succ 0| := by
  intro i
  have colred : (∑ k₁, ∑ k₂, L i.succ k₁ * D k₁ k₂ * L 0 k₂)
      = ∑ k₁, L i.succ k₁ * D k₁ 0 := by
    apply Finset.sum_congr rfl; intro k₁ _
    rw [Fin.sum_univ_succ, hL00, mul_one]
    have : (∑ k₂ : Fin n, L i.succ k₁ * D k₁ k₂.succ * L 0 k₂.succ) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hL0s k, mul_zero]
    rw [this, add_zero]
  rw [colred, Fin.sum_univ_succ, hD00]
  have : (∑ k₁ : Fin n, L i.succ k₁.succ * D k₁.succ 0) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hDs0 k, mul_zero]
  rw [this, add_zero, hLcol i]
  obtain ⟨δ, hδ, hd⟩ := fp.model_div (A i.succ 0) (A 0 0) he
  rw [hd]
  have hrw : A i.succ 0 / A 0 0 * (1 + δ) * A 0 0 - A i.succ 0 = A i.succ 0 * δ := by
    field_simp; ring
  rw [hrw, abs_mul]
  exact (mul_le_mul_of_nonneg_left hδ (abs_nonneg _)).trans_eq (by rw [mul_comm])

/-- Entrywise one-stage backward-error envelope for a rounded 1×1-pivot
    block-LDLᵀ assemble step.  The leading pivot has exact error `0`; the pivot
    row/column have the 1×1 solve error `u|A|`; and the trailing block has the
    per-stage Schur error plus the recursive trailing envelope `Bs`. -/
noncomputable def flBlockLDLTOneByOneStageBound (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (Bs : Fin n → Fin n → ℝ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun I J =>
    Fin.cases
      (Fin.cases 0 (fun j => fp.u * |A 0 j.succ|) J)
      (fun i =>
        Fin.cases
          (fp.u * |A i.succ 0|)
          (fun j =>
            2 * gamma fp 3 *
              (|A i.succ j.succ| + |A i.succ 0 * A 0 j.succ / A 0 0|)
              + Bs i j)
          J)
      I

/-- **Complete one-stage 1×1-pivot floating-point assemble bound** for
    Theorem 11.3.  This packages the pivot entry, pivot row, pivot column, and
    trailing-block estimates into a single all-index statement:
    `|(L̂D̂L̂ᵀ) I J - A I J|` is bounded by
    `flBlockLDLTOneByOneStageBound`.  The trailing recursive hypothesis is still
    explicit; the full multi-stage induction remains a separate theorem. -/
theorem fl_blockLDLT_oneByOne_stage_bound (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (he : A 0 0 ≠ 0) (hsym1 : ∀ i : Fin n, A 0 i.succ = A i.succ 0)
    (hval : gammaValid fp 3)
    (L_S D_S : Fin n → Fin n → ℝ) (Bs : Fin n → Fin n → ℝ)
    (hIH : ∀ i j : Fin n,
      |(∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂)
        - fp.fl_sub (A i.succ j.succ)
            (fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ))| ≤ Bs i j)
    (L D : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hL00 : L 0 0 = 1)
    (hLcol : ∀ i : Fin n, L i.succ 0 = fp.fl_div (A i.succ 0) (A 0 0))
    (hL0s : ∀ j : Fin n, L 0 j.succ = 0)
    (hLtr : ∀ i j : Fin n, L i.succ j.succ = L_S i j)
    (hD00 : D 0 0 = A 0 0)
    (hD0s : ∀ j : Fin n, D 0 j.succ = 0)
    (hDs0 : ∀ i : Fin n, D i.succ 0 = 0)
    (hDtr : ∀ i j : Fin n, D i.succ j.succ = D_S i j) :
    ∀ I J : Fin (n + 1),
      |(∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) - A I J|
        ≤ flBlockLDLTOneByOneStageBound n fp A Bs I J := by
  obtain ⟨h00, hrow⟩ :=
    fl_blockLDLT_pivot_row_bound n fp A he hsym1 L D
      hL00 hLcol hL0s hD00 hD0s
  have hcol :=
    fl_blockLDLT_pivot_col_bound n fp A he L D
      hL00 hLcol hL0s hD00 hDs0
  have htrail :=
    fl_blockLDLT_trailing_bound n fp A he hsym1 hval L_S D_S Bs hIH L D
      hLcol hLtr hD00 hD0s hDs0 hDtr
  intro I J
  rcases Fin.eq_zero_or_eq_succ I with hI | ⟨i, hI⟩
  · subst I
    rcases Fin.eq_zero_or_eq_succ J with hJ | ⟨j, hJ⟩
    · subst J
      simp [flBlockLDLTOneByOneStageBound, h00]
    · subst J
      simpa [flBlockLDLTOneByOneStageBound] using hrow j
  · subst I
    rcases Fin.eq_zero_or_eq_succ J with hJ | ⟨j, hJ⟩
    · subst J
      simpa [flBlockLDLTOneByOneStageBound] using hcol i
    · subst J
      simpa [flBlockLDLTOneByOneStageBound] using htrail i j

/-- Rounded Schur complement produced by one computed 1×1-pivot block-LDLᵀ
    elimination step.  This is the recursive matrix consumed by the floating
    all-1×1 path of Theorem 11.3. -/
noncomputable def flSchurCompl (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    fp.fl_sub (A i.succ j.succ)
      (fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ))

/-- Stored-symmetric rounded Schur complement for the 1×1-pivot path.  The
    upper triangle is computed by `flSchurCompl`; lower-triangular entries are
    copied from the opposite upper-triangular entry, matching the usual
    symmetric-storage implementation convention. -/
noncomputable def flStoredSymSchurCompl (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    if i.val ≤ j.val then flSchurCompl n fp A i j else flSchurCompl n fp A j i

/-- The stored-symmetric rounded Schur complement is symmetric by construction. -/
theorem flStoredSymSchurCompl_symm (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    ∀ i j : Fin n, flStoredSymSchurCompl n fp A i j =
      flStoredSymSchurCompl n fp A j i := by
  intro i j
  classical
  unfold flStoredSymSchurCompl
  by_cases hij : i.val ≤ j.val
  · by_cases hji : j.val ≤ i.val
    · have hval : i.val = j.val := Nat.le_antisymm hij hji
      have hfin : i = j := Fin.ext hval
      subst j
      simp
    · simp [hij, hji]
  · have hji : j.val ≤ i.val := (Nat.le_total j.val i.val).resolve_right hij
    simp [hij, hji]

/-- First-row/first-column equality supplied by the stored-symmetric rounded
    Schur complement when the stored trailing matrix is nonempty. -/
theorem flStoredSymSchurCompl_first_row_col (n : ℕ) (fp : FPModel)
    (A : Fin (n + 2) → Fin (n + 2) → ℝ) :
    ∀ i : Fin n, flStoredSymSchurCompl (n + 1) fp A 0 i.succ =
      flStoredSymSchurCompl (n + 1) fp A i.succ 0 := by
  intro i
  exact flStoredSymSchurCompl_symm (n + 1) fp A 0 i.succ

/-- Entrywise difference between the stored-symmetric rounded Schur complement
    and the raw rounded Schur update.  This is zero on the computed triangle and
    records the explicit storage-copy discrepancy on the opposite triangle. -/
noncomputable def flStoredSymSchurDefect (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => |flStoredSymSchurCompl n fp A i j - flSchurCompl n fp A i j|

/-- One-stage floating block-LDLᵀ bound when the recursive trailing factors
    approximate the stored-symmetric Schur complement.  The existing raw-Schur
    one-stage theorem applies with the stored trailing envelope plus the explicit
    storage defect `flStoredSymSchurDefect`. -/
theorem fl_blockLDLT_oneByOne_stage_bound_of_stored_schur (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (he : A 0 0 ≠ 0) (hsym1 : ∀ i : Fin n, A 0 i.succ = A i.succ 0)
    (hval : gammaValid fp 3)
    (L_S D_S B : Fin n → Fin n → ℝ)
    (hIH : ∀ i j : Fin n,
      |(∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂)
        - flStoredSymSchurCompl n fp A i j| ≤ B i j)
    (L D : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hL00 : L 0 0 = 1)
    (hLcol : ∀ i : Fin n, L i.succ 0 = fp.fl_div (A i.succ 0) (A 0 0))
    (hL0s : ∀ j : Fin n, L 0 j.succ = 0)
    (hLtr : ∀ i j : Fin n, L i.succ j.succ = L_S i j)
    (hD00 : D 0 0 = A 0 0)
    (hD0s : ∀ j : Fin n, D 0 j.succ = 0)
    (hDs0 : ∀ i : Fin n, D i.succ 0 = 0)
    (hDtr : ∀ i j : Fin n, D i.succ j.succ = D_S i j) :
    ∀ I J : Fin (n + 1),
      |(∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) - A I J|
        ≤ flBlockLDLTOneByOneStageBound n fp A
          (fun i j => B i j + flStoredSymSchurDefect n fp A i j) I J := by
  apply fl_blockLDLT_oneByOne_stage_bound n fp A he hsym1 hval L_S D_S
    (fun i j => B i j + flStoredSymSchurDefect n fp A i j)
  · intro i j
    set P := (∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂)
    set S := flStoredSymSchurCompl n fp A i j
    set R := flSchurCompl n fp A i j
    have htri : |P - R| ≤ |P - S| + |S - R| := by
      have hdecomp : P - R = (P - S) + (S - R) := by ring
      rw [hdecomp]
      exact abs_add_le _ _
    have hbound : |P - R| ≤ B i j + flStoredSymSchurDefect n fp A i j := by
      calc |P - R| ≤ |P - S| + |S - R| := htri
        _ ≤ B i j + flStoredSymSchurDefect n fp A i j := by
          apply add_le_add
          · simpa [P, S] using hIH i j
          · simp [flStoredSymSchurDefect, S, R]
    simpa [P, R, flSchurCompl] using hbound
  · exact hL00
  · exact hLcol
  · exact hL0s
  · exact hLtr
  · exact hD00
  · exact hD0s
  · exact hDs0
  · exact hDtr

/-- Recursive nonzero-pivot condition for the stored-symmetric all-1×1
    floating block-LDLᵀ path.  Each recursive trailing matrix is the
    stored-symmetric rounded Schur complement. -/
noncomputable def FlStoredAllOnePivots (fp : FPModel) :
    (n : ℕ) → (Fin n → Fin n → ℝ) → Prop
  | 0, _ => True
  | n + 1, A =>
      A 0 0 ≠ 0 ∧ FlStoredAllOnePivots fp n (flStoredSymSchurCompl n fp A)

/-- Recursive entrywise envelope for the stored-symmetric all-1×1 floating
    block-LDLᵀ path.  The trailing envelope is the recursive stored envelope plus
    the explicit stored-vs-raw Schur defect for the current stage. -/
noncomputable def flBlockLDLTStoredAllOneByOneBound (fp : FPModel) :
    (n : ℕ) → (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | 0, _ => fun I _ => Fin.elim0 I
  | n + 1, A =>
      flBlockLDLTOneByOneStageBound n fp A
        (fun i j =>
          flBlockLDLTStoredAllOneByOneBound fp n
              (flStoredSymSchurCompl n fp A) i j
            + flStoredSymSchurDefect n fp A i j)

/-- **Recursive stored-symmetric all-1×1 floating block-LDLᵀ bound**.  For a
    symmetric input whose stored-symmetric rounded Schur path has nonzero
    successive pivots, recursively constructed factors `L̂,D̂` approximate `A`
    entrywise within `flBlockLDLTStoredAllOneByOneBound`.  This discharges the
    per-stage symmetry side condition by storing each Schur complement
    symmetrically, while accounting for the stored-vs-raw Schur defect. -/
theorem fl_blockLDLT_stored_all_oneByOne_bound (fp : FPModel)
    (hval : gammaValid fp 3) :
    ∀ (n : ℕ) (A : Fin n → Fin n → ℝ),
      (∀ i j, A i j = A j i) →
      FlStoredAllOnePivots fp n A →
      ∃ L D : Fin n → Fin n → ℝ,
        ∀ I J,
          |(∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) - A I J|
            ≤ flBlockLDLTStoredAllOneByOneBound fp n A I J := by
  intro n
  induction n with
  | zero =>
      intro A _hsym _hp
      refine ⟨A, A, ?_⟩
      intro I
      exact Fin.elim0 I
  | succ n ih =>
      intro A hsym hp
      obtain ⟨ha, hpS⟩ := hp
      obtain ⟨L_S, D_S, hprodS⟩ :=
        ih (flStoredSymSchurCompl n fp A) (flStoredSymSchurCompl_symm n fp A) hpS
      refine ⟨fun I J => Fin.cases (Fin.cases 1 (fun _ => 0) J)
                (fun i => Fin.cases (fp.fl_div (A i.succ 0) (A 0 0))
                  (fun j => L_S i j) J) I,
              fun I J => Fin.cases (Fin.cases (A 0 0) (fun _ => 0) J)
                (fun i => Fin.cases 0 (fun j => D_S i j) J) I, ?_⟩
      apply fl_blockLDLT_oneByOne_stage_bound_of_stored_schur n fp A ha
        (fun i => hsym 0 i.succ) hval L_S D_S
        (flBlockLDLTStoredAllOneByOneBound fp n (flStoredSymSchurCompl n fp A))
      · exact hprodS
      · simp
      · intro i; simp
      · intro j; simp
      · intro i j; simp
      · simp
      · intro j; simp
      · intro i; simp
      · intro i j; simp

/-- Recursive rounded-pivot side condition for the all-1×1 floating block-LDLᵀ
    path.  At each rounded Schur-complement stage the pivot is nonzero and the
    active first row agrees with the active first column, which is exactly the
    symmetry side condition required by the one-stage floating assemble bound. -/
noncomputable def FlAllOneSymmetricPivots (fp : FPModel) :
    (n : ℕ) → (Fin n → Fin n → ℝ) → Prop
  | 0, _ => True
  | n + 1, A =>
      A 0 0 ≠ 0 ∧
      (∀ i : Fin n, A 0 i.succ = A i.succ 0) ∧
      FlAllOneSymmetricPivots fp n (flSchurCompl n fp A)

/-- Recursive entrywise backward-error envelope for the rounded all-1×1-pivot
    block-LDLᵀ path.  Each stage wraps the recursive trailing envelope in
    `flBlockLDLTOneByOneStageBound`. -/
noncomputable def flBlockLDLTAllOneByOneBound (fp : FPModel) :
    (n : ℕ) → (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | 0, _ => fun I _ => Fin.elim0 I
  | n + 1, A =>
      flBlockLDLTOneByOneStageBound n fp A
        (flBlockLDLTAllOneByOneBound fp n (flSchurCompl n fp A))

/-- **Recursive all-1×1-pivot floating-point block-LDLᵀ bound** for Theorem
    11.3's `s = 1` path.  If every rounded Schur-complement stage has a nonzero
    pivot and satisfies the first-row/first-column symmetry needed by the local
    assemble theorem, then recursively constructed factors `L̂,D̂` satisfy the
    entrywise envelope `flBlockLDLTAllOneByOneBound`. -/
theorem fl_blockLDLT_all_oneByOne_bound (fp : FPModel) (hval : gammaValid fp 3) :
    ∀ (n : ℕ) (A : Fin n → Fin n → ℝ),
      FlAllOneSymmetricPivots fp n A →
      ∃ L D : Fin n → Fin n → ℝ,
        ∀ I J,
          |(∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) - A I J|
            ≤ flBlockLDLTAllOneByOneBound fp n A I J := by
  intro n
  induction n with
  | zero =>
      intro A _hp
      refine ⟨A, A, ?_⟩
      intro I
      exact Fin.elim0 I
  | succ n ih =>
      intro A hp
      obtain ⟨ha, hsym1, hpS⟩ := hp
      obtain ⟨L_S, D_S, hprodS⟩ := ih (flSchurCompl n fp A) hpS
      refine ⟨fun I J => Fin.cases (Fin.cases 1 (fun _ => 0) J)
                (fun i => Fin.cases (fp.fl_div (A i.succ 0) (A 0 0))
                  (fun j => L_S i j) J) I,
              fun I J => Fin.cases (Fin.cases (A 0 0) (fun _ => 0) J)
                (fun i => Fin.cases 0 (fun j => D_S i j) J) I, ?_⟩
      apply fl_blockLDLT_oneByOne_stage_bound n fp A ha hsym1 hval L_S D_S
        (flBlockLDLTAllOneByOneBound fp n (flSchurCompl n fp A))
      · intro i j
        simpa [flSchurCompl] using hprodS i j
      · simp
      · intro i; simp
      · intro j; simp
      · intro i j; simp
      · simp
      · intro j; simp
      · intro i; simp
      · intro i j; simp

end NumStability
