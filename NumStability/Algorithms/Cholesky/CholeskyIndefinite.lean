-- Algorithms/Cholesky/CholeskyIndefinite.lean
--
-- Chapter 11: Symmetric indefinite and skew-symmetric systems.
--
-- Block LDL^T factorization: PAPT = LDLT where L is unit lower triangular
-- and D is block diagonal with 1×1 or 2×2 blocks.
--
-- Pivoting strategies:
-- - Complete pivoting (Bunch-Parlett): α = (1+√17)/8, growth ≤ (2.57)^{n-1}
-- - Partial pivoting (Bunch-Kaufman): same α, O(n²) comparisons

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Algorithms.LU.GaussianElimination

namespace NumStability

open scoped BigOperators

-- ============================================================
-- Chapter 11  Source predicates and block diagonal structure
-- ============================================================

/-- A symmetric tridiagonal matrix predicate, used by Aasen's method and by the
    symmetric-tridiagonal specialization of block LDL^T. -/
def IsSymTridiagonal (n : ℕ) (T : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, T i j = T j i) ∧
  (∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → T i j = 0)

/-- A real skew-symmetric matrix predicate, `A^T = -A`. -/
def IsSkewSymmetric (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, A i j = -A j i

/-- A skew-symmetric matrix has zero diagonal. -/
theorem skewSymmetric_diag_zero (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hA : IsSkewSymmetric n A) :
    ∀ i : Fin n, A i i = 0 := by
  intro i
  have h := hA i i
  linarith

/-- **Block diagonal predicate** for the D factor in block LDL^T.

    D is block diagonal with blocks of size 1 or 2.
    Entries D_{ij} = 0 whenever i and j are not in the same block.

    We model this by requiring: for |i - j| > 1, D_{ij} = 0;
    and D is symmetric. The block structure means each 2×2 block
    [d_{k,k}  d_{k,k+1}; d_{k+1,k}  d_{k+1,k+1}] is nonsingular. -/
def IsBlockDiag (n : ℕ) (D : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, D i j = D j i) ∧
  (∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → D i j = 0)

/-- Skew block diagonal structure for Chapter 11, equation (11.16): diagonal
    blocks are zero `1x1` blocks or skew `2x2` blocks. -/
def IsSkewBlockDiag (n : ℕ) (D : Fin n → Fin n → ℝ) : Prop :=
  IsSkewSymmetric n D ∧
  (∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → D i j = 0)

-- ============================================================
-- Chapter 11  Block LDL^T and Aasen specifications
-- ============================================================

/-- **Block LDL^T factorization** (Higham Chapter 11).

    For a symmetric matrix A, the diagonal pivoting method computes:
      P A P^T = L D L^T

    where P is a permutation, L is unit lower triangular, and D is
    block diagonal with 1×1 or 2×2 diagonal blocks.

    The 2×2 blocks arise when a 1×1 pivot would be too small
    (potentially causing instability). Each 2×2 block is nonsingular. -/
structure BlockLDLTSpec (n : ℕ) (A L D : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L is unit lower triangular: diagonal entries are 1. -/
  L_diag : ∀ i : Fin n, L i i = 1
  /-- L is lower triangular: entries above diagonal are 0. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  /-- D is block diagonal with 1×1 or 2×2 blocks. -/
  D_block_diag : IsBlockDiag n D
  /-- P A P^T = L D L^T: the product recovers the permuted matrix. -/
  product_eq : ∀ i j : Fin n,
    ∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * D k₁ k₂ * L j k₂ = A (σ i) (σ j)

/-- **Aasen factorization** source specification:
`P A P^T = L T L^T`, with `L` unit lower triangular, first column `e_1`,
and `T` symmetric tridiagonal. -/
structure AasenSpec (n : ℕ) (A L T : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L i i = 1
  /-- L is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  /-- The first column of L is the first coordinate vector. -/
  L_first_col : ∀ i j : Fin n, j.val = 0 → i.val ≠ 0 → L i j = 0
  /-- T is symmetric tridiagonal. -/
  T_tridiag : IsSymTridiagonal n T
  /-- P A P^T = L T L^T. -/
  product_eq : ∀ i j : Fin n,
    ∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * T k₁ k₂ * L j k₂ = A (σ i) (σ j)

/-- Skew-symmetric block LDL^T factorization source specification for
Chapter 11, equation (11.16). -/
structure SkewBlockLDLTSpec (n : ℕ) (A L D : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) : Prop where
  /-- The input is skew-symmetric. -/
  skew_A : IsSkewSymmetric n A
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L i i = 1
  /-- L is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  /-- D is skew block diagonal. -/
  D_skew_block_diag : IsSkewBlockDiag n D
  /-- P A P^T = L D L^T. -/
  product_eq : ∀ i j : Fin n,
    ∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * D k₁ k₂ * L j k₂ = A (σ i) (σ j)

/-- **Block LDL^T backward error** (Higham Chapter 11).

    The computed factors satisfy:
      |L̂ D̂ L̂^T − PAP^T| ≤ ε · |L̂| · |D̂| · |L̂^T|  componentwise -/
structure BlockLDLTBackwardError (n : ℕ) (A L_hat D_hat : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (ε : ℝ) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L̂ is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L_hat i i = 1
  /-- L̂ is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0
  /-- D̂ is block diagonal. -/
  D_block_diag : IsBlockDiag n D_hat
  /-- Componentwise backward error. -/
  backward_bound : ∀ i j : Fin n,
    |∑ k₁ : Fin n, ∑ k₂ : Fin n, L_hat i k₁ * D_hat k₁ k₂ * L_hat j k₂ -
      A (σ i) (σ j)| ≤
    ε * ∑ k₁ : Fin n, ∑ k₂ : Fin n, |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂|

/-- Pivot block size used by Chapter 11 algorithms. -/
inductive PivotSize where
  | one
  | two
  deriving DecidableEq, Repr

/-- Algorithm 11.1 source decision predicate for the first Bunch-Parlett
complete-pivoting step, expressed in terms of the printed scalar quantities
`mu0` and `mu1`. -/
def BunchParlettCompletePivotChoice (α μ0 μ1 : ℝ) (s : PivotSize) : Prop :=
  match s with
  | PivotSize.one => μ1 ≥ α * μ0
  | PivotSize.two => μ1 < α * μ0

/-- Branch labels for Algorithm 11.2. -/
inductive BunchKaufmanCase where
  | noAction
  | case1
  | case2
  | case3
  | case4
  deriving DecidableEq, Repr

/-- Algorithm 11.2 source decision predicate for the Bunch-Kaufman partial
pivoting tests at the first stage. -/
def BunchKaufmanPartialPivotCase
    (α a11 arr ω1 ωr : ℝ) (branch : BunchKaufmanCase) : Prop :=
  match branch with
  | BunchKaufmanCase.noAction => ω1 = 0
  | BunchKaufmanCase.case1 => ω1 ≠ 0 ∧ |a11| ≥ α * ω1
  | BunchKaufmanCase.case2 =>
      ω1 ≠ 0 ∧ |a11| < α * ω1 ∧ |a11| * ωr ≥ α * ω1 ^ 2
  | BunchKaufmanCase.case3 =>
      ω1 ≠ 0 ∧ |a11| < α * ω1 ∧ |a11| * ωr < α * ω1 ^ 2 ∧
        |arr| ≥ α * ωr
  | BunchKaufmanCase.case4 =>
      ω1 ≠ 0 ∧ |a11| < α * ω1 ∧ |a11| * ωr < α * ω1 ^ 2 ∧
        |arr| < α * ωr

/-- Algorithm 11.5 source predicate for a successful symmetric rook-pivot
first-stage decision.  The loop and search path are not modeled here; this
records the printed local tests that certify the returned pivot size. -/
def SymmetricRookFirstPivotChoice
    (α a11 arr ω1 ωr : ℝ) (s : PivotSize) : Prop :=
  (|a11| ≥ α * ω1 ∧ s = PivotSize.one) ∨
  (|arr| ≥ α * ωr ∧ s = PivotSize.one) ∨
  (ω1 = ωr ∧ s = PivotSize.two)

-- ============================================================
-- Chapter 11.1.1  Complete pivoting (Bunch-Parlett)
-- ============================================================

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

-- ============================================================
-- Chapter 11.1.2  Partial pivoting (Bunch-Kaufman)
-- ============================================================

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

-- ============================================================
-- Chapter 11.1.4  Tridiagonal symmetric matrices
-- ============================================================

/-- Bunch's symmetric-tridiagonal pivoting parameter from Algorithm 11.6,
`alpha = (sqrt 5 - 1)/2`. -/
noncomputable def bunchTridiagonalAlpha : ℝ := (Real.sqrt 5 - 1) / 2

/-- The tridiagonal pivoting parameter satisfies `alpha^2 + alpha - 1 = 0`. -/
theorem bunch_tridiagonal_alpha_root :
    bunchTridiagonalAlpha ^ 2 + bunchTridiagonalAlpha - 1 = 0 := by
  unfold bunchTridiagonalAlpha
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  field_simp
  nlinarith [h5]

/-- Bunch's symmetric-tridiagonal pivoting parameter is strictly positive. -/
theorem bunch_tridiagonal_alpha_pos : 0 < bunchTridiagonalAlpha := by
  unfold bunchTridiagonalAlpha
  have h : (1 : ℝ) < Real.sqrt 5 :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by norm_num)
  linarith

/-- Bunch's symmetric-tridiagonal pivoting parameter is less than one. -/
theorem bunch_tridiagonal_alpha_lt_one : bunchTridiagonalAlpha < 1 := by
  unfold bunchTridiagonalAlpha
  have h : Real.sqrt 5 < 3 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- From the root identity, `α² = 1 - α` for Bunch's tridiagonal parameter. -/
theorem bunch_tridiagonal_alpha_sq :
    bunchTridiagonalAlpha ^ 2 = 1 - bunchTridiagonalAlpha := by
  nlinarith [bunch_tridiagonal_alpha_root]

/-- Algorithm 11.6 source decision predicate for Bunch's tridiagonal pivot-size
strategy. -/
def BunchTridiagonalPivotChoice
    (σ a11 a21 : ℝ) (s : PivotSize) : Prop :=
  (σ * |a11| ≥ bunchTridiagonalAlpha * a21 ^ 2 ∧ s = PivotSize.one) ∨
  (σ * |a11| < bunchTridiagonalAlpha * a21 ^ 2 ∧ s = PivotSize.two)

/-- The one-by-one branch of Algorithm 11.6 exposes the printed threshold
inequality. -/
theorem bunch_tridiagonal_pivot_choice_one_threshold (σ a11 a21 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.one) :
    σ * |a11| ≥ bunchTridiagonalAlpha * a21 ^ 2 := by
  rcases hchoice with hchoice | hchoice
  · exact hchoice.1
  · cases hchoice.2

/-- The two-by-two branch of Algorithm 11.6 exposes the strict printed
threshold inequality. -/
theorem bunch_tridiagonal_pivot_choice_two_threshold (σ a11 a21 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two) :
    σ * |a11| < bunchTridiagonalAlpha * a21 ^ 2 := by
  rcases hchoice with hchoice | hchoice
  · cases hchoice.2
  · exact hchoice.1

/-- The printed non-strict threshold certifies the one-by-one branch of
Algorithm 11.6. -/
theorem bunch_tridiagonal_pivot_choice_one_of_threshold (σ a11 a21 : ℝ)
    (hthreshold : σ * |a11| ≥ bunchTridiagonalAlpha * a21 ^ 2) :
    BunchTridiagonalPivotChoice σ a11 a21 PivotSize.one :=
  Or.inl ⟨hthreshold, rfl⟩

/-- The printed strict threshold certifies the two-by-two branch of
Algorithm 11.6. -/
theorem bunch_tridiagonal_pivot_choice_two_of_threshold (σ a11 a21 : ℝ)
    (hthreshold : σ * |a11| < bunchTridiagonalAlpha * a21 ^ 2) :
    BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two :=
  Or.inr ⟨hthreshold, rfl⟩

/-- In the one-by-one branch, a nonzero adjacent offdiagonal entry forces the
accepted scalar pivot to be nonzero.  This is the local nonsingularity fact used
when the tridiagonal factorization step divides by `a11`. -/
theorem bunch_tridiagonal_pivot_choice_one_a11_ne_zero_of_a21_ne_zero
    (σ a11 a21 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.one)
    (ha21 : a21 ≠ 0) :
    a11 ≠ 0 := by
  have hthreshold :=
    bunch_tridiagonal_pivot_choice_one_threshold σ a11 a21 hchoice
  have hsquare : 0 < a21 ^ 2 := sq_pos_of_ne_zero ha21
  have hright_pos : 0 < bunchTridiagonalAlpha * a21 ^ 2 :=
    mul_pos bunch_tridiagonal_alpha_pos hsquare
  have hleft_pos : 0 < σ * |a11| := lt_of_lt_of_le hright_pos hthreshold
  intro ha11
  rw [ha11] at hleft_pos
  simp at hleft_pos

/-- In the two-by-two branch, if the left side of the printed comparison is
nonnegative, the accepted offdiagonal pivot is nonzero. -/
theorem bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_left_nonneg
    (σ a11 a21 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hleft_nonneg : 0 ≤ σ * |a11|) :
    a21 ≠ 0 := by
  have hthreshold :=
    bunch_tridiagonal_pivot_choice_two_threshold σ a11 a21 hchoice
  have hright_pos : 0 < bunchTridiagonalAlpha * a21 ^ 2 :=
    lt_of_le_of_lt hleft_nonneg hthreshold
  intro ha21
  rw [ha21] at hright_pos
  simp at hright_pos

/-- A source-shaped variant of the two-by-two branch nonsingularity fact when
`σ` is known nonnegative. -/
theorem bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg
    (σ a11 a21 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσ : 0 ≤ σ) :
    a21 ≠ 0 :=
  bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_left_nonneg σ a11 a21
    hchoice (mul_nonneg hσ (abs_nonneg a11))

/-- In the two-by-two branch of Algorithm 11.6, if `σ` dominates the second
diagonal entry, the accepted tridiagonal pivot block has determinant bounded
away from zero by `(1 - α) a21²`. -/
theorem bunch_tridiagonal_twoByTwo_absdet_lower_of_sigma_bound
    (σ a11 a21 a22 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa22 : |a22| ≤ σ) :
    (1 - bunchTridiagonalAlpha) * a21 ^ 2 ≤ |a11 * a22 - a21 ^ 2| := by
  have hthreshold :=
    bunch_tridiagonal_pivot_choice_two_threshold σ a11 a21 hchoice
  have hprod_le : |a11 * a22| ≤ σ * |a11| := by
    have hmul := mul_le_mul_of_nonneg_left hσa22 (abs_nonneg a11)
    rw [abs_mul]
    nlinarith
  have hprod_lt : |a11 * a22| < bunchTridiagonalAlpha * a21 ^ 2 :=
    lt_of_le_of_lt hprod_le hthreshold
  have hdecomp : (a21 ^ 2 - a11 * a22) + a11 * a22 = a21 ^ 2 := by ring
  have hsum : |a21 ^ 2| ≤ |a21 ^ 2 - a11 * a22| + |a11 * a22| := by
    calc
      |a21 ^ 2| = |(a21 ^ 2 - a11 * a22) + a11 * a22| := by rw [hdecomp]
      _ ≤ |a21 ^ 2 - a11 * a22| + |a11 * a22| := abs_add_le _ _
  have hsq_abs : |a21 ^ 2| = a21 ^ 2 := abs_of_nonneg (sq_nonneg a21)
  have hlower_basic : a21 ^ 2 - |a11 * a22| ≤
      |a21 ^ 2 - a11 * a22| := by
    rw [hsq_abs] at hsum
    linarith
  have hcoeff_le_basic :
      (1 - bunchTridiagonalAlpha) * a21 ^ 2 ≤ a21 ^ 2 - |a11 * a22| := by
    nlinarith [hprod_lt]
  calc
    (1 - bunchTridiagonalAlpha) * a21 ^ 2 ≤
        a21 ^ 2 - |a11 * a22| := hcoeff_le_basic
    _ ≤ |a21 ^ 2 - a11 * a22| := hlower_basic
    _ = |a11 * a22 - a21 ^ 2| := by rw [abs_sub_comm]

/-- The two-by-two tridiagonal pivot block accepted by Algorithm 11.6 is
nonsingular when `σ` dominates the second diagonal entry. -/
theorem bunch_tridiagonal_twoByTwo_det_ne_zero_of_sigma_bound
    (σ a11 a21 a22 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa22 : |a22| ≤ σ) :
    a11 * a22 - a21 ^ 2 ≠ 0 := by
  have hσ : 0 ≤ σ := le_trans (abs_nonneg a22) hσa22
  have ha21 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ a11 a21
      hchoice hσ
  have hsquare : 0 < a21 ^ 2 := sq_pos_of_ne_zero ha21
  have halpha_gap : 0 < 1 - bunchTridiagonalAlpha := by
    linarith [bunch_tridiagonal_alpha_lt_one]
  have hlower :=
    bunch_tridiagonal_twoByTwo_absdet_lower_of_sigma_bound σ a11 a21 a22
      hchoice hσa22
  have hdet_abs_pos : 0 < |a11 * a22 - a21 ^ 2| :=
    lt_of_lt_of_le (mul_pos halpha_gap hsquare) hlower
  exact abs_pos.mp hdet_abs_pos

/-- Entrywise inverse bounds for the `2 × 2` tridiagonal pivot block
`[[a11, a21], [a21, a22]]` accepted by Algorithm 11.6.  The inverse entries are
`a22/det`, `-a21/det`, and `a11/det`, with
`det = a11*a22 - a21²`. -/
theorem bunch_tridiagonal_twoByTwo_inverse_entry_bounds_of_sigma_bound
    (σ a11 a21 a22 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ) :
    |a22 / (a11 * a22 - a21 ^ 2)| ≤
        σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ∧
    |(-a21) / (a11 * a22 - a21 ^ 2)| ≤
        |a21| / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ∧
    |a11 / (a11 * a22 - a21 ^ 2)| ≤
        σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) := by
  let det := a11 * a22 - a21 ^ 2
  let lower := (1 - bunchTridiagonalAlpha) * a21 ^ 2
  have hσ : 0 ≤ σ := le_trans (abs_nonneg a11) hσa11
  have ha21 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ a11 a21
      hchoice hσ
  have hsquare : 0 < a21 ^ 2 := sq_pos_of_ne_zero ha21
  have halpha_gap : 0 < 1 - bunchTridiagonalAlpha := by
    linarith [bunch_tridiagonal_alpha_lt_one]
  have hlower_pos : 0 < lower := by
    dsimp [lower]
    exact mul_pos halpha_gap hsquare
  have hdet_lower : lower ≤ |det| := by
    dsimp [lower, det]
    exact bunch_tridiagonal_twoByTwo_absdet_lower_of_sigma_bound σ a11 a21 a22
      hchoice hσa22
  have hdet_abs_pos : 0 < |det| := lt_of_lt_of_le hlower_pos hdet_lower
  constructor
  · rw [abs_div]
    have hnum : |a22| / |det| ≤ σ / |det| :=
      div_le_div_of_nonneg_right hσa22 (le_of_lt hdet_abs_pos)
    have hden : σ / |det| ≤ σ / lower :=
      div_le_div_of_nonneg_left hσ hlower_pos hdet_lower
    exact hnum.trans hden
  · constructor
    · rw [abs_div, abs_neg]
      exact div_le_div_of_nonneg_left (abs_nonneg a21) hlower_pos hdet_lower
    · rw [abs_div]
      have hnum : |a11| / |det| ≤ σ / |det| :=
        div_le_div_of_nonneg_right hσa11 (le_of_lt hdet_abs_pos)
      have hden : σ / |det| ≤ σ / lower :=
        div_le_div_of_nonneg_left hσ hlower_pos hdet_lower
      exact hnum.trans hden

/-- Floating-point backward error of the scalar Schur update in a tridiagonal
`2 × 2` pivot step.  In a symmetric tridiagonal matrix, after accepting the
leading `2 × 2` block, the only trailing update has the form
`b - c*f*c`, where `f` is the bottom-right entry of the inverse pivot block.
The rounded computation `fl(b - fl(fl(c*f)*c))` differs from the exact update by
a residual bounded by `γ₃ (|b| + |c*f*c|)`. -/
theorem fl_tridiagonal_twoByTwo_schur_step_error
    (fp : FPModel) (b c f : ℝ) (hval : gammaValid fp 3) :
    ∃ Δ : ℝ,
      |Δ| ≤ gamma fp 3 * (|b| + |c * f * c|) ∧
      fp.fl_sub b (fp.fl_mul (fp.fl_mul c f) c) = (b - c * f * c) + Δ := by
  obtain ⟨δ1, hδ1, hm1⟩ := fp.model_mul c f
  obtain ⟨δ2, hδ2, hm2⟩ := fp.model_mul (fp.fl_mul c f) c
  obtain ⟨δ3, hδ3, hs⟩ := fp.model_sub b (fp.fl_mul (fp.fl_mul c f) c)
  obtain ⟨θ, hθ, hprod⟩ :=
    prod_error_bound fp 3 ![δ1, δ2, δ3]
      (by intro i; fin_cases i <;> simp_all) hval
  have hfactor : (1 + δ1) * (1 + δ2) * (1 + δ3) = 1 + θ := by
    have h := hprod
    rw [Fin.prod_univ_three] at h
    simpa using h
  have hs_eq : fp.fl_sub b (fp.fl_mul (fp.fl_mul c f) c)
      = b * (1 + δ3) - (c * f * c) * (1 + θ) := by
    rw [hs, hm2, hm1, ← hfactor]
    ring
  refine ⟨b * δ3 - (c * f * c) * θ, ?_, ?_⟩
  · have hu3 : fp.u ≤ gamma fp 3 := u_le_gamma fp (by norm_num) hval
    have hγ0 : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
    have htri : |b * δ3 - (c * f * c) * θ| ≤
        |b * δ3| + |(c * f * c) * θ| := by
      have h := abs_add_le (b * δ3) (-((c * f * c) * θ))
      rwa [← sub_eq_add_neg, abs_neg] at h
    have e1 : |b * δ3 - (c * f * c) * θ|
        ≤ |b| * fp.u + |c * f * c| * gamma fp 3 := by
      calc |b * δ3 - (c * f * c) * θ|
          ≤ |b * δ3| + |(c * f * c) * θ| := htri
        _ = |b| * |δ3| + |c * f * c| * |θ| := by rw [abs_mul, abs_mul]
        _ ≤ |b| * fp.u + |c * f * c| * gamma fp 3 :=
            add_le_add (mul_le_mul_of_nonneg_left hδ3 (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hθ (abs_nonneg _))
    have e2 : |b| * fp.u + |c * f * c| * gamma fp 3
        ≤ gamma fp 3 * (|b| + |c * f * c|) := by
      have hle : |b| * fp.u ≤ |b| * gamma fp 3 :=
        mul_le_mul_of_nonneg_left hu3 (abs_nonneg _)
      nlinarith [hle, abs_nonneg (c * f * c), hγ0]
    exact le_trans e1 e2
  · rw [hs_eq]
    ring

/-- Source-shaped version of `fl_tridiagonal_twoByTwo_schur_step_error` for the
accepted Algorithm 11.6 `2 × 2` pivot block.  The inverse-entry bound converts
the abstract correction `|c*f*c|` into the scalar budget using
`σ / ((1 - α) a21²)`. -/
theorem fl_tridiagonal_twoByTwo_schur_step_error_of_sigma_bound
    (fp : FPModel) (σ a11 a21 a22 b c : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hval : gammaValid fp 3) :
    ∃ Δ : ℝ,
      |Δ| ≤ gamma fp 3 *
        (|b| + |c| * (σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2)) * |c|) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) + Δ := by
  obtain ⟨hInv22, hInv21, hInv11⟩ :=
    bunch_tridiagonal_twoByTwo_inverse_entry_bounds_of_sigma_bound σ a11 a21 a22
      hchoice hσa11 hσa22
  obtain ⟨Δ, hΔ, hstep⟩ :=
    fl_tridiagonal_twoByTwo_schur_step_error fp b c
      (a11 / (a11 * a22 - a21 ^ 2)) hval
  refine ⟨Δ, ?_, hstep⟩
  have hcorr : |c * (a11 / (a11 * a22 - a21 ^ 2)) * c| ≤
      |c| * (σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2)) * |c| := by
    rw [abs_mul, abs_mul]
    have hleft :=
      mul_le_mul_of_nonneg_left hInv11 (abs_nonneg c)
    exact mul_le_mul_of_nonneg_right hleft (abs_nonneg c)
  have hγ0 : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
  have hbudget :
      gamma fp 3 * (|b| + |c * (a11 / (a11 * a22 - a21 ^ 2)) * c|)
        ≤ gamma fp 3 *
          (|b| + |c| * (σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2)) * |c|) :=
    mul_le_mul_of_nonneg_left (add_le_add (le_refl |b|) hcorr) hγ0
  exact le_trans hΔ hbudget

/-- Backward-error form of the scalar rounded update for an accepted
tridiagonal `2 × 2` pivot: the computed trailing Schur entry is the exact Schur
update for a perturbed trailing scalar `b + Δb`. -/
theorem fl_tridiagonal_twoByTwo_schur_step_backward_error_of_sigma_bound
    (fp : FPModel) (σ a11 a21 a22 b c : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hval : gammaValid fp 3) :
    ∃ Δb : ℝ,
      |Δb| ≤ gamma fp 3 *
        (|b| + |c| * (σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2)) * |c|) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b + Δb) - c * (a11 / (a11 * a22 - a21 ^ 2)) * c := by
  obtain ⟨Δ, hΔ, hstep⟩ :=
    fl_tridiagonal_twoByTwo_schur_step_error_of_sigma_bound fp σ a11 a21 a22 b c
      hchoice hσa11 hσa22 hval
  refine ⟨Δ, hΔ, ?_⟩
  rw [hstep]
  ring

/-- Uniform scalar budget for the backward-error form of the accepted
tridiagonal `2 × 2` pivot update.  This is the local bridge from the Algorithm
11.6 inverse-entry scalar to a one-stage normwise envelope. -/
theorem fl_tridiagonal_twoByTwo_schur_step_backward_error_uniform_bound
    (fp : FPModel) (σ a11 a21 a22 b c Amax κ : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hval : gammaValid fp 3) :
    ∃ Δb : ℝ,
      |Δb| ≤ gamma fp 3 * (Amax + Amax * κ * Amax) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b + Δb) - c * (a11 / (a11 * a22 - a21 ^ 2)) * c := by
  obtain ⟨Δb, hΔb, hstep⟩ :=
    fl_tridiagonal_twoByTwo_schur_step_backward_error_of_sigma_bound fp
      σ a11 a21 a22 b c hchoice hσa11 hσa22 hval
  refine ⟨Δb, ?_, hstep⟩
  have hσ : 0 ≤ σ := le_trans (abs_nonneg a11) hσa11
  have ha21 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ a11 a21
      hchoice hσ
  have hsquare : 0 < a21 ^ 2 := sq_pos_of_ne_zero ha21
  have halpha_gap : 0 < 1 - bunchTridiagonalAlpha := by
    linarith [bunch_tridiagonal_alpha_lt_one]
  have hlower_pos : 0 < (1 - bunchTridiagonalAlpha) * a21 ^ 2 :=
    mul_pos halpha_gap hsquare
  have hratio_nonneg :
      0 ≤ σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) :=
    div_nonneg hσ (le_of_lt hlower_pos)
  have hcorr1 :
      |c| * (σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2)) ≤ Amax * κ :=
    mul_le_mul hc hratio hratio_nonneg hAmax
  have hcorr :
      |c| * (σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2)) * |c| ≤
        Amax * κ * Amax :=
    mul_le_mul hcorr1 hc (abs_nonneg c) (mul_nonneg hAmax hκ)
  have hinside :
      |b| + |c| * (σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2)) * |c| ≤
        Amax + Amax * κ * Amax :=
    add_le_add hb hcorr
  have hγ0 : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
  exact le_trans hΔb (mul_le_mul_of_nonneg_left hinside hγ0)

/-- One-stage `1 × 1` trailing-block envelope for an accepted tridiagonal
`2 × 2` pivot.  Since a symmetric tridiagonal matrix has only one trailing
entry touched by the first `2 × 2` pivot, the scalar backward-error bound lifts
to a `Fin 1 × Fin 1` perturbation directly. -/
theorem fl_tridiagonal_twoByTwo_trailing_one_stage_bound
    (fp : FPModel) (σ a11 a21 a22 b c Amax κ : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hval : gammaValid fp 3) :
    ∃ ΔS : Fin 1 → Fin 1 → ℝ,
      (∀ i j : Fin 1, |ΔS i j| ≤ gamma fp 3 * (Amax + Amax * κ * Amax)) ∧
      (∀ i j : Fin 1,
        fp.fl_sub b
            (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
          = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) + ΔS i j) := by
  obtain ⟨Δb, hΔb, hstep⟩ :=
    fl_tridiagonal_twoByTwo_schur_step_backward_error_uniform_bound fp
      σ a11 a21 a22 b c Amax κ hchoice hσa11 hσa22 hAmax hκ hb hc
      hratio hval
  refine ⟨fun _ _ => Δb, ?_, ?_⟩
  · intro _ _
    exact hΔb
  · intro _ _
    rw [hstep]
    ring

/-- Printed-budget handoff for the single trailing block in an accepted
tridiagonal `2 × 2` pivot step.  Once the local scalar budget is bounded by
`c_bound * u * Amax`, the perturbation has the componentwise shape used in
Theorem 11.7. -/
theorem fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound
    (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound u : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3) :
    ∃ ΔS : Fin 1 → Fin 1 → ℝ,
      (∀ i j : Fin 1, |ΔS i j| ≤ c_bound * u * Amax) ∧
      (∀ i j : Fin 1,
        fp.fl_sub b
            (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
          = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) + ΔS i j) := by
  obtain ⟨ΔS, hΔS, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_one_stage_bound fp
      σ a11 a21 a22 b c Amax κ hchoice hσa11 hσa22 hAmax hκ hb hc
      hratio hval
  refine ⟨ΔS, ?_, hstep⟩
  intro i j
  exact le_trans (hΔS i j) hbudget

/-- First-stage embedding of the printed `2 × 2` tridiagonal trailing scalar
backward error into the ambient `3 × 3` tridiagonal block-LDLᵀ step.  The
perturbation is zero outside the single trailing entry, so this is the local
handoff needed before iterating the tridiagonal recursion. -/
theorem fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_three
    (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound u : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3) :
    ∃ ΔA : Fin 3 → Fin 3 → ℝ,
      (∀ i j : Fin 3, |ΔA i j| ≤ c_bound * u * Amax) ∧
      (∀ i j : Fin 3,
        i ≠ (⟨2, by decide⟩ : Fin 3) ∨
          j ≠ (⟨2, by decide⟩ : Fin 3) →
        ΔA i j = 0) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (⟨2, by decide⟩ : Fin 3) (⟨2, by decide⟩ : Fin 3) := by
  obtain ⟨ΔS, hΔS, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound fp
      σ a11 a21 a22 b c Amax κ c_bound u hchoice hσa11 hσa22 hAmax hκ
      hb hc hratio hbudget hval
  let tail : Fin 3 := ⟨2, by decide⟩
  let zero : Fin 1 := ⟨0, by decide⟩
  let ΔA : Fin 3 → Fin 3 → ℝ :=
    fun i j => if i = tail ∧ j = tail then ΔS zero zero else 0
  refine ⟨ΔA, ?_, ?_, ?_⟩
  · intro i j
    have hzero_bound : |(0 : ℝ)| ≤ c_bound * u * Amax := by
      simpa using (abs_nonneg (ΔS zero zero)).trans (hΔS zero zero)
    by_cases htail : i = tail ∧ j = tail
    · simpa [ΔA, htail] using hΔS zero zero
    · simpa [ΔA, htail] using hzero_bound
  · intro i j houtside
    have htail : ¬(i = tail ∧ j = tail) := by
      intro htail
      rcases houtside with hi | hj
      · exact hi htail.1
      · exact hj htail.2
    simp [ΔA, htail]
  · simpa [ΔA, tail, zero] using hstep zero zero

/-- Local index of the first trailing scalar after a leading `2 × 2`
tridiagonal pivot inside a block of size `n+3`. -/
def tridiagonalTwoByTwoFirstTrailingIndex (n : ℕ) : Fin (n + 3) :=
  ⟨2, by
    have h23 : 2 < 3 := by norm_num
    have h3 : 3 ≤ n + 3 := Nat.le_add_left 3 n
    exact lt_of_lt_of_le h23 h3⟩

@[simp] theorem tridiagonalTwoByTwoFirstTrailingIndex_val (n : ℕ) :
    (tridiagonalTwoByTwoFirstTrailingIndex n).val = 2 := rfl

/-- Offset embedding of the recursive trailing subproblem after a leading
`2 × 2` tridiagonal pivot.  Local trailing index `0` maps to ambient index `2`. -/
def tridiagonalTwoByTwoTrailingSubproblemIndex (n : ℕ)
    (i : Fin (n + 1)) : Fin (n + 3) :=
  ⟨i.val + 2, by
    have h := Nat.add_lt_add_right i.isLt 2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h⟩

@[simp] theorem tridiagonalTwoByTwoTrailingSubproblemIndex_val
    (n : ℕ) (i : Fin (n + 1)) :
    (tridiagonalTwoByTwoTrailingSubproblemIndex n i).val = i.val + 2 := rfl

@[simp] theorem tridiagonalTwoByTwoTrailingSubproblemIndex_zero
    (n : ℕ) :
    tridiagonalTwoByTwoTrailingSubproblemIndex n 0 =
      tridiagonalTwoByTwoFirstTrailingIndex n := by
  apply Fin.ext
  simp [tridiagonalTwoByTwoTrailingSubproblemIndex,
    tridiagonalTwoByTwoFirstTrailingIndex]

/-- The recursive trailing-subproblem embedding after a leading tridiagonal
`2 × 2` pivot is injective. -/
theorem tridiagonalTwoByTwoTrailingSubproblemIndex_injective (n : ℕ) :
    Function.Injective (tridiagonalTwoByTwoTrailingSubproblemIndex n) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simpa [tridiagonalTwoByTwoTrailingSubproblemIndex] using
    Nat.add_right_cancel hval

/-- An ambient perturbation is supported in the trailing block left after a
leading `2 × 2` tridiagonal pivot if it vanishes on the first two rows and
columns. -/
def TridiagonalTwoByTwoTrailingBlockSupport (n : ℕ)
    (E : Fin (n + 3) → Fin (n + 3) → ℝ) : Prop :=
  ∀ i j : Fin (n + 3), i.val < 2 ∨ j.val < 2 → E i j = 0

/-- General zero-prefix support predicate: a perturbation vanishes on the
leading `offset` rows and columns.  The tridiagonal `2 × 2` trailing-block
support predicate is the `offset = 2` instance. -/
def TridiagonalLeadingBlockSupport (m offset : ℕ)
    (E : Fin m → Fin m → ℝ) : Prop :=
  ∀ i j : Fin m, i.val < offset ∨ j.val < offset → E i j = 0

/-- A perturbation that vanishes on a deeper zero-prefix also vanishes on any
shallower zero-prefix. -/
theorem tridiagonalLeadingBlockSupport_of_le_offset
    (m offset offset' : ℕ) (E : Fin m → Fin m → ℝ)
    (hoff : offset ≤ offset')
    (hEsupp : TridiagonalLeadingBlockSupport m offset' E) :
    TridiagonalLeadingBlockSupport m offset E := by
  intro i j hlead
  apply hEsupp
  rcases hlead with hi | hj
  · exact Or.inl (Nat.lt_of_lt_of_le hi hoff)
  · exact Or.inr (Nat.lt_of_lt_of_le hj hoff)

/-- The zero perturbation has any zero-prefix support, with any nonnegative
componentwise bound.  This is the base bookkeeping object for recursive
tridiagonal perturbation assembly. -/
theorem tridiagonalLeadingBlockSupport_zero_bound
    (m offset : ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ Z : Fin m → Fin m → ℝ,
      (∀ i j : Fin m, |Z i j| ≤ β) ∧
      TridiagonalLeadingBlockSupport m offset Z ∧
      (∀ i j : Fin m, Z i j = 0) := by
  refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
  · intro i j
    simpa using hβ
  · intro i j hlead
    rfl
  · intro i j
    rfl

/-- Printed-coefficient version of the zero perturbation package. -/
theorem tridiagonalLeadingBlockSupport_zero_printed_bound
    (m offset : ℕ) (c u Amax : ℝ) (hβ : 0 ≤ c * u * Amax) :
    ∃ Z : Fin m → Fin m → ℝ,
      (∀ i j : Fin m, |Z i j| ≤ c * u * Amax) ∧
      TridiagonalLeadingBlockSupport m offset Z ∧
      (∀ i j : Fin m, Z i j = 0) :=
  tridiagonalLeadingBlockSupport_zero_bound m offset (c * u * Amax) hβ

/-- Zero-prefix supported perturbations are closed under addition, and their
componentwise bounds add.  This is the offset-generic version used when several
recursive tridiagonal lifts are accumulated at different depths. -/
theorem tridiagonalLeadingBlockSupport_add_bound
    (m offset : ℕ) (E F : Fin m → Fin m → ℝ) (βE βF : ℝ)
    (hEbound : ∀ i j : Fin m, |E i j| ≤ βE)
    (hFbound : ∀ i j : Fin m, |F i j| ≤ βF)
    (hEsupp : TridiagonalLeadingBlockSupport m offset E)
    (hFsupp : TridiagonalLeadingBlockSupport m offset F) :
    ∃ G : Fin m → Fin m → ℝ,
      (∀ i j : Fin m, |G i j| ≤ βE + βF) ∧
      TridiagonalLeadingBlockSupport m offset G ∧
      (∀ i j : Fin m, G i j = E i j + F i j) := by
  refine ⟨fun i j => E i j + F i j, ?_, ?_, ?_⟩
  · intro i j
    calc
      |E i j + F i j| ≤ |E i j| + |F i j| := abs_add_le _ _
      _ ≤ βE + βF := add_le_add (hEbound i j) (hFbound i j)
  · intro i j hlead
    change E i j + F i j = 0
    rw [hEsupp i j hlead, hFsupp i j hlead, add_zero]
  · intro i j
    rfl

/-- Add two zero-prefix supported perturbations, allowing each input to be
supported at a deeper offset than the common output offset. -/
theorem tridiagonalLeadingBlockSupport_add_bound_of_le_offset
    (m offset offsetE offsetF : ℕ) (E F : Fin m → Fin m → ℝ) (βE βF : ℝ)
    (hoffE : offset ≤ offsetE) (hoffF : offset ≤ offsetF)
    (hEbound : ∀ i j : Fin m, |E i j| ≤ βE)
    (hFbound : ∀ i j : Fin m, |F i j| ≤ βF)
    (hEsupp : TridiagonalLeadingBlockSupport m offsetE E)
    (hFsupp : TridiagonalLeadingBlockSupport m offsetF F) :
    ∃ G : Fin m → Fin m → ℝ,
      (∀ i j : Fin m, |G i j| ≤ βE + βF) ∧
      TridiagonalLeadingBlockSupport m offset G ∧
      (∀ i j : Fin m, G i j = E i j + F i j) :=
  tridiagonalLeadingBlockSupport_add_bound m offset E F βE βF
    hEbound hFbound
    (tridiagonalLeadingBlockSupport_of_le_offset m offset offsetE E
      hoffE hEsupp)
    (tridiagonalLeadingBlockSupport_of_le_offset m offset offsetF F
      hoffF hFsupp)

/-- Printed-coefficient version of the zero-prefix support add/bound combiner:
two perturbations bounded by `cE * u * Amax` and `cF * u * Amax` combine with
coefficient `cE + cF`. -/
theorem tridiagonalLeadingBlockSupport_add_bound_printed
    (m offset : ℕ) (E F : Fin m → Fin m → ℝ) (cE cF u Amax : ℝ)
    (hEbound : ∀ i j : Fin m, |E i j| ≤ cE * u * Amax)
    (hFbound : ∀ i j : Fin m, |F i j| ≤ cF * u * Amax)
    (hEsupp : TridiagonalLeadingBlockSupport m offset E)
    (hFsupp : TridiagonalLeadingBlockSupport m offset F) :
    ∃ G : Fin m → Fin m → ℝ,
      (∀ i j : Fin m, |G i j| ≤ (cE + cF) * u * Amax) ∧
      TridiagonalLeadingBlockSupport m offset G ∧
      (∀ i j : Fin m, G i j = E i j + F i j) := by
  obtain ⟨G, hG, hGsupp, hsum⟩ :=
    tridiagonalLeadingBlockSupport_add_bound m offset E F
      (cE * u * Amax) (cF * u * Amax) hEbound hFbound hEsupp hFsupp
  refine ⟨G, ?_, hGsupp, hsum⟩
  intro i j
  calc
    |G i j| ≤ cE * u * Amax + cF * u * Amax := hG i j
    _ = (cE + cF) * u * Amax := by ring

/-- Printed-coefficient mixed-depth version of the zero-prefix support
add/bound combiner. -/
theorem tridiagonalLeadingBlockSupport_add_bound_printed_of_le_offset
    (m offset offsetE offsetF : ℕ) (E F : Fin m → Fin m → ℝ)
    (cE cF u Amax : ℝ)
    (hoffE : offset ≤ offsetE) (hoffF : offset ≤ offsetF)
    (hEbound : ∀ i j : Fin m, |E i j| ≤ cE * u * Amax)
    (hFbound : ∀ i j : Fin m, |F i j| ≤ cF * u * Amax)
    (hEsupp : TridiagonalLeadingBlockSupport m offsetE E)
    (hFsupp : TridiagonalLeadingBlockSupport m offsetF F) :
    ∃ G : Fin m → Fin m → ℝ,
      (∀ i j : Fin m, |G i j| ≤ (cE + cF) * u * Amax) ∧
      TridiagonalLeadingBlockSupport m offset G ∧
      (∀ i j : Fin m, G i j = E i j + F i j) :=
  tridiagonalLeadingBlockSupport_add_bound_printed m offset E F cE cF u Amax
    hEbound hFbound
    (tridiagonalLeadingBlockSupport_of_le_offset m offset offsetE E
      hoffE hEsupp)
    (tridiagonalLeadingBlockSupport_of_le_offset m offset offsetF F
      hoffF hFsupp)

/-- The specialized trailing-block support predicate is exactly the
zero-prefix support predicate with offset two. -/
theorem tridiagonalTwoByTwoTrailingBlockSupport_iff_leadingBlockSupport
    (n : ℕ) (E : Fin (n + 3) → Fin (n + 3) → ℝ) :
    TridiagonalTwoByTwoTrailingBlockSupport n E ↔
      TridiagonalLeadingBlockSupport (n + 3) 2 E := by
  rfl

/-- Supported perturbations in the trailing block after a leading `2 × 2`
tridiagonal pivot are closed under addition, and their componentwise bounds add. -/
theorem tridiagonalTwoByTwoTrailingBlockSupport_add_bound
    (n : ℕ) (E F : Fin (n + 3) → Fin (n + 3) → ℝ) (βE βF : ℝ)
    (hEbound : ∀ i j : Fin (n + 3), |E i j| ≤ βE)
    (hFbound : ∀ i j : Fin (n + 3), |F i j| ≤ βF)
    (hEsupp : TridiagonalTwoByTwoTrailingBlockSupport n E)
    (hFsupp : TridiagonalTwoByTwoTrailingBlockSupport n F) :
    ∃ G : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |G i j| ≤ βE + βF) ∧
      TridiagonalTwoByTwoTrailingBlockSupport n G ∧
      (∀ i j : Fin (n + 3), G i j = E i j + F i j) := by
  refine ⟨fun i j => E i j + F i j, ?_, ?_, ?_⟩
  · intro i j
    calc
      |E i j + F i j| ≤ |E i j| + |F i j| := abs_add_le _ _
      _ ≤ βE + βF := add_le_add (hEbound i j) (hFbound i j)
  · intro i j hlead
    change E i j + F i j = 0
    rw [hEsupp i j hlead, hFsupp i j hlead, add_zero]
  · intro i j
    rfl

/-- Lift a perturbation on the recursive trailing subproblem after a leading
`2 × 2` tridiagonal pivot into the ambient local block.  Entries outside the
embedded trailing subproblem are set to zero. -/
noncomputable def tridiagonalTwoByTwoLiftTrailingPerturbation (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin (n + 3) → Fin (n + 3) → ℝ :=
  fun i j =>
    if hi : ∃ a : Fin (n + 1),
        tridiagonalTwoByTwoTrailingSubproblemIndex n a = i then
      if hj : ∃ b : Fin (n + 1),
          tridiagonalTwoByTwoTrailingSubproblemIndex n b = j then
        E (Classical.choose hi) (Classical.choose hj)
      else 0
    else 0

/-- A leading-row/column index is not in the embedded recursive trailing
subproblem after a leading `2 × 2` tridiagonal pivot. -/
theorem not_exists_tridiagonalTwoByTwoTrailingSubproblemIndex_of_val_lt_two
    {n : ℕ} {i : Fin (n + 3)} (hi : i.val < 2) :
    ¬ ∃ a : Fin (n + 1), tridiagonalTwoByTwoTrailingSubproblemIndex n a = i := by
  intro h
  rcases h with ⟨a, ha⟩
  have hval := congrArg Fin.val ha
  have hge : 2 ≤ i.val := by
    rw [← hval]
    simp [tridiagonalTwoByTwoTrailingSubproblemIndex]
  exact (not_lt_of_ge hge) hi

/-- The lifted recursive trailing perturbation agrees with the source
perturbation on embedded trailing-subproblem entries. -/
@[simp] theorem tridiagonalTwoByTwoLiftTrailingPerturbation_apply_embedded
    (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) :
    tridiagonalTwoByTwoLiftTrailingPerturbation n E
        (tridiagonalTwoByTwoTrailingSubproblemIndex n i)
        (tridiagonalTwoByTwoTrailingSubproblemIndex n j) =
      E i j := by
  classical
  let emb := tridiagonalTwoByTwoTrailingSubproblemIndex n
  have hi : ∃ a : Fin (n + 1), emb a = emb i := ⟨i, rfl⟩
  have hj : ∃ b : Fin (n + 1), emb b = emb j := ⟨j, rfl⟩
  have hci : Classical.choose hi = i := by
    exact (tridiagonalTwoByTwoTrailingSubproblemIndex_injective n)
      (Classical.choose_spec hi)
  have hcj : Classical.choose hj = j := by
    exact (tridiagonalTwoByTwoTrailingSubproblemIndex_injective n)
      (Classical.choose_spec hj)
  simp [tridiagonalTwoByTwoLiftTrailingPerturbation, emb, hi, hj, hci, hcj]

/-- Componentwise bounds lift from the recursive trailing subproblem to the
ambient perturbation. -/
theorem tridiagonalTwoByTwoLiftTrailingPerturbation_bound
    (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → ℝ) (β : ℝ)
    (hEbound : ∀ i j : Fin (n + 1), |E i j| ≤ β) :
    ∀ i j : Fin (n + 3),
      |tridiagonalTwoByTwoLiftTrailingPerturbation n E i j| ≤ β := by
  classical
  have hβ : 0 ≤ β := by
    exact (abs_nonneg (E 0 0)).trans (hEbound 0 0)
  intro i j
  by_cases hi : ∃ a : Fin (n + 1),
      tridiagonalTwoByTwoTrailingSubproblemIndex n a = i
  · by_cases hj : ∃ b : Fin (n + 1),
        tridiagonalTwoByTwoTrailingSubproblemIndex n b = j
    · rw [tridiagonalTwoByTwoLiftTrailingPerturbation, dif_pos hi, dif_pos hj]
      exact hEbound (Classical.choose hi) (Classical.choose hj)
    · rw [tridiagonalTwoByTwoLiftTrailingPerturbation, dif_pos hi, dif_neg hj]
      simpa using hβ
  · rw [tridiagonalTwoByTwoLiftTrailingPerturbation, dif_neg hi]
    simpa using hβ

/-- The lifted recursive trailing perturbation is supported entirely in the
trailing block left after the leading `2 × 2` pivot. -/
theorem tridiagonalTwoByTwoLiftTrailingPerturbation_support
    (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → ℝ) :
    TridiagonalTwoByTwoTrailingBlockSupport n
      (tridiagonalTwoByTwoLiftTrailingPerturbation n E) := by
  classical
  intro i j hlead
  rcases hlead with hi | hj
  · have hnot :=
      not_exists_tridiagonalTwoByTwoTrailingSubproblemIndex_of_val_lt_two hi
    simp [tridiagonalTwoByTwoLiftTrailingPerturbation, hnot]
  · by_cases hi : ∃ a : Fin (n + 1),
        tridiagonalTwoByTwoTrailingSubproblemIndex n a = i
    · have hnot :=
        not_exists_tridiagonalTwoByTwoTrailingSubproblemIndex_of_val_lt_two hj
      simp [tridiagonalTwoByTwoLiftTrailingPerturbation, hi, hnot]
    · simp [tridiagonalTwoByTwoLiftTrailingPerturbation, hi]

/-- Lifting a recursive trailing-subproblem perturbation through a leading
`2 × 2` tridiagonal pivot shifts any existing zero-prefix support by two
ambient indices.  This is the support bookkeeping for iterating the
tridiagonal recursion. -/
theorem tridiagonalTwoByTwoLiftTrailingPerturbation_leadingBlockSupport
    (n offset : ℕ) (E : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hEsupp : TridiagonalLeadingBlockSupport (n + 1) offset E) :
    TridiagonalLeadingBlockSupport (n + 3) (offset + 2)
      (tridiagonalTwoByTwoLiftTrailingPerturbation n E) := by
  classical
  intro i j hlead
  by_cases hi : ∃ a : Fin (n + 1),
      tridiagonalTwoByTwoTrailingSubproblemIndex n a = i
  · by_cases hj : ∃ b : Fin (n + 1),
        tridiagonalTwoByTwoTrailingSubproblemIndex n b = j
    · rw [tridiagonalTwoByTwoLiftTrailingPerturbation, dif_pos hi, dif_pos hj]
      apply hEsupp
      rcases hlead with hilt | hjlt
      · left
        have hval :
            (Classical.choose hi).val + 2 = i.val := by
          simpa [tridiagonalTwoByTwoTrailingSubproblemIndex] using
            congrArg Fin.val (Classical.choose_spec hi)
        have hsum : (Classical.choose hi).val + 2 < offset + 2 := by
          rwa [hval]
        exact (Nat.add_lt_add_iff_right (k := 2)).1 hsum
      · right
        have hval :
            (Classical.choose hj).val + 2 = j.val := by
          simpa [tridiagonalTwoByTwoTrailingSubproblemIndex] using
            congrArg Fin.val (Classical.choose_spec hj)
        have hsum : (Classical.choose hj).val + 2 < offset + 2 := by
          rwa [hval]
        exact (Nat.add_lt_add_iff_right (k := 2)).1 hsum
    · rw [tridiagonalTwoByTwoLiftTrailingPerturbation, dif_pos hi, dif_neg hj]
  · rw [tridiagonalTwoByTwoLiftTrailingPerturbation, dif_neg hi]

/-- Package the recursive trailing perturbation lift with its ambient bound,
shifted zero-prefix support, and embedded-entry identity. -/
theorem tridiagonalTwoByTwoLiftTrailingPerturbation_bound_leadingBlockSupport
    (n offset : ℕ) (E : Fin (n + 1) → Fin (n + 1) → ℝ) (β : ℝ)
    (hEbound : ∀ i j : Fin (n + 1), |E i j| ≤ β)
    (hEsupp : TridiagonalLeadingBlockSupport (n + 1) offset E) :
    ∃ ΔR : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔR i j| ≤ β) ∧
      TridiagonalLeadingBlockSupport (n + 3) (offset + 2) ΔR ∧
      (∀ i j : Fin (n + 1),
        ΔR (tridiagonalTwoByTwoTrailingSubproblemIndex n i)
          (tridiagonalTwoByTwoTrailingSubproblemIndex n j) = E i j) := by
  refine ⟨tridiagonalTwoByTwoLiftTrailingPerturbation n E, ?_, ?_, ?_⟩
  · exact tridiagonalTwoByTwoLiftTrailingPerturbation_bound n E β hEbound
  · exact tridiagonalTwoByTwoLiftTrailingPerturbation_leadingBlockSupport
      n offset E hEsupp
  · intro i j
    exact tridiagonalTwoByTwoLiftTrailingPerturbation_apply_embedded n E i j

/-- Package the recursive trailing perturbation lift with its ambient bound,
support, and embedded-entry identity. -/
theorem tridiagonalTwoByTwoLiftTrailingPerturbation_bound_support
    (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → ℝ) (β : ℝ)
    (hEbound : ∀ i j : Fin (n + 1), |E i j| ≤ β) :
    ∃ ΔR : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔR i j| ≤ β) ∧
      TridiagonalTwoByTwoTrailingBlockSupport n ΔR ∧
      (∀ i j : Fin (n + 1),
        ΔR (tridiagonalTwoByTwoTrailingSubproblemIndex n i)
          (tridiagonalTwoByTwoTrailingSubproblemIndex n j) = E i j) := by
  refine ⟨tridiagonalTwoByTwoLiftTrailingPerturbation n E, ?_, ?_, ?_⟩
  · exact tridiagonalTwoByTwoLiftTrailingPerturbation_bound n E β hEbound
  · exact tridiagonalTwoByTwoLiftTrailingPerturbation_support n E
  · intro i j
    exact tridiagonalTwoByTwoLiftTrailingPerturbation_apply_embedded n E i j

/-- Any index with value `< 2` is outside the first trailing scalar after a
leading `2 × 2` tridiagonal pivot. -/
theorem ne_tridiagonalTwoByTwoFirstTrailingIndex_of_val_lt_two
    {n : ℕ} {i : Fin (n + 3)} (hi : i.val < 2) :
    i ≠ tridiagonalTwoByTwoFirstTrailingIndex n := by
  intro h
  have hlt : (tridiagonalTwoByTwoFirstTrailingIndex n).val < 2 := by
    rw [← h]
    exact hi
  have hval : (tridiagonalTwoByTwoFirstTrailingIndex n).val = 2 := by simp
  rw [hval] at hlt
  exact (Nat.lt_irrefl 2) hlt

/-- Dimension-generic first-stage embedding of the printed `2 × 2`
tridiagonal trailing scalar backward error.  In a local block of size `n+3`,
the first accepted `2 × 2` pivot only touches the first trailing scalar of a
tridiagonal matrix; the ambient perturbation is therefore zero at every entry
except `tridiagonalTwoByTwoFirstTrailingIndex n`. -/
theorem fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed
    (n : ℕ) (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound u : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ c_bound * u * Amax) ∧
      (∀ i j : Fin (n + 3),
        i ≠ tridiagonalTwoByTwoFirstTrailingIndex n ∨
          j ≠ tridiagonalTwoByTwoFirstTrailingIndex n →
        ΔA i j = 0) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔS, hΔS, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound fp
      σ a11 a21 a22 b c Amax κ c_bound u hchoice hσa11 hσa22 hAmax hκ
      hb hc hratio hbudget hval
  let tail : Fin (n + 3) := tridiagonalTwoByTwoFirstTrailingIndex n
  let zero : Fin 1 := ⟨0, by decide⟩
  let ΔA : Fin (n + 3) → Fin (n + 3) → ℝ :=
    fun i j => if i = tail ∧ j = tail then ΔS zero zero else 0
  refine ⟨ΔA, ?_, ?_, ?_⟩
  · intro i j
    have hzero_bound : |(0 : ℝ)| ≤ c_bound * u * Amax := by
      simpa using (abs_nonneg (ΔS zero zero)).trans (hΔS zero zero)
    by_cases htail : i = tail ∧ j = tail
    · simpa [ΔA, htail] using hΔS zero zero
    · simpa [ΔA, htail] using hzero_bound
  · intro i j houtside
    have htail : ¬(i = tail ∧ j = tail) := by
      intro htail
      rcases houtside with hi | hj
      · exact hi htail.1
      · exact hj htail.2
    simp [ΔA, htail]
  · simpa [ΔA, tail, zero] using hstep zero zero

/-- Dimension-generic first-stage embedding of the printed `2 × 2`
tridiagonal trailing scalar backward error, with the support property needed to
compose with a recursive trailing-subproblem hypothesis. -/
theorem fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_support
    (n : ℕ) (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound u : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ c_bound * u * Amax) ∧
      TridiagonalTwoByTwoTrailingBlockSupport n ΔA ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔA, hΔA, hzero, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed n fp
      σ a11 a21 a22 b c Amax κ c_bound u hchoice hσa11 hσa22 hAmax hκ
      hb hc hratio hbudget hval
  refine ⟨ΔA, hΔA, ?_, hstep⟩
  intro i j hlead
  apply hzero
  rcases hlead with hi | hj
  · exact Or.inl (ne_tridiagonalTwoByTwoFirstTrailingIndex_of_val_lt_two hi)
  · exact Or.inr (ne_tridiagonalTwoByTwoFirstTrailingIndex_of_val_lt_two hj)

/-- Accumulate the local printed-budget residual from a leading `2 × 2`
tridiagonal pivot with an already-supported recursive trailing perturbation.
This is the local algebraic handoff used when iterating the tridiagonal
block-LDLᵀ recursion. -/
theorem fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate
    (n : ℕ) (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound u βR : ℝ)
    (ΔR : Fin (n + 3) → Fin (n + 3) → ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3)
    (hRbound : ∀ i j : Fin (n + 3), |ΔR i j| ≤ βR)
    (hRsupp : TridiagonalTwoByTwoTrailingBlockSupport n ΔR) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ c_bound * u * Amax + βR) ∧
      TridiagonalTwoByTwoTrailingBlockSupport n ΔA ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
          ΔR (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔS, hΔS, hSsupp, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_support n fp
      σ a11 a21 a22 b c Amax κ c_bound u hchoice hσa11 hσa22 hAmax hκ
      hb hc hratio hbudget hval
  obtain ⟨ΔA, hΔA, hAsupp, hsum⟩ :=
    tridiagonalTwoByTwoTrailingBlockSupport_add_bound n ΔS ΔR
      (c_bound * u * Amax) βR hΔS hRbound hSsupp hRsupp
  refine ⟨ΔA, hΔA, hAsupp, ?_⟩
  rw [hstep, hsum (tridiagonalTwoByTwoFirstTrailingIndex n)
    (tridiagonalTwoByTwoFirstTrailingIndex n)]
  ring

/-- Printed-coefficient form of the local recursive accumulation step: if the
recursive trailing perturbation is already bounded by `c_rec * u * Amax`, then
the accumulated perturbation is bounded by `(c_bound + c_rec) * u * Amax`. -/
theorem fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate_printed
    (n : ℕ) (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound c_rec u : ℝ)
    (ΔR : Fin (n + 3) → Fin (n + 3) → ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3)
    (hRbound : ∀ i j : Fin (n + 3), |ΔR i j| ≤ c_rec * u * Amax)
    (hRsupp : TridiagonalTwoByTwoTrailingBlockSupport n ΔR) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ (c_bound + c_rec) * u * Amax) ∧
      TridiagonalTwoByTwoTrailingBlockSupport n ΔA ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
          ΔR (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔA, hΔA, hAsupp, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate n fp
      σ a11 a21 a22 b c Amax κ c_bound u (c_rec * u * Amax) ΔR
      hchoice hσa11 hσa22 hAmax hκ hb hc hratio hbudget hval hRbound hRsupp
  refine ⟨ΔA, ?_, hAsupp, hstep⟩
  intro i j
  calc
    |ΔA i j| ≤ c_bound * u * Amax + c_rec * u * Amax := hΔA i j
    _ = (c_bound + c_rec) * u * Amax := by ring

/-- Recursive-subproblem form of the printed accumulation step.  A perturbation
proved on the trailing subproblem `Fin (n+1)` is first lifted into the ambient
`Fin (n+3)` block, then accumulated with the local `2 × 2` tridiagonal rounded
Schur residual. -/
theorem fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate
    (n : ℕ) (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound c_rec u : ℝ)
    (ΔRtail : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3)
    (hRtail_bound : ∀ i j : Fin (n + 1),
      |ΔRtail i j| ≤ c_rec * u * Amax) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ (c_bound + c_rec) * u * Amax) ∧
      TridiagonalTwoByTwoTrailingBlockSupport n ΔA ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
          ΔRtail 0 0
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔR, hRbound, hRsupp, hRembed⟩ :=
    tridiagonalTwoByTwoLiftTrailingPerturbation_bound_support n ΔRtail
      (c_rec * u * Amax) hRtail_bound
  obtain ⟨ΔA, hΔA, hAsupp, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate_printed
      n fp σ a11 a21 a22 b c Amax κ c_bound c_rec u ΔR hchoice
      hσa11 hσa22 hAmax hκ hb hc hratio hbudget hval hRbound hRsupp
  refine ⟨ΔA, hΔA, hAsupp, ?_⟩
  have htail :
      ΔR (tridiagonalTwoByTwoFirstTrailingIndex n)
          (tridiagonalTwoByTwoFirstTrailingIndex n) = ΔRtail 0 0 := by
    simpa [tridiagonalTwoByTwoTrailingSubproblemIndex_zero] using
      hRembed 0 0
  simpa [htail] using hstep

/-- Recursive-residual form of the printed accumulation step.  If the recursive
trailing subproblem already has a scalar backward-error certificate
`tail_fl = tail_exact + ΔRtail 0 0`, the leading `2 × 2` tridiagonal step
absorbs that certificate into one ambient perturbation with coefficient
`c_bound + c_rec`. -/
theorem fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate
    (n : ℕ) (fp : FPModel)
    (σ a11 a21 a22 b c Amax κ c_bound c_rec u tail_fl tail_exact : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3)
    (hrec : ∃ ΔRtail : Fin (n + 1) → Fin (n + 1) → ℝ,
      (∀ i j : Fin (n + 1), |ΔRtail i j| ≤ c_rec * u * Amax) ∧
      tail_fl = tail_exact + ΔRtail 0 0) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ (c_bound + c_rec) * u * Amax) ∧
      TridiagonalTwoByTwoTrailingBlockSupport n ΔA ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
          tail_fl
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          tail_exact +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔRtail, hRtail_bound, htail⟩ := hrec
  obtain ⟨ΔA, hΔA, hAsupp, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate
      n fp σ a11 a21 a22 b c Amax κ c_bound c_rec u ΔRtail
      hchoice hσa11 hσa22 hAmax hκ hb hc hratio hbudget hval
      hRtail_bound
  refine ⟨ΔA, hΔA, hAsupp, ?_⟩
  rw [htail]
  calc
    fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
          (tail_exact + ΔRtail 0 0)
        =
          (fp.fl_sub b
              (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
            ΔRtail 0 0) + tail_exact := by
      ring
    _ =
          ((b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
            ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
              (tridiagonalTwoByTwoFirstTrailingIndex n)) + tail_exact := by
      rw [hstep]
    _ =
          (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          tail_exact +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
      ring

/-- Recursive-subproblem printed accumulation with the generic zero-prefix
support predicate.  This is the same algebraic handoff as
`fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate`, but
with support stated as `TridiagonalLeadingBlockSupport ... 2` for recursive
assembly. -/
theorem fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate_leadingBlockSupport
    (n : ℕ) (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound c_rec u : ℝ)
    (ΔRtail : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3)
    (hRtail_bound : ∀ i j : Fin (n + 1),
      |ΔRtail i j| ≤ c_rec * u * Amax) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ (c_bound + c_rec) * u * Amax) ∧
      TridiagonalLeadingBlockSupport (n + 3) 2 ΔA ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
          ΔRtail 0 0
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔA, hΔA, hAsupp, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate
      n fp σ a11 a21 a22 b c Amax κ c_bound c_rec u ΔRtail
      hchoice hσa11 hσa22 hAmax hκ hb hc hratio hbudget hval
      hRtail_bound
  refine ⟨ΔA, hΔA, ?_, hstep⟩
  exact (tridiagonalTwoByTwoTrailingBlockSupport_iff_leadingBlockSupport
    n ΔA).1 hAsupp

/-- Recursive-residual printed accumulation with the generic zero-prefix
support predicate. -/
theorem fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport
    (n : ℕ) (fp : FPModel)
    (σ a11 a21 a22 b c Amax κ c_bound c_rec u tail_fl tail_exact : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3)
    (hrec : ∃ ΔRtail : Fin (n + 1) → Fin (n + 1) → ℝ,
      (∀ i j : Fin (n + 1), |ΔRtail i j| ≤ c_rec * u * Amax) ∧
      tail_fl = tail_exact + ΔRtail 0 0) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ (c_bound + c_rec) * u * Amax) ∧
      TridiagonalLeadingBlockSupport (n + 3) 2 ΔA ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
          tail_fl
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          tail_exact +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔA, hΔA, hAsupp, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate
      n fp σ a11 a21 a22 b c Amax κ c_bound c_rec u tail_fl tail_exact
      hchoice hσa11 hσa22 hAmax hκ hb hc hratio hbudget hval hrec
  refine ⟨ΔA, hΔA, ?_, hstep⟩
  exact (tridiagonalTwoByTwoTrailingBlockSupport_iff_leadingBlockSupport
    n ΔA).1 hAsupp

-- ============================================================
-- Chapter 11.3  Skew-symmetric block LDL^T
-- ============================================================

/-- Algorithm 11.9 source decision predicate for Bunch's skew-symmetric pivoting
strategy at the first stage. -/
def SkewBunchPivotChoice (firstColumnTailZero : Prop)
    (pivotMagnitude : ℝ) (s : PivotSize) : Prop :=
  (firstColumnTailZero ∧ s = PivotSize.one) ∨
  (¬ firstColumnTailZero ∧ 0 < pivotMagnitude ∧ s = PivotSize.two)

/-- **Skew 2×2 multiplier bound** (Higham §11.3).  For Bunch's skew-symmetric
    pivoting, the row of `CE⁻¹` has entries `−a_{i2}/a₂₁, a_{i1}/a₂₁`; since the
    pivot `a₂₁` is the largest-magnitude entry (`|c| ≤ |a₂₁|`), each multiplier —
    and hence every entry of `L` — is bounded by 1.  Derived, not assumed. -/
theorem skew_twoByTwo_multiplier_bound (c a : ℝ) (ha : a ≠ 0) (hc : |c| ≤ |a|) :
    |c / a| ≤ 1 := by
  rw [abs_div, div_le_one (abs_pos.mpr ha)]
  exact hc

/-- **Skew 2×2 Schur-complement entry bound** (Higham §11.3).  The Schur entry
    `s = a_ij − (a_{i2}/a₂₁)·a_{j1} + (a_{i1}/a₂₁)·a_{j2}` for a 2×2 skew pivot,
    with every active entry bounded by `M` and multipliers bounded by 1
    (`|a_{i1}|, |a_{i2}| ≤ |a₂₁|`), satisfies the printed bound `|s| ≤ 3·M`. -/
theorem skew_twoByTwo_schur_entry_bound
    (aij ai1 ai2 aj1 aj2 a21 M : ℝ)
    (ha : a21 ≠ 0)
    (hij : |aij| ≤ M) (hj1 : |aj1| ≤ M) (hj2 : |aj2| ≤ M)
    (hi1 : |ai1| ≤ |a21|) (hi2 : |ai2| ≤ |a21|) :
    |aij - (ai2 / a21) * aj1 + (ai1 / a21) * aj2| ≤ 3 * M := by
  have hm1 : |ai2 / a21| ≤ 1 := skew_twoByTwo_multiplier_bound ai2 a21 ha hi2
  have hm2 : |ai1 / a21| ≤ 1 := skew_twoByTwo_multiplier_bound ai1 a21 ha hi1
  have t1 : |ai2 / a21 * aj1| ≤ M := by
    rw [abs_mul]
    calc |ai2 / a21| * |aj1| ≤ 1 * M := mul_le_mul hm1 hj1 (abs_nonneg _) (by norm_num)
      _ = M := by ring
  have t2 : |ai1 / a21 * aj2| ≤ M := by
    rw [abs_mul]
    calc |ai1 / a21| * |aj2| ≤ 1 * M := mul_le_mul hm2 hj2 (abs_nonneg _) (by norm_num)
      _ = M := by ring
  have htriA : |aij - ai2 / a21 * aj1| ≤ |aij| + |ai2 / a21 * aj1| := by
    have h := abs_add_le aij (-(ai2 / a21 * aj1))
    rwa [← sub_eq_add_neg, abs_neg] at h
  calc |aij - ai2 / a21 * aj1 + ai1 / a21 * aj2|
      ≤ |aij - ai2 / a21 * aj1| + |ai1 / a21 * aj2| := abs_add_le _ _
    _ ≤ (|aij| + |ai2 / a21 * aj1|) + |ai1 / a21 * aj2| := add_le_add htriA (le_refl _)
    _ ≤ (M + M) + M := add_le_add (add_le_add hij t1) t2
    _ = 3 * M := by ring

-- ============================================================
-- Chapter 11.1  Exact block-LDL^T factorization step (eq (11.3), s = 1)
-- ============================================================

/-- **Equation (11.3), `s = 1` case** — one 1×1-pivot block-LDLᵀ elimination step
    is an exact factorization (exact arithmetic).  For a symmetric
    `A : Fin (m+1) → Fin (m+1) → ℝ` with nonzero pivot `A 0 0`, the unit lower
    triangular `L` (first column `A i0 / A00` below the pivot, identity in the
    trailing block) and the block-diagonal `D` (pivot `A00`, trailing Schur
    complement `A i j − A i0·A 0j / A00`) satisfy
    `∑_{k₁,k₂} L I k₁·D k₁ k₂·L J k₂ = A I J`.  This is the exact base of the
    diagonal-pivoting recursion underlying Theorem 11.3 (the floating-point
    version adds the rounding error `fl_oneByOne_schur_step_error`). -/
theorem oneByOne_step_factorization (m : ℕ) (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (ha : A 0 0 ≠ 0) (hsym : ∀ i : Fin m, A 0 i.succ = A i.succ 0)
    (L D : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hL0 : L 0 0 = 1)
    (hLcol : ∀ i : Fin m, L i.succ 0 = A i.succ 0 / A 0 0)
    (hL0s : ∀ j : Fin m, L 0 j.succ = 0)
    (hLtr : ∀ i j : Fin m, L i.succ j.succ = if i = j then 1 else 0)
    (hD00 : D 0 0 = A 0 0)
    (hD0s : ∀ j : Fin m, D 0 j.succ = 0)
    (hDs0 : ∀ i : Fin m, D i.succ 0 = 0)
    (hDtr : ∀ i j : Fin m, D i.succ j.succ
      = A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) :
    ∀ I J : Fin (m + 1),
      (∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = A I J := by
  have inner : ∀ (I k₁ J : Fin (m + 1)),
      (∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = L I k₁ * (∑ k₂, D k₁ k₂ * L J k₂) := by
    intro I k₁ J; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  have cdl0 : ∀ J : Fin (m + 1), (∑ k₂, D 0 k₂ * L J k₂) = A 0 0 * L J 0 := by
    intro J; rw [Fin.sum_univ_succ, hD00]
    have : (∑ k₂ : Fin m, D 0 k₂.succ * L J k₂.succ) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hD0s k, zero_mul]
    rw [this, add_zero]
  have cdls : ∀ (i : Fin m) (J : Fin (m + 1)),
      (∑ k₂, D i.succ k₂ * L J k₂)
        = ∑ k₂' : Fin m, D i.succ k₂'.succ * L J k₂'.succ := by
    intro i J; rw [Fin.sum_univ_succ, hDs0 i, zero_mul, zero_add]
  intro I J
  rw [Fin.sum_univ_succ, inner I 0 J, cdl0 J]
  have hrest : (∑ i : Fin m, ∑ k₂, L I i.succ * D i.succ k₂ * L J k₂)
      = ∑ i : Fin m, L I i.succ * (∑ k₂' : Fin m, D i.succ k₂'.succ * L J k₂'.succ) := by
    apply Finset.sum_congr rfl; intro i _; rw [inner I i.succ J, cdls i J]
  rw [hrest]
  rcases Fin.eq_zero_or_eq_succ I with hI | ⟨i0, hI⟩ <;>
    rcases Fin.eq_zero_or_eq_succ J with hJ | ⟨j0, hJ⟩ <;> subst hI <;> subst hJ
  · have : (∑ i : Fin m, L 0 i.succ *
        (∑ k₂' : Fin m, D i.succ k₂'.succ * L 0 k₂'.succ)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hL0s i, zero_mul]
    rw [this, hL0, add_zero]; ring
  · have : (∑ i : Fin m, L 0 i.succ *
        (∑ k₂' : Fin m, D i.succ k₂'.succ * L j0.succ k₂'.succ)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hL0s i, zero_mul]
    rw [this, hL0, add_zero, hLcol j0, hsym j0]; field_simp
  · have hz : (∑ i : Fin m, L i0.succ i.succ *
        (∑ k₂' : Fin m, D i.succ k₂'.succ * L 0 k₂'.succ)) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [show (∑ k₂' : Fin m, D i.succ k₂'.succ * L 0 k₂'.succ) = 0 from
          Finset.sum_eq_zero fun k _ => by rw [hL0s k, mul_zero], mul_zero]
    rw [hz, add_zero, hLcol i0, hL0]; field_simp
  · have hrsum : (∑ i : Fin m, L i0.succ i.succ *
        (∑ k₂' : Fin m, D i.succ k₂'.succ * L j0.succ k₂'.succ))
        = A i0.succ j0.succ - A i0.succ 0 * A 0 j0.succ / A 0 0 := by
      rw [Finset.sum_eq_single i0]
      · rw [hLtr i0 i0, if_pos rfl, one_mul, Finset.sum_eq_single j0]
        · rw [hDtr i0 j0, hLtr j0 j0, if_pos rfl, mul_one]
        · intro k _ hk; rw [hLtr j0 k, if_neg (Ne.symm hk), mul_zero]
        · intro h; exact absurd (Finset.mem_univ j0) h
      · intro i _ hi; rw [hLtr i0 i, if_neg (Ne.symm hi), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i0) h
    rw [hrsum, hLcol i0, hLcol j0, hsym j0]; field_simp; ring

/-- **Inductive step of the exact block-LDLᵀ recursion** (1×1 pivot), Higham
    eq (11.1)/(11.3).  Generalises `oneByOne_step_factorization`: the trailing
    block of `L`/`D` is a *recursively computed* factorization
    `L_S·D_S·L_Sᵀ = S` of the Schur complement `S` (the induction hypothesis
    `hIH`), not the identity.  With first-stage multipliers `A i0/A00` and Schur
    complement `S i j = A i.succ j.succ − A i.succ 0·A 0 j.succ / A00`, the
    assembled factors reproduce `A` exactly.  Iterating this is the exact
    `PAPᵀ = LDLᵀ` recursion underlying Theorem 11.3. -/
theorem blockLDLT_assemble_step (n : ℕ) (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (ha : A 0 0 ≠ 0) (hsym : ∀ i : Fin n, A 0 i.succ = A i.succ 0)
    (S L_S D_S : Fin n → Fin n → ℝ)
    (hS : ∀ i j : Fin n, S i j = A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0)
    (hIH : ∀ i j : Fin n, (∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂) = S i j)
    (L D : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hL0 : L 0 0 = 1)
    (hLcol : ∀ i : Fin n, L i.succ 0 = A i.succ 0 / A 0 0)
    (hL0s : ∀ j : Fin n, L 0 j.succ = 0)
    (hLtr : ∀ i j : Fin n, L i.succ j.succ = L_S i j)
    (hD00 : D 0 0 = A 0 0)
    (hD0s : ∀ j : Fin n, D 0 j.succ = 0)
    (hDs0 : ∀ i : Fin n, D i.succ 0 = 0)
    (hDtr : ∀ i j : Fin n, D i.succ j.succ = D_S i j) :
    ∀ I J : Fin (n + 1),
      (∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = A I J := by
  have inner : ∀ (I k₁ J : Fin (n + 1)),
      (∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = L I k₁ * (∑ k₂, D k₁ k₂ * L J k₂) := by
    intro I k₁ J; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  have cdl0 : ∀ J : Fin (n + 1), (∑ k₂, D 0 k₂ * L J k₂) = A 0 0 * L J 0 := by
    intro J; rw [Fin.sum_univ_succ, hD00]
    have : (∑ k₂ : Fin n, D 0 k₂.succ * L J k₂.succ) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hD0s k, zero_mul]
    rw [this, add_zero]
  have cdls : ∀ (i : Fin n) (J : Fin (n + 1)),
      (∑ k₂, D i.succ k₂ * L J k₂)
        = ∑ k₂' : Fin n, D_S i k₂' * L J k₂'.succ := by
    intro i J; rw [Fin.sum_univ_succ, hDs0 i, zero_mul, zero_add]
    apply Finset.sum_congr rfl; intro k _; rw [hDtr i k]
  intro I J
  rw [Fin.sum_univ_succ, inner I 0 J, cdl0 J]
  have hrest : (∑ i : Fin n, ∑ k₂, L I i.succ * D i.succ k₂ * L J k₂)
      = ∑ i : Fin n, L I i.succ * (∑ k₂' : Fin n, D_S i k₂' * L J k₂'.succ) := by
    apply Finset.sum_congr rfl; intro i _; rw [inner I i.succ J, cdls i J]
  rw [hrest]
  rcases Fin.eq_zero_or_eq_succ I with hI | ⟨i0, hI⟩ <;>
    rcases Fin.eq_zero_or_eq_succ J with hJ | ⟨j0, hJ⟩ <;> subst hI <;> subst hJ
  · have : (∑ i : Fin n, L 0 i.succ *
        (∑ k₂' : Fin n, D_S i k₂' * L 0 k₂'.succ)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hL0s i, zero_mul]
    rw [this, hL0, add_zero]; ring
  · have : (∑ i : Fin n, L 0 i.succ *
        (∑ k₂' : Fin n, D_S i k₂' * L j0.succ k₂'.succ)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hL0s i, zero_mul]
    rw [this, hL0, add_zero, hLcol j0, hsym j0]; field_simp
  · have hz : (∑ i : Fin n, L i0.succ i.succ *
        (∑ k₂' : Fin n, D_S i k₂' * L 0 k₂'.succ)) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [show (∑ k₂' : Fin n, D_S i k₂' * L 0 k₂'.succ) = 0 from
          Finset.sum_eq_zero fun k _ => by rw [hL0s k, mul_zero], mul_zero]
    rw [hz, add_zero, hLcol i0, hL0]; field_simp
  · have htrail : (∑ i : Fin n, L i0.succ i.succ *
        (∑ k₂' : Fin n, D_S i k₂' * L j0.succ k₂'.succ)) = S i0 j0 := by
      rw [← hIH i0 j0]
      apply Finset.sum_congr rfl; intro i _
      rw [hLtr i0 i, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [hLtr j0 k]; ring
    rw [htrail, hLcol i0, hLcol j0, hS i0 j0, hsym j0]
    field_simp; ring

/-- Schur complement of the leading 1×1 pivot,
`S i j = A i.succ j.succ − A i.succ 0 · A 0 j.succ / A 0 0`. -/
noncomputable def schurCompl (n : ℕ) (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0

/-- Symmetry is inherited by the Schur complement. -/
theorem schurCompl_symm (n : ℕ) (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, A i j = A j i) :
    ∀ i j : Fin n, schurCompl n A i j = schurCompl n A j i := by
  intro i j
  simp only [schurCompl]
  rw [hsym i.succ j.succ, hsym i.succ 0, hsym 0 j.succ]; ring

/-- The successive leading 1×1 pivots of the diagonal-pivoting recursion are all
nonzero (the "no 2×2 pivot needed / leading principal minors nonzero" case). -/
def AllOnePivots : (n : ℕ) → (Fin n → Fin n → ℝ) → Prop
  | 0, _ => True
  | (n + 1), A => A 0 0 ≠ 0 ∧ AllOnePivots n (schurCompl n A)

/-- **Exact all-1×1 block-LDLᵀ factorization existence** (Higham eqs (11.1)/(11.2),
the no-2×2-pivot / root-free `LDLᵀ` case).  If `A` is symmetric and every
successive Schur-complement pivot is nonzero (`AllOnePivots`), there exist factors
`L, D` with `∑ L·D·Lᵀ = A` — the exact `PAPᵀ = LDLᵀ` recursion (with `P = I`)
underlying Theorem 11.3, obtained by iterating `blockLDLT_assemble_step`. -/
theorem exact_blockLDLT_all_oneByOne :
    ∀ (n : ℕ) (A : Fin n → Fin n → ℝ),
      (∀ i j, A i j = A j i) → AllOnePivots n A →
      ∃ L D : Fin n → Fin n → ℝ,
        ∀ I J, (∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = A I J := by
  intro n
  induction n with
  | zero => intro A _ _; exact ⟨A, A, fun I => I.elim0⟩
  | succ n ih =>
    intro A hsym hp
    obtain ⟨ha, hpS⟩ := hp
    obtain ⟨L_S, D_S, hprodS⟩ := ih (schurCompl n A) (schurCompl_symm n A hsym) hpS
    refine ⟨fun I J => Fin.cases (Fin.cases 1 (fun _ => 0) J)
              (fun i => Fin.cases (A i.succ 0 / A 0 0) (fun j => L_S i j) J) I,
            fun I J => Fin.cases (Fin.cases (A 0 0) (fun _ => 0) J)
              (fun i => Fin.cases 0 (fun j => D_S i j) J) I, ?_⟩
    apply blockLDLT_assemble_step n A ha (fun i => hsym 0 i.succ)
      (schurCompl n A) L_S D_S (fun i j => rfl) hprodS
    · simp
    · intro i; simp
    · intro j; simp
    · intro i j; simp
    · simp
    · intro j; simp
    · intro i; simp
    · intro i j; simp

end NumStability
