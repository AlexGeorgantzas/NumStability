/-
Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Chapter 14 ("Matrix Inversion"), §14.2.2, equation (14.14), Method 2B
(pp. 266-267).

  Method 2B computes the off-diagonal block as `X21 = -X22 L21 X11`, so the
  rounded block satisfies (14.14)

      X̂21 = -X̂22 L21 X̂11 + Δ(X̂22, L21, X̂11).

  Postmultiplying by `L11` and using the Method 2 relation
  `X̂11 L11 = I + Δ11` gives Higham's displayed relation

      X̂21 L11 + X̂22 L21 (I + Δ11)
        = Δ(X̂22, L21, X̂11) L11.

  Its bound carries the extra factor `|X̂11||L11|`, so the analysis does not
  yield the desired residual form (14.8).  The local residual hinge used below
  is the exact-left-inverse specialization `Δ11 = 0`.

  `MatrixInversion.lean` supplies the algebraic hinge and a conditional
  obstruction wrapper.  This file first gives the general two-`fl_matMul`
  implementation and derives its composed product-error bound.  It then gives
  a 2×2 family, both abstractly and as a deterministic `FPModel` execution, in
  which an update error of size `u` becomes an absolute residual entry `u*t`.

  That family does not refute the source-shaped normalized bound (14.8): at the
  selected entry, `u * (|Xhat| |L|) = u * (2 + u) * t`.  It is retained only as
  an absolute-error amplification example.  A source-shaped unbounded
  normalized-residual witness is not claimed here.

  The operational result composes the repository's matrix-product bounds and
  equation-(14.14) wrappers.  No new axioms.
-/
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.Ch14Method2Loop
import NumStability.Algorithms.LU.BlockLU
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatrixInversion

namespace NumStability.Ch14Ext

open scoped BigOperators

/-!
### General two-product implementation of equation (14.14)

Method 2B forms `T_hat = fl(X22 * L21)` and then
`X21_hat = -fl(T_hat * X11)`.  The declarations in this section work for
arbitrary compatible block sizes.  The error theorem composes the two calls to
`matMul_error_bound`; it does not assume a triple-product error certificate.
-/

/-- The first rounded product in Method 2B, `T_hat = fl(X22 * L21)`. -/
noncomputable def ch14ext_method2B_flFirstProduct (fp : FPModel) {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ) :
    Fin r → Fin m → ℝ :=
  fl_matMul fp r r m X22 L21

/-- The unsigned second rounded product, `fl(T_hat * X11)`. -/
noncomputable def ch14ext_method2B_flSecondProduct (fp : FPModel) {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) : Fin r → Fin m → ℝ :=
  fl_matMul fp r m m (ch14ext_method2B_flFirstProduct fp X22 L21) X11

/-- The actual two-`fl_matMul` Method 2B update.  Negation is exact here, as in
    the repository's equation-(14.14) update surface. -/
noncomputable def ch14ext_method2B_flUpdate (fp : FPModel) {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) : Fin r → Fin m → ℝ :=
  fun i j => -ch14ext_method2B_flSecondProduct fp X22 L21 X11 i j

/-- Equation (14.14)'s exact decomposition specialized to the general actual
    two-product update.  Its perturbation is bounded nondefinitionally below. -/
theorem ch14ext_method2B_flUpdate_decomposition (fp : FPModel) {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) (i : Fin r) (j : Fin m) :
    ch14ext_method2B_flUpdate fp X22 L21 X11 i j =
      higham14_method2BBlockUpdateExact X22 L21 X11 i j +
        higham14_method2BBlockUpdateDelta
          (ch14ext_method2B_flUpdate fp X22 L21 X11) X22 L21 X11 i j :=
  higham14_eq14_14_method2B_block_update_decomposition
    (ch14ext_method2B_flUpdate fp X22 L21 X11) X22 L21 X11 i j

/-- Componentwise absolute triple-product envelope `|X22| |L21| |X11|`. -/
noncomputable def ch14ext_method2B_absTripleBudget {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) : Fin r → Fin m → ℝ :=
  fun i j =>
    ∑ k : Fin m, (∑ l : Fin r, |X22 i l| * |L21 l k|) * |X11 k j|

/-- The first product's exact (13.4) perturbation. -/
noncomputable def ch14ext_method2B_flFirstDelta (fp : FPModel) {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ) :
    Fin r → Fin m → ℝ :=
  fun i k => ch14ext_method2B_flFirstProduct fp X22 L21 i k -
    rectMatMul X22 L21 i k

/-- The second product's exact (13.4) perturbation, relative to its computed
    first factor `T_hat`. -/
noncomputable def ch14ext_method2B_flSecondDelta (fp : FPModel) {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) : Fin r → Fin m → ℝ :=
  fun i j => ch14ext_method2B_flSecondProduct fp X22 L21 X11 i j -
    rectMatMul (ch14ext_method2B_flFirstProduct fp X22 L21) X11 i j

/-- The first actual rounded product satisfies the componentwise matrix-product
    error bound for every compatible block size. -/
theorem ch14ext_method2B_flFirstProduct_error_bound (fp : FPModel) {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (hr : gammaValid fp r) (i : Fin r) (k : Fin m) :
    |ch14ext_method2B_flFirstProduct fp X22 L21 i k -
        rectMatMul X22 L21 i k| ≤
      gamma fp r * ∑ l : Fin r, |X22 i l| * |L21 l k| := by
  simpa [ch14ext_method2B_flFirstProduct, rectMatMul] using
    matMul_error_bound fp r r m X22 L21 hr i k

/-- The second actual rounded product satisfies the componentwise matrix-product
    error bound with the computed first factor. -/
theorem ch14ext_method2B_flSecondProduct_error_bound (fp : FPModel) {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) (hm : gammaValid fp m)
    (i : Fin r) (j : Fin m) :
    |ch14ext_method2B_flSecondProduct fp X22 L21 X11 i j -
        rectMatMul (ch14ext_method2B_flFirstProduct fp X22 L21) X11 i j| ≤
      gamma fp m * ∑ k : Fin m,
        |ch14ext_method2B_flFirstProduct fp X22 L21 i k| * |X11 k j| := by
  simpa [ch14ext_method2B_flSecondProduct, rectMatMul] using
    matMul_error_bound fp r m m
      (ch14ext_method2B_flFirstProduct fp X22 L21) X11 hm i j

/-- Equation (13.4) wrapper for the first Method 2B product.  The scalar
    `FirstOrderLe` remainder is supplied by Chapter 13's conventional-product
    theorem, with `c₁ = r²`. -/
theorem ch14ext_method2B_flFirstProduct_firstOrderSpec (fp : FPModel) {m r : ℕ}
    (hr0 : 0 < r) (hm0 : 0 < m)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (hr : gammaValid fp r) :
    MatMulFirstOrderSpec fp.u ((r : ℝ) ^ 2)
      (maxEntryNormRect hr0 hr0 X22) (maxEntryNormRect hr0 hm0 L21)
      (maxEntryNormRect hr0 hm0 (ch14ext_method2B_flFirstDelta fp X22 L21))
      X22 L21 (ch14ext_method2B_flFirstProduct fp X22 L21)
      (ch14ext_method2B_flFirstDelta fp X22 L21) := by
  simpa [ch14ext_method2B_flFirstProduct, ch14ext_method2B_flFirstDelta,
    rectMatMul] using
    higham13_conventional_matmul_spec_c1_maxEntry
      fp hr0 hr0 hm0 X22 L21 hr

/-- The explicit `FirstOrderLe` consequence of the first equation-(13.4)
    wrapper. -/
theorem ch14ext_method2B_flFirstDelta_firstOrderLe (fp : FPModel) {m r : ℕ}
    (hr0 : 0 < r) (hm0 : 0 < m)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (hr : gammaValid fp r) :
    FirstOrderLe fp.u
      (((r : ℝ) ^ 2) * fp.u * maxEntryNormRect hr0 hr0 X22 *
        maxEntryNormRect hr0 hm0 L21)
      (maxEntryNormRect hr0 hm0 (ch14ext_method2B_flFirstDelta fp X22 L21)) := by
  simpa [MatMulFirstOrderBound] using
    (ch14ext_method2B_flFirstProduct_firstOrderSpec
      fp hr0 hm0 X22 L21 hr).norm_bound

/-- Equation (13.4) wrapper for the second Method 2B product, now with
    `c₁ = m²` and the computed first product as its left factor. -/
theorem ch14ext_method2B_flSecondProduct_firstOrderSpec (fp : FPModel) {m r : ℕ}
    (hr0 : 0 < r) (hm0 : 0 < m)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) (hm : gammaValid fp m) :
    MatMulFirstOrderSpec fp.u ((m : ℝ) ^ 2)
      (maxEntryNormRect hr0 hm0
        (ch14ext_method2B_flFirstProduct fp X22 L21))
      (maxEntryNormRect hm0 hm0 X11)
      (maxEntryNormRect hr0 hm0
        (ch14ext_method2B_flSecondDelta fp X22 L21 X11))
      (ch14ext_method2B_flFirstProduct fp X22 L21) X11
      (ch14ext_method2B_flSecondProduct fp X22 L21 X11)
      (ch14ext_method2B_flSecondDelta fp X22 L21 X11) := by
  simpa [ch14ext_method2B_flSecondProduct, ch14ext_method2B_flSecondDelta,
    rectMatMul] using
    higham13_conventional_matmul_spec_c1_maxEntry
      fp hr0 hm0 hm0 (ch14ext_method2B_flFirstProduct fp X22 L21) X11 hm

/-- The explicit `FirstOrderLe` consequence of the second equation-(13.4)
    wrapper. -/
theorem ch14ext_method2B_flSecondDelta_firstOrderLe (fp : FPModel) {m r : ℕ}
    (hr0 : 0 < r) (hm0 : 0 < m)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) (hm : gammaValid fp m) :
    FirstOrderLe fp.u
      (((m : ℝ) ^ 2) * fp.u *
        maxEntryNormRect hr0 hm0
          (ch14ext_method2B_flFirstProduct fp X22 L21) *
        maxEntryNormRect hm0 hm0 X11)
      (maxEntryNormRect hr0 hm0
        (ch14ext_method2B_flSecondDelta fp X22 L21 X11)) := by
  simpa [MatMulFirstOrderBound] using
    (ch14ext_method2B_flSecondProduct_firstOrderSpec
      fp hr0 hm0 X22 L21 X11 hm).norm_bound

/-- The absolute triple-product envelope is nonnegative entrywise. -/
theorem ch14ext_method2B_absTripleBudget_nonneg {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) (i : Fin r) (j : Fin m) :
    0 ≤ ch14ext_method2B_absTripleBudget X22 L21 X11 i j := by
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg
    (Finset.sum_nonneg (fun l _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    (abs_nonneg _)

/-- The first rounded product is bounded by `(1 + gamma_r) |X22| |L21|`.
    This is the bridge needed to compose the second product error explicitly. -/
theorem ch14ext_method2B_flFirstProduct_abs_bound (fp : FPModel) {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (hr : gammaValid fp r) (i : Fin r) (k : Fin m) :
    |ch14ext_method2B_flFirstProduct fp X22 L21 i k| ≤
      (1 + gamma fp r) * (∑ l : Fin r, |X22 i l| * |L21 l k|) := by
  have herror := ch14ext_method2B_flFirstProduct_error_bound fp X22 L21 hr i k
  have hexact :
      |rectMatMul X22 L21 i k| ≤ ∑ l : Fin r, |X22 i l| * |L21 l k| := by
    calc
      |rectMatMul X22 L21 i k|
          = |∑ l : Fin r, X22 i l * L21 l k| := by rfl
      _ ≤ ∑ l : Fin r, |X22 i l * L21 l k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l : Fin r, |X22 i l| * |L21 l k| := by
        apply Finset.sum_congr rfl
        intro l _
        rw [abs_mul]
  calc
    |ch14ext_method2B_flFirstProduct fp X22 L21 i k|
        = |(ch14ext_method2B_flFirstProduct fp X22 L21 i k -
              rectMatMul X22 L21 i k) + rectMatMul X22 L21 i k| := by
            congr 1
            ring
    _ ≤ |ch14ext_method2B_flFirstProduct fp X22 L21 i k -
            rectMatMul X22 L21 i k| + |rectMatMul X22 L21 i k| := abs_add_le _ _
    _ ≤ gamma fp r * (∑ l : Fin r, |X22 i l| * |L21 l k|) +
          (∑ l : Fin r, |X22 i l| * |L21 l k|) := add_le_add herror hexact
    _ = (1 + gamma fp r) * (∑ l : Fin r, |X22 i l| * |L21 l k|) := by ring

/-- Explicit two-product composition.  The first term is the second
    multiplication's own error; the second is the first multiplication error
    propagated through `X11`. -/
theorem ch14ext_method2B_flUpdate_error_bound_explicit (fp : FPModel) {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) (hr : gammaValid fp r)
    (hm : gammaValid fp m) (i : Fin r) (j : Fin m) :
    |ch14ext_method2B_flUpdate fp X22 L21 X11 i j -
        higham14_method2BBlockUpdateExact X22 L21 X11 i j| ≤
      gamma fp m * (∑ k : Fin m,
        |ch14ext_method2B_flFirstProduct fp X22 L21 i k| * |X11 k j|) +
      gamma fp r * ch14ext_method2B_absTripleBudget X22 L21 X11 i j := by
  let That := ch14ext_method2B_flFirstProduct fp X22 L21
  let T := rectMatMul X22 L21
  let P := ch14ext_method2B_flSecondProduct fp X22 L21 X11
  have hsecond :
      |P i j - rectMatMul That X11 i j| ≤
        gamma fp m * ∑ k : Fin m, |That i k| * |X11 k j| := by
    simpa [P, That] using
      ch14ext_method2B_flSecondProduct_error_bound fp X22 L21 X11 hm i j
  have hprop :
      |rectMatMul That X11 i j - rectMatMul T X11 i j| ≤
        gamma fp r * ch14ext_method2B_absTripleBudget X22 L21 X11 i j := by
    calc
      |rectMatMul That X11 i j - rectMatMul T X11 i j|
          = |∑ k : Fin m, (That i k - T i k) * X11 k j| := by
              simp only [rectMatMul]
              congr 1
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ ≤ ∑ k : Fin m, |(That i k - T i k) * X11 k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin m, |That i k - T i k| * |X11 k j| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_mul]
      _ ≤ ∑ k : Fin m,
          (gamma fp r * ∑ l : Fin r, |X22 i l| * |L21 l k|) * |X11 k j| := by
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        simpa [That, T] using
          ch14ext_method2B_flFirstProduct_error_bound fp X22 L21 hr i k
      _ = gamma fp r * ch14ext_method2B_absTripleBudget X22 L21 X11 i j := by
        unfold ch14ext_method2B_absTripleBudget
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  change |-ch14ext_method2B_flSecondProduct fp X22 L21 X11 i j -
      (-rectMatMul (rectMatMul X22 L21) X11 i j)| ≤ _
  rw [show -ch14ext_method2B_flSecondProduct fp X22 L21 X11 i j -
      (-rectMatMul (rectMatMul X22 L21) X11 i j) =
      -(P i j - rectMatMul T X11 i j) by dsimp [P, T]; ring, abs_neg]
  calc
    |P i j - rectMatMul T X11 i j|
        = |(P i j - rectMatMul That X11 i j) +
            (rectMatMul That X11 i j - rectMatMul T X11 i j)| := by
          congr 1
          ring
    _ ≤ |P i j - rectMatMul That X11 i j| +
          |rectMatMul That X11 i j - rectMatMul T X11 i j| := abs_add_le _ _
    _ ≤ gamma fp m * (∑ k : Fin m, |That i k| * |X11 k j|) +
          gamma fp r * ch14ext_method2B_absTripleBudget X22 L21 X11 i j :=
      add_le_add hsecond hprop

/-- Closed componentwise bound for the general two-`fl_matMul` update:
    `(gamma_m + gamma_r + gamma_m*gamma_r) |X22| |L21| |X11|`. -/
theorem ch14ext_method2B_flUpdate_error_bound (fp : FPModel) {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) (hr : gammaValid fp r)
    (hm : gammaValid fp m) (i : Fin r) (j : Fin m) :
    |ch14ext_method2B_flUpdate fp X22 L21 X11 i j -
        higham14_method2BBlockUpdateExact X22 L21 X11 i j| ≤
      (gamma fp m + gamma fp r + gamma fp m * gamma fp r) *
        ch14ext_method2B_absTripleBudget X22 L21 X11 i j := by
  have hexplicit :=
    ch14ext_method2B_flUpdate_error_bound_explicit fp X22 L21 X11 hr hm i j
  have hgm : 0 ≤ gamma fp m := gamma_nonneg fp hm
  have hsum :
      (∑ k : Fin m,
          |ch14ext_method2B_flFirstProduct fp X22 L21 i k| * |X11 k j|) ≤
        (1 + gamma fp r) *
          ch14ext_method2B_absTripleBudget X22 L21 X11 i j := by
    calc
      (∑ k : Fin m,
          |ch14ext_method2B_flFirstProduct fp X22 L21 i k| * |X11 k j|)
          ≤ ∑ k : Fin m,
              ((1 + gamma fp r) *
                (∑ l : Fin r, |X22 i l| * |L21 l k|)) * |X11 k j| := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_right
              (ch14ext_method2B_flFirstProduct_abs_bound fp X22 L21 hr i k)
              (abs_nonneg _)
      _ = (1 + gamma fp r) *
          ch14ext_method2B_absTripleBudget X22 L21 X11 i j := by
            unfold ch14ext_method2B_absTripleBudget
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
  calc
    |ch14ext_method2B_flUpdate fp X22 L21 X11 i j -
        higham14_method2BBlockUpdateExact X22 L21 X11 i j|
        ≤ gamma fp m * (∑ k : Fin m,
            |ch14ext_method2B_flFirstProduct fp X22 L21 i k| * |X11 k j|) +
          gamma fp r * ch14ext_method2B_absTripleBudget X22 L21 X11 i j :=
      hexplicit
    _ ≤ gamma fp m * ((1 + gamma fp r) *
            ch14ext_method2B_absTripleBudget X22 L21 X11 i j) +
          gamma fp r * ch14ext_method2B_absTripleBudget X22 L21 X11 i j :=
      add_le_add (mul_le_mul_of_nonneg_left hsum hgm) (le_refl _)
    _ = (gamma fp m + gamma fp r + gamma fp m * gamma fp r) *
          ch14ext_method2B_absTripleBudget X22 L21 X11 i j := by ring

/-- General operational form of equation (14.14).  Unlike the generic
    definitional decomposition, this package is instantiated by the actual two
    rounded products and its perturbation envelope is proved from
    `matMul_error_bound`. -/
theorem ch14ext_method2B_flUpdate_eq14_14_spec (fp : FPModel) {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) (hr : gammaValid fp r)
    (hm : gammaValid fp m) :
    Method2BBlockUpdateSpec (ch14ext_method2B_flUpdate fp X22 L21 X11)
      X22 L21 X11 (gamma fp m + gamma fp r + gamma fp m * gamma fp r)
      (ch14ext_method2B_absTripleBudget X22 L21 X11) := by
  apply higham14_eq14_14_method2B_block_update_spec_of_product_error
  intro i j
  exact ch14ext_method2B_flUpdate_error_bound fp X22 L21 X11 hr hm i j

/-!
### Concrete Method 2B absolute-error examples (block size `m = 2`, `r = 1`)

All data is parametrized by the conditioning parameter `t` and the roundoff
level `ε`.  The diagonal block `L11` is the classic unit lower-triangular
ill-conditioned matrix `[[1,0],[-t,1]]`; its exact inverse `X11 = [[1,0],[t,1]]`
satisfies `X11 L11 = I` but has `|X11||L11|` entries of size `t`.
-/

/-- Method 2B diagonal block `L11 = [[1, 0], [-t, 1]]` (unit lower triangular,
    ill conditioned for large `t`). -/
noncomputable def ch14ext_method2B_L11 (t : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![1, 0], ![-t, 1]]

/-- Exact inverse of `L11`: `X11 = [[1, 0], [t, 1]]`.  Here `X11 L11 = I`
    holds exactly, modelling "X11 computed by Method 2" at its best case. -/
noncomputable def ch14ext_method2B_X11 (t : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![1, 0], ![t, 1]]

/-- Trailing diagonal-block inverse `X̂22` (a fixed nonzero `1×1` value). -/
noncomputable def ch14ext_method2B_X22 : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => 2

/-- Rectangular lower-left block `L21` (a fixed nonzero `1×2` block). -/
noncomputable def ch14ext_method2B_L21 : Fin 1 → Fin 2 → ℝ :=
  ![![3, 5]]

/-- The chosen abstract block-update perturbation `Δ = [0, ε]`, placed in the
    second column so that postmultiplication by the large `L11` entry `-t`
    amplifies its absolute size. -/
noncomputable def ch14ext_method2B_delta (ε : ℝ) : Fin 1 → Fin 2 → ℝ :=
  ![![0, ε]]

/-- The rounded off-diagonal block from equation (14.14):
    `X̂21 = -X̂22 L21 X̂11 + Δ`, i.e. the exact Method 2B triple product plus the
    explicit product-rounding perturbation `Δ`. -/
noncomputable def ch14ext_method2B_X21hat (ε t : ℝ) : Fin 1 → Fin 2 → ℝ :=
  fun i j =>
    higham14_method2BBlockUpdateExact
        ch14ext_method2B_X22 ch14ext_method2B_L21 (ch14ext_method2B_X11 t) i j +
      ch14ext_method2B_delta ε i j

/-- `X̂11 L11 = I` exactly: `X11 = [[1,0],[t,1]]` is a left inverse of
    `L11 = [[1,0],[-t,1]]`.  This is the "X11 computed by Method 2" premise of
    the (14.14) residual analysis, in its exact best case. -/
theorem ch14ext_method2B_left_inverse (t : ℝ) :
    IsLeftInverse 2 (ch14ext_method2B_L11 t) (ch14ext_method2B_X11 t) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [ch14ext_method2B_L11, ch14ext_method2B_X11, Fin.sum_univ_two]

/-- The Method 2B block-update perturbation of this instance is exactly the
    explicit `Δ = [0, ε]` (the exact triple product cancels). -/
theorem ch14ext_method2B_delta_eq (ε t : ℝ) :
    higham14_method2BBlockUpdateDelta (ch14ext_method2B_X21hat ε t)
        ch14ext_method2B_X22 ch14ext_method2B_L21 (ch14ext_method2B_X11 t) =
      ch14ext_method2B_delta ε := by
  funext i j
  simp [higham14_method2BBlockUpdateDelta, ch14ext_method2B_X21hat]

/-- The perturbation satisfies the generic block-update package with parameter
    `ε` and the chosen unit envelope `absBound ≡ 1`.  This theorem alone does
    not identify that envelope with `|X22| |L21| |X11|`; the general operational
    theorem above and the fixed execution below supply actual product bounds. -/
theorem ch14ext_method2B_spec (ε t : ℝ) (hε : 0 ≤ ε) :
    Method2BBlockUpdateSpec (ch14ext_method2B_X21hat ε t)
      ch14ext_method2B_X22 ch14ext_method2B_L21 (ch14ext_method2B_X11 t)
      ε (fun _ _ => 1) := by
  apply higham14_eq14_14_method2B_block_update_spec_of_product_error
  intro i j
  have hΔ :
      ch14ext_method2B_X21hat ε t i j -
        higham14_method2BBlockUpdateExact ch14ext_method2B_X22
          ch14ext_method2B_L21 (ch14ext_method2B_X11 t) i j =
        ch14ext_method2B_delta ε i j := by
    simp [ch14ext_method2B_X21hat]
  rw [hΔ]
  fin_cases j <;>
    simp [ch14ext_method2B_delta, abs_of_nonneg, hε]

/-- **Named residual (absolute-error calculation).**  The propagated block-update
    perturbation `Δ L11`, which by the equation-(14.14) residual identity equals the whole
    off-diagonal left residual `X̂21 L11 + X̂22 L21`, has `(0,0)` entry exactly
    `-(ε·t)`.  This is an absolute amplification statement only; the
    source-shaped right-hand side in (14.8) also grows with `t`. -/
theorem ch14ext_method2B_residual_value (ε t : ℝ) :
    rectMatMul (ch14ext_method2B_delta ε) (ch14ext_method2B_L11 t)
        (0 : Fin 1) (0 : Fin 2) = -(ε * t) := by
  simp [rectMatMul, Fin.sum_univ_two, ch14ext_method2B_delta,
    ch14ext_method2B_L11]

/-- **Abstract Method 2B absolute-budget example.**

    For any positive roundoff level `ε` and any conditioning `t > 1`, the
    concrete instance's off-diagonal left-residual block
    `X̂21 L11 + X̂22 L21` cannot satisfy the absolute budget `ε`: it already
    violates it in the `(0,0)` entry, where the residual has magnitude `ε·t`.

    This derives the "large propagated delta" hypothesis that the
    `higham14_eq14_14_method2B_no_small_offdiag_residual_of_propagated_delta`
    wrapper left assumed, for the chosen abstract block-update error
    amplified by an ill-conditioned `L11`.  It does not assert failure of the
    normalized source bound (14.8). -/
theorem ch14ext_method2B_offdiag_residual_exceeds_absolute_epsilon_budget
    (ε t : ℝ) (hε : 0 < ε) (ht : 1 < t) :
    ¬ (∀ (i : Fin 1) (j : Fin 2),
        |rectMatMul (ch14ext_method2B_X21hat ε t) (ch14ext_method2B_L11 t) i j +
            rectMatMul ch14ext_method2B_X22 ch14ext_method2B_L21 i j| ≤ ε) := by
  have hεt : (0 : ℝ) < ε * t := mul_pos hε (lt_trans one_pos ht)
  refine
    higham14_eq14_14_method2B_no_small_offdiag_residual_of_propagated_delta
      (ch14ext_method2B_L11 t) (ch14ext_method2B_X11 t)
      (ch14ext_method2B_X21hat ε t) ch14ext_method2B_X22 ch14ext_method2B_L21
      ε (fun _ _ => 1) (fun _ _ => ε)
      (ch14ext_method2B_spec ε t (le_of_lt hε))
      (ch14ext_method2B_left_inverse t)
      (i0 := (0 : Fin 1)) (j0 := (0 : Fin 2)) ?_
  -- Derive the largeness: `ε < |Δ L11 (0,0)| = ε·t`.
  rw [ch14ext_method2B_delta_eq ε t, ch14ext_method2B_residual_value ε t,
    abs_neg, abs_of_pos hεt]
  nlinarith [hε, ht]

/-- **Unbounded absolute amplification.**  For a fixed positive roundoff
    level `ε`, the `(0,0)` off-diagonal residual entry exceeds any prescribed
    absolute bound `C` once the conditioning parameter is large enough.  The
    matrix-dependent factor in (14.8) grows at the same time, so this theorem
    is not a normalized-residual counterexample. -/
theorem ch14ext_method2B_absolute_residual_amplification_unbounded
    (ε : ℝ) (hε : 0 < ε) (C : ℝ) :
    ∃ t : ℝ, C < |rectMatMul (ch14ext_method2B_delta ε)
        (ch14ext_method2B_L11 t) (0 : Fin 1) (0 : Fin 2)| := by
  refine ⟨(|C| + 1) / ε + 1, ?_⟩
  rw [ch14ext_method2B_residual_value]
  have ht : (0 : ℝ) < (|C| + 1) / ε + 1 := by positivity
  have hεt : (0 : ℝ) < ε * ((|C| + 1) / ε + 1) := mul_pos hε ht
  rw [abs_neg, abs_of_pos hεt]
  have hCle : C ≤ |C| := le_abs_self C
  have hexp : ε * ((|C| + 1) / ε + 1) = (|C| + 1) + ε := by
    field_simp
  rw [hexp]
  linarith [hCle, hε]

/-!
### An actual rounded Method 2B execution

The preceding construction chooses its perturbation directly.  The declarations below
exhibit a deterministic `FPModel` and evaluate the same two `fl_matMul` calls
for this fixed family.

All primitive operations are exact except multiplication of `1` by `1`, which
has relative error `u`.  This is a valid instance of Higham's standard model.
For `X22 = [2]` and `L21 = [0, 1/2]`, the first product is exact and equals
`[0, 1]`.  In the second product with `X11 = [[1,0],[t,1]]`, only its second
output rounds, producing update perturbation `[0,-u]`.  Multiplication by
`L11 = [[1,0],[-t,1]]` then gives residual entry `u*t`.
-/

/-- A deterministic Higham-model realization in which only `1 * 1` rounds,
    with relative error `u`; all other primitive operations are exact. -/
noncomputable def ch14ext_method2B_selectiveModel (u : ℝ) (hu : 0 ≤ u) : FPModel := by
  classical
  exact
    { u := u
      u_nonneg := hu
      fl_add := fun x y => x + y
      fl_sub := fun x y => x - y
      fl_mul := fun x y =>
        if x = 1 ∧ y = 1 then (x * y) * (1 + u) else x * y
      fl_div := fun x y => x / y
      fl_sqrt := fun x => Real.sqrt x
      fl_add_zero := by
        intro x
        ring
      model_add := by
        intro x y
        refine ⟨0, ?_, ?_⟩
        · simpa using hu
        · ring
      model_sub := by
        intro x y
        refine ⟨0, ?_, ?_⟩
        · simpa using hu
        · ring
      model_mul := by
        intro x y
        by_cases hxy : x = 1 ∧ y = 1
        · refine ⟨u, ?_, ?_⟩
          · simp [abs_of_nonneg hu]
          · simp [hxy]
        · refine ⟨0, ?_, ?_⟩
          · simpa using hu
          · simp [hxy]
      model_div := by
        intro x y _hy
        refine ⟨0, ?_, ?_⟩
        · simpa using hu
        · ring
      model_sqrt := by
        intro x _hx
        refine ⟨0, ?_, ?_⟩
        · simpa using hu
        · ring }

/-- The trailing scalar block whose Method 2 inverse is `X22 = [2]`. -/
noncomputable def ch14ext_method2B_exec_L22 : Fin 1 → Fin 1 → ℝ :=
  ![![(1 / 2 : ℝ)]]

/-- The concrete Method 2 loop computes the advertised trailing inverse
    `X22 = [2]` under the same selective model. -/
theorem ch14ext_method2B_exec_X22_from_method2 (u : ℝ) (hu : 0 ≤ u) :
    ch14ext_method2Inv 1 (ch14ext_method2B_selectiveModel u hu)
        ch14ext_method2B_exec_L22 = ch14ext_method2B_X22 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [ch14ext_method2Inv_diag_val, ch14ext_method2B_exec_L22,
    ch14ext_method2B_X22, ch14ext_method2B_selectiveModel]

/-- For `t > 1`, the concrete Method 2 loop computes
    `X11 = [[1,0],[t,1]]` from `L11 = [[1,0],[-t,1]]` under the same selective
    model.  Thus both diagonal blocks in the absolute-budget example are actual
    Method 2 outputs, not supplied inverse certificates. -/
theorem ch14ext_method2B_exec_X11_from_method2 (u : ℝ) (hu : 0 ≤ u) (t : ℝ)
    (ht : 1 < t) :
    ch14ext_method2Inv 2 (ch14ext_method2B_selectiveModel u hu)
        (ch14ext_method2B_L11 t) = ch14ext_method2B_X11 t := by
  have hneg : -t ≠ 1 := by linarith
  ext i j
  fin_cases i <;> fin_cases j
  · simp [ch14ext_method2Inv_diag_val, ch14ext_method2B_L11,
      ch14ext_method2B_X11, ch14ext_method2B_selectiveModel]
  · change ch14ext_method2Inv 2 (ch14ext_method2B_selectiveModel u hu)
        (ch14ext_method2B_L11 t) (0 : Fin 2) (1 : Fin 2) = 0
    exact ch14ext_method2Inv_upper 2 (ch14ext_method2B_selectiveModel u hu)
      (ch14ext_method2B_L11 t) (0 : Fin 2) (1 : Fin 2) (by omega)
  · change ch14ext_method2Inv 2 (ch14ext_method2B_selectiveModel u hu)
        (ch14ext_method2B_L11 t) (1 : Fin 2) (0 : Fin 2) = t
    rw [ch14ext_method2Inv_below 2 (ch14ext_method2B_selectiveModel u hu)
      (ch14ext_method2B_L11 t) (1 : Fin 2) (0 : Fin 2) (by omega)]
    simp [ch14ext_method2Inv_diag_val, ch14ext_method2B_L11,
      fl_dotProduct, Fin.foldl_succ, ch14ext_method2B_selectiveModel, hneg]
  · simp [ch14ext_method2Inv_diag_val, ch14ext_method2B_L11,
      ch14ext_method2B_X11, ch14ext_method2B_selectiveModel]

/-- Lower-left block used by the rounded execution.  Multiplication by
    `X22 = [2]` is exact in the selective model and yields `[0, 1]`. -/
noncomputable def ch14ext_method2B_exec_L21 : Fin 1 → Fin 2 → ℝ :=
  ![![0, (1 / 2 : ℝ)]]

/-- First Method 2B block product, computed by `fl_matMul`. -/
noncomputable def ch14ext_method2B_exec_temp (u : ℝ) (hu : 0 ≤ u) :
    Fin 1 → Fin 2 → ℝ :=
  fl_matMul (ch14ext_method2B_selectiveModel u hu) 1 1 2
    ch14ext_method2B_X22 ch14ext_method2B_exec_L21

/-- Actual Method 2B off-diagonal update: two rounded block products followed
    by exact sign negation, as in equation (14.14). -/
noncomputable def ch14ext_method2B_exec_X21hat (u : ℝ) (hu : 0 ≤ u) (t : ℝ) :
    Fin 1 → Fin 2 → ℝ :=
  fun i j =>
    -fl_matMul (ch14ext_method2B_selectiveModel u hu) 1 2 2
      (ch14ext_method2B_exec_temp u hu) (ch14ext_method2B_X11 t) i j

/-- The fixed execution is definitionally the corresponding specialization of
    the general two-`fl_matMul` update. -/
theorem ch14ext_method2B_exec_X21hat_eq_flUpdate (u : ℝ) (hu : 0 ≤ u) (t : ℝ) :
    ch14ext_method2B_exec_X21hat u hu t =
      ch14ext_method2B_flUpdate (ch14ext_method2B_selectiveModel u hu)
        ch14ext_method2B_X22 ch14ext_method2B_exec_L21
        (ch14ext_method2B_X11 t) := rfl

/-- The first rounded block product is exactly `[0, 1]`. -/
theorem ch14ext_method2B_exec_temp_eq (u : ℝ) (hu : 0 ≤ u) :
    ch14ext_method2B_exec_temp u hu = ![![0, 1]] := by
  ext i j
  fin_cases i
  fin_cases j
  · simp [ch14ext_method2B_exec_temp, ch14ext_method2B_exec_L21,
      ch14ext_method2B_X22, fl_matMul, fl_matVec, fl_dotProduct,
      ch14ext_method2B_selectiveModel]
  · simp [ch14ext_method2B_exec_temp, ch14ext_method2B_exec_L21,
      ch14ext_method2B_X22, fl_matMul, fl_matVec, fl_dotProduct,
      ch14ext_method2B_selectiveModel]

/-- For `t ≠ 1`, the actual second block product rounds only its `(0,1)`
    output, so the computed update is `[-t, -(1+u)]`. -/
theorem ch14ext_method2B_exec_X21hat_eq (u : ℝ) (hu : 0 ≤ u) (t : ℝ)
    (ht : t ≠ 1) :
    ch14ext_method2B_exec_X21hat u hu t = ![![-t, -(1 + u)]] := by
  unfold ch14ext_method2B_exec_X21hat
  rw [ch14ext_method2B_exec_temp_eq u hu]
  ext i j
  fin_cases i
  fin_cases j
  · simp [ch14ext_method2B_X11, fl_matMul, fl_matVec, fl_dotProduct,
      Fin.foldl_succ, ch14ext_method2B_selectiveModel, ht]
  · simp [ch14ext_method2B_X11, fl_matMul, fl_matVec, fl_dotProduct,
      Fin.foldl_succ, ch14ext_method2B_selectiveModel]

/-- Equation (14.14) for the actual execution: its block-update perturbation is
    exactly `[0, -u]`. -/
theorem ch14ext_method2B_exec_delta_eq (u : ℝ) (hu : 0 ≤ u) (t : ℝ)
    (ht : t ≠ 1) :
    higham14_method2BBlockUpdateDelta
        (ch14ext_method2B_exec_X21hat u hu t)
        ch14ext_method2B_X22 ch14ext_method2B_exec_L21
        (ch14ext_method2B_X11 t) = ![![0, -u]] := by
  rw [ch14ext_method2B_exec_X21hat_eq u hu t ht]
  ext i j
  fin_cases i
  fin_cases j
  · simp [higham14_method2BBlockUpdateDelta,
      higham14_method2BBlockUpdateExact, rectMatMul, Fin.sum_univ_two,
      ch14ext_method2B_X22, ch14ext_method2B_exec_L21,
      ch14ext_method2B_X11]
  · simp [higham14_method2BBlockUpdateDelta,
      higham14_method2BBlockUpdateExact, rectMatMul, Fin.sum_univ_two,
      ch14ext_method2B_X22, ch14ext_method2B_exec_L21,
      ch14ext_method2B_X11]

/-- The actual two-`fl_matMul` execution satisfies the source-facing (14.14)
    update package with local error budget `u` and unit envelope. -/
theorem ch14ext_method2B_exec_spec (u : ℝ) (hu : 0 ≤ u) (t : ℝ)
    (ht : t ≠ 1) :
    Method2BBlockUpdateSpec
      (ch14ext_method2B_exec_X21hat u hu t)
      ch14ext_method2B_X22 ch14ext_method2B_exec_L21
      (ch14ext_method2B_X11 t) u (fun _ _ => 1) := by
  refine
    { update_decomposition :=
        higham14_eq14_14_method2B_block_update_decomposition
          (ch14ext_method2B_exec_X21hat u hu t)
          ch14ext_method2B_X22 ch14ext_method2B_exec_L21
          (ch14ext_method2B_X11 t)
      delta_bound := ?_ }
  intro i j
  rw [ch14ext_method2B_exec_delta_eq u hu t ht]
  fin_cases i
  fin_cases j
  · simp [hu]
  · simp [abs_of_nonneg hu]

/-- The actual rounded Method 2B execution has `(0,0)` off-diagonal left
    residual entry exactly `u*t`. -/
theorem ch14ext_method2B_exec_residual_value (u : ℝ) (hu : 0 ≤ u) (t : ℝ)
    (ht : t ≠ 1) :
    rectMatMul (ch14ext_method2B_exec_X21hat u hu t)
        (ch14ext_method2B_L11 t) (0 : Fin 1) (0 : Fin 2) +
      rectMatMul ch14ext_method2B_X22 ch14ext_method2B_exec_L21
        (0 : Fin 1) (0 : Fin 2) = u * t := by
  rw [ch14ext_method2B_exec_X21hat_eq u hu t ht]
  simp [rectMatMul, Fin.sum_univ_two, ch14ext_method2B_L11,
    ch14ext_method2B_X22, ch14ext_method2B_exec_L21]
  ring

/-- At the same entry, the off-diagonal block of the source scale
    `|Xhat| |L|` is `(2 + u) * t`.  This includes both
    `|X21hat| |L11|` and `|X22| |L21|`. -/
theorem ch14ext_method2B_exec_source_scale_value (u : ℝ) (hu : 0 ≤ u) (t : ℝ)
    (ht : 1 < t) :
    rectMatMul
        (fun i k => |ch14ext_method2B_exec_X21hat u hu t i k|)
        (fun k j => |ch14ext_method2B_L11 t k j|)
        (0 : Fin 1) (0 : Fin 2) +
      rectMatMul
        (fun i k => |ch14ext_method2B_X22 i k|)
        (fun k j => |ch14ext_method2B_exec_L21 k j|)
        (0 : Fin 1) (0 : Fin 2) = (2 + u) * t := by
  rw [ch14ext_method2B_exec_X21hat_eq u hu t (ne_of_gt ht)]
  have ht0 : 0 < t := lt_trans one_pos ht
  have h1u : 0 ≤ 1 + u := by linarith
  simp [rectMatMul, Fin.sum_univ_two, ch14ext_method2B_L11,
    ch14ext_method2B_X22, ch14ext_method2B_exec_L21,
    abs_of_pos ht0]
  rw [show -u + -1 = -(1 + u) by ring, abs_neg, abs_of_nonneg h1u]
  ring

/-- The fixed execution satisfies, rather than refutes, the coefficient-one
    source-shaped residual inequality at its selected entry. -/
theorem ch14ext_method2B_exec_selected_entry_satisfies_source_bound
    (u : ℝ) (hu : 0 ≤ u) (t : ℝ) (ht : 1 < t) :
    |rectMatMul (ch14ext_method2B_exec_X21hat u hu t)
          (ch14ext_method2B_L11 t) (0 : Fin 1) (0 : Fin 2) +
        rectMatMul ch14ext_method2B_X22 ch14ext_method2B_exec_L21
          (0 : Fin 1) (0 : Fin 2)| ≤
      u *
        (rectMatMul
            (fun i k => |ch14ext_method2B_exec_X21hat u hu t i k|)
            (fun k j => |ch14ext_method2B_L11 t k j|)
            (0 : Fin 1) (0 : Fin 2) +
          rectMatMul
            (fun i k => |ch14ext_method2B_X22 i k|)
            (fun k j => |ch14ext_method2B_exec_L21 k j|)
            (0 : Fin 1) (0 : Fin 2)) := by
  rw [ch14ext_method2B_exec_residual_value u hu t (ne_of_gt ht),
    ch14ext_method2B_exec_source_scale_value u hu t ht]
  have ht0 : 0 ≤ t := le_of_lt (lt_trans one_pos ht)
  rw [abs_of_nonneg (mul_nonneg hu ht0)]
  have hone : (1 : ℝ) ≤ 2 + u := by linarith
  have hu_le : u ≤ u * (2 + u) := by
    simpa using mul_le_mul_of_nonneg_left hone hu
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right hu_le ht0

/-- **Equation (14.14), implementation-level absolute-budget example.**

    For every positive unit roundoff `u` and conditioning parameter `t > 1`,
    the actual two-`fl_matMul` Method 2B update in the selective standard model
    violates the entrywise residual budget `u`: its `(0,0)` residual is `u*t`.
    No product error or propagated-residual hypothesis is assumed.  This still
    does not violate the matrix-scaled source bound (14.8). -/
theorem ch14ext_method2B_fp_offdiag_residual_exceeds_absolute_u_budget
    (u t : ℝ) (hu : 0 < u) (ht : 1 < t) :
    ¬ (∀ (i : Fin 1) (j : Fin 2),
        |rectMatMul (ch14ext_method2B_exec_X21hat u (le_of_lt hu) t)
              (ch14ext_method2B_L11 t) i j +
            rectMatMul ch14ext_method2B_X22 ch14ext_method2B_exec_L21 i j| ≤ u) := by
  intro hsmall
  have hentry := hsmall (0 : Fin 1) (0 : Fin 2)
  rw [ch14ext_method2B_exec_residual_value u (le_of_lt hu) t (ne_of_gt ht)] at hentry
  have hut : 0 < u * t := mul_pos hu (lt_trans one_pos ht)
  rw [abs_of_pos hut] at hentry
  nlinarith [hu, ht]

end NumStability.Ch14Ext
