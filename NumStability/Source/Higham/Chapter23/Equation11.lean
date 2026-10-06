/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter23.BilinearAlgorithm
import NumStability.Source.Higham.Chapter23.GammaAsymptotics

namespace NumStability

open scoped BigOperators Topology
open Filter

/-!
# Higham Chapter 23, equation (23.11)

This module formalizes Miller's finite bilinear polynomial circuit, its
literal rounded evaluation, tensor-weighted first-order coefficient, and the
componentwise and normwise bounds corresponding to equation (23.11).
-/

/-! ## Miller's finite bilinear polynomial circuit (23.11) -/

/-- Flatten a square matrix in the same fixed order used by the rounded
linear forms below. -/
def higham23MillerFlatten {h : ℕ}
    (A : Matrix (Fin h) (Fin h) ℝ) (q : Fin (h * h)) : ℝ :=
  A (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

def higham23MillerFlattenU {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (k : Fin t)
    (q : Fin (h * h)) : ℝ :=
  alg.U k (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

def higham23MillerFlattenV {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (k : Fin t)
    (q : Fin (h * h)) : ℝ :=
  alg.V k (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

noncomputable def higham23MillerUWeight {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (k : Fin t) : ℝ :=
  ∑ q : Fin (h * h), |higham23MillerFlattenU alg k q|

noncomputable def higham23MillerVWeight {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (k : Fin t) : ℝ :=
  ∑ q : Fin (h * h), |higham23MillerFlattenV alg k q|

noncomputable def higham23MillerExactU {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) : ℝ :=
  ∑ q : Fin (h * h),
    higham23MillerFlattenU alg k q * higham23MillerFlatten A q

noncomputable def higham23MillerExactV {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (B : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) : ℝ :=
  ∑ q : Fin (h * h),
    higham23MillerFlattenV alg k q * higham23MillerFlatten B q

/-- The literal rounded linear forms: coefficient multiplications and their
left-to-right accumulation are the library's actual `fl_dotProduct`. -/
noncomputable def higham23MillerFlU (fp : FPModel) {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) : ℝ :=
  fl_dotProduct fp (h * h) (higham23MillerFlattenU alg k)
    (higham23MillerFlatten A)

noncomputable def higham23MillerFlV (fp : FPModel) {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (B : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) : ℝ :=
  fl_dotProduct fp (h * h) (higham23MillerFlattenV alg k)
    (higham23MillerFlatten B)

noncomputable def higham23MillerExactProduct {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) : ℝ :=
  higham23MillerExactU alg A k * higham23MillerExactV alg B k

noncomputable def higham23MillerFlProduct (fp : FPModel) {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) : ℝ :=
  fp.fl_mul (higham23MillerFlU fp alg A k) (higham23MillerFlV fp alg B k)

noncomputable def higham23MillerExactEvaluate {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j ↦ ∑ k : Fin t, alg.W i j k * higham23MillerExactProduct alg A B k

/-- Literal rounded bilinear circuit: rounded input linear forms, one rounded
multiplication for each bilinear product, and one rounded reconstruction dot
product for every output entry. -/
noncomputable def higham23MillerFlEvaluate (fp : FPModel) {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j ↦ fl_dotProduct fp t (alg.W i j)
    (higham23MillerFlProduct fp alg A B)

theorem higham23_miller_flat_sum {h : ℕ} (f : Fin h → Fin h → ℝ) :
    (∑ q : Fin (h * h),
      f (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) =
      ∑ i : Fin h, ∑ j : Fin h, f i j := by
  have he : (∑ p : Fin h × Fin h, f p.1 p.2) =
      ∑ q : Fin (h * h),
        f (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 := by
    simpa using (Equiv.sum_comp finProdFinEquiv
      (fun q : Fin (h * h) ↦
        f (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2))
  calc
    (∑ q : Fin (h * h),
        f (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) =
        ∑ p : Fin h × Fin h, f p.1 p.2 := he.symm
    _ = ∑ i : Fin h, ∑ j : Fin h, f i j := Fintype.sum_prod_type _

theorem higham23_millerExactEvaluate_eq_bilinearEvaluate {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) :
    higham23MillerExactEvaluate alg A B = higham23BilinearEvaluate alg A B := by
  funext i j
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  unfold higham23MillerExactProduct higham23MillerExactU
    higham23MillerExactV higham23MillerFlattenU
    higham23MillerFlattenV higham23MillerFlatten
    higham23BilinearProduct
  have hU := higham23_miller_flat_sum (h := h)
    (fun x y ↦ alg.U k x y * A x y)
  have hV := higham23_miller_flat_sum (h := h)
    (fun x y ↦ alg.V k x y * B x y)
  rw [hU, hV]

theorem higham23_millerExactEvaluate_correct {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (halg : alg.IsCorrect)
    (A B : Matrix (Fin h) (Fin h) ℝ) :
    higham23MillerExactEvaluate alg A B = A * B := by
  rw [higham23_millerExactEvaluate_eq_bilinearEvaluate]
  exact halg A B

private theorem higham23_miller_linearForm_error
    (fp : FPModel) (n : ℕ) (hvalid : gammaValid fp n)
    (c x : Fin n → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hx : ∀ q, |x q| ≤ a) :
    |(∑ q : Fin n, c q * x q) - fl_dotProduct fp n c x| ≤
      gamma fp n * (∑ q : Fin n, |c q|) * a := by
  have hd := dotProduct_error_bound fp n c x hvalid
  have hs : (∑ q : Fin n, |c q| * |x q|) ≤
      (∑ q : Fin n, |c q|) * a := by
    calc
      (∑ q : Fin n, |c q| * |x q|) ≤ ∑ q : Fin n, |c q| * a := by
        apply Finset.sum_le_sum
        intro q _
        exact mul_le_mul_of_nonneg_left (hx q) (abs_nonneg _)
      _ = (∑ q : Fin n, |c q|) * a := by rw [Finset.sum_mul]
  calc
    |(∑ q : Fin n, c q * x q) - fl_dotProduct fp n c x| =
        |fl_dotProduct fp n c x - ∑ q : Fin n, c q * x q| := abs_sub_comm _ _
    _ ≤ gamma fp n * ∑ q : Fin n, |c q| * |x q| := hd
    _ ≤ gamma fp n * ((∑ q : Fin n, |c q|) * a) :=
      mul_le_mul_of_nonneg_left hs (gamma_nonneg fp hvalid)
    _ = _ := by ring

private theorem higham23_miller_linearForm_exact_abs
    (n : ℕ) (c x : Fin n → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hx : ∀ q, |x q| ≤ a) :
    |∑ q : Fin n, c q * x q| ≤ (∑ q : Fin n, |c q|) * a := by
  calc
    |∑ q : Fin n, c q * x q| ≤ ∑ q : Fin n, |c q * x q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q : Fin n, |c q| * a := by
      apply Finset.sum_le_sum
      intro q _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hx q) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

private theorem higham23_miller_linearForm_fl_abs
    (fp : FPModel) (n : ℕ) (hvalid : gammaValid fp n)
    (c x : Fin n → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hx : ∀ q, |x q| ≤ a) :
    |fl_dotProduct fp n c x| ≤
      (1 + gamma fp n) * (∑ q : Fin n, |c q|) * a := by
  have he := higham23_miller_linearForm_error fp n hvalid c x a ha hx
  have hn := higham23_miller_linearForm_exact_abs n c x a ha hx
  calc
    |fl_dotProduct fp n c x| ≤
        |∑ q : Fin n, c q * x q| +
          |(∑ q : Fin n, c q * x q) - fl_dotProduct fp n c x| := by
      have h := abs_add_le (∑ q : Fin n, c q * x q)
        (fl_dotProduct fp n c x - ∑ q : Fin n, c q * x q)
      rw [show (∑ q : Fin n, c q * x q) +
        (fl_dotProduct fp n c x - ∑ q : Fin n, c q * x q) =
          fl_dotProduct fp n c x by ring] at h
      simpa [abs_sub_comm] using h
    _ ≤ (∑ q : Fin n, |c q|) * a +
        gamma fp n * (∑ q : Fin n, |c q|) * a := add_le_add hn he
    _ = _ := by ring

noncomputable def higham23MillerProductCore (g u : ℝ) : ℝ :=
  g + (1 + g) * g + u * (1 + g) ^ 2

noncomputable def higham23MillerProductNormCore (g u : ℝ) : ℝ :=
  (1 + u) * (1 + g) ^ 2

noncomputable def higham23MillerCore (g gt u : ℝ) : ℝ :=
  higham23MillerProductCore g u +
    gt * higham23MillerProductNormCore g u

private theorem higham23_miller_product_error
    (fp : FPModel) (g wx wy a b : ℝ)
    (hg : 0 ≤ g) (hwx : 0 ≤ wx) (hwy : 0 ≤ wy)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (x xhat y yhat : ℝ)
    (hx : |x| ≤ wx * a) (hy : |y| ≤ wy * b)
    (hex : |x - xhat| ≤ g * wx * a)
    (hey : |y - yhat| ≤ g * wy * b)
    (hxhat : |xhat| ≤ (1 + g) * wx * a)
    (hyhat : |yhat| ≤ (1 + g) * wy * b) :
    |x * y - fp.fl_mul xhat yhat| ≤
      higham23MillerProductCore g fp.u * wx * wy * a * b := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul xhat yhat
  have hinput : |x * y - xhat * yhat| ≤
      g * wx * a * (wy * b) + ((1 + g) * wx * a) * (g * wy * b) := by
    calc
      |x * y - xhat * yhat| = |(x - xhat) * y + xhat * (y - yhat)| := by ring_nf
      _ ≤ |x - xhat| * |y| + |xhat| * |y - yhat| := by
        simpa [abs_mul] using abs_add_le ((x - xhat) * y) (xhat * (y - yhat))
      _ ≤ g * wx * a * (wy * b) + ((1 + g) * wx * a) * (g * wy * b) := by
        exact add_le_add
          (mul_le_mul hex hy (abs_nonneg _) (by positivity))
          (mul_le_mul hxhat hey (abs_nonneg _) (by positivity))
  have hlocal : |xhat * yhat - fp.fl_mul xhat yhat| ≤
      fp.u * ((1 + g) * wx * a) * ((1 + g) * wy * b) := by
    rw [hfl, show xhat * yhat - xhat * yhat * (1 + δ) =
      -(xhat * yhat) * δ by ring, abs_mul, abs_neg, abs_mul]
    calc
      |xhat| * |yhat| * |δ| ≤
          ((1 + g) * wx * a) * ((1 + g) * wy * b) * fp.u := by
        exact mul_le_mul
          (mul_le_mul hxhat hyhat (abs_nonneg _) (by positivity))
          hδ (abs_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    |x * y - fp.fl_mul xhat yhat| ≤
        |x * y - xhat * yhat| + |xhat * yhat - fp.fl_mul xhat yhat| := by
      have h := abs_add_le (x * y - xhat * yhat)
        (xhat * yhat - fp.fl_mul xhat yhat)
      convert h using 1 <;> ring
    _ ≤ _ := by
      rw [higham23MillerProductCore]
      nlinarith

private theorem higham23_miller_product_fl_abs
    (fp : FPModel) (g wx wy a b : ℝ)
    (hg : 0 ≤ g) (hwx : 0 ≤ wx) (hwy : 0 ≤ wy)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (xhat yhat : ℝ)
    (hxhat : |xhat| ≤ (1 + g) * wx * a)
    (hyhat : |yhat| ≤ (1 + g) * wy * b) :
    |fp.fl_mul xhat yhat| ≤
      higham23MillerProductNormCore g fp.u * wx * wy * a * b := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul xhat yhat
  rw [hfl, abs_mul, abs_mul]
  have hone : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ 1 + |δ| := by simpa using abs_add_le 1 δ
      _ ≤ 1 + fp.u := by linarith
  calc
    |xhat| * |yhat| * |1 + δ| ≤
        ((1 + g) * wx * a) * ((1 + g) * wy * b) * (1 + fp.u) := by
      exact mul_le_mul
        (mul_le_mul hxhat hyhat (abs_nonneg _) (by positivity))
        hone (abs_nonneg _) (by positivity)
    _ = _ := by unfold higham23MillerProductNormCore; ring

noncomputable def higham23MillerWeight {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (i j : Fin h) : ℝ :=
  ∑ k : Fin t, |alg.W i j k| *
    higham23MillerUWeight alg k * higham23MillerVWeight alg k

noncomputable def higham23MillerWeightTotal {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) : ℝ :=
  ∑ i : Fin h, ∑ j : Fin h, higham23MillerWeight alg i j

theorem higham23_miller_literalCircuit_exact_error
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b)
    (i j : Fin h) :
    |higham23MillerExactEvaluate alg A B i j -
        higham23MillerFlEvaluate fp alg A B i j| ≤
      higham23MillerCore (gamma fp (h * h)) (gamma fp t) fp.u *
        higham23MillerWeight alg i j * a * b := by
  let g := gamma fp (h * h)
  let gt := gamma fp t
  have hg : 0 ≤ g := gamma_nonneg fp hLinear
  have hgt : 0 ≤ gt := gamma_nonneg fp hOutput
  have hu1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  have hUWeight (k : Fin t) : 0 ≤ higham23MillerUWeight alg k := by
    unfold higham23MillerUWeight
    positivity
  have hVWeight (k : Fin t) : 0 ≤ higham23MillerVWeight alg k := by
    unfold higham23MillerVWeight
    positivity
  have hAflat (q : Fin (h * h)) : |higham23MillerFlatten A q| ≤ a := by
    exact hA _ _
  have hBflat (q : Fin (h * h)) : |higham23MillerFlatten B q| ≤ b := by
    exact hB _ _
  have hUexact (k : Fin t) :
      |higham23MillerExactU alg A k| ≤ higham23MillerUWeight alg k * a := by
    simpa [higham23MillerExactU, higham23MillerUWeight] using
      higham23_miller_linearForm_exact_abs (h * h)
        (higham23MillerFlattenU alg k) (higham23MillerFlatten A) a ha hAflat
  have hVexact (k : Fin t) :
      |higham23MillerExactV alg B k| ≤ higham23MillerVWeight alg k * b := by
    simpa [higham23MillerExactV, higham23MillerVWeight] using
      higham23_miller_linearForm_exact_abs (h * h)
        (higham23MillerFlattenV alg k) (higham23MillerFlatten B) b hb hBflat
  have hUerr (k : Fin t) :
      |higham23MillerExactU alg A k - higham23MillerFlU fp alg A k| ≤
        g * higham23MillerUWeight alg k * a := by
    simpa [g, higham23MillerExactU, higham23MillerFlU,
      higham23MillerUWeight] using
      higham23_miller_linearForm_error fp (h * h) hLinear
        (higham23MillerFlattenU alg k) (higham23MillerFlatten A) a ha hAflat
  have hVerr (k : Fin t) :
      |higham23MillerExactV alg B k - higham23MillerFlV fp alg B k| ≤
        g * higham23MillerVWeight alg k * b := by
    simpa [g, higham23MillerExactV, higham23MillerFlV,
      higham23MillerVWeight] using
      higham23_miller_linearForm_error fp (h * h) hLinear
        (higham23MillerFlattenV alg k) (higham23MillerFlatten B) b hb hBflat
  have hUfl (k : Fin t) :
      |higham23MillerFlU fp alg A k| ≤
        (1 + g) * higham23MillerUWeight alg k * a := by
    simpa [g, higham23MillerFlU, higham23MillerUWeight] using
      higham23_miller_linearForm_fl_abs fp (h * h) hLinear
        (higham23MillerFlattenU alg k) (higham23MillerFlatten A) a ha hAflat
  have hVfl (k : Fin t) :
      |higham23MillerFlV fp alg B k| ≤
        (1 + g) * higham23MillerVWeight alg k * b := by
    simpa [g, higham23MillerFlV, higham23MillerVWeight] using
      higham23_miller_linearForm_fl_abs fp (h * h) hLinear
        (higham23MillerFlattenV alg k) (higham23MillerFlatten B) b hb hBflat
  have hProductErr (k : Fin t) :
      |higham23MillerExactProduct alg A B k -
          higham23MillerFlProduct fp alg A B k| ≤
        higham23MillerProductCore g fp.u *
          higham23MillerUWeight alg k * higham23MillerVWeight alg k * a * b := by
    simpa [higham23MillerExactProduct, higham23MillerFlProduct] using
      higham23_miller_product_error fp g
        (higham23MillerUWeight alg k) (higham23MillerVWeight alg k) a b
        hg (hUWeight k) (hVWeight k) ha hb
        (higham23MillerExactU alg A k) (higham23MillerFlU fp alg A k)
        (higham23MillerExactV alg B k) (higham23MillerFlV fp alg B k)
        (hUexact k) (hVexact k) (hUerr k) (hVerr k) (hUfl k) (hVfl k)
  have hProductNorm (k : Fin t) :
      |higham23MillerFlProduct fp alg A B k| ≤
        higham23MillerProductNormCore g fp.u *
          higham23MillerUWeight alg k * higham23MillerVWeight alg k * a * b := by
    simpa [higham23MillerFlProduct] using
      higham23_miller_product_fl_abs fp g
        (higham23MillerUWeight alg k) (higham23MillerVWeight alg k) a b
        hg (hUWeight k) (hVWeight k) ha hb
        (higham23MillerFlU fp alg A k) (higham23MillerFlV fp alg B k)
        (hUfl k) (hVfl k)
  let mid := ∑ k : Fin t, alg.W i j k * higham23MillerFlProduct fp alg A B k
  have hProducts :
      |higham23MillerExactEvaluate alg A B i j - mid| ≤
        higham23MillerProductCore g fp.u * higham23MillerWeight alg i j * a * b := by
    unfold higham23MillerExactEvaluate
    dsimp only [mid]
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ k : Fin t, (alg.W i j k * higham23MillerExactProduct alg A B k -
          alg.W i j k * higham23MillerFlProduct fp alg A B k)| ≤
          ∑ k : Fin t, |alg.W i j k * higham23MillerExactProduct alg A B k -
            alg.W i j k * higham23MillerFlProduct fp alg A B k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin t, |alg.W i j k| *
          (higham23MillerProductCore g fp.u *
            higham23MillerUWeight alg k * higham23MillerVWeight alg k * a * b) := by
        apply Finset.sum_le_sum
        intro k _
        rw [show alg.W i j k * higham23MillerExactProduct alg A B k -
          alg.W i j k * higham23MillerFlProduct fp alg A B k =
            alg.W i j k * (higham23MillerExactProduct alg A B k -
              higham23MillerFlProduct fp alg A B k) by ring, abs_mul]
        exact mul_le_mul_of_nonneg_left (hProductErr k) (abs_nonneg _)
      _ = higham23MillerProductCore g fp.u *
          higham23MillerWeight alg i j * a * b := by
        unfold higham23MillerWeight
        calc
          (∑ k : Fin t, |alg.W i j k| *
              (higham23MillerProductCore g fp.u *
                higham23MillerUWeight alg k * higham23MillerVWeight alg k * a * b)) =
              ∑ k : Fin t, higham23MillerProductCore g fp.u *
                (|alg.W i j k| * higham23MillerUWeight alg k *
                  higham23MillerVWeight alg k) * a * b := by
            apply Finset.sum_congr rfl
            intro k _
            ring
          _ = _ := by
            rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  have hDotRaw := dotProduct_error_bound fp t (alg.W i j)
    (higham23MillerFlProduct fp alg A B) hOutput
  have hWeightedNorm :
      (∑ k : Fin t, |alg.W i j k| *
          |higham23MillerFlProduct fp alg A B k|) ≤
        higham23MillerProductNormCore g fp.u *
          higham23MillerWeight alg i j * a * b := by
    calc
      (∑ k : Fin t, |alg.W i j k| *
          |higham23MillerFlProduct fp alg A B k|) ≤
          ∑ k : Fin t, |alg.W i j k| *
            (higham23MillerProductNormCore g fp.u *
              higham23MillerUWeight alg k * higham23MillerVWeight alg k * a * b) := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hProductNorm k) (abs_nonneg _)
      _ = higham23MillerProductNormCore g fp.u *
          higham23MillerWeight alg i j * a * b := by
        unfold higham23MillerWeight
        calc
          (∑ k : Fin t, |alg.W i j k| *
              (higham23MillerProductNormCore g fp.u *
                higham23MillerUWeight alg k * higham23MillerVWeight alg k * a * b)) =
              ∑ k : Fin t, higham23MillerProductNormCore g fp.u *
                (|alg.W i j k| * higham23MillerUWeight alg k *
                  higham23MillerVWeight alg k) * a * b := by
            apply Finset.sum_congr rfl
            intro k _
            ring
          _ = _ := by
            rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  have hDot : |mid - higham23MillerFlEvaluate fp alg A B i j| ≤
      gt * higham23MillerProductNormCore g fp.u *
        higham23MillerWeight alg i j * a * b := by
    unfold higham23MillerFlEvaluate
    dsimp only [mid]
    calc
      |(∑ k : Fin t, alg.W i j k * higham23MillerFlProduct fp alg A B k) -
          fl_dotProduct fp t (alg.W i j) (higham23MillerFlProduct fp alg A B)| =
          |fl_dotProduct fp t (alg.W i j) (higham23MillerFlProduct fp alg A B) -
            ∑ k : Fin t, alg.W i j k * higham23MillerFlProduct fp alg A B k| :=
        abs_sub_comm _ _
      _ ≤ gamma fp t * (∑ k : Fin t, |alg.W i j k| *
          |higham23MillerFlProduct fp alg A B k|) := hDotRaw
      _ ≤ gamma fp t * (higham23MillerProductNormCore g fp.u *
          higham23MillerWeight alg i j * a * b) :=
        mul_le_mul_of_nonneg_left hWeightedNorm hgt
      _ = _ := by dsimp [gt]; ring
  calc
    |higham23MillerExactEvaluate alg A B i j -
        higham23MillerFlEvaluate fp alg A B i j| ≤
      |higham23MillerExactEvaluate alg A B i j - mid| +
        |mid - higham23MillerFlEvaluate fp alg A B i j| := by
      have h := abs_add_le
        (higham23MillerExactEvaluate alg A B i j - mid)
        (mid - higham23MillerFlEvaluate fp alg A B i j)
      convert h using 1 <;> ring
    _ ≤ higham23MillerProductCore g fp.u * higham23MillerWeight alg i j * a * b +
      gt * higham23MillerProductNormCore g fp.u *
        higham23MillerWeight alg i j * a * b := add_le_add hProducts hDot
    _ = _ := by unfold higham23MillerCore; dsimp [g, gt]; ring

/-- Miller's (23.11) for the fully specified finite bilinear circuit, at an
exact nonlinear radius. -/
theorem higham23_eq23_11_miller_exact
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (halg : alg.IsCorrect)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b) :
    ∀ i j,
      |(A * B) i j - higham23MillerFlEvaluate fp alg A B i j| ≤
        higham23MillerCore (gamma fp (h * h)) (gamma fp t) fp.u *
          higham23MillerWeight alg i j * a * b := by
  intro i j
  rw [← higham23_millerExactEvaluate_correct alg halg A B]
  exact higham23_miller_literalCircuit_exact_error fp alg hLinear hOutput
    A B a b ha hb hA hB i j

noncomputable def higham23MillerGammaFamily (n : ℕ) (u : ℝ) : ℝ :=
  (n : ℝ) * u + higham23GammaRemainder n u

noncomputable def higham23MillerCoreFamily (h t : ℕ) (u : ℝ) : ℝ :=
  higham23MillerCore (higham23MillerGammaFamily (h * h) u)
    (higham23MillerGammaFamily t u) u

noncomputable def higham23MillerFirstOrderCoefficient (h t : ℕ) : ℝ :=
  2 * (h * h : ℕ) + 1 + t

noncomputable def higham23MillerRemainder (h t : ℕ) (u : ℝ) : ℝ :=
  higham23MillerCoreFamily h t u -
    higham23MillerFirstOrderCoefficient h t * u

theorem higham23_millerCore_eq_family
    (fp : FPModel) (h t : ℕ)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t) :
    higham23MillerCore (gamma fp (h * h)) (gamma fp t) fp.u =
      higham23MillerCoreFamily h t fp.u := by
  rw [higham23_gamma_split fp (h * h) hLinear,
    higham23_gamma_split fp t hOutput]
  rfl

theorem higham23_millerRemainder_isBigO_u_sq (h t : ℕ) :
    (fun u : ℝ ↦ higham23MillerRemainder h t u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  let rN : ℝ → ℝ := higham23GammaRemainder (h * h)
  let rT : ℝ → ℝ := higham23GammaRemainder t
  let g : ℝ → ℝ := higham23MillerGammaFamily (h * h)
  let gt : ℝ → ℝ := higham23MillerGammaFamily t
  have hrN : rN =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) :=
    higham23_gammaRemainder_isBigO_u_sq (h * h)
  have hrT : rT =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) :=
    higham23_gammaRemainder_isBigO_u_sq t
  have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
    Asymptotics.isBigO_refl _ _
  have huOne : (fun u : ℝ ↦ u) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    continuousAt_id.isBigO_one ℝ
  have huSq : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) :=
    Asymptotics.isBigO_refl _ _
  have huSqOu : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u) := by
    simpa only [pow_two, mul_one] using hu.mul huOne
  have hg : g =O[𝓝 0] (fun u : ℝ ↦ u) := by
    have hlin := hu.const_mul_left (((h * h : ℕ) : ℝ))
    have hsum := hlin.add (hrN.trans huSqOu)
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [g, rN, higham23MillerGammaFamily]
    · exact Filter.EventuallyEq.rfl
  have hgt : gt =O[𝓝 0] (fun u : ℝ ↦ u) := by
    have hlin := hu.const_mul_left ((t : ℝ))
    have hsum := hlin.add (hrT.trans huSqOu)
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [gt, rT, higham23MillerGammaFamily]
    · exact Filter.EventuallyEq.rfl
  have hgg : (fun u : ℝ ↦ g u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hg.mul hg
  have hug : (fun u : ℝ ↦ u * g u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hu.mul hg
  have hug2 : (fun u : ℝ ↦ u * g u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    have h := huOne.mul hgg
    simpa only [one_mul] using h
  let fminus : ℝ → ℝ := fun u ↦
    u + 2 * g u + 2 * u * g u + g u ^ 2 + u * g u ^ 2
  have hfminus : fminus =O[𝓝 0] (fun u : ℝ ↦ u) := by
    have h2g := hg.const_mul_left (2 : ℝ)
    have h2ug := hug.const_mul_left (2 : ℝ)
    have hquad := (h2ug.add hgg).add hug2
    have hquadOu := hquad.trans huSqOu
    have hlin := hu.add h2g
    have hsum := hlin.add hquadOu
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [fminus]
        ring
    · exact Filter.EventuallyEq.rfl
  have hgtf : (fun u : ℝ ↦ gt u * fminus u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hgt.mul hfminus
  have hsum :=
    (((hrN.const_mul_left (2 : ℝ)).add hgg).add
      (hug.const_mul_left (2 : ℝ))).add hug2
  have hsum := (hsum.add hrT).add hgtf
  apply hsum.congr'
  · exact Filter.Eventually.of_forall fun u ↦ by
      dsimp [higham23MillerRemainder, higham23MillerCoreFamily,
        higham23MillerCore, higham23MillerProductCore,
        higham23MillerProductNormCore, higham23MillerFirstOrderCoefficient,
        g, gt, rN, rT, fminus, higham23MillerGammaFamily]
      push_cast
      ring
  · exact Filter.EventuallyEq.rfl

theorem higham23_eq23_11_miller_firstOrder
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (halg : alg.IsCorrect)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b) :
    ∀ i j,
      |(A * B) i j - higham23MillerFlEvaluate fp alg A B i j| ≤
        ((higham23MillerFirstOrderCoefficient h t *
            higham23MillerWeight alg i j) * fp.u +
          higham23MillerRemainder h t fp.u *
            higham23MillerWeight alg i j) * a * b := by
  intro i j
  have hExact := higham23_eq23_11_miller_exact fp alg halg hLinear hOutput
    A B a b ha hb hA hB i j
  rw [higham23_millerCore_eq_family fp h t hLinear hOutput] at hExact
  have hsplit : higham23MillerCoreFamily h t fp.u =
      higham23MillerFirstOrderCoefficient h t * fp.u +
        higham23MillerRemainder h t fp.u := by
    unfold higham23MillerRemainder
    ring
  rw [hsplit] at hExact
  convert hExact using 1 <;> ring

theorem higham23_miller_weight_nonneg {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (i j : Fin h) :
    0 ≤ higham23MillerWeight alg i j := by
  unfold higham23MillerWeight higham23MillerUWeight higham23MillerVWeight
  positivity

theorem higham23_miller_weight_le_total {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (i j : Fin h) :
    higham23MillerWeight alg i j ≤ higham23MillerWeightTotal alg := by
  unfold higham23MillerWeightTotal
  have hj : higham23MillerWeight alg i j ≤
      ∑ y : Fin h, higham23MillerWeight alg i y := by
    exact Finset.single_le_sum
      (fun y _ ↦ higham23_miller_weight_nonneg alg i y) (Finset.mem_univ j)
  have hi : (∑ y : Fin h, higham23MillerWeight alg i y) ≤
      ∑ x : Fin h, ∑ y : Fin h, higham23MillerWeight alg x y := by
    exact Finset.single_le_sum
      (fun x _ ↦ Finset.sum_nonneg fun y _ ↦
        higham23_miller_weight_nonneg alg x y) (Finset.mem_univ i)
  exact hj.trans hi

theorem higham23_miller_normwiseRemainder_isBigO_u_sq {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) :
    (fun u : ℝ ↦ higham23MillerRemainder h t u *
      higham23MillerWeightTotal alg) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  simpa only [mul_comm] using
    (higham23_millerRemainder_isBigO_u_sq h t).const_mul_left
      (higham23MillerWeightTotal alg)

/-- The max-entry form of Miller's (23.11): an explicit algorithm-dependent
`f_n`, plus a genuinely quadratic remainder, for the literal rounded
polynomial circuit above. -/
theorem higham23_eq23_11_miller_normwise
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (halg : alg.IsCorrect)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b) :
    ∀ i j,
      |(A * B) i j - higham23MillerFlEvaluate fp alg A B i j| ≤
        ((higham23MillerFirstOrderCoefficient h t *
            higham23MillerWeightTotal alg) * fp.u +
          higham23MillerRemainder h t fp.u *
            higham23MillerWeightTotal alg) * a * b := by
  intro i j
  have hEntry := higham23_eq23_11_miller_firstOrder fp alg halg hLinear hOutput
    A B a b ha hb hA hB i j
  let q := higham23MillerWeight alg i j
  let Q := higham23MillerWeightTotal alg
  let c := higham23MillerFirstOrderCoefficient h t
  let R := higham23MillerRemainder h t fp.u
  have hqQ : q ≤ Q := higham23_miller_weight_le_total alg i j
  have hcoreNonneg : 0 ≤ c * fp.u + R := by
    have heq : c * fp.u + R = higham23MillerCoreFamily h t fp.u := by
      dsimp [c, R, higham23MillerRemainder]
      ring
    rw [heq, ← higham23_millerCore_eq_family fp h t hLinear hOutput]
    unfold higham23MillerCore higham23MillerProductCore
      higham23MillerProductNormCore
    have hg := gamma_nonneg fp hLinear
    have hgt := gamma_nonneg fp hOutput
    have hu : 0 ≤ fp.u := fp.u_nonneg
    have hg1 : 0 ≤ 1 + gamma fp (h * h) := by linarith
    have hu1 : 0 ≤ 1 + fp.u := by linarith
    positivity
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hscale := mul_le_mul_of_nonneg_left hqQ hcoreNonneg
  have hscale' := mul_le_mul_of_nonneg_right hscale hab
  apply le_trans hEntry
  change ((c * q) * fp.u + R * q) * a * b ≤
    ((c * Q) * fp.u + R * Q) * a * b
  calc
    ((c * q) * fp.u + R * q) * a * b =
        (c * fp.u + R) * q * (a * b) := by ring
    _ ≤ (c * fp.u + R) * Q * (a * b) := hscale'
    _ = ((c * Q) * fp.u + R * Q) * a * b := by ring

end NumStability
