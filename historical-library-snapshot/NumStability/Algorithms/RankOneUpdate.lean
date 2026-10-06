-- Algorithms/RankOneUpdate.lean
--
-- Higham Chapter 3, Lemma 3.9: floating-point rank-1 update.

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators

/-!
# Rank-One Update

This file formalizes the componentwise and normwise error bounds from Higham
Chapter 3, Lemma 3.9 for the update

`y = (I - a b^T) x = x - a * (b^T x)`.
-/

/-- Exact rank-one update `x - a * (b^T x)`. -/
noncomputable def rankOneUpdateExact (n : ℕ)
    (a b x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i - a i * (∑ j : Fin n, b j * x j)

/-- Floating-point rank-one update modeled as
`t = fl_dotProduct b x; w_i = fl_mul a_i t; y_i = fl_sub x_i w_i`. -/
noncomputable def fl_rankOneUpdate (fp : FPModel) (n : ℕ)
    (a b x : Fin n → ℝ) : Fin n → ℝ :=
  let t := fl_dotProduct fp n b x
  fun i => fp.fl_sub (x i) (fp.fl_mul (a i) t)

/-- Componentwise source budget `(I + |a||b^T|)|x|`. -/
noncomputable def rankOneUpdateAbsBudget (n : ℕ)
    (a b x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => |x i| + |a i| * ∑ j : Fin n, |b j| * |x j|

/-- Scalar gamma coefficient used in the proof of Lemma 3.9:
`gamma_n + u(1+gamma_n)` from the computed `a*(b^T x)` step, followed by one
more subtraction rounding, is bounded by `gamma_{n+3}`. -/
theorem rankOneUpdate_scalar_coeff_le_gamma (fp : FPModel) (n : ℕ)
    (hγ : gammaValid fp (n + 3)) :
    (gamma fp n + fp.u * (1 + gamma fp n)) +
        fp.u * (1 + (gamma fp n + fp.u * (1 + gamma fp n))) ≤
      gamma fp (n + 3) := by
  let C : ℝ := gamma fp n + fp.u * (1 + gamma fp n)
  let D : ℝ := C + fp.u * (1 + C)
  have hγn_valid : gammaValid fp n := gammaValid_mono fp (by omega) hγ
  have hγ1_valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hγ
  have hγn1_valid : gammaValid fp (n + 1) := gammaValid_mono fp (by omega) hγ
  have hγn2_valid : gammaValid fp (n + 2) := gammaValid_mono fp (by omega) hγ
  have hγn_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hγn_valid
  have hγ1_nonneg : 0 ≤ gamma fp 1 := gamma_nonneg fp hγ1_valid
  have hu_abs_gamma1 : |fp.u| ≤ gamma fp 1 := by
    simpa [abs_of_nonneg fp.u_nonneg] using u_le_gamma fp one_pos hγ1_valid
  have hγn_abs : |gamma fp n| ≤ gamma fp n := by
    simp [abs_of_nonneg hγn_nonneg]
  obtain ⟨θ1, hθ1, hprod1⟩ :=
    gamma_mul fp n 1 (gamma fp n) fp.u hγn_abs hu_abs_gamma1 hγn1_valid
  have hC_eq : C = θ1 := by
    have hC_prod : C = (1 + gamma fp n) * (1 + fp.u) - 1 := by
      simp [C]
      ring
    rw [hC_prod]
    linarith
  have hC_nonneg : 0 ≤ C := by
    simp [C]
    nlinarith [fp.u_nonneg, hγn_nonneg]
  have hC_abs : |C| ≤ gamma fp (n + 1) := by
    rw [hC_eq]
    exact hθ1
  obtain ⟨θ2, hθ2, hprod2⟩ :=
    gamma_mul fp (n + 1) 1 C fp.u hC_abs hu_abs_gamma1 hγn2_valid
  have hD_eq : D = θ2 := by
    have hD_prod : D = (1 + C) * (1 + fp.u) - 1 := by
      simp [D]
      ring
    rw [hD_prod]
    linarith
  have hD_nonneg : 0 ≤ D := by
    simp [D]
    nlinarith [fp.u_nonneg, hC_nonneg]
  have hD_le_n2 : D ≤ gamma fp (n + 2) := by
    rw [hD_eq]
    have hθ2_nonneg : 0 ≤ θ2 := by rwa [← hD_eq]
    simpa [abs_of_nonneg hθ2_nonneg] using hθ2
  have hmono : gamma fp (n + 2) ≤ gamma fp (n + 3) :=
    gamma_mono fp (by omega) hγ
  exact le_trans hD_le_n2 hmono

/-- The unit roundoff is bounded by the same final `gamma_{n+3}` coefficient
used in Lemma 3.9. -/
theorem rankOneUpdate_u_le_gamma (fp : FPModel) (n : ℕ)
    (hγ : gammaValid fp (n + 3)) :
    fp.u ≤ gamma fp (n + 3) :=
  u_le_gamma fp (by omega) hγ

/-- **Higham Chapter 3, Lemma 3.9, componentwise bound.**

For the concrete routine `fl(x - a(b^T x))`, implemented as a rounded dot
product, rounded scalar-vector multiply, and componentwise rounded subtraction,
the error satisfies

`|Delta y| <= gamma_{n+3} (I + |a||b^T|)|x|`.
-/
theorem fl_rankOneUpdate_componentwise_error_bound (fp : FPModel) (n : ℕ)
    (a b x : Fin n → ℝ) (hγ : gammaValid fp (n + 3)) :
    ∀ i : Fin n,
      |fl_rankOneUpdate fp n a b x i - rankOneUpdateExact n a b x i| ≤
        gamma fp (n + 3) * rankOneUpdateAbsBudget n a b x i := by
  intro i
  let t : ℝ := ∑ j : Fin n, b j * x j
  let th : ℝ := fl_dotProduct fp n b x
  let S : ℝ := ∑ j : Fin n, |b j| * |x j|
  let wh : ℝ := fp.fl_mul (a i) th
  let w : ℝ := a i * t
  let C : ℝ := gamma fp n + fp.u * (1 + gamma fp n)
  let D : ℝ := C + fp.u * (1 + C)
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hγ
  have hγn_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hγN_nonneg : 0 ≤ gamma fp (n + 3) := gamma_nonneg fp hγ
  have hS_nonneg : 0 ≤ S :=
    Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have ht_err : |th - t| ≤ gamma fp n * S := by
    simpa [t, th, S] using dotProduct_error_bound fp n b x hn
  have ht_abs : |t| ≤ S := by
    calc
      |t| = |∑ j : Fin n, b j * x j| := rfl
      _ ≤ ∑ j : Fin n, |b j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = S := by
        simp [S, abs_mul]
  obtain ⟨δm, hδm, hmul⟩ := fp.model_mul (a i) th
  have hδm_abs_one : |1 + δm| ≤ 1 + fp.u := by
    calc
      |1 + δm| ≤ |(1 : ℝ)| + |δm| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδm 1
  have hwhat_err : |wh - w| ≤ C * (|a i| * S) := by
    have hrewrite : wh - w =
        a i * (th - t) * (1 + δm) + a i * t * δm := by
      simp [wh, w, hmul]
      ring
    rw [hrewrite]
    calc
      |a i * (th - t) * (1 + δm) + a i * t * δm|
          ≤ |a i * (th - t) * (1 + δm)| + |a i * t * δm| :=
            abs_add_le _ _
      _ = |a i| * |th - t| * |1 + δm| + |a i| * |t| * |δm| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul]
      _ ≤ |a i| * (gamma fp n * S) * (1 + fp.u) +
            |a i| * S * fp.u := by
        apply add_le_add
        · simpa [mul_assoc] using mul_le_mul_of_nonneg_left
            (mul_le_mul ht_err hδm_abs_one
              (abs_nonneg _) (mul_nonneg hγn_nonneg hS_nonneg))
            (abs_nonneg _)
        · simpa [mul_assoc] using mul_le_mul_of_nonneg_left
            (mul_le_mul ht_abs hδm (abs_nonneg _) hS_nonneg)
            (abs_nonneg _)
      _ = C * (|a i| * S) := by
        simp [C]
        ring
  have hwhat_abs : |wh| ≤ (1 + C) * (|a i| * S) := by
    calc
      |wh| ≤ |w| + |wh - w| := by
        have hwh : wh = w + (wh - w) := by ring
        calc
          |wh| = |w + (wh - w)| := congrArg abs hwh
          _ ≤ |w| + |wh - w| := abs_add_le w (wh - w)
      _ ≤ |a i| * S + C * (|a i| * S) := by
        have hw_abs : |w| ≤ |a i| * S := by
          simp [w, abs_mul]
          exact mul_le_mul_of_nonneg_left ht_abs (abs_nonneg _)
        exact add_le_add hw_abs hwhat_err
      _ = (1 + C) * (|a i| * S) := by ring
  obtain ⟨δs, hδs, hsub⟩ := fp.model_sub (x i) wh
  have hfinal_rewrite :
      fl_rankOneUpdate fp n a b x i - rankOneUpdateExact n a b x i =
        -(wh - w) + (x i - wh) * δs := by
    simp [fl_rankOneUpdate, rankOneUpdateExact, th, wh, w, t, hsub]
    ring
  have hfinal :
      |fl_rankOneUpdate fp n a b x i - rankOneUpdateExact n a b x i| ≤
        fp.u * |x i| + D * (|a i| * S) := by
    rw [hfinal_rewrite]
    calc
      |-(wh - w) + (x i - wh) * δs|
          ≤ |wh - w| + |(x i - wh) * δs| := by
            calc
              |-(wh - w) + (x i - wh) * δs|
                  ≤ |-(wh - w)| + |(x i - wh) * δs| :=
                    abs_add_le _ _
              _ = |wh - w| + |(x i - wh) * δs| := by rw [abs_neg]
      _ = |wh - w| + |x i - wh| * |δs| := by rw [abs_mul]
      _ ≤ |wh - w| + (|x i| + |wh|) * fp.u := by
        have hxiwh : |x i - wh| ≤ |x i| + |wh| := by
          calc
            |x i - wh| = |x i + -wh| := by ring_nf
            _ ≤ |x i| + |-wh| := abs_add_le _ _
            _ = |x i| + |wh| := by rw [abs_neg]
        have hterm := mul_le_mul hxiwh hδs (abs_nonneg _)
          (add_nonneg (abs_nonneg _) (abs_nonneg _))
        exact add_le_add (le_refl _) hterm
      _ ≤ C * (|a i| * S) + (|x i| + (1 + C) * (|a i| * S)) * fp.u := by
        apply add_le_add hwhat_err
        exact mul_le_mul_of_nonneg_right
          (add_le_add (le_refl _) hwhat_abs) fp.u_nonneg
      _ = fp.u * |x i| + D * (|a i| * S) := by
        simp [D]
        ring
  have hu_le := rankOneUpdate_u_le_gamma fp n hγ
  have hD_le := rankOneUpdate_scalar_coeff_le_gamma fp n hγ
  have hbudget_nonneg : 0 ≤ rankOneUpdateAbsBudget n a b x i := by
    simp [rankOneUpdateAbsBudget]
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) hS_nonneg)
  calc
    |fl_rankOneUpdate fp n a b x i - rankOneUpdateExact n a b x i|
        ≤ fp.u * |x i| + D * (|a i| * S) := hfinal
    _ ≤ gamma fp (n + 3) * |x i| +
          gamma fp (n + 3) * (|a i| * S) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hu_le (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hD_le
            (mul_nonneg (abs_nonneg _) hS_nonneg))
    _ = gamma fp (n + 3) * rankOneUpdateAbsBudget n a b x i := by
        simp [rankOneUpdateAbsBudget, S]
        ring

/-- Norm of the source componentwise budget in Lemma 3.9. -/
theorem rankOneUpdateAbsBudget_norm2_le (n : ℕ)
    (a b x : Fin n → ℝ) :
    vecNorm2 (rankOneUpdateAbsBudget n a b x) ≤
      (1 + vecNorm2 a * vecNorm2 b) * vecNorm2 x := by
  let S : ℝ := ∑ j : Fin n, |b j| * |x j|
  have hS_nonneg : 0 ≤ S :=
    Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hS_bound : S ≤ vecNorm2 b * vecNorm2 x := by
    have hcs := abs_vecInnerProduct_le_vecNorm2_mul
      (fun j : Fin n => |b j|) (fun j : Fin n => |x j|)
    have hS_abs : |S| = S := abs_of_nonneg hS_nonneg
    simpa [S, hS_abs, vecNorm2_abs] using hcs
  have hbudget_eq :
      rankOneUpdateAbsBudget n a b x =
        fun i : Fin n => |x i| + S * |a i| := by
    ext i
    simp [rankOneUpdateAbsBudget, S, mul_comm]
  rw [hbudget_eq]
  calc
    vecNorm2 (fun i : Fin n => |x i| + S * |a i|)
        ≤ vecNorm2 (fun i : Fin n => |x i|) +
            vecNorm2 (fun i : Fin n => S * |a i|) :=
          vecNorm2_add_le _ _
    _ = vecNorm2 x + S * vecNorm2 a := by
          rw [vecNorm2_abs, vecNorm2_smul, abs_of_nonneg hS_nonneg,
            vecNorm2_abs]
    _ ≤ vecNorm2 x + (vecNorm2 b * vecNorm2 x) * vecNorm2 a := by
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_right hS_bound (vecNorm2_nonneg a))
    _ = (1 + vecNorm2 a * vecNorm2 b) * vecNorm2 x := by ring

/-- **Higham Chapter 3, Lemma 3.9, Euclidean-norm corollary.** -/
theorem fl_rankOneUpdate_error_bound_vecNorm2 (fp : FPModel) (n : ℕ)
    (a b x : Fin n → ℝ) (hγ : gammaValid fp (n + 3)) :
    vecNorm2 (fun i : Fin n =>
        fl_rankOneUpdate fp n a b x i - rankOneUpdateExact n a b x i) ≤
      gamma fp (n + 3) * (1 + vecNorm2 a * vecNorm2 b) * vecNorm2 x := by
  let γ : ℝ := gamma fp (n + 3)
  let e : Fin n → ℝ := fun i =>
    fl_rankOneUpdate fp n a b x i - rankOneUpdateExact n a b x i
  let B : Fin n → ℝ := rankOneUpdateAbsBudget n a b x
  have hγ_nonneg : 0 ≤ γ := gamma_nonneg fp hγ
  have hcomp := fl_rankOneUpdate_componentwise_error_bound fp n a b x hγ
  have hentry : ∀ i : Fin n, |e i| ≤ (fun i => γ * B i) i := by
    intro i
    simpa [e, B, γ] using hcomp i
  have hnorm_entry :
      vecNorm2 e ≤ vecNorm2 (fun i : Fin n => γ * B i) :=
    vecNorm2_le_of_abs_le e (fun i : Fin n => γ * B i) hentry
  have hscale :
      vecNorm2 (fun i : Fin n => γ * B i) = γ * vecNorm2 B := by
    rw [vecNorm2_smul, abs_of_nonneg hγ_nonneg]
  have hbudget := rankOneUpdateAbsBudget_norm2_le n a b x
  calc
    vecNorm2 (fun i : Fin n =>
        fl_rankOneUpdate fp n a b x i - rankOneUpdateExact n a b x i)
        = vecNorm2 e := rfl
    _ ≤ vecNorm2 (fun i : Fin n => γ * B i) := hnorm_entry
    _ = γ * vecNorm2 B := hscale
    _ ≤ γ * ((1 + vecNorm2 a * vecNorm2 b) * vecNorm2 x) :=
        mul_le_mul_of_nonneg_left hbudget hγ_nonneg
    _ = gamma fp (n + 3) * (1 + vecNorm2 a * vecNorm2 b) * vecNorm2 x := by
        simp [γ]
        ring

end NumStability
