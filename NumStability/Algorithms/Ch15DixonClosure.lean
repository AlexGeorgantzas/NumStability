/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/

import NumStability.Algorithms.HighamChapter10
import NumStability.Algorithms.Ch15CondEstimators
import NumStability.Algorithms.Ch15DixonProbability
import NumStability.Algorithms.TestMatrices.Higham28OrthogonalCoordinates
import Mathlib.Analysis.Matrix.Order

namespace NumStability

open MeasureTheory Set
open scoped BigOperators Matrix MatrixOrder RealInnerProductSpace

set_option maxHeartbeats 800000

theorem ch15Closure_matPow_matrix_eq_pow {n : ℕ}
    (M : Fin n → Fin n → ℝ) (k : ℕ) :
    (matPow n M k : Matrix (Fin n) (Fin n) ℝ) =
      (Matrix.of M) ^ k := by
  induction k with
  | zero =>
      ext i j
      by_cases hij : i = j <;> simp [matPow, idMatrix, hij]
  | succ k ih =>
      rw [matPow_succ, pow_succ']
      ext i j
      change (∑ p : Fin n, M i p * matPow n M k p j) =
        ∑ p : Fin n, Matrix.of M i p * (Matrix.of M ^ k) p j
      apply Finset.sum_congr rfl
      intro p _
      rw [show matPow n M k p j = (Matrix.of M ^ k) p j from
        congrFun (congrFun ih p) j]
      rfl

theorem ch15Closure_gram_symmetric {n : ℕ} (B : Fin n → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (matMul n (matTranspose B) B) := by
  intro i j
  simp only [matMul, matTranspose]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem ch15Closure_gram_pow_finitePSD {n : ℕ} (B : Fin n → Fin n → ℝ) (k : ℕ) :
    finitePSD (matPow n (matMul n (matTranspose B) B) k) := by
  let BM : Matrix (Fin n) (Fin n) ℝ := B
  let G : Fin n → Fin n → ℝ := matMul n (matTranspose B) B
  have hG : (G : Matrix (Fin n) (Fin n) ℝ) = BM.transpose * BM := by
    ext i j
    simp [G, BM, matMul, matTranspose, Matrix.mul_apply]
  have hGpos : Matrix.PosSemidef (G : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hG]
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.posSemidef_conjTranspose_mul_self BM
  let GM : Matrix (Fin n) (Fin n) ℝ := Matrix.of G
  have hGM : GM = (G : Matrix (Fin n) (Fin n) ℝ) := rfl
  have hGMpos : Matrix.PosSemidef GM := by simpa [hGM] using hGpos
  have hpow_pos : Matrix.PosSemidef (GM ^ k) := by
    induction k with
    | zero => simpa using (Matrix.PosSemidef.one :
        Matrix.PosSemidef (1 : Matrix (Fin n) (Fin n) ℝ))
    | succ k ih =>
        rw [pow_succ']
        exact (Matrix.PosSemidef.commute_iff hGMpos ih).mp
          (Commute.self_pow GM k)
  apply Matrix_posSemidef.to_finitePSD
  rw [ch15Closure_matPow_matrix_eq_pow]
  simpa [GM, G] using hpow_pos

theorem ch15Closure_matPow_symmetric {n : ℕ}
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M) (k : ℕ) :
    IsSymmetricFiniteMatrix (matPow n M k) := by
  let MM : Matrix (Fin n) (Fin n) ℝ := Matrix.of M
  have hHerm : Matrix.IsHermitian MM :=
    IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM
  have hpHerm : Matrix.IsHermitian
      (MM ^ k) := hHerm.pow k
  intro i j
  have hij := Matrix.IsHermitian.apply hpHerm i j
  rw [show MM = Matrix.of M from rfl, ← ch15Closure_matPow_matrix_eq_pow M k] at hij
  simpa using hij.symm

theorem ch15Closure_matPow_mulVec_eigenvector {n : ℕ}
    (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (lam : ℝ)
    (hEig : matMulVec n M v = fun i => lam * v i) (k : ℕ) :
    matMulVec n (matPow n M k) v = fun i => lam ^ k * v i := by
  induction k with
  | zero =>
      funext i
      simp [matPow, matMulVec, idMatrix]
  | succ k ih =>
      funext i
      rw [matPow_succ_right]
      rw [matMulVec_matMul]
      rw [hEig]
      have hscale := congrFun
        (matMulVec_const_mul_right n (matPow n M k) lam v) i
      rw [hscale, congrFun ih i]
      ring

theorem ch15Closure_quadForm_power_lower_of_unit_eigenvector {n : ℕ}
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M)
    (k : ℕ) (hPowPSD : finitePSD (matPow n M k))
    (v : Fin n → ℝ) (lam : ℝ)
    (hvnorm : ∑ i : Fin n, v i ^ 2 = 1)
    (hEig : matMulVec n M v = fun i => lam * v i)
    (x : Fin n → ℝ) :
    lam ^ k * (∑ i : Fin n, v i * x i) ^ 2 ≤
      finiteQuadraticForm (matPow n M k) x := by
  let H : Fin n → Fin n → ℝ := matPow n M k
  let α : ℝ := ∑ i : Fin n, v i * x i
  let y : Fin n → ℝ := fun i => x i - α * v i
  have hHsym : IsSymmetricFiniteMatrix H := by
    simpa [H] using ch15Closure_matPow_symmetric M hM k
  have hHeig : finiteMatVec H v = fun i => lam ^ k * v i := by
    simpa [H, finiteMatVec, matMulVec] using
      ch15Closure_matPow_mulVec_eigenvector M v lam hEig k
  have hyorth : (∑ i : Fin n, v i * y i) = 0 := by
    calc
      (∑ i : Fin n, v i * y i) =
          (∑ i : Fin n, v i * x i) - α * ∑ i : Fin n, v i ^ 2 := by
        simp only [y, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hvnorm]; simp [α]
  have hvHy : (∑ i : Fin n, v i * finiteMatVec H y i) = 0 := by
    rw [finiteVecInnerProduct_finiteMatVec_left_eq_right_of_symmetric H hHsym]
    simp_rw [hHeig]
    calc
      (∑ i : Fin n, (lam ^ k * v i) * y i) =
          lam ^ k * ∑ i : Fin n, v i * y i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hyorth, mul_zero]
  have hyHv : (∑ i : Fin n, y i * finiteMatVec H v i) = 0 := by
    simp_rw [hHeig]
    calc
      (∑ i : Fin n, y i * (lam ^ k * v i)) =
          lam ^ k * ∑ i : Fin n, v i * y i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hyorth, mul_zero]
  have hqv : finiteQuadraticForm H v = lam ^ k := by
    unfold finiteQuadraticForm
    simp_rw [hHeig]
    calc
      (∑ i : Fin n, v i * (lam ^ k * v i)) =
          lam ^ k * ∑ i : Fin n, v i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = lam ^ k := by rw [hvnorm, mul_one]
  have hxdecomp : x = fun i => α * v i + y i := by
    funext i
    simp [y]
  have hscale : finiteMatVec H (fun i => α * v i) =
      fun i => α * finiteMatVec H v i := by
    funext i
    unfold finiteMatVec
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hqexpand :
      finiteQuadraticForm H x =
        α ^ 2 * finiteQuadraticForm H v +
          α * (∑ i : Fin n, v i * finiteMatVec H y i) +
          α * (∑ i : Fin n, y i * finiteMatVec H v i) +
          finiteQuadraticForm H y := by
    rw [hxdecomp]
    unfold finiteQuadraticForm
    rw [finiteMatVec_add, hscale]
    calc
      (∑ i : Fin n,
          (α * v i + y i) *
            (α * finiteMatVec H v i + finiteMatVec H y i)) =
          ∑ i : Fin n,
            (α ^ 2 * (v i * finiteMatVec H v i) +
              α * (v i * finiteMatVec H y i) +
              α * (y i * finiteMatVec H v i) +
              y i * finiteMatVec H y i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = α ^ 2 * (∑ i : Fin n, v i * finiteMatVec H v i) +
          α * (∑ i : Fin n, v i * finiteMatVec H y i) +
          α * (∑ i : Fin n, y i * finiteMatVec H v i) +
          ∑ i : Fin n, y i * finiteMatVec H y i := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hqy : 0 ≤ finiteQuadraticForm H y := by
    simpa [H] using hPowPSD y
  rw [show ∑ i : Fin n, v i * x i = α from rfl]
  rw [show finiteQuadraticForm (matPow n M k) x = finiteQuadraticForm H x from rfl]
  rw [hqexpand, hqv, hvHy, hyHv]
  nlinarith

theorem ch15Closure_exists_gram_opNorm2_sq_unit_eigenvector (d : ℕ)
    (B : Fin (d + 1) → Fin (d + 1) → ℝ) :
    ∃ v : Fin (d + 1) → ℝ,
      (∑ i : Fin (d + 1), v i ^ 2) = 1 ∧
      matMulVec (d + 1) (matMul (d + 1) (matTranspose B) B) v =
        fun i => opNorm2 B ^ 2 * v i := by
  let n := d + 1
  let G : Fin n → Fin n → ℝ := matMul n (matTranspose B) B
  have hn : 0 < n := by omega
  have hGsym : IsSymmetricFiniteMatrix G := by
    simpa [G, n] using ch15Closure_gram_symmetric B
  let lam : ℝ := finiteMaxEigenvalue hn G hGsym
  obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hn G hGsym
  let v : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian G hGsym).eigenvectorBasis a)
  have hvnorm : (∑ i : Fin n, v i ^ 2) = 1 := by
    have h := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one G hGsym a
    simpa [finiteVecNorm2Sq, v] using h
  have hveig_lam : matMulVec n G v = fun i => lam * v i := by
    have h := finiteMatVec_finiteHermitianEigenvector_eq G hGsym a
    rw [ha] at h
    simpa [finiteMatVec, matMulVec, lam, v] using h
  have hcert : opNorm2Le B (Real.sqrt lam) := by
    have h := opNorm2Le_sqrt_maxEigenvalue_gram n hn B
      (by simpa [G, matMul, matTranspose] using hGsym)
    simpa [lam, G, matMul, matTranspose] using h
  have hlam_nonneg : 0 ≤ lam := by
    have hpsd : finitePSD G := by
      have hp := ch15Closure_gram_pow_finitePSD B 1
      simpa [G, n, matPow_one] using hp
    have heigs := (finitePSD_iff_finiteHermitianEigenvalues_nonneg G hGsym).mp hpsd a
    simpa [lam, ha] using heigs
  have hop_le_sqrt : opNorm2 B ≤ Real.sqrt lam :=
    opNorm2_le_of_opNorm2Le B (Real.sqrt_nonneg lam) hcert
  have hop_sq_le : opNorm2 B ^ 2 ≤ lam := by
    nlinarith [Real.sq_sqrt hlam_nonneg, opNorm2_nonneg B,
      Real.sqrt_nonneg lam]
  have hlam_le : lam ≤ opNorm2 B ^ 2 := by
    have h := maxEigenvalue_gram_le_sq_of_opNorm2Le n hn B
      (by simpa [G, matMul, matTranspose] using hGsym)
      (opNorm2 B) (opNorm2Le_opNorm2 B)
    simpa [lam, G, matMul, matTranspose] using h
  have hlam : lam = opNorm2 B ^ 2 := le_antisymm hlam_le hop_sq_le
  refine ⟨v, ?_, ?_⟩
  · simpa [n] using hvnorm
  · simpa [n, G, hlam] using hveig_lam

noncomputable def ch15Closure_unitSphereOfFiniteVec (d : ℕ)
    (v : Fin (d + 1) → ℝ) (hv : (∑ i, v i ^ 2) = 1) :
    OrthogonalSphere (d + 1) :=
  ⟨WithLp.toLp 2 v, by
    rw [Metric.mem_sphere, dist_zero_right]
    have hsq : ‖WithLp.toLp 2 v‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simpa [Real.norm_eq_abs, sq_abs] using hv
    nlinarith [norm_nonneg (WithLp.toLp 2 v)]⟩

theorem ch15Closure_ch15SphereInner_unitSphereOfFiniteVec (d : ℕ)
    (v : Fin (d + 1) → ℝ) (hv : (∑ i, v i ^ 2) = 1)
    (x : OrthogonalSphere (d + 1)) :
    ch15SphereInner d (ch15Closure_unitSphereOfFiniteVec d v hv) x =
      ∑ i : Fin (d + 1), v i *
        WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1))) i := by
  have hscalar (a b : ℝ) : @inner ℝ ℝ _ a b = a * b := by
    calc
      @inner ℝ ℝ _ a b = @inner ℝ ℝ _ (a • (1 : ℝ)) (b • (1 : ℝ)) := by
        congr <;> simp
      _ = a * b * @inner ℝ ℝ _ (1 : ℝ) 1 := by
        rw [real_inner_smul_left, real_inner_smul_right]
        ring
      _ = a * b := by simp
  simp only [ch15SphereInner, ch15Closure_unitSphereOfFiniteVec, PiLp.inner_apply]
  simp_rw [hscalar]

theorem ch15Closure_exists_dixon_sphere_direction_power_lower
    (d k : ℕ) (B : Fin (d + 1) → Fin (d + 1) → ℝ) :
    ∃ u : OrthogonalSphere (d + 1),
      ∀ x : OrthogonalSphere (d + 1),
        opNorm2 B ^ (2 * k) * (ch15SphereInner d u x) ^ 2 ≤
          finiteQuadraticForm
            (matPow (d + 1)
              (matMul (d + 1) (matTranspose B) B) k)
            (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) := by
  obtain ⟨v, hv, hEig⟩ := ch15Closure_exists_gram_opNorm2_sq_unit_eigenvector d B
  let u := ch15Closure_unitSphereOfFiniteVec d v hv
  refine ⟨u, fun x => ?_⟩
  let xv : Fin (d + 1) → ℝ :=
    WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))
  have hlower := ch15Closure_quadForm_power_lower_of_unit_eigenvector
    (matMul (d + 1) (matTranspose B) B)
    (ch15Closure_gram_symmetric B) k
    (ch15Closure_gram_pow_finitePSD B k) v (opNorm2 B ^ 2) hv hEig xv
  rw [← pow_mul] at hlower
  simpa [u, xv, ch15Closure_ch15SphereInner_unitSphereOfFiniteVec] using hlower

theorem ch15Closure_sqrt_inv_pow_eq_rpow_neg_half (θ : ℝ) (hθ : 0 ≤ θ) (k : ℕ) :
    Real.sqrt ((θ ^ k)⁻¹) = θ ^ (-(k : ℝ) / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  rw [Real.inv_rpow (pow_nonneg hθ k)]
  rw [← Real.rpow_neg (pow_nonneg hθ k)]
  rw [← Real.rpow_natCast_mul hθ]
  congr 1
  ring

theorem ch15Closure_dixon_failure_probability_le
    (d k : ℕ) (hk : 0 < k)
    (B : Fin (d + 1) → Fin (d + 1) → ℝ)
    (θ : ℝ) (hθ : 1 < θ) :
    standardGaussianDirectionMeasure d
        {x : OrthogonalSphere (d + 1) |
          (θ ^ k) ^ 2 *
              finiteQuadraticForm
                (matPow (d + 1)
                  (matMul (d + 1) (matTranspose B) B) k)
                (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) <
            opNorm2 B ^ (2 * k)} ≤
      ENNReal.ofReal (((4 : ℝ) / 5) * Real.sqrt (d + 1) *
        θ ^ (-(k : ℝ) / 2 : ℝ)) := by
  obtain ⟨u, hlower⟩ := ch15Closure_exists_dixon_sphere_direction_power_lower d k B
  let s : ℝ := θ ^ k
  let δ : ℝ := s⁻¹
  have hsone : 1 < s := by
    exact one_lt_pow₀ hθ (Nat.ne_of_gt hk)
  have hspos : 0 < s := lt_trans zero_lt_one hsone
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hδpos : 0 < δ := inv_pos.mpr hspos
  have hδlt : δ < 1 := (inv_lt_one₀ hspos).2 hsone
  have hsδ : s * δ = 1 := by simp [δ, hsne]
  have hsδsq : s ^ 2 * δ ^ 2 = 1 := by
    rw [← mul_pow, hsδ, one_pow]
  have hsubset :
      {x : OrthogonalSphere (d + 1) |
        (θ ^ k) ^ 2 *
              finiteQuadraticForm
                (matPow (d + 1)
                  (matMul (d + 1) (matTranspose B) B) k)
                (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) <
            opNorm2 B ^ (2 * k)} ⊆
        {x | |ch15SphereInner d u x| ≤ δ} := by
    intro x hx
    change s ^ 2 *
          finiteQuadraticForm
            (matPow (d + 1)
              (matMul (d + 1) (matTranspose B) B) k)
            (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) <
        opNorm2 B ^ (2 * k) at hx
    by_cases hopzero : opNorm2 B = 0
    · have hqnonneg := ch15Closure_gram_pow_finitePSD B k
        (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1))))
      have hrhs : opNorm2 B ^ (2 * k) = 0 := by
        rw [hopzero, zero_pow]
        omega
      rw [hrhs] at hx
      nlinarith [sq_nonneg s]
    · by_contra hnot
      have hnot' : δ < |ch15SphereInner d u x| := lt_of_not_ge hnot
      have hrpos : 0 < opNorm2 B :=
        lt_of_le_of_ne (opNorm2_nonneg B) (Ne.symm hopzero)
      have hrpowpos : 0 < opNorm2 B ^ (2 * k) := pow_pos hrpos _
      have habssq : δ ^ 2 < (ch15SphereInner d u x) ^ 2 := by
        have h := (sq_lt_sq₀ hδpos.le (abs_nonneg _)).2 hnot'
        simpa [sq_abs] using h
      have hscaled :
          opNorm2 B ^ (2 * k) * δ ^ 2 <
            opNorm2 B ^ (2 * k) * (ch15SphereInner d u x) ^ 2 :=
        mul_lt_mul_of_pos_left habssq hrpowpos
      have hqgt :
          opNorm2 B ^ (2 * k) * δ ^ 2 <
            finiteQuadraticForm
              (matPow (d + 1)
                (matMul (d + 1) (matTranspose B) B) k)
              (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) :=
        hscaled.trans_le (hlower x)
      have hmul := mul_lt_mul_of_pos_left hqgt (sq_pos_of_pos hspos)
      have hleft :
          s ^ 2 * (opNorm2 B ^ (2 * k) * δ ^ 2) =
            opNorm2 B ^ (2 * k) := by
        calc
          s ^ 2 * (opNorm2 B ^ (2 * k) * δ ^ 2) =
              opNorm2 B ^ (2 * k) * (s ^ 2 * δ ^ 2) := by ring
          _ = opNorm2 B ^ (2 * k) := by rw [hsδsq, mul_one]
      rw [hleft] at hmul
      exact (not_lt_of_ge (le_of_lt hx)) hmul
  calc
    standardGaussianDirectionMeasure d
        {x : OrthogonalSphere (d + 1) |
          (θ ^ k) ^ 2 *
              finiteQuadraticForm
                (matPow (d + 1)
                  (matMul (d + 1) (matTranspose B) B) k)
                (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) <
            opNorm2 B ^ (2 * k)} ≤
        standardGaussianDirectionMeasure d
          {x | |ch15SphereInner d u x| ≤ δ} := measure_mono hsubset
    _ ≤ ENNReal.ofReal (((4 : ℝ) / 5) * Real.sqrt (d + 1) * Real.sqrt δ) :=
      ch15_standardGaussianDirection_inner_dixon_bound d u δ hδpos.le hδlt
    _ = ENNReal.ofReal (((4 : ℝ) / 5) * Real.sqrt (d + 1) *
        θ ^ (-(k : ℝ) / 2 : ℝ)) := by
      have hsqrt : Real.sqrt δ = θ ^ (-(k : ℝ) / 2 : ℝ) := by
        simpa [δ, s] using ch15Closure_sqrt_inv_pow_eq_rpow_neg_half θ
          (le_of_lt (lt_trans zero_lt_one hθ)) k
      rw [hsqrt]

theorem ch15Closure_dixon_success_probability_ge
    (d k : ℕ) (hk : 0 < k)
    (B : Fin (d + 1) → Fin (d + 1) → ℝ)
    (θ : ℝ) (hθ : 1 < θ) :
    ENNReal.ofReal
        (1 - ((4 : ℝ) / 5) * Real.sqrt (d + 1) *
          θ ^ (-(k : ℝ) / 2 : ℝ)) ≤
      standardGaussianDirectionMeasure d
        {x : OrthogonalSphere (d + 1) |
          opNorm2 B ^ (2 * k) ≤
            (θ ^ k) ^ 2 *
              finiteQuadraticForm
                (matPow (d + 1)
                  (matMul (d + 1) (matTranspose B) B) k)
                (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1))))} := by
  let Good : Set (OrthogonalSphere (d + 1)) :=
    {x | opNorm2 B ^ (2 * k) ≤
      (θ ^ k) ^ 2 *
        finiteQuadraticForm
          (matPow (d + 1)
            (matMul (d + 1) (matTranspose B) B) k)
          (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1))))}
  let Bad : Set (OrthogonalSphere (d + 1)) :=
    {x | (θ ^ k) ^ 2 *
        finiteQuadraticForm
          (matPow (d + 1)
            (matMul (d + 1) (matTranspose B) B) k)
          (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) <
      opNorm2 B ^ (2 * k)}
  let c : ℝ := ((4 : ℝ) / 5) * Real.sqrt (d + 1) *
    θ ^ (-(k : ℝ) / 2 : ℝ)
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hBad : standardGaussianDirectionMeasure d Bad ≤ ENNReal.ofReal c := by
    simpa [Bad, c] using ch15Closure_dixon_failure_probability_le d k hk B θ hθ
  have hGoodMeas : MeasurableSet Good := by
    dsimp [Good]
    apply measurableSet_le
    · exact measurable_const
    · unfold finiteQuadraticForm finiteMatVec
      fun_prop
  have hcompl : Goodᶜ = Bad := by
    ext x
    simp [Good, Bad, not_le]
  have hBadMeas : MeasurableSet Bad := by
    rw [← hcompl]
    exact hGoodMeas.compl
  have hGoodEq : Good = Badᶜ := by
    rw [← hcompl]
    simp
  change ENNReal.ofReal (1 - c) ≤ standardGaussianDirectionMeasure d Good
  rw [ENNReal.ofReal_sub 1 hc]
  rw [hGoodEq, prob_compl_eq_one_sub hBadMeas]
  simpa using tsub_le_tsub_left hBad 1

/-- Repeated operator-norm composition for repository-native matrix powers. -/
theorem ch15Closure_opNorm2Le_matPow {n : ℕ}
    (M : Fin n → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hM : opNorm2Le M c) (k : ℕ) :
    opNorm2Le (matPow n M k) (c ^ k) := by
  induction k with
  | zero =>
      intro x
      rw [matPow_zero, matMulVec_id]
      simp
  | succ k ih =>
      simpa [matPow_succ, pow_succ'] using
        opNorm2Le_matMul n M (matPow n M k) c (c ^ k) hc hM ih

/-- The always-valid left side of Dixon's inequality for every positive
power: on the unit sphere,
`xᵀ(BᵀB)^k x ≤ ‖B‖₂^(2k)`. -/
theorem ch15Closure_dixon_left_power_inequality
    (d k : ℕ) (B : Fin (d + 1) → Fin (d + 1) → ℝ)
    (x : OrthogonalSphere (d + 1)) :
    finiteQuadraticForm
        (matPow (d + 1) (matMul (d + 1) (matTranspose B) B) k)
        (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) ≤
      opNorm2 B ^ (2 * k) := by
  let xv : Fin (d + 1) → ℝ :=
    WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))
  let G : Fin (d + 1) → Fin (d + 1) → ℝ :=
    matMul (d + 1) (matTranspose B) B
  let H : Fin (d + 1) → Fin (d + 1) → ℝ := matPow (d + 1) G k
  have hBt : opNorm2Le (matTranspose B) (opNorm2 B) :=
    opNorm2Le_transpose B (opNorm2_nonneg B) (opNorm2Le_opNorm2 B)
  have hG : opNorm2Le G (opNorm2 B ^ 2) := by
    simpa [G, pow_two] using
      opNorm2Le_matMul (d + 1) (matTranspose B) B
        (opNorm2 B) (opNorm2 B) (opNorm2_nonneg B) hBt
        (opNorm2Le_opNorm2 B)
  have hH : opNorm2Le H ((opNorm2 B ^ 2) ^ k) := by
    exact ch15Closure_opNorm2Le_matPow G (opNorm2 B ^ 2)
      (sq_nonneg (opNorm2 B)) hG k
  have hxnorm : ‖WithLp.toLp 2 xv‖ = 1 := by
    simpa [xv, Metric.mem_sphere, dist_zero_right] using x.property
  have hxsq : vecNorm2Sq xv = 1 := by
    have hsq : ‖WithLp.toLp 2 xv‖ ^ 2 = 1 := by rw [hxnorm]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at hsq
    simpa [vecNorm2Sq, Real.norm_eq_abs, sq_abs] using hsq
  have habs := abs_vecInnerProduct_matMulVec_le_of_opNorm2Le H hH xv
  have hqnonneg : 0 ≤ finiteQuadraticForm H xv := by
    simpa [H, G] using ch15Closure_gram_pow_finitePSD B k xv
  have hqle : finiteQuadraticForm H xv ≤ (opNorm2 B ^ 2) ^ k := by
    unfold finiteQuadraticForm finiteMatVec at hqnonneg ⊢
    simpa [matMulVec, hxsq, abs_of_nonneg hqnonneg] using habs
  rw [show finiteQuadraticForm
      (matPow (d + 1) (matMul (d + 1) (matTranspose B) B) k) xv =
      finiteQuadraticForm H xv from rfl]
  rw [← pow_mul] at hqle
  exact hqle

/-- **Higham Theorem 15.6 (Dixon), closed source-shaped endpoint.**

For a certified inverse `B = A⁻¹`, a positive integer `k`, and `θ > 1`,
the actual inverse Gram matrix is `BᵀB = (AAᵀ)⁻¹`; the left powered
inequality holds for every unit vector; and the right powered inequality
holds for a uniform sphere point with probability at least
`1 - 0.8 * θ^(-k/2) * sqrt n`.  The powered event is exactly the
nonnegative `2k`-th-power form of display (15.7):
`‖B‖₂ ≤ θ * (xᵀ(BᵀB)^k x)^(1/(2k))`. -/
theorem higham15_6_dixon_closed
    (d k : ℕ) (hk : 0 < k)
    (A B : Fin (d + 1) → Fin (d + 1) → ℝ)
    (hR : IsRightInverse (d + 1) A B)
    (hL : IsLeftInverse (d + 1) A B)
    (θ : ℝ) (hθ : 1 < θ) :
    IsInverse (d + 1)
        (matMul (d + 1) A (matTranspose A))
        (matMul (d + 1) (matTranspose B) B) ∧
      (∀ x : OrthogonalSphere (d + 1),
        finiteQuadraticForm
            (matPow (d + 1)
              (matMul (d + 1) (matTranspose B) B) k)
            (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) ≤
          opNorm2 B ^ (2 * k)) ∧
      ENNReal.ofReal
          (1 - ((4 : ℝ) / 5) * Real.sqrt (d + 1) *
            θ ^ (-(k : ℝ) / 2 : ℝ)) ≤
        standardGaussianDirectionMeasure d
          {x : OrthogonalSphere (d + 1) |
            opNorm2 B ^ (2 * k) ≤
              (θ ^ k) ^ 2 *
                finiteQuadraticForm
                  (matPow (d + 1)
                    (matMul (d + 1) (matTranspose B) B) k)
                  (WithLp.ofLp
                    (x : EuclideanSpace ℝ (Fin (d + 1))))} := by
  refine ⟨Ch15.gram_inv_of_isInverse hR hL, ?_, ?_⟩
  · exact fun x => ch15Closure_dixon_left_power_inequality d k B x
  · exact ch15Closure_dixon_success_probability_ge d k hk B θ hθ

end NumStability
