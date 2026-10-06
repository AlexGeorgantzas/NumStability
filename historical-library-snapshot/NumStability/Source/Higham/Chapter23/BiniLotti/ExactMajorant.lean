/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter23.BilinearAlgorithm
import NumStability.Source.Higham.Chapter23.BiniLotti.Execution
import NumStability.Source.Higham.Chapter23.BiniLotti.RecursiveAlgebra
import NumStability.Source.Higham.Chapter23.Equation11

namespace NumStability

open scoped Topology BigOperators
open Filter

/-!
# Higham Chapter 23: Bini--Lotti exact majorant

Nonnegativity and the exact recursive error majorant for Theorem 23.4.
-/

theorem higham23_biniExactMajorant_nonneg
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t) :
    ∀ depth, 0 ≤ higham23BiniExactMajorant fp alg depth
  | 0 => fp.u_nonneg
  | depth + 1 => by
      rw [higham23BiniExactMajorant]
      have hK : 0 ≤ higham23MillerWeightTotal alg := by
        unfold higham23MillerWeightTotal
        exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
          higham23_miller_weight_nonneg alg i j
      have hN : 0 ≤ (((h ^ depth : ℕ) : ℝ)) := Nat.cast_nonneg _
      have he := higham23_biniExactMajorant_nonneg fp alg hLinear hOutput depth
      have hg := gamma_nonneg fp hLinear
      have hgt := gamma_nonneg fp hOutput
      unfold higham23BiniStepMajorant higham23BiniProductErrorCore
        higham23BiniProductNormCore
      positivity

/-- Exact nonlinear Bini--Lotti bound for the literal recursive evaluator. -/
theorem higham23_theorem23_4_biniLotti_exactMajorant
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (halg : alg.IsNoncommutativeCorrect)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t) :
    ∀ depth (A B : Higham23BiniMatrix h depth) (a b : ℝ),
      0 ≤ a → 0 ≤ b →
      Higham23BiniNormLe h depth A a → Higham23BiniNormLe h depth B b →
      Higham23BiniErrorLe h depth (higham23BiniMul h depth A B)
        (higham23BiniFlEvaluate fp alg depth A B)
        (higham23BiniExactMajorant fp alg depth * a * b) := by
  intro depth
  induction depth with
  | zero =>
      intro A B a b ha hb hA hB
      obtain ⟨δ, hδ, hfl⟩ := fp.model_mul A B
      change |A * B - fp.fl_mul A B| ≤ _
      rw [hfl, show A * B - A * B * (1 + δ) = -(A * B) * δ by ring,
        abs_mul, abs_neg, abs_mul]
      calc
        |A| * |B| * |δ| ≤ a * b * fp.u := by
          exact mul_le_mul (mul_le_mul hA hB (abs_nonneg _) ha)
            hδ (abs_nonneg _) (mul_nonneg ha hb)
        _ = _ := by simp [higham23BiniExactMajorant]; ring
  | succ depth ih =>
      intro A B a b ha hb hA hB
      let g := gamma fp (h * h)
      let gt := gamma fp t
      let N : ℝ := ((h ^ depth : ℕ) : ℝ)
      let e := higham23BiniExactMajorant fp alg depth
      let K := higham23MillerWeightTotal alg
      let PE := higham23BiniProductErrorCore N e g
      let PN := higham23BiniProductNormCore N e g
      have hg : 0 ≤ g := gamma_nonneg fp hLinear
      have hgt : 0 ≤ gt := gamma_nonneg fp hOutput
      have hN : 0 ≤ N := by dsimp [N]; positivity
      have he : 0 ≤ e := higham23_biniExactMajorant_nonneg fp alg hLinear hOutput depth
      have hK : 0 ≤ K := by
        dsimp [K, higham23MillerWeightTotal]
        exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
          higham23_miller_weight_nonneg alg i j
      have hPE : 0 ≤ PE := by
        dsimp [PE, higham23BiniProductErrorCore]
        positivity
      have hPN : 0 ≤ PN := by
        dsimp [PN, higham23BiniProductNormCore]
        positivity
      let X := fun k : Fin t ↦
        higham23BiniExactDot h (h * h) depth (higham23MillerFlattenU alg k)
          (higham23BiniFlattenBlock A)
      let Y := fun k : Fin t ↦
        higham23BiniExactDot h (h * h) depth (higham23MillerFlattenV alg k)
          (higham23BiniFlattenBlock B)
      let Xhat := fun k : Fin t ↦
        higham23BiniFlDot fp h (h * h) depth (higham23MillerFlattenU alg k)
          (higham23BiniFlattenBlock A)
      let Yhat := fun k : Fin t ↦
        higham23BiniFlDot fp h (h * h) depth (higham23MillerFlattenV alg k)
          (higham23BiniFlattenBlock B)
      let P := fun k : Fin t ↦ higham23BiniFlEvaluate fp alg depth (Xhat k) (Yhat k)
      have hAflat (q : Fin (h * h)) :
          Higham23BiniNormLe h depth (higham23BiniFlattenBlock A q) a :=
        hA _ _
      have hBflat (q : Fin (h * h)) :
          Higham23BiniNormLe h depth (higham23BiniFlattenBlock B q) b :=
        hB _ _
      have hXcert (k : Fin t) : Higham23BiniCertificate h depth (X k) (Xhat k)
          (g * higham23MillerUWeight alg k * a)
          ((1 + g) * higham23MillerUWeight alg k * a) := by
        have hc := higham23_biniFlDot_certificate fp h (h * h) hLinear depth
          (higham23MillerFlattenU alg k)
          (higham23BiniFlattenBlock A) (higham23BiniFlattenBlock A)
          (fun _ ↦ 0) (fun _ ↦ a) (fun _ ↦ by norm_num) (fun _ ↦ ha)
          (fun q ↦ higham23_biniError_refl h depth _ ) hAflat
        constructor
        · simpa [X, Xhat, g, higham23MillerUWeight, pow_two,
            Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
            using hc.1
        · simpa [Xhat, g, higham23MillerUWeight, pow_two,
            Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
            using hc.2
      have hYcert (k : Fin t) : Higham23BiniCertificate h depth (Y k) (Yhat k)
          (g * higham23MillerVWeight alg k * b)
          ((1 + g) * higham23MillerVWeight alg k * b) := by
        have hc := higham23_biniFlDot_certificate fp h (h * h) hLinear depth
          (higham23MillerFlattenV alg k)
          (higham23BiniFlattenBlock B) (higham23BiniFlattenBlock B)
          (fun _ ↦ 0) (fun _ ↦ b) (fun _ ↦ by norm_num) (fun _ ↦ hb)
          (fun q ↦ higham23_biniError_refl h depth _) hBflat
        constructor
        · simpa [Y, Yhat, g, higham23MillerVWeight, pow_two,
            Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
            using hc.1
        · simpa [Yhat, g, higham23MillerVWeight, pow_two,
            Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
            using hc.2
      have hYexact (k : Fin t) : Higham23BiniNormLe h depth (Y k)
          (higham23MillerVWeight alg k * b) := by
        have hn := higham23_biniExactDot_norm h (h * h) depth
          (higham23MillerFlattenV alg k) (higham23BiniFlattenBlock B)
          (fun _ ↦ b) (fun _ ↦ hb) hBflat
        simpa [Y, higham23MillerVWeight, Finset.mul_sum, Finset.sum_mul,
          mul_comm, mul_left_comm, mul_assoc] using hn
      have hProduct (k : Fin t) : Higham23BiniCertificate h depth
          (higham23BiniMul h depth (X k) (Y k)) (P k)
          (PE * higham23MillerUWeight alg k *
            higham23MillerVWeight alg k * a * b)
          (PN * higham23MillerUWeight alg k *
            higham23MillerVWeight alg k * a * b) := by
        let uw := higham23MillerUWeight alg k
        let vw := higham23MillerVWeight alg k
        have huw : 0 ≤ uw := by dsimp [uw, higham23MillerUWeight]; positivity
        have hvw : 0 ≤ vw := by dsimp [vw, higham23MillerVWeight]; positivity
        have hrec := ih (Xhat k) (Yhat k) ((1 + g) * uw * a)
          ((1 + g) * vw * b) (by positivity) (by positivity)
          (hXcert k).norm_le (hYcert k).norm_le
        have hp := higham23_biniCertificate_product h depth
          (X k) (Xhat k) (Y k) (Yhat k) (P k)
          (vw * b) (g * uw * a) ((1 + g) * uw * a)
          (g * vw * b) ((1 + g) * vw * b) e
          (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
          (by simpa [vw] using hYexact k)
          (by simpa [uw] using hXcert k) (by simpa [vw] using hYcert k)
          (by simpa [P, e, uw, vw] using hrec)
        constructor
        · convert hp.error_le using 1 <;>
            dsimp [PE, higham23BiniProductErrorCore, N, e, g, uw, vw] <;> ring
        · convert hp.norm_le using 1 <;>
            dsimp [PN, higham23BiniProductNormCore, N, e, g, uw, vw] <;> ring
      have hOutCert (i j : Fin h) := higham23_biniFlDot_certificate fp h t hOutput
        depth (alg.W i j)
        (fun k ↦ higham23BiniMul h depth (X k) (Y k)) P
        (fun k ↦ PE * higham23MillerUWeight alg k *
          higham23MillerVWeight alg k * a * b)
        (fun k ↦ PN * higham23MillerUWeight alg k *
          higham23MillerVWeight alg k * a * b)
        (fun k ↦ by
          have hu : 0 ≤ higham23MillerUWeight alg k := by
            unfold higham23MillerUWeight
            positivity
          have hv : 0 ≤ higham23MillerVWeight alg k := by
            unfold higham23MillerVWeight
            positivity
          positivity)
        (fun k ↦ by
          have hu : 0 ≤ higham23MillerUWeight alg k := by
            unfold higham23MillerUWeight
            positivity
          have hv : 0 ≤ higham23MillerVWeight alg k := by
            unfold higham23MillerVWeight
            positivity
          positivity)
        (fun k ↦ (hProduct k).error_le) (fun k ↦ (hProduct k).norm_le)
      have hCorrect := halg depth A B
      intro i j
      have hEntry := (hOutCert i j).1
      have hWeight := higham23_miller_weight_le_total alg i j
      have hcore : 0 ≤ PE + gt * PN := add_nonneg hPE (mul_nonneg hgt hPN)
      have hscaled := mul_le_mul_of_nonneg_left hWeight hcore
      have hab : 0 ≤ a * b := mul_nonneg ha hb
      have hscaled := mul_le_mul_of_nonneg_right hscaled hab
      have hPEsum :
          (∑ q, |alg.W i j q| * (PE * higham23MillerUWeight alg q *
            higham23MillerVWeight alg q * a * b)) =
            PE * higham23MillerWeight alg i j * (a * b) := by
        rw [higham23MillerWeight]
        calc
          _ = ∑ q, PE * (|alg.W i j q| * higham23MillerUWeight alg q *
                higham23MillerVWeight alg q) * (a * b) := by
              apply Finset.sum_congr rfl
              intro q _
              ring
          _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]
      have hPNsum :
          (∑ q, |alg.W i j q| * (PN * higham23MillerUWeight alg q *
            higham23MillerVWeight alg q * a * b)) =
            PN * higham23MillerWeight alg i j * (a * b) := by
        rw [higham23MillerWeight]
        calc
          _ = ∑ q, PN * (|alg.W i j q| * higham23MillerUWeight alg q *
                higham23MillerVWeight alg q) * (a * b) := by
              apply Finset.sum_congr rfl
              intro q _
              ring
          _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]
      have hEntry' := higham23_biniError_mono h depth _ _ hEntry
        (show
          (∑ q, |alg.W i j q| * (PE * higham23MillerUWeight alg q *
              higham23MillerVWeight alg q * a * b)) +
            gt * (∑ q, |alg.W i j q| * (PN * higham23MillerUWeight alg q *
              higham23MillerVWeight alg q * a * b)) ≤
            (PE + gt * PN) * higham23MillerWeight alg i j * (a * b) by
          rw [hPEsum, hPNsum]
          ring_nf
          exact le_rfl)
      have hmonoRaw := higham23_biniError_mono h depth _ _ hEntry' hscaled
      have hmono : Higham23BiniErrorLe h depth
          (higham23BiniExactLevel alg A B i j)
          (higham23BiniFlEvaluate fp alg (depth + 1) A B i j)
          (higham23BiniStepMajorant K N e g gt * a * b) := by
        convert hmonoRaw using 1 <;>
          dsimp [higham23BiniExactLevel, higham23BiniFlEvaluate, X, Y, Xhat, Yhat,
            P, higham23BiniStepMajorant, K, N, e, g, gt, PE, PN] <;> ring
      have hCorrectEntry := congrArg
        (fun M : Higham23BiniMatrix h (depth + 1) ↦ M i j) hCorrect
      change higham23BiniExactLevel alg A B i j =
        higham23BiniMul h (depth + 1) A B i j at hCorrectEntry
      rw [← hCorrectEntry]
      simpa [higham23BiniExactMajorant, K, N, e, g, gt] using hmono

end NumStability
