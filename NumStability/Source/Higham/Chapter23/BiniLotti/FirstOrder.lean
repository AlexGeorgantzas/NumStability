/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter23.BilinearAlgorithm
import NumStability.Source.Higham.Chapter23.BiniLotti.ExactMajorant
import NumStability.Source.Higham.Chapter23.BiniLotti.Execution
import NumStability.Source.Higham.Chapter23.BiniLotti.RecursiveAlgebra
import NumStability.Source.Higham.Chapter23.Equation11
import NumStability.Source.Higham.Chapter23.ErrorRecurrences
import NumStability.Source.Higham.Chapter23.GammaAsymptotics

namespace NumStability

open scoped Topology BigOperators
open Filter

/-!
# Higham Chapter 23: Bini--Lotti first-order bound

First-order coefficients, quadratic remainders, and the source-facing bound for Theorem 23.4.
-/

/-! ### First-order coefficient and the genuine quadratic remainder -/

/-- The exact majorant with unit roundoff exposed as a variable. -/
noncomputable def higham23BiniMajorantFamily
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) : ℕ → ℝ → ℝ
  | 0, u => u
  | depth + 1, u =>
      higham23BiniStepMajorant (higham23MillerWeightTotal alg)
        (((h ^ depth : ℕ) : ℝ)) (higham23BiniMajorantFamily alg depth u)
        (higham23MillerGammaFamily (h * h) u)
        (higham23MillerGammaFamily t u)

/-- The derivative at zero of the exact Bini--Lotti majorant. -/
noncomputable def higham23BiniFirstOrderCoefficient
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) : ℕ → ℝ
  | 0 => 1
  | depth + 1 =>
      higham23MillerWeightTotal alg *
        (higham23BiniFirstOrderCoefficient alg depth +
          (((h ^ depth : ℕ) : ℝ)) *
            (2 * (((h * h : ℕ) : ℝ)) + (t : ℝ)))

noncomputable def higham23BiniMajorantRemainder
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) (depth : ℕ) (u : ℝ) : ℝ :=
  higham23BiniMajorantFamily alg depth u -
    higham23BiniFirstOrderCoefficient alg depth * u

theorem higham23_biniExactMajorant_eq_family
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t) :
    ∀ depth, higham23BiniExactMajorant fp alg depth =
      higham23BiniMajorantFamily alg depth fp.u
  | 0 => rfl
  | depth + 1 => by
      rw [higham23BiniExactMajorant, higham23BiniMajorantFamily,
        higham23_biniExactMajorant_eq_family fp alg hLinear hOutput depth,
        higham23_gamma_split fp (h * h) hLinear,
        higham23_gamma_split fp t hOutput]
      rfl

/-- A polynomial one-step lemma: after the displayed linear term is removed,
the Bini--Lotti step is quadratic whenever each incoming remainder is. -/
theorem higham23_biniStepRemainder_isBigO_u_sq
    (K N s τ c : ℝ) (e g gt : ℝ → ℝ)
    (he : e =O[𝓝 0] (fun u : ℝ ↦ u))
    (hg : g =O[𝓝 0] (fun u : ℝ ↦ u))
    (hgt : gt =O[𝓝 0] (fun u : ℝ ↦ u))
    (heR : (fun u : ℝ ↦ e u - c * u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2))
    (hgR : (fun u : ℝ ↦ g u - s * u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2))
    (hgtR : (fun u : ℝ ↦ gt u - τ * u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2)) :
    (fun u : ℝ ↦ higham23BiniStepMajorant K N (e u) (g u) (gt u) -
      K * (c + N * (2 * s + τ)) * u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
    Asymptotics.isBigO_refl _ _
  have huOne : (fun u : ℝ ↦ u) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    continuousAt_id.isBigO_one ℝ
  have huSqOu : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u) := by
    simpa only [pow_two, mul_one] using hu.mul huOne
  have hgSq : (fun u : ℝ ↦ g u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hg.mul hg
  have heg : (fun u : ℝ ↦ e u * g u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using he.mul hg
  have hegSq : (fun u : ℝ ↦ e u * g u ^ 2)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    have heOne := he.trans huOne
    simpa only [one_mul] using heOne.mul hgSq
  have hPE :=
    (((hgR.const_mul_left (2 * N)).add heR).add
      (hgSq.const_mul_left N)).add
      ((heg.const_mul_left 2).add hegSq)
  have hPE : (fun u : ℝ ↦
      (2 * N) * (g u - s * u) + (e u - c * u) + N * g u ^ 2 +
        2 * (e u * g u) + e u * g u ^ 2)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [add_assoc] using hPE
  have hBracket : (fun u : ℝ ↦
      e u + 2 * N * g u + 2 * e u * g u + N * g u ^ 2 +
        e u * g u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u) := by
    have hlin := he.add (hg.const_mul_left (2 * N))
    have hquad := ((heg.const_mul_left 2).add
      (hgSq.const_mul_left N)).add hegSq
    have hsum := hlin.add (hquad.trans huSqOu)
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by ring
    · exact Filter.EventuallyEq.rfl
  have hOutputNonlinear : (fun u : ℝ ↦ gt u *
      (e u + 2 * N * g u + 2 * e u * g u + N * g u ^ 2 +
        e u * g u ^ 2)) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hgt.mul hBracket
  have hOutput := (hgtR.const_mul_left N).add hOutputNonlinear
  have hTotal := (hPE.add hOutput).const_mul_left K
  apply hTotal.congr'
  · exact Filter.Eventually.of_forall fun u ↦ by
      unfold higham23BiniStepMajorant higham23BiniProductErrorCore
        higham23BiniProductNormCore
      ring
  · exact Filter.EventuallyEq.rfl

theorem higham23_biniMajorantRemainder_isBigO_u_sq
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) :
    ∀ depth, (fun u : ℝ ↦ higham23BiniMajorantRemainder alg depth u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2)
  | 0 => by
      simp only [higham23BiniMajorantRemainder, higham23BiniMajorantFamily,
        higham23BiniFirstOrderCoefficient, one_mul, sub_self]
      exact Asymptotics.isBigO_zero _ _
  | depth + 1 => by
      let K := higham23MillerWeightTotal alg
      let N : ℝ := (((h ^ depth : ℕ) : ℝ))
      let s : ℝ := (((h * h : ℕ) : ℝ))
      let τ : ℝ := (t : ℝ)
      let c := higham23BiniFirstOrderCoefficient alg depth
      let e : ℝ → ℝ := higham23BiniMajorantFamily alg depth
      let g : ℝ → ℝ := higham23MillerGammaFamily (h * h)
      let gt : ℝ → ℝ := higham23MillerGammaFamily t
      have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
        Asymptotics.isBigO_refl _ _
      have huOne : (fun u : ℝ ↦ u) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
        continuousAt_id.isBigO_one ℝ
      have huSqOu : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u) := by
        simpa only [pow_two, mul_one] using hu.mul huOne
      have heR : (fun u : ℝ ↦ e u - c * u)
          =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
        simpa [e, c, higham23BiniMajorantRemainder] using
          higham23_biniMajorantRemainder_isBigO_u_sq alg depth
      have he : e =O[𝓝 0] (fun u : ℝ ↦ u) := by
        have hlin := hu.const_mul_left c
        have hsum := hlin.add (heR.trans huSqOu)
        apply hsum.congr'
        · exact Filter.Eventually.of_forall fun u ↦ by
            dsimp [e, c, higham23BiniMajorantRemainder]
            ring
        · exact Filter.EventuallyEq.rfl
      have hgR : (fun u : ℝ ↦ g u - s * u)
          =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
        simpa [g, s, higham23MillerGammaFamily] using
          higham23_gammaRemainder_isBigO_u_sq (h * h)
      have hgtR : (fun u : ℝ ↦ gt u - τ * u)
          =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
        simpa [gt, τ, higham23MillerGammaFamily] using
          higham23_gammaRemainder_isBigO_u_sq t
      have hg : g =O[𝓝 0] (fun u : ℝ ↦ u) := by
        have hlin := hu.const_mul_left s
        have hsum := hlin.add (hgR.trans huSqOu)
        apply hsum.congr'
        · exact Filter.Eventually.of_forall fun u ↦ by ring
        · exact Filter.EventuallyEq.rfl
      have hgt : gt =O[𝓝 0] (fun u : ℝ ↦ u) := by
        have hlin := hu.const_mul_left τ
        have hsum := hlin.add (hgtR.trans huSqOu)
        apply hsum.congr'
        · exact Filter.Eventually.of_forall fun u ↦ by ring
        · exact Filter.EventuallyEq.rfl
      have hStep := higham23_biniStepRemainder_isBigO_u_sq
        K N s τ c e g gt he hg hgt heR hgR hgtR
      simpa [higham23BiniMajorantRemainder, higham23BiniMajorantFamily,
        higham23BiniFirstOrderCoefficient, K, N, s, τ, c, e, g, gt]
        using hStep

/-- Theorem 23.4 for the literal recursive evaluator, split into its explicit
first-order recurrence coefficient and a genuine `O(u²)` remainder. -/
theorem higham23_theorem23_4_biniLotti_firstOrder
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (halg : alg.IsNoncommutativeCorrect)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t)
    (depth : ℕ) (A B : Higham23BiniMatrix h depth) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23BiniNormLe h depth A a)
    (hB : Higham23BiniNormLe h depth B b) :
    Higham23BiniErrorLe h depth (higham23BiniMul h depth A B)
      (higham23BiniFlEvaluate fp alg depth A B)
      ((higham23BiniFirstOrderCoefficient alg depth * fp.u +
        higham23BiniMajorantRemainder alg depth fp.u) * a * b) := by
  have hExact := higham23_theorem23_4_biniLotti_exactMajorant
    fp alg halg hLinear hOutput depth A B a b ha hb hA hB
  rw [higham23_biniExactMajorant_eq_family fp alg hLinear hOutput depth] at hExact
  have hsplit : higham23BiniMajorantFamily alg depth fp.u =
      higham23BiniFirstOrderCoefficient alg depth * fp.u +
        higham23BiniMajorantRemainder alg depth fp.u := by
    unfold higham23BiniMajorantRemainder
    ring
  rwa [hsplit] at hExact

/-- An explicit algorithm-dependent `α` for (23.19). -/
noncomputable def higham23BiniLottiAlpha
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) : ℝ :=
  1 + higham23MillerWeightTotal alg *
    (2 * (((h * h : ℕ) : ℝ)) + (t : ℝ))

/-- An explicit algorithm-dependent `β` for (23.19). -/
noncomputable def higham23BiniLottiBeta
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) : ℝ :=
  1 + higham23MillerWeightTotal alg + (h : ℝ)

theorem higham23_biniWeightTotal_nonneg
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) :
    0 ≤ higham23MillerWeightTotal alg := by
  unfold higham23MillerWeightTotal
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    higham23_miller_weight_nonneg alg i j

theorem higham23_biniFirstOrderCoefficient_nonneg
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) :
    ∀ depth, 0 ≤ higham23BiniFirstOrderCoefficient alg depth
  | 0 => by simp [higham23BiniFirstOrderCoefficient]
  | depth + 1 => by
      rw [higham23BiniFirstOrderCoefficient]
      have hK := higham23_biniWeightTotal_nonneg alg
      have hc := higham23_biniFirstOrderCoefficient_nonneg alg depth
      positivity

theorem higham23_biniLottiAlpha_nonneg
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) :
    0 ≤ higham23BiniLottiAlpha alg := by
  unfold higham23BiniLottiAlpha
  have hK := higham23_biniWeightTotal_nonneg alg
  positivity

theorem higham23_biniLottiBeta_nonneg
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) :
    0 ≤ higham23BiniLottiBeta alg := by
  unfold higham23BiniLottiBeta
  have hK := higham23_biniWeightTotal_nonneg alg
  positivity

/-- The recurrence coefficient is bounded by the source shape
`α β^depth depth = α n^(log_h β) log_h n` at every positive depth. -/
theorem higham23_biniFirstOrderCoefficient_le_source
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) :
    ∀ depth,
      higham23BiniFirstOrderCoefficient alg (depth + 1) ≤
        higham23BiniLottiCoefficient (higham23BiniLottiAlpha alg)
          (higham23BiniLottiBeta alg) h (depth + 1)
  | 0 => by
      let K := higham23MillerWeightTotal alg
      let S : ℝ := 2 * (((h * h : ℕ) : ℝ)) + (t : ℝ)
      let q := K * S
      let α := higham23BiniLottiAlpha alg
      let β := higham23BiniLottiBeta alg
      have hK : 0 ≤ K := by simpa [K] using higham23_biniWeightTotal_nonneg alg
      have hS : 0 ≤ S := by dsimp [S]; positivity
      have hq : 0 ≤ q := mul_nonneg hK hS
      have hcast : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
      have hid : α * β = (K + q) +
          (1 + (h : ℝ) + q * K + q * (h : ℝ)) := by
        dsimp [α, β, q, K, S, higham23BiniLottiAlpha,
          higham23BiniLottiBeta]
        ring
      have hbase : K * (1 + S) ≤ α * β := by
        calc
          _ = K + q := by dsimp [q]; ring
          _ ≤ _ := by
            rw [hid]
            have hp : 0 ≤ 1 + (h : ℝ) + q * K + q * (h : ℝ) := by positivity
            linarith
      simpa [higham23BiniFirstOrderCoefficient, higham23BiniLottiCoefficient,
        K, S, α, β, Nat.cast_pow, Nat.cast_mul] using hbase
  | depth + 1 => by
      let K := higham23MillerWeightTotal alg
      let S : ℝ := 2 * (((h * h : ℕ) : ℝ)) + (t : ℝ)
      let q := K * S
      let α := higham23BiniLottiAlpha alg
      let β := higham23BiniLottiBeta alg
      have hK : 0 ≤ K := by simpa [K] using higham23_biniWeightTotal_nonneg alg
      have hS : 0 ≤ S := by dsimp [S]; positivity
      have hq : 0 ≤ q := mul_nonneg hK hS
      have hα : 0 ≤ α := by simpa [α] using higham23_biniLottiAlpha_nonneg alg
      have hβ : 0 ≤ β := by simpa [β] using higham23_biniLottiBeta_nonneg alg
      have hKβ : K ≤ β := by
        dsimp [K, β, higham23BiniLottiBeta]
        have hK0 := higham23_biniWeightTotal_nonneg alg
        have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
        linarith
      have hhβ : (h : ℝ) ≤ β := by
        dsimp [β, higham23BiniLottiBeta]
        have hK0 := higham23_biniWeightTotal_nonneg alg
        linarith
      have hqαβ : q ≤ α * β := by
        have hβone : 1 ≤ β := by
          dsimp [β, higham23BiniLottiBeta]
          have hK0 := higham23_biniWeightTotal_nonneg alg
          have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
          linarith
        have hqα : q ≤ α := by
          dsimp [q, α, K, S, higham23BiniLottiAlpha]
          linarith
        exact hqα.trans (by
          have := mul_le_mul_of_nonneg_left hβone hα
          simpa using this)
      have ih := higham23_biniFirstOrderCoefficient_le_source alg depth
      have ih' : higham23BiniFirstOrderCoefficient alg (depth + 1) ≤
          α * β ^ (depth + 1) * ((depth + 1 : ℕ) : ℝ) := by
        simpa [higham23BiniLottiCoefficient, α, β] using ih
      have hPow : ((h : ℝ) ^ (depth + 1)) ≤ β ^ (depth + 1) := by
        gcongr
      have hKterm : K * higham23BiniFirstOrderCoefficient alg (depth + 1) ≤
          α * β ^ (depth + 2) * ((depth + 1 : ℕ) : ℝ) := by
        calc
          _ ≤ K * (α * β ^ (depth + 1) * ((depth + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left ih' hK
          _ ≤ β * (α * β ^ (depth + 1) * ((depth + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hKβ (by positivity)
          _ = _ := by rw [pow_succ]; ring
      have hqterm : q * (h : ℝ) ^ (depth + 1) ≤
          α * β ^ (depth + 2) := by
        calc
          _ ≤ q * β ^ (depth + 1) := mul_le_mul_of_nonneg_left hPow hq
          _ ≤ (α * β) * β ^ (depth + 1) :=
            mul_le_mul_of_nonneg_right hqαβ (by positivity)
          _ = _ := by rw [pow_succ]; ring
      have hfinal : K * (higham23BiniFirstOrderCoefficient alg (depth + 1) +
          ((h : ℝ) ^ (depth + 1)) * S) ≤
          α * β ^ (depth + 2) * ((depth + 2 : ℕ) : ℝ) := by
        calc
          _ = K * higham23BiniFirstOrderCoefficient alg (depth + 1) +
              q * (h : ℝ) ^ (depth + 1) := by dsimp [q]; ring
          _ ≤ α * β ^ (depth + 2) * ((depth + 1 : ℕ) : ℝ) +
              α * β ^ (depth + 2) := add_le_add hKterm hqterm
          _ = _ := by push_cast; ring
      simpa [higham23BiniFirstOrderCoefficient, higham23BiniLottiCoefficient,
        K, S, α, β, Nat.cast_pow, Nat.cast_mul, Nat.add_assoc] using hfinal

/-- Equation (23.19) with explicit algorithm-dependent `α` and `β`, for the
literal recursive bilinear evaluator. -/
theorem higham23_theorem23_4_biniLotti_eq23_19
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (halg : alg.IsNoncommutativeCorrect)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t)
    (depth : ℕ) (A B : Higham23BiniMatrix h (depth + 1)) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23BiniNormLe h (depth + 1) A a)
    (hB : Higham23BiniNormLe h (depth + 1) B b) :
    Higham23BiniErrorLe h (depth + 1)
      (higham23BiniMul h (depth + 1) A B)
      (higham23BiniFlEvaluate fp alg (depth + 1) A B)
      ((higham23BiniLottiCoefficient (higham23BiniLottiAlpha alg)
          (higham23BiniLottiBeta alg) h (depth + 1) * fp.u +
        higham23BiniMajorantRemainder alg (depth + 1) fp.u) * a * b) := by
  have hFirst := higham23_theorem23_4_biniLotti_firstOrder fp alg halg
    hLinear hOutput (depth + 1) A B a b ha hb hA hB
  apply higham23_biniError_mono h (depth + 1) _ _ hFirst
  have hCoeff := higham23_biniFirstOrderCoefficient_le_source alg depth
  have hScale := mul_le_mul_of_nonneg_right hCoeff fp.u_nonneg
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  calc
    _ = (higham23BiniFirstOrderCoefficient alg (depth + 1) * fp.u +
        higham23BiniMajorantRemainder alg (depth + 1) fp.u) * (a * b) := by ring
    _ ≤ (higham23BiniLottiCoefficient (higham23BiniLottiAlpha alg)
          (higham23BiniLottiBeta alg) h (depth + 1) * fp.u +
        higham23BiniMajorantRemainder alg (depth + 1) fp.u) * (a * b) :=
      mul_le_mul_of_nonneg_right (add_le_add hScale le_rfl) hab
    _ = _ := by ring

theorem higham23_biniLotti_scaledRemainder_isBigO_u_sq
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) (depth : ℕ) (a b : ℝ) :
    (fun u : ℝ ↦ higham23BiniMajorantRemainder alg depth u * a * b)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  have hR := (higham23_biniMajorantRemainder_isBigO_u_sq alg depth).const_mul_left
    (a * b)
  apply hR.congr'
  · exact Filter.Eventually.of_forall fun u ↦ by ring
  · exact Filter.EventuallyEq.rfl

end NumStability
