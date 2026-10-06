/-
  Algorithms/LU/BlockLUFirstOrderFamilies.lean

  Source-faithful family-level first-order contracts for Higham Chapter 13.

  The legacy `FirstOrderLe` API in `BlockLU` is a useful pointwise envelope,
  but its existential coefficient is selected after fixing `u`; it therefore
  does not express the source's uniform `O(u^2)` remainder.  This module uses
  `FamilyFirstOrderLe` and ties every scalar norm in equations (13.4)--(13.7),
  (13.14), and (13.15) to the matrix occurring in the corresponding equation.
-/

import NumStability.Algorithms.LU.BlockLU
import NumStability.Analysis.FirstOrder

namespace NumStability

open Filter Asymptotics
open scoped Topology

/-! ## Primitive operation models -/

/-- Higham equation (13.4), uniformly along a vanishing-roundoff family.
Both operand norms are locally bounded, so later products cannot hide an
index-dependent constant. -/
structure Higham13MatMulFamilySpec {ι : Type*} {l : Filter ι}
    (U : RoundoffFamily ι l) {m n p : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) (c₁ : ℝ)
    (A : ι → Matrix (Fin m) (Fin n) ℝ)
    (B : ι → Matrix (Fin n) (Fin p) ℝ)
    (Chat DeltaC : ι → Matrix (Fin m) (Fin p) ℝ) where
  equation : ∀ t, Chat t = A t * B t + DeltaC t
  left_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => maxEntryNormRect hm hn (A t))
  right_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => maxEntryNormRect hn hp (B t))
  norm_bound : FamilyFirstOrderLe l U.unit
    (fun t => c₁ * U.unit t * maxEntryNormRect hm hn (A t) *
      maxEntryNormRect hn hp (B t))
    (fun t => maxEntryNormRect hm hp (DeltaC t))

/-- Higham equation (13.5), left triangular-solve orientation. -/
structure Higham13TriangularSolveFamilySpec {ι : Type*} {l : Filter ι}
    (U : RoundoffFamily ι l) {m p : ℕ}
    (hm : 0 < m) (hp : 0 < p) (c₂ : ℝ)
    (T : ι → Matrix (Fin m) (Fin m) ℝ)
    (B DeltaB Xhat : ι → Matrix (Fin m) (Fin p) ℝ) where
  equation : ∀ t, T t * Xhat t = B t + DeltaB t
  triangular_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => maxEntryNorm hm (T t))
  solution_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => maxEntryNormRect hm hp (Xhat t))
  norm_bound : FamilyFirstOrderLe l U.unit
    (fun t => c₂ * U.unit t * maxEntryNorm hm (T t) *
      maxEntryNormRect hm hp (Xhat t))
    (fun t => maxEntryNormRect hm hp (DeltaB t))

/-- Higham equation (13.5), right triangular-solve orientation. -/
structure Higham13RightTriangularSolveFamilySpec {ι : Type*} {l : Filter ι}
    (U : RoundoffFamily ι l) {m p : ℕ}
    (hm : 0 < m) (hp : 0 < p) (c₂ : ℝ)
    (T : ι → Matrix (Fin p) (Fin p) ℝ)
    (B DeltaB Xhat : ι → Matrix (Fin m) (Fin p) ℝ) where
  equation : ∀ t, Xhat t * T t = B t + DeltaB t
  triangular_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => maxEntryNorm hp (T t))
  solution_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => maxEntryNormRect hm hp (Xhat t))
  norm_bound : FamilyFirstOrderLe l U.unit
    (fun t => c₂ * U.unit t * maxEntryNorm hp (T t) *
      maxEntryNormRect hm hp (Xhat t))
    (fun t => maxEntryNormRect hm hp (DeltaB t))

/-- Higham equation (13.6), local diagonal-block LU model. -/
structure Higham13LocalLUFamilySpec {ι : Type*} {l : Filter ι}
    (U : RoundoffFamily ι l) {r : ℕ} (hr : 0 < r) (c₃ : ℝ)
    (A DeltaA Lhat Uhat : ι → Matrix (Fin r) (Fin r) ℝ) where
  equation : ∀ t, Lhat t * Uhat t = A t + DeltaA t
  lower_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => maxEntryNorm hr (Lhat t))
  upper_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => maxEntryNorm hr (Uhat t))
  norm_bound : FamilyFirstOrderLe l U.unit
    (fun t => c₃ * U.unit t * maxEntryNorm hr (Lhat t) *
      maxEntryNorm hr (Uhat t))
    (fun t => maxEntryNorm hr (DeltaA t))

/-- Rounded subtraction in equation (13.10), with actual matrix norms. -/
structure Higham13SubtractionFamilySpec {ι : Type*} {l : Filter ι}
    (U : RoundoffFamily ι l) {m p : ℕ}
    (hm : 0 < m) (hp : 0 < p)
    (A Computed F Shat : ι → Matrix (Fin m) (Fin p) ℝ) where
  equation : ∀ t, Shat t = A t - Computed t + F t
  norm_bound : ∀ t,
    maxEntryNormRect hm hp (F t) ≤ U.unit t *
      (maxEntryNormRect hm hp (A t) +
        maxEntryNormRect hm hp (Computed t))

/-- Higham equation (13.14), Algorithm 13.3 step-2 block solve. -/
structure Higham13BlockSolveFamilySpec {ι : Type*} {l : Filter ι}
    (U : RoundoffFamily ι l) {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (c₄ : ℝ)
    (Lhat21 A21 E21 : ι → Matrix (Fin s) (Fin r) ℝ)
    (A11 : ι → Matrix (Fin r) (Fin r) ℝ) where
  equation : ∀ t, Lhat21 t * A11 t = A21 t + E21 t
  multiplier_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => maxEntryNormRect hs hr (Lhat21 t))
  diagonal_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => maxEntryNorm hr (A11 t))
  norm_bound : FamilyFirstOrderLe l U.unit
    (fun t => c₄ * U.unit t * maxEntryNormRect hs hr (Lhat21 t) *
      maxEntryNorm hr (A11 t))
    (fun t => maxEntryNormRect hs hr (E21 t))

/-- Higham equation (13.15), diagonal-block solve perturbation. -/
structure Higham13DiagonalBlockSolveFamilySpec {ι : Type*} {l : Filter ι}
    (U : RoundoffFamily ι l) {r p : ℕ}
    (hr : 0 < r) (hp : 0 < p) (c₅ : ℝ)
    (Uii DeltaUii : ι → Matrix (Fin r) (Fin r) ℝ)
    (Xhat D : ι → Matrix (Fin r) (Fin p) ℝ) where
  equation : ∀ t, (Uii t + DeltaUii t) * Xhat t = D t
  diagonal_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => maxEntryNorm hr (Uii t))
  norm_bound : FamilyFirstOrderLe l U.unit
    (fun t => c₅ * U.unit t * maxEntryNorm hr (Uii t))
    (fun t => maxEntryNorm hr (DeltaUii t))

/-! ## Source conclusions -/

/-- Family-level Theorem 13.5 / equation (13.7) conclusion.  This is an
output contract, not a computation hypothesis: the residual equation and the
bound both use the actual assembled matrix and factor norms. -/
structure Higham13PartitionedLUFamilySpec {ι : Type*} {l : Filter ι}
    (U : RoundoffFamily ι l) {n : ℕ} (hn : 0 < n)
    (δ θ : ℝ)
    (A DeltaA Lhat Uhat : ι → Matrix (Fin n) (Fin n) ℝ) : Prop where
  equation : ∀ t, Lhat t * Uhat t = A t + DeltaA t
  input_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => maxEntryNorm hn (A t))
  lower_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => maxEntryNorm hn (Lhat t))
  upper_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => maxEntryNorm hn (Uhat t))
  norm_bound : FamilyFirstOrderLe l U.unit
    (fun t => U.unit t *
      (δ * maxEntryNorm hn (A t) +
        θ * maxEntryNorm hn (Lhat t) *
          maxEntryNorm hn (Uhat t)))
    (fun t => maxEntryNorm hn (DeltaA t))

/-! ## Uniform scalar closure for the recursive proof of Theorem 13.5 -/

/-- A nonnegative family bounded by an `O(1)` family is itself `O(1)`. -/
theorem higham13_scalarFamily_isBigO_one_of_le {ι : Type*} {l : Filter ι}
    {x y : ι → ℝ} (hx : ∀ t, 0 ≤ x t) (hy : ∀ t, 0 ≤ y t)
    (hxy : ∀ t, x t ≤ y t) (hyO : ScalarFamilyIsBigOOne l y) :
    ScalarFamilyIsBigOOne l x :=
  ScalarFamilyIsBigOOne.mono hx hy hxy hyO

/-- A uniform first-order bound with an `O(1)` leading term also makes its
nonnegative value locally bounded. -/
theorem higham13_familyFirstOrder_value_isBigO_one
    {ι : Type*} {l : Filter ι} (U : RoundoffFamily ι l)
    {leading value : ι → ℝ}
    (hleading : ∀ t, 0 ≤ leading t) (hvalue : ∀ t, 0 ≤ value t)
    (hleadingO : ScalarFamilyIsBigOOne l leading)
    (h : FamilyFirstOrderLe l U.unit leading value) :
    ScalarFamilyIsBigOOne l value := by
  rcases h with ⟨remainder, hremainder, hbound, hremO⟩
  have huSqO : ScalarFamilyIsBigOOne l (fun t => U.unit t ^ 2) := by
    simpa [pow_two] using U.unit_isBigO_one.mul U.unit_isBigO_one
  have hremOne : ScalarFamilyIsBigOOne l remainder := hremO.trans huSqO
  exact higham13_scalarFamily_isBigO_one_of_le hvalue
    (fun t => add_nonneg (hleading t) (hremainder t)) hbound
    (hleadingO.add hremOne)

/-- Equation (13.10) and the uniform matrix-product model imply that the
rounded Schur complement differs from `‖A₂₂‖ + ‖L₂₁‖‖U₁₂‖` by `O(u)`.
All quantities here are the actual nonnegative norm families used later in
the recursive error estimate. -/
theorem higham13_theorem13_5_schur_norm_family_linear_majorant
    {ι : Type*} {l : Filter ι} (U : RoundoffFamily ι l)
    (c₁ : ℝ)
    (normA normL normU normChat normF normDeltaC normShat : ι → ℝ)
    (hc₁ : 0 ≤ c₁)
    (hA : ∀ t, 0 ≤ normA t) (hL : ∀ t, 0 ≤ normL t)
    (hU : ∀ t, 0 ≤ normU t) (hChat_nonneg : ∀ t, 0 ≤ normChat t)
    (hDeltaC_nonneg : ∀ t, 0 ≤ normDeltaC t)
    (hA_O : ScalarFamilyIsBigOOne l normA)
    (hL_O : ScalarFamilyIsBigOOne l normL)
    (hU_O : ScalarFamilyIsBigOOne l normU)
    (hDeltaC : FamilyFirstOrderLe l U.unit
      (fun t => c₁ * U.unit t * normL t * normU t) normDeltaC)
    (hF : ∀ t, normF t ≤ U.unit t * (normA t + normChat t))
    (hChat : ∀ t, normChat t ≤ normL t * normU t + normDeltaC t)
    (hShat : ∀ t, normShat t ≤ normA t + normChat t + normF t) :
    FamilyLinearRemainderLe l U.unit
      (fun t => normA t + normL t * normU t) normShat := by
  rcases hDeltaC with ⟨remainder, hremainder, hDeltaC_bound, hremO⟩
  have hunitO := U.unit_isBigO_one
  have hLUO : ScalarFamilyIsBigOOne l (fun t => normL t * normU t) :=
    hL_O.mul hU_O
  have hleadingO : ScalarFamilyIsBigOOne l
      (fun t => c₁ * U.unit t * normL t * normU t) := by
    simpa only [mul_assoc] using
      ((ScalarFamilyIsBigOOne.const c₁).mul hunitO).mul hLUO
  have hDeltaCO : ScalarFamilyIsBigOOne l normDeltaC :=
    higham13_familyFirstOrder_value_isBigO_one U
      (fun t => mul_nonneg
        (mul_nonneg (mul_nonneg hc₁ (U.unit_nonneg t)) (hL t)) (hU t))
      hDeltaC_nonneg hleadingO
      ⟨remainder, hremainder, hDeltaC_bound, hremO⟩
  have hChatO : ScalarFamilyIsBigOOne l normChat :=
    higham13_scalarFamily_isBigO_one_of_le hChat_nonneg
      (fun t => add_nonneg (mul_nonneg (hL t) (hU t)) (hDeltaC_nonneg t))
      hChat (hLUO.add hDeltaCO)
  refine ⟨fun t =>
      c₁ * U.unit t * normL t * normU t + remainder t +
        U.unit t * (normA t + normChat t), ?_, ?_, ?_⟩
  · intro t
    exact add_nonneg
      (add_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg hc₁ (U.unit_nonneg t)) (hL t)) (hU t))
        (hremainder t))
      (mul_nonneg (U.unit_nonneg t) (add_nonneg (hA t) (hChat_nonneg t)))
  · intro t
    calc
      normShat t ≤ normA t + normChat t + normF t := hShat t
      _ ≤ normA t + (normL t * normU t + normDeltaC t) +
          U.unit t * (normA t + normChat t) := by
        linarith [hChat t, hF t]
      _ ≤ normA t + normL t * normU t +
          (c₁ * U.unit t * normL t * normU t + remainder t +
            U.unit t * (normA t + normChat t)) := by
        linarith [hDeltaC_bound t]
  · have hleadingLinear :
        (fun t => c₁ * U.unit t * normL t * normU t) =O[l] U.unit := by
      simpa only [mul_assoc, mul_one] using
        ((Asymptotics.isBigO_refl U.unit l).const_mul_left c₁).mul hLUO
    have hremLinear : remainder =O[l] U.unit :=
      hremO.trans U.unit_sq_isBigO_unit
    have hlast : (fun t => U.unit t * (normA t + normChat t)) =O[l]
        U.unit := by
      simpa using (Asymptotics.isBigO_refl U.unit l).mul (hA_O.add hChatO)
    exact (hleadingLinear.add hremLinear).add hlast

/-- The recursive tail bound may be rewritten using the full-matrix norm
families.  The Schur-norm transfer contributes only `O(u²)` after the outer
factor of `u`. -/
theorem higham13_theorem13_5_recursive_error_family_global_majorant
    {ι : Type*} {l : Filter ι} (U : RoundoffFamily ι l)
    (δ θ : ℝ)
    (normA normL normU normShat normLtail normUtail normDeltaTail : ι → ℝ)
    (hδ : 0 ≤ δ) (hθ : 0 ≤ θ)
    (hL : ∀ t, 0 ≤ normL t) (hUtail : ∀ t, 0 ≤ normUtail t)
    (hind : FamilyFirstOrderLe l U.unit
      (fun t => U.unit t *
        (δ * normShat t + θ * normLtail t * normUtail t)) normDeltaTail)
    (hSchur : FamilyLinearRemainderLe l U.unit
      (fun t => normA t + normL t * normU t) normShat)
    (hLtail_le : ∀ t, normLtail t ≤ normL t)
    (hUtail_le : ∀ t, normUtail t ≤ normU t) :
    FamilyFirstOrderLe l U.unit
      (fun t => U.unit t *
        (δ * normA t + δ * (normL t * normU t) +
          θ * (normL t * normU t))) normDeltaTail := by
  rcases hSchur with ⟨transfer, htransfer_nonneg, hShat_bound, htransferO⟩
  have hcoefficient : FamilyLinearRemainderLe l U.unit
      (fun t => δ * normA t + δ * (normL t * normU t) +
        θ * (normL t * normU t))
      (fun t => δ * normShat t + θ * normLtail t * normUtail t) := by
    refine ⟨fun t => δ * transfer t,
      (fun t => mul_nonneg hδ (htransfer_nonneg t)), ?_, ?_⟩
    · intro t
      have hTailProduct : normLtail t * normUtail t ≤ normL t * normU t :=
        mul_le_mul (hLtail_le t) (hUtail_le t) (hUtail t) (hL t)
      have hSchurScaled := mul_le_mul_of_nonneg_left (hShat_bound t) hδ
      have hTailScaled := mul_le_mul_of_nonneg_left hTailProduct hθ
      dsimp
      linarith
    · simpa using htransferO.const_mul_left δ
  have hind' : FamilyFirstOrderLe l U.unit
      (fun t => (1 : ℝ) * U.unit t *
        (0 + (δ * normShat t + θ * normLtail t * normUtail t)))
      normDeltaTail := by
    convert hind using 1
    funext t
    ring
  have hscaled := FamilyFirstOrderLe.coefficient_of_linear_transfer_to
    (c := (1 : ℝ)) (fixed := fun _ => 0) zero_le_one U.unit_nonneg
    hind' hcoefficient
  convert hscaled using 1
  funext t
  ring

/-- Uniform family form of the local Schur-update estimate (13.11b). -/
theorem higham13_theorem13_5_schur_error_family_firstOrder
    {ι : Type*} {l : Filter ι} (U : RoundoffFamily ι l)
    (c₁ : ℝ)
    (normA normL normU normChat normF normDeltaC normDeltaS : ι → ℝ)
    (hc₁ : 0 ≤ c₁)
    (hL : ∀ t, 0 ≤ normL t) (hU : ∀ t, 0 ≤ normU t)
    (hDeltaC_nonneg : ∀ t, 0 ≤ normDeltaC t)
    (hL_O : ScalarFamilyIsBigOOne l normL)
    (hU_O : ScalarFamilyIsBigOOne l normU)
    (hDeltaC : FamilyFirstOrderLe l U.unit
      (fun t => c₁ * U.unit t * normL t * normU t) normDeltaC)
    (hF : ∀ t, normF t ≤ U.unit t * (normA t + normChat t))
    (hChat : ∀ t, normChat t ≤ normL t * normU t + normDeltaC t)
    (hDeltaS : ∀ t, normDeltaS t ≤ normDeltaC t + normF t) :
    FamilyFirstOrderLe l U.unit
      (fun t => U.unit t *
        (normA t + normL t * normU t + c₁ * (normL t * normU t)))
      normDeltaS := by
  rcases hDeltaC with ⟨remainder, hremainder, hDeltaC_bound, hremO⟩
  have hLUO : ScalarFamilyIsBigOOne l (fun t => normL t * normU t) :=
    hL_O.mul hU_O
  have hleadingLinear :
      (fun t => c₁ * U.unit t * normL t * normU t) =O[l] U.unit := by
    simpa only [mul_assoc, mul_one] using
      ((Asymptotics.isBigO_refl U.unit l).const_mul_left c₁).mul hLUO
  have hremLinear : remainder =O[l] U.unit :=
    hremO.trans U.unit_sq_isBigO_unit
  have hDeltaCLinear : normDeltaC =O[l] U.unit := by
    have hcompare := scalarFamily_isBigO_of_nonneg_le (l := l) hDeltaC_nonneg
      (fun t => add_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg hc₁ (U.unit_nonneg t)) (hL t)) (hU t))
        (hremainder t)) hDeltaC_bound
    exact hcompare.trans (hleadingLinear.add hremLinear)
  have hChatTransfer : FamilyLinearRemainderLe l U.unit
      (fun t => normL t * normU t) normChat :=
    ⟨normDeltaC, hDeltaC_nonneg, hChat, hDeltaCLinear⟩
  have hFfirst : FamilyFirstOrderLe l U.unit
      (fun t => U.unit t * (normA t + normL t * normU t)) normF := by
    have hFzero : FamilyFirstOrderLe l U.unit
        (fun t => (1 : ℝ) * U.unit t * (normA t + normChat t)) normF :=
      FamilyFirstOrderLe.of_le (fun t => by simpa using hF t)
    have htransfer := FamilyFirstOrderLe.coefficient_of_linear_transfer_to
      (c := (1 : ℝ)) zero_le_one U.unit_nonneg hFzero hChatTransfer
    convert htransfer using 1
    funext t
    ring
  have hsum := FamilyFirstOrderLe.add
    (⟨remainder, hremainder, hDeltaC_bound, hremO⟩ :
      FamilyFirstOrderLe l U.unit
        (fun t => c₁ * U.unit t * normL t * normU t) normDeltaC)
    hFfirst hDeltaS
  convert hsum using 1
  funext t
  ring

/-- Scalar recursive execution certificate for the family-level proof of
Theorem 13.5.  Its constructors contain only the primitive operation bounds
and ordinary norm inequalities used in Higham's induction; the advertised
global error bound is not a field. -/
inductive Higham13PartitionedLUScalarFamilyComputation
    {ι : Type*} {l : Filter ι} (U : RoundoffFamily ι l)
    (c₁ c₂ c₃ : ℝ) :
    ℕ → (ι → ℝ) → (ι → ℝ) → (ι → ℝ) → (ι → ℝ) → Prop
  | base
      (normA normL normU normDeltaA : ι → ℝ)
      (hA : ∀ t, 0 ≤ normA t) (hL : ∀ t, 0 ≤ normL t)
      (hU : ∀ t, 0 ≤ normU t)
      (hA_O : ScalarFamilyIsBigOOne l normA)
      (hL_O : ScalarFamilyIsBigOOne l normL)
      (hU_O : ScalarFamilyIsBigOOne l normU)
      (hlocal : FamilyFirstOrderLe l U.unit
        (fun t => c₃ * U.unit t * normL t * normU t) normDeltaA) :
      Higham13PartitionedLUScalarFamilyComputation U c₁ c₂ c₃ 1
        normA normL normU normDeltaA
  | step
      (m : ℕ)
      (normA normL normU normChat normF normDeltaA11 normDeltaA12
        normDeltaA21 normDeltaC normDeltaS normDeltaTail normDeltaA22
        normShat normLtail normUtail : ι → ℝ)
      (hA : ∀ t, 0 ≤ normA t) (hL : ∀ t, 0 ≤ normL t)
      (hU : ∀ t, 0 ≤ normU t)
      (hChat_nonneg : ∀ t, 0 ≤ normChat t)
      (hDeltaC_nonneg : ∀ t, 0 ≤ normDeltaC t)
      (hUtail_nonneg : ∀ t, 0 ≤ normUtail t)
      (hA_O : ScalarFamilyIsBigOOne l normA)
      (hL_O : ScalarFamilyIsBigOOne l normL)
      (hU_O : ScalarFamilyIsBigOOne l normU)
      (h11 : FamilyFirstOrderLe l U.unit
        (fun t => c₃ * U.unit t * normL t * normU t) normDeltaA11)
      (h12 : FamilyFirstOrderLe l U.unit
        (fun t => c₂ * U.unit t * normL t * normU t) normDeltaA12)
      (h21 : FamilyFirstOrderLe l U.unit
        (fun t => c₂ * U.unit t * normL t * normU t) normDeltaA21)
      (hmul : FamilyFirstOrderLe l U.unit
        (fun t => c₁ * U.unit t * normL t * normU t) normDeltaC)
      (hF : ∀ t, normF t ≤ U.unit t * (normA t + normChat t))
      (htail : Higham13PartitionedLUScalarFamilyComputation U c₁ c₂ c₃
        (m + 1) normShat normLtail normUtail normDeltaTail)
      (hDeltaS : ∀ t, normDeltaS t ≤ normDeltaC t + normF t)
      (hChat : ∀ t, normChat t ≤ normL t * normU t + normDeltaC t)
      (hShat : ∀ t, normShat t ≤ normA t + normChat t + normF t)
      (hDeltaA22 : ∀ t, normDeltaA22 t ≤ normDeltaS t + normDeltaTail t)
      (hLtail_le : ∀ t, normLtail t ≤ normL t)
      (hUtail_le : ∀ t, normUtail t ≤ normU t) :
      Higham13PartitionedLUScalarFamilyComputation U c₁ c₂ c₃ (m + 2)
        normA normL normU
        (fun t => max (max (normDeltaA11 t) (normDeltaA12 t))
          (max (normDeltaA21 t) (normDeltaA22 t)))

/-- The scalar family computation derives Higham's complete recurrence bound
with one uniform `O(u²)` remainder. -/
theorem Higham13PartitionedLUScalarFamilyComputation.to_bound
    {ι : Type*} {l : Filter ι} {U : RoundoffFamily ι l}
    {c₁ c₂ c₃ : ℝ} {m : ℕ}
    {normA normL normU normDeltaA : ι → ℝ}
    (hcomp : Higham13PartitionedLUScalarFamilyComputation U c₁ c₂ c₃ m
      normA normL normU normDeltaA)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) :
    FamilyFirstOrderLe l U.unit
        (fun t => U.unit t *
          (blockErrorDelta m * normA t +
            blockErrorTheta c₁ c₂ c₃ m * normL t * normU t)) normDeltaA ∧
      ScalarFamilyIsBigOOne l normA ∧
      ScalarFamilyIsBigOOne l normL ∧
      ScalarFamilyIsBigOOne l normU := by
  induction hcomp with
  | base normA normL normU normDeltaA hA hL hU hA_O hL_O hU_O hlocal =>
      refine ⟨?_, hA_O, hL_O, hU_O⟩
      convert hlocal using 1
      funext t
      simp [blockErrorDelta, blockErrorTheta]
      ring
  | step m normA normL normU normChat normF normDeltaA11 normDeltaA12
      normDeltaA21 normDeltaC normDeltaS normDeltaTail normDeltaA22
      normShat normLtail normUtail hA hL hU hChat_nonneg hDeltaC_nonneg
      hUtail_nonneg hA_O hL_O hU_O h11 h12 h21 hmul hF htail hDeltaS hChat hShat
      hDeltaA22 hLtail_le hUtail_le ih =>
      have hSchurMajorant : FamilyLinearRemainderLe l U.unit
          (fun t => normA t + normL t * normU t) normShat :=
        higham13_theorem13_5_schur_norm_family_linear_majorant U c₁
          normA normL normU normChat normF normDeltaC normShat hc₁
          hA hL hU hChat_nonneg hDeltaC_nonneg hA_O hL_O hU_O hmul
          hF hChat hShat
      have hTailGlobal : FamilyFirstOrderLe l U.unit
          (fun t => U.unit t *
            (blockErrorDelta (m + 1) * normA t +
              blockErrorDelta (m + 1) * (normL t * normU t) +
              blockErrorTheta c₁ c₂ c₃ (m + 1) *
                (normL t * normU t))) normDeltaTail :=
        higham13_theorem13_5_recursive_error_family_global_majorant U
          (blockErrorDelta (m + 1))
          (blockErrorTheta c₁ c₂ c₃ (m + 1))
          normA normL normU normShat normLtail normUtail normDeltaTail
          (blockErrorDelta_nonneg (m + 1))
          (blockErrorTheta_nonneg_of_c3_nonneg c₁ c₂ c₃ hc₃ (m + 1))
          hL hUtail_nonneg ih.1 hSchurMajorant hLtail_le hUtail_le
      have hSchurError :=
        higham13_theorem13_5_schur_error_family_firstOrder U c₁
          normA normL normU normChat normF normDeltaC normDeltaS hc₁
          hL hU hDeltaC_nonneg hL_O hU_O hmul hF hChat hDeltaS
      have h22raw := FamilyFirstOrderLe.add hSchurError hTailGlobal hDeltaA22
      have h22 : FamilyFirstOrderLe l U.unit
          (fun t => U.unit t *
            ((1 + blockErrorDelta (m + 1)) * normA t +
              (1 + c₁ + blockErrorDelta (m + 1) +
                blockErrorTheta c₁ c₂ c₃ (m + 1)) *
                  normL t * normU t)) normDeltaA22 := by
        convert h22raw using 1
        funext t
        ring
      have hcombined :=
        (FamilyFirstOrderLe.combineMax h11 h12).combineMax
          (FamilyFirstOrderLe.combineMax h21 h22)
      refine ⟨hcombined.mono_leading ?_, hA_O, hL_O, hU_O⟩
      intro t
      exact higham13_theorem13_5_recurrence_step m
        (c₃ * U.unit t * normL t * normU t)
        (c₂ * U.unit t * normL t * normU t)
        (c₂ * U.unit t * normL t * normU t)
        (U.unit t *
          ((1 + blockErrorDelta (m + 1)) * normA t +
            (1 + c₁ + blockErrorDelta (m + 1) +
              blockErrorTheta c₁ c₂ c₃ (m + 1)) * normL t * normU t))
        (normA t) (normL t) (normU t) (U.unit t) c₁ c₂ c₃
        (U.unit_nonneg t) hc₁ hc₂ hc₃ (hA t) (hL t) (hU t)
        le_rfl le_rfl le_rfl le_rfl

/-- **Theorem 13.5 / equation (13.7), source-faithful family endpoint.**

The exact matrix residual comes from an actual recursive partitioned-LU
execution at every family index.  Independently, the scalar recursive
certificate derives a single uniform `O(u²)` bound, and all four scalar
families in the conclusion are definitionally the max-entry norms of the
displayed matrices.  Thus neither the final residual equation nor unrelated
norm fields are accepted as hypotheses. -/
theorem higham13_theorem13_5_eq13_7_family_from_computation
    {ι : Type*} {l : Filter ι} (U : RoundoffFamily ι l)
    {n m : ℕ} (hn : 0 < n) (c₁ c₂ c₃ : ℝ)
    (A DeltaA Lhat Uhat : ι → Matrix (Fin n) (Fin n) ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hmatrix : ∀ t,
      PartitionedLUComputationFirstOrder (U.unit t) c₁ c₂ c₃ m
        (maxEntryNorm hn (A t)) (maxEntryNorm hn (Lhat t))
        (maxEntryNorm hn (Uhat t)) (maxEntryNorm hn (DeltaA t))
        (A t) (DeltaA t) (Lhat t) (Uhat t))
    (hscalar : Higham13PartitionedLUScalarFamilyComputation U c₁ c₂ c₃ m
      (fun t => maxEntryNorm hn (A t))
      (fun t => maxEntryNorm hn (Lhat t))
      (fun t => maxEntryNorm hn (Uhat t))
      (fun t => maxEntryNorm hn (DeltaA t))) :
    Higham13PartitionedLUFamilySpec U hn (blockErrorDelta m)
      (blockErrorTheta c₁ c₂ c₃ m) A DeltaA Lhat Uhat := by
  have hbound := hscalar.to_bound hc₁ hc₂ hc₃
  refine ⟨?_, hbound.2.1, hbound.2.2.1, hbound.2.2.2, hbound.1⟩
  intro t
  exact (higham13_theorem13_5_eq13_7_from_computation
    (hmatrix t) (U.unit_nonneg t) hc₁ hc₂ hc₃).1

/-- Uniform Table 13.1 composition.  The product comparison is `O(u)`, so
substitution into the outer Theorem 13.6 factor contributes only `O(u²)`. -/
theorem higham13_table13_1_family_from_product_transfer
    {ι : Type*} {l : Filter ι} (U : RoundoffFamily ι l)
    (c tableValue : ℝ)
    (normA computedProduct err : ι → ℝ)
    (hc : 0 ≤ c)
    (hErr : FamilyFirstOrderLe l U.unit
      (fun t => c * U.unit t * (normA t + computedProduct t)) err)
    (hProductTransfer : FamilyLinearRemainderLe l U.unit
      (fun t => tableValue * normA t) computedProduct) :
    FamilyFirstOrderLe l U.unit
      (fun t => c * U.unit t * ((1 + tableValue) * normA t)) err := by
  have h := FamilyFirstOrderLe.coefficient_of_linear_transfer_to
    hc U.unit_nonneg hErr hProductTransfer
  convert h using 1
  funext t
  ring

/-- Table 13.1 bridge with every scalar in the premise and conclusion tied to
the displayed matrix families' actual max-entry norms. -/
theorem higham13_table13_1_family_actual_maxEntry
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    {n : ℕ} (hn : 0 < n) (c tableValue : ℝ)
    (A Lhat Uhat Delta : ι → Matrix (Fin n) (Fin n) ℝ)
    (hc : 0 ≤ c)
    (hTheorem13_6 : FamilyFirstOrderLe l Uround.unit
      (fun t => c * Uround.unit t *
        (maxEntryNorm hn (A t) +
          maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t)))
      (fun t => maxEntryNorm hn (Delta t)))
    (hProductTransfer : FamilyLinearRemainderLe l Uround.unit
      (fun t => tableValue * maxEntryNorm hn (A t))
      (fun t => maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t))) :
    FamilyFirstOrderLe l Uround.unit
      (fun t => c * Uround.unit t *
        ((1 + tableValue) * maxEntryNorm hn (A t)))
      (fun t => maxEntryNorm hn (Delta t)) :=
  higham13_table13_1_family_from_product_transfer Uround c tableValue
    (fun t => maxEntryNorm hn (A t))
    (fun t => maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t))
    (fun t => maxEntryNorm hn (Delta t)) hc hTheorem13_6 hProductTransfer

/-- Equation (13.4) can be read directly from its family operation model. -/
theorem higham13_eq13_4_family_from_spec {ι : Type*} {l : Filter ι}
    (U : RoundoffFamily ι l) {m n p : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) (c₁ : ℝ)
    (A : ι → Matrix (Fin m) (Fin n) ℝ)
    (B : ι → Matrix (Fin n) (Fin p) ℝ)
    (Chat DeltaC : ι → Matrix (Fin m) (Fin p) ℝ)
    (h : Higham13MatMulFamilySpec U hm hn hp c₁ A B Chat DeltaC) :
    (∀ t, Chat t = A t * B t + DeltaC t) ∧
      FamilyFirstOrderLe l U.unit
        (fun t => c₁ * U.unit t * maxEntryNormRect hm hn (A t) *
          maxEntryNormRect hn hp (B t))
        (fun t => maxEntryNormRect hm hp (DeltaC t)) :=
  ⟨h.equation, h.norm_bound⟩

/-- Equation (13.5) can be read directly from its family operation model. -/
theorem higham13_eq13_5_family_from_spec {ι : Type*} {l : Filter ι}
    (U : RoundoffFamily ι l) {m p : ℕ}
    (hm : 0 < m) (hp : 0 < p) (c₂ : ℝ)
    (T : ι → Matrix (Fin m) (Fin m) ℝ)
    (B DeltaB Xhat : ι → Matrix (Fin m) (Fin p) ℝ)
    (h : Higham13TriangularSolveFamilySpec U hm hp c₂ T B DeltaB Xhat) :
    (∀ t, T t * Xhat t = B t + DeltaB t) ∧
      FamilyFirstOrderLe l U.unit
        (fun t => c₂ * U.unit t * maxEntryNorm hm (T t) *
          maxEntryNormRect hm hp (Xhat t))
        (fun t => maxEntryNormRect hm hp (DeltaB t)) :=
  ⟨h.equation, h.norm_bound⟩

/-- Equation (13.6) can be read directly from its family operation model. -/
theorem higham13_eq13_6_family_from_spec {ι : Type*} {l : Filter ι}
    (U : RoundoffFamily ι l) {r : ℕ} (hr : 0 < r) (c₃ : ℝ)
    (A DeltaA Lhat Uhat : ι → Matrix (Fin r) (Fin r) ℝ)
    (h : Higham13LocalLUFamilySpec U hr c₃ A DeltaA Lhat Uhat) :
    (∀ t, Lhat t * Uhat t = A t + DeltaA t) ∧
      FamilyFirstOrderLe l U.unit
        (fun t => c₃ * U.unit t * maxEntryNorm hr (Lhat t) *
          maxEntryNorm hr (Uhat t))
        (fun t => maxEntryNorm hr (DeltaA t)) :=
  ⟨h.equation, h.norm_bound⟩

end NumStability
