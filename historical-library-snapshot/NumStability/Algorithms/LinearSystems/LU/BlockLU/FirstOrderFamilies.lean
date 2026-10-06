import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum

/-!
# Reusable first-order block-LU family contracts

Uniform family-level operation models used by the Chapter 13 source layer.
-/

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

end NumStability
