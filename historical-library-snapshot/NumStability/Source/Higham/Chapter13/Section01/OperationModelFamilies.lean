import NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderFamilies

/-!
# Higham equations (13.4)--(13.6), family forms

Source locators exposing the reusable family operation models as the three
numbered equation conclusions.
-/

namespace NumStability

open Filter Asymptotics
open scoped Topology

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
