/-
  Algorithms/LU/BlockLUSPDFamilies.lean

  Uniform source composition for Higham equation (13.25).

  The source explicitly uses the reasonable first-order comparison between
  exact and computed factor products.  This module records that comparison as
  a uniform `O(u)` family contract; multiplication by the outer roundoff then
  gives the required `O(u^2)` remainder.
-/

import NumStability.Algorithms.LU.BlockLUSPDSourceClosure
import NumStability.Algorithms.LU.BlockLUFirstOrderFamilies

namespace NumStability

open Filter Asymptotics
open scoped Topology

/-- Scalar family composition behind equation (13.25).

`hProductTransfer` is the source's explicit first-order comparison between
the computed factor product and the equation-(13.24) upper bound. -/
theorem higham13_eq13_25_family_from_eq13_24_product_transfer
    {ι : Type*} {l : Filter ι} (U : RoundoffFamily ι l)
    (m : ℕ) (hm : 0 < m)
    (c_n normA kappa : ℝ)
    (computedProduct err : ι → ℝ)
    (hc : 0 ≤ c_n) (hA : 0 ≤ normA)
    (hErr : FamilyFirstOrderLe l U.unit
      (fun t => c_n * U.unit t * (normA + computedProduct t)) err)
    (hProductTransfer : FamilyLinearRemainderLe l U.unit
      (fun _ => Real.sqrt (m : ℝ) *
        (1 + (m : ℝ) * Real.sqrt kappa) * normA)
      computedProduct) :
    FamilyFirstOrderLe l U.unit
      (fun t => c_n * Real.sqrt (m : ℝ) * U.unit t * normA *
        (2 + (m : ℝ) * Real.sqrt kappa)) err := by
  have hIntermediate :=
    FamilyFirstOrderLe.coefficient_of_linear_transfer_to
      hc U.unit_nonneg hErr hProductTransfer
  apply hIntermediate.mono_leading
  intro t
  have hmone : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsqrt : 1 ≤ Real.sqrt (m : ℝ) := by
    nlinarith [Real.sqrt_nonneg (m : ℝ),
      Real.sq_sqrt (Nat.cast_nonneg m)]
  have hfactor :
      1 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa) ≤
        Real.sqrt (m : ℝ) * (2 + (m : ℝ) * Real.sqrt kappa) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg m) (Real.sqrt_nonneg kappa)]
  have hscale : 0 ≤ c_n * U.unit t * normA :=
    mul_nonneg (mul_nonneg hc (U.unit_nonneg t)) hA
  calc
    c_n * U.unit t *
          (normA +
            Real.sqrt (m : ℝ) *
              (1 + (m : ℝ) * Real.sqrt kappa) * normA)
        = (c_n * U.unit t * normA) *
            (1 + Real.sqrt (m : ℝ) *
              (1 + (m : ℝ) * Real.sqrt kappa)) := by ring
    _ ≤ (c_n * U.unit t * normA) *
          (Real.sqrt (m : ℝ) *
            (2 + (m : ℝ) * Real.sqrt kappa)) :=
      mul_le_mul_of_nonneg_left hfactor hscale
    _ = c_n * Real.sqrt (m : ℝ) * U.unit t * normA *
          (2 + (m : ℝ) * Real.sqrt kappa) := by ring

/-- Equation (13.25) for the concrete exact Algorithm 13.3 SPD factors.

Equation (13.24) constructs and bounds the exact factors.  The two remaining
premises of the implication are precisely (i) the source's first-order
exact/computed factor-product comparison and (ii) the family-level Theorem
13.6 backward-error conclusion for the computed factors.  Thus SPD alone is
not misrepresented as proving a floating-point error bound. -/
theorem higham13_eq13_25_algorithm13_3_spd_family_from_theorem13_6_and_product_transfer
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hSPD : IsSymPosDef (m * r) (blockMatrixFlatFin A))
    (computedProduct err : ι → ℝ) (c_n : ℝ) (hc : 0 ≤ c_n) :
    ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
      (∀ k : ℕ, ∀ hk : k < m,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k)) ∧
      BlockLUFactSpec m r A
        (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ∧
      (FamilyLinearRemainderLe l Uround.unit
          (fun _ =>
            opNorm2
                (blockMatrixFlatFin
                  (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)) *
              opNorm2
                (blockMatrixFlatFin
                  (higham13_algorithm13_3_upperFromMatrixStages A pivotInv)))
          computedProduct →
        FamilyFirstOrderLe l Uround.unit
          (fun t => c_n * Uround.unit t *
            (opNorm2 (blockMatrixFlatFin A) + computedProduct t)) err →
        FamilyFirstOrderLe l Uround.unit
          (fun t => c_n * Real.sqrt (m : ℝ) * Uround.unit t *
            opNorm2 (blockMatrixFlatFin A) *
            (2 + (m : ℝ) *
              Real.sqrt
                (kappa2 (blockMatrixFlatFin A)
                  (nonsingInv (m * r) (blockMatrixFlatFin A))))) err) := by
  rcases higham13_eq13_24_algorithm13_3_spd hr A hSPD with
    ⟨pivotInv, hPivot, hFact, _hL, _hU, hProduct⟩
  refine ⟨pivotInv, hPivot, hFact, ?_⟩
  intro hTransfer hErr
  have hTransferBound : FamilyLinearRemainderLe l Uround.unit
      (fun _ => Real.sqrt (m : ℝ) *
        (1 + (m : ℝ) *
          Real.sqrt
            (kappa2 (blockMatrixFlatFin A)
              (nonsingInv (m * r) (blockMatrixFlatFin A)))) *
        opNorm2 (blockMatrixFlatFin A))
      computedProduct := by
    apply hTransfer.mono_base
    intro t
    exact hProduct
  apply higham13_eq13_25_family_from_eq13_24_product_transfer
    Uround m hm c_n (opNorm2 (blockMatrixFlatFin A))
      (kappa2 (blockMatrixFlatFin A)
        (nonsingInv (m * r) (blockMatrixFlatFin A)))
      computedProduct err hc (opNorm2_nonneg _)
  · exact hErr
  · exact hTransferBound

/-- Equation (13.25) with the computed product and backward error tied to the
actual computed factor and perturbation matrices.

The only numerical premises are the two statements made explicitly in the
source at this point: the Theorem 13.6 family bound for those computed
matrices, and the first-order comparison of their product with the exact SPD
Algorithm 13.3 factor product. -/
theorem higham13_eq13_25_algorithm13_3_spd_family_actual_matrices
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hSPD : IsSymPosDef (m * r) (blockMatrixFlatFin A))
    (Lhat Uhat Delta : ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
    (c_n : ℝ) (hc : 0 ≤ c_n)
    (hProductTransfer : FamilyLinearRemainderLe l Uround.unit
      (fun _ =>
        opNorm2
            (blockMatrixFlatFin
              (higham13_algorithm13_3_lowerFromMatrixStages A
                (Classical.choose
                  (higham13_eq13_24_algorithm13_3_spd hr A hSPD)))) *
          opNorm2
            (blockMatrixFlatFin
              (higham13_algorithm13_3_upperFromMatrixStages A
                (Classical.choose
                  (higham13_eq13_24_algorithm13_3_spd hr A hSPD)))))
      (fun t => opNorm2 (Lhat t) * opNorm2 (Uhat t)))
    (hTheorem13_6 : FamilyFirstOrderLe l Uround.unit
      (fun t => c_n * Uround.unit t *
        (opNorm2 (blockMatrixFlatFin A) +
          opNorm2 (Lhat t) * opNorm2 (Uhat t)))
      (fun t => opNorm2 (Delta t))) :
    FamilyFirstOrderLe l Uround.unit
      (fun t => c_n * Real.sqrt (m : ℝ) * Uround.unit t *
        opNorm2 (blockMatrixFlatFin A) *
        (2 + (m : ℝ) *
          Real.sqrt
            (kappa2 (blockMatrixFlatFin A)
              (nonsingInv (m * r) (blockMatrixFlatFin A)))))
      (fun t => opNorm2 (Delta t)) := by
  let pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ :=
    Classical.choose (higham13_eq13_24_algorithm13_3_spd hr A hSPD)
  have hExactProduct :=
    (Classical.choose_spec
      (higham13_eq13_24_algorithm13_3_spd hr A hSPD)).2.2.2.2
  have hTransferBound : FamilyLinearRemainderLe l Uround.unit
      (fun _ => Real.sqrt (m : ℝ) *
        (1 + (m : ℝ) *
          Real.sqrt
            (kappa2 (blockMatrixFlatFin A)
              (nonsingInv (m * r) (blockMatrixFlatFin A)))) *
        opNorm2 (blockMatrixFlatFin A))
      (fun t => opNorm2 (Lhat t) * opNorm2 (Uhat t)) := by
    apply hProductTransfer.mono_base
    intro t
    simpa [pivotInv] using hExactProduct
  exact higham13_eq13_25_family_from_eq13_24_product_transfer
    Uround m hm c_n (opNorm2 (blockMatrixFlatFin A))
      (kappa2 (blockMatrixFlatFin A)
        (nonsingInv (m * r) (blockMatrixFlatFin A)))
      (fun t => opNorm2 (Lhat t) * opNorm2 (Uhat t))
      (fun t => opNorm2 (Delta t)) hc (opNorm2_nonneg _)
      hTheorem13_6 hTransferBound

/-- Full `i = 1 : 2` form of equation (13.25) for the actual factorization and
solve perturbation matrix families. -/
theorem higham13_eq13_25_algorithm13_3_spd_family_actual_factor_and_solve
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    {m r p : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hSPD : IsSymPosDef (m * r) (blockMatrixFlatFin A))
    (Lhat Uhat DeltaFact DeltaSolve :
      ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
    (xhat b : ι → Matrix (Fin (m * r)) (Fin p) ℝ)
    (c_n : ℝ) (hc : 0 ≤ c_n)
    (hFactEquation : ∀ t,
      Lhat t * Uhat t = blockMatrixFlatFin A + DeltaFact t)
    (hSolveEquation : ∀ t,
      (blockMatrixFlatFin A + DeltaSolve t) * xhat t = b t)
    (hProductTransfer : FamilyLinearRemainderLe l Uround.unit
      (fun _ =>
        opNorm2
            (blockMatrixFlatFin
              (higham13_algorithm13_3_lowerFromMatrixStages A
                (Classical.choose
                  (higham13_eq13_24_algorithm13_3_spd hr A hSPD)))) *
          opNorm2
            (blockMatrixFlatFin
              (higham13_algorithm13_3_upperFromMatrixStages A
                (Classical.choose
                  (higham13_eq13_24_algorithm13_3_spd hr A hSPD)))))
      (fun t => opNorm2 (Lhat t) * opNorm2 (Uhat t)))
    (hFactBound : FamilyFirstOrderLe l Uround.unit
      (fun t => c_n * Uround.unit t *
        (opNorm2 (blockMatrixFlatFin A) +
          opNorm2 (Lhat t) * opNorm2 (Uhat t)))
      (fun t => opNorm2 (DeltaFact t)))
    (hSolveBound : FamilyFirstOrderLe l Uround.unit
      (fun t => c_n * Uround.unit t *
        (opNorm2 (blockMatrixFlatFin A) +
          opNorm2 (Lhat t) * opNorm2 (Uhat t)))
      (fun t => opNorm2 (DeltaSolve t))) :
    (∀ t, Lhat t * Uhat t = blockMatrixFlatFin A + DeltaFact t) ∧
      (∀ t, (blockMatrixFlatFin A + DeltaSolve t) * xhat t = b t) ∧
      FamilyFirstOrderLe l Uround.unit
          (fun t => c_n * Real.sqrt (m : ℝ) * Uround.unit t *
            opNorm2 (blockMatrixFlatFin A) *
            (2 + (m : ℝ) *
              Real.sqrt
                (kappa2 (blockMatrixFlatFin A)
                  (nonsingInv (m * r) (blockMatrixFlatFin A)))))
          (fun t => opNorm2 (DeltaFact t)) ∧
      FamilyFirstOrderLe l Uround.unit
          (fun t => c_n * Real.sqrt (m : ℝ) * Uround.unit t *
            opNorm2 (blockMatrixFlatFin A) *
            (2 + (m : ℝ) *
              Real.sqrt
                (kappa2 (blockMatrixFlatFin A)
                  (nonsingInv (m * r) (blockMatrixFlatFin A)))))
          (fun t => opNorm2 (DeltaSolve t)) ∧
      FamilyFirstOrderLe l Uround.unit
          (fun t => c_n * Real.sqrt (m : ℝ) * Uround.unit t *
            opNorm2 (blockMatrixFlatFin A) *
            (2 + (m : ℝ) *
              Real.sqrt
                (kappa2 (blockMatrixFlatFin A)
                  (nonsingInv (m * r) (blockMatrixFlatFin A)))))
          (fun t => max (opNorm2 (DeltaFact t))
            (opNorm2 (DeltaSolve t))) := by
  have hFact := higham13_eq13_25_algorithm13_3_spd_family_actual_matrices
    Uround hm hr A hSPD Lhat Uhat DeltaFact c_n hc
      hProductTransfer hFactBound
  have hSolve := higham13_eq13_25_algorithm13_3_spd_family_actual_matrices
    Uround hm hr A hSPD Lhat Uhat DeltaSolve c_n hc
      hProductTransfer hSolveBound
  have hBoth := FamilyFirstOrderLe.combineMax hFact hSolve
  refine ⟨hFactEquation, hSolveEquation, hFact, hSolve, ?_⟩
  exact hBoth.mono_leading (fun _ => (max_self _).le)

end NumStability
