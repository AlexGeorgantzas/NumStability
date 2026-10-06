import NumStability.Source.Higham.Chapter13.Section03.SPDFactorBounds
import NumStability.Source.Higham.Chapter13.Table01

/-!
# Higham equation (13.25), concrete SPD factorization

The exact first-order equation (13.25) consequence for the concrete Algorithm
13.3 factors supplied by the SPD equation (13.24) theorem.
-/

namespace NumStability

/-- Higham, Chapter 13, equation (13.25), as the exact first-order
    composition of Theorem 13.6 with equation (13.24). -/
theorem higham13_eq13_25_spd_firstOrder_from_eq13_24
    (err u c_n normA normLU kappa : ℝ) (m : ℕ)
    (hm : 0 < m) (hu : 0 ≤ u) (hc : 0 ≤ c_n) (hA : 0 ≤ normA)
    (hErr : FirstOrderLe u (c_n * u * (normA + normLU)) err)
    (hLU : normLU ≤
      Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa) * normA) :
    FirstOrderLe u
      (c_n * Real.sqrt (m : ℝ) * u * normA *
        (2 + (m : ℝ) * Real.sqrt kappa)) err := by
  have hIntermediate := higham13_table13_1_backward_error_from_product_bound
    err u c_n normA normLU
      (Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa))
      hu hc hErr hLU
  apply hIntermediate.mono_leading
  have hmone : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsqrt : 1 ≤ Real.sqrt (m : ℝ) := by
    nlinarith [Real.sqrt_nonneg (m : ℝ),
      Real.sq_sqrt (Nat.cast_nonneg m)]
  have hfactor :
      1 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa) ≤
        Real.sqrt (m : ℝ) * (2 + (m : ℝ) * Real.sqrt kappa) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg m) (Real.sqrt_nonneg kappa)]
  have hscale : 0 ≤ c_n * u * normA := by positivity
  calc
    c_n * u *
          ((1 + Real.sqrt (m : ℝ) *
            (1 + (m : ℝ) * Real.sqrt kappa)) * normA)
        = (c_n * u * normA) *
            (1 + Real.sqrt (m : ℝ) *
              (1 + (m : ℝ) * Real.sqrt kappa)) := by ring
    _ ≤ (c_n * u * normA) *
          (Real.sqrt (m : ℝ) *
            (2 + (m : ℝ) * Real.sqrt kappa)) :=
      mul_le_mul_of_nonneg_left hfactor hscale
    _ = c_n * Real.sqrt (m : ℝ) * u * normA *
          (2 + (m : ℝ) * Real.sqrt kappa) := by ring

/-- Higham, Chapter 13, equation (13.25), packaged with the concrete
    Algorithm 13.3 factors supplied by the SPD equation (13.24) theorem.

    The implication's premise is exactly the Theorem 13.6/Table 13.1
    first-order perturbation bound for those factors.  Its conclusion is the
    printed SPD coefficient, with no factor-norm certificate left for the
    caller to provide. -/
theorem higham13_eq13_25_algorithm13_3_spd
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hSPD : IsSymPosDef (m * r) (blockMatrixFlatFin A))
    (err u c_n : ℝ) (hu : 0 ≤ u) (hc : 0 ≤ c_n) :
    ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
      (∀ k : ℕ, ∀ hk : k < m,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k)) ∧
      BlockLUFactSpec m r A
        (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ∧
      (FirstOrderLe u
          (c_n * u *
            (opNorm2 (blockMatrixFlatFin A) +
              opNorm2
                  (blockMatrixFlatFin
                    (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)) *
                opNorm2
                  (blockMatrixFlatFin
                    (higham13_algorithm13_3_upperFromMatrixStages A pivotInv))))
          err →
        FirstOrderLe u
          (c_n * Real.sqrt (m : ℝ) * u * opNorm2 (blockMatrixFlatFin A) *
            (2 + (m : ℝ) *
              Real.sqrt
                (kappa2 (blockMatrixFlatFin A)
                  (nonsingInv (m * r) (blockMatrixFlatFin A)))))
          err) := by
  rcases higham13_eq13_24_algorithm13_3_spd hr A hSPD with
    ⟨pivotInv, hPivot, hFact, _hL, _hU, hProduct⟩
  refine ⟨pivotInv, hPivot, hFact, ?_⟩
  intro hErr
  exact higham13_eq13_25_spd_firstOrder_from_eq13_24
    err u c_n (opNorm2 (blockMatrixFlatFin A))
      (opNorm2
          (blockMatrixFlatFin
            (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)) *
        opNorm2
          (blockMatrixFlatFin
            (higham13_algorithm13_3_upperFromMatrixStages A pivotInv)))
      (kappa2 (blockMatrixFlatFin A)
        (nonsingInv (m * r) (blockMatrixFlatFin A)))
      m hm hu hc (opNorm2_nonneg _) hErr hProduct

end NumStability
