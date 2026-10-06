import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Normed

namespace HighamBench

open scoped BigOperators

noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p03MatVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n, A i j * x j

noncomputable def p03VecAbs {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => |x i|

noncomputable def p03MatAbs {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => |A i j|

noncomputable def p03VecInfNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ‖x‖

noncomputable def p03MatInfNorm {n : ℕ}
    (A : Fin n → Fin n → ℝ) : ℝ :=
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  ‖(Matrix.of A : Matrix (Fin n) (Fin n) ℝ)‖

noncomputable def p03AugmentedRowNnz {n : ℕ}
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j : Fin n => A i j ≠ 0).card +
    if b i ≠ 0 then 1 else 0

noncomputable def p03MaxAugmentedRowNnz {n : ℕ}
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : ℕ :=
  Finset.univ.sup (p03AugmentedRowNnz A b)

structure P03NormwiseIRRun (n : ℕ) where
  dimension_pos : 0 < n
  A : Fin n → Fin n → ℝ
  Ainv : Fin n → Fin n → ℝ
  b : Fin n → ℝ
  x : ℕ → Fin n → ℝ
  rHat : ℕ → Fin n → ℝ
  dHat : ℕ → Fin n → ℝ
  deltaR : ℕ → Fin n → ℝ
  deltaX : ℕ → Fin n → ℝ
  uR : ℝ
  u : ℝ
  uS : ℝ
  uF : ℝ
  c1 : ℕ → ℝ
  c2 : ℕ → ℝ
  uR_nonneg : 0 ≤ uR
  uR_le_u : uR ≤ u
  u_le_uS : u ≤ uS
  uS_le_uF : uS ≤ uF
  gamma_valid : GammaValid uR (p03MaxAugmentedRowNnz A b)
  c1_nonneg : ∀ i, 0 ≤ c1 i
  c2_nonneg : ∀ i, 0 ≤ c2 i
  inverse_action : ∀ (z : Fin n → ℝ) (j : Fin n),
    p03MatVec Ainv (p03MatVec A z) j = z j
  residual_equation : ∀ (i : ℕ) (j : Fin n),
    rHat i j = b j - p03MatVec A (x i) j + deltaR i j
  residual_error_bound : ∀ (i : ℕ) (j : Fin n),
    |deltaR i j| ≤
      uS * |b j - p03MatVec A (x i) j| +
        (1 + uS) * gamma uR (p03MaxAugmentedRowNnz A b) *
          (|b j| + p03MatVec (p03MatAbs A) (p03VecAbs (x i)) j)
  correction_solver_bound : ∀ i : ℕ,
    p03VecInfNorm (fun j => rHat i j - p03MatVec A (dHat i) j) ≤
      uS *
        (c1 i * p03MatInfNorm A * p03VecInfNorm (dHat i) +
          c2 i * p03VecInfNorm (rHat i))
  update_equation : ∀ (i : ℕ) (j : Fin n),
    x (i + 1) j = x i j + dHat i j + deltaX i j
  update_error_bound : ∀ (i : ℕ) (j : Fin n),
    |deltaX i j| ≤ u * |x (i + 1) j|
  denominator_condition : ∀ i : ℕ,
    c1 i * (p03MatInfNorm Ainv * p03MatInfNorm A) * uS < 1

noncomputable def p03ExactResidual {n : ℕ}
    (run : P03NormwiseIRRun n) (i : ℕ) : Fin n → ℝ :=
  fun j => run.b j - p03MatVec run.A (run.x i) j

noncomputable def p03KappaInf {n : ℕ} (run : P03NormwiseIRRun n) : ℝ :=
  p03MatInfNorm run.Ainv * p03MatInfNorm run.A

noncomputable def p03CorrectionRatio {n : ℕ}
    (run : P03NormwiseIRRun n) (i : ℕ) : ℝ :=
  (run.c1 i * p03KappaInf run + run.c2 i) /
    (1 - run.c1 i * p03KappaInf run * run.uS)

noncomputable def p03Alpha {n : ℕ}
    (run : P03NormwiseIRRun n) (i : ℕ) : ℝ :=
  run.uS * (1 + (1 + run.uS) * p03CorrectionRatio run i)

noncomputable def p03Beta {n : ℕ}
    (run : P03NormwiseIRRun n) (i : ℕ) : ℝ :=
  (1 + run.uS * p03CorrectionRatio run i) * (1 + run.uS) *
      gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
        (p03VecInfNorm run.b +
          p03MatInfNorm run.A * p03VecInfNorm (run.x i)) +
    run.u * p03MatInfNorm run.A * p03VecInfNorm (run.x (i + 1))

end HighamBench
