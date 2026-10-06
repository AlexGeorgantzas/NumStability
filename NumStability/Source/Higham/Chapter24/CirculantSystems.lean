/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter24.Radix2FFT
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.Tactic.NoncommRing

namespace NumStability

open scoped Matrix.Norms.L2Operator
open Filter Topology Asymptotics

/-! # Higham Chapter 24: circulant systems

This module connects section 24.2 to Mathlib's exact circulant matrices and
proves the noncommutative matrix rearrangement in equation (24.8).  The
floating-point norm estimates and the final first-order `O(u^2)` statement are
kept distinct from this exact algebra.
-/

/-- The circulant `C(c)` used in section 24.2. -/
def higham24Circulant {n : ℕ} (c : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.circulant c

/-- The generator is the first column of its circulant matrix. -/
theorem higham24_circulant_first_column {n : ℕ}
    (c : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    higham24Circulant c i 0 = c i := by
  change Matrix.circulant c i 0 = c i
  exact Matrix.circulant_col_zero_eq c i

/-- A circulant is uniquely determined by its generator. -/
theorem higham24_circulant_injective {n : ℕ} :
    Function.Injective (higham24Circulant : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ) := by
  intro c d h
  exact Matrix.Fin.circulant_injective n (by simpa [higham24Circulant] using h)

/-- Structured perturbations remain circulant. -/
theorem higham24_circulant_add {n : ℕ} (c deltaC : Fin n → ℂ) :
    higham24Circulant (c + deltaC) =
      higham24Circulant c + higham24Circulant deltaC := by
  exact Matrix.circulant_add c deltaC

/-- Products of circulants remain circulant. -/
theorem higham24_circulant_mul {n : ℕ} (c d : Fin n → ℂ) :
    higham24Circulant c * higham24Circulant d =
      higham24Circulant ((higham24Circulant c).mulVec d) := by
  exact Matrix.Fin.circulant_mul c d

/-- Circulants commute, a structural property behind their simultaneous DFT
diagonalization. -/
theorem higham24_circulant_mul_comm {n : ℕ} (c d : Fin n → ℂ) :
    higham24Circulant c * higham24Circulant d =
      higham24Circulant d * higham24Circulant c := by
  exact Matrix.Fin.circulant_mul_comm c d

/-- A Chapter-24 DFT entry is a power of the primitive Fourier root. -/
theorem higham24_dft_entry_as_root {n : ℕ} (hn : 0 < n) (k j : Fin n) :
    higham24DFT n k j = higham24FourierRoot n ^ (k.val * j.val) := by
  unfold higham24DFT higham9_13_fourierVandermonde
  simp only [Matrix.of_apply]
  rw [higham24FourierRoot_pow n (k.val * j.val) hn]
  congr 2
  norm_num [Nat.cast_mul]
  ring

/-- Fourier characters turn cyclic addition into multiplication. -/
theorem higham24_dft_entry_add {n : ℕ} (hn : 0 < n) (k r j : Fin n) :
    higham24DFT n k (r + j) = higham24DFT n k r * higham24DFT n k j := by
  rw [higham24_dft_entry_as_root hn, higham24_dft_entry_as_root hn,
    higham24_dft_entry_as_root hn, ← pow_add]
  apply pow_eq_pow_of_modEq
  · simpa [Fin.val_add, Nat.mul_add] using
      (Nat.ModEq.mul_left k.val (Nat.mod_modEq (r.val + j.val) n))
  · exact higham24FourierRoot_pow_card n hn

/-- The intertwining identity behind the circulant diagonalization on printed
page 455: the DFT of a cyclic convolution is pointwise multiplication by
`F_n c`. -/
theorem higham24_dft_mul_circulant {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    higham24DFT n * higham24Circulant c =
      Matrix.diagonal (higham24DFTApply c) * higham24DFT n := by
  letI : NeZero n := ⟨hn.ne'⟩
  ext k j
  rw [Matrix.mul_apply, Matrix.diagonal_mul]
  unfold higham24DFTApply
  simp only [Matrix.mulVec, dotProduct, higham24Circulant, Matrix.circulant_apply]
  rw [Finset.sum_mul]
  apply (Fintype.sum_equiv (Equiv.addRight j)
    (fun r : Fin n => higham24DFT n k r * c r * higham24DFT n k j)
    (fun x : Fin n => higham24DFT n k x * c (x - j)) ?_).symm
  intro r
  change higham24DFT n k r * c r * higham24DFT n k j =
    higham24DFT n k (r + j) * c (r + j - j)
  rw [higham24_dft_entry_add hn]
  simp
  ring

/-- Section 24.2, printed page 455: `F_n C(c) F_n⁻¹` is diagonal and its
diagonal is exactly `F_n c`. -/
theorem higham24_circulant_diagonalization {n : ℕ} (hn : 0 < n)
    (c : Fin n → ℂ) :
    higham24DFT n * higham24Circulant c * higham24DFTInverse n =
      Matrix.diagonal (higham24DFTApply c) := by
  rw [higham24_dft_mul_circulant hn, Matrix.mul_assoc,
    higham24_dft_mul_dftInverse, mul_one]

/-- The eigenvalue vector `d = F_n c` used by the four-stage solver. -/
noncomputable abbrev higham24CirculantEigenvalues {n : ℕ}
    (c : Fin n → ℂ) : Fin n → ℂ :=
  higham24DFTApply c

/-- The exact four-stage circulant solver on printed page 455:
`d = F_n c`, `g = F_n b`, `h = D⁻¹g`, `x = F_n⁻¹h`. -/
noncomputable def higham24ExactCirculantSolve {n : ℕ}
    (c b : Fin n → ℂ) : Fin n → ℂ :=
  higham24DFTInverseApply
    (fun i => (higham24CirculantEigenvalues c i)⁻¹ * higham24DFTApply b i)

/-- End-to-end exact correctness of the four-stage circulant solver whenever
all Fourier eigenvalues are nonzero. -/
theorem higham24_exactCirculantSolve_correct {n : ℕ} (hn : 0 < n)
    (c b : Fin n → ℂ) (hdiag : ∀ i, higham24CirculantEigenvalues c i ≠ 0) :
    (higham24Circulant c).mulVec (higham24ExactCirculantSolve c b) = b := by
  apply_fun higham24DFTApply
  · unfold higham24DFTApply
    rw [Matrix.mulVec_mulVec, higham24_dft_mul_circulant hn,
      ← Matrix.mulVec_mulVec]
    funext i
    rw [Matrix.mulVec_diagonal]
    unfold higham24ExactCirculantSolve higham24DFTInverseApply
    rw [Matrix.mulVec_mulVec, higham24_dft_mul_dftInverse, Matrix.one_mulVec]
    unfold higham24CirculantEigenvalues
    have hd : higham24DFTApply c i ≠ 0 := hdiag i
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
    rfl
  · intro x y h
    unfold higham24DFTApply at h
    have h' := congrArg (higham24DFTInverse n).mulVec h
    simpa only [Matrix.mulVec_mulVec, higham24_dftInverse_mul_dft,
      Matrix.one_mulVec] using h'

/-- Equations (24.6)--(24.7), abstracted as an exact additive perturbation and
its norm budget.  The chosen matrix norm remains a parameter so the algebra is
not tied to a second, incompatible norm implementation. -/
structure Higham24FFTMatrixPerturbation {n : ℕ}
    (exact computed delta : Matrix (Fin n) (Fin n) ℂ)
    (matrixNorm : Matrix (Fin n) (Fin n) ℂ → ℝ) (bound : ℝ) where
  representation : computed = exact + delta
  norm_bound : matrixNorm delta ≤ bound

/-- A concrete nonvacuity witness for (24.6): exact execution is the zero
matrix perturbation whenever the advertised budget is nonnegative. -/
noncomputable def higham24_eq24_6_exact_witness {n : ℕ}
    (F : Matrix (Fin n) (Fin n) ℂ) (bound : ℝ) (hbound : 0 ≤ bound) :
    Higham24FFTMatrixPerturbation F F 0 norm bound where
  representation := by simp
  norm_bound := by simpa using hbound

/-- The two actual forward FFT stages in (24.7), on an explicit matrix
perturbation domain with the spectral norm used by the source. -/
structure Higham24Eq24_7Execution {n : ℕ}
    (F : Matrix (Fin n) (Fin n) ℂ) (c b : Fin n → ℂ) (bound : ℝ) where
  delta1 : Matrix (Fin n) (Fin n) ℂ
  delta2 : Matrix (Fin n) (Fin n) ℂ
  dHat : Fin n → ℂ
  gHat : Fin n → ℂ
  d_stage : dHat = (F + delta1).mulVec c
  g_stage : gHat = (F + delta2).mulVec b
  delta1_bound : ‖delta1‖ ≤ bound
  delta2_bound : ‖delta2‖ ≤ bound

/-- The explicit (24.7) execution domain is nonempty; zero perturbations give
the exact two FFT stages. -/
noncomputable def higham24Eq24_7ExactExecution {n : ℕ}
    (F : Matrix (Fin n) (Fin n) ℂ) (c b : Fin n → ℂ)
    (bound : ℝ) (hbound : 0 ≤ bound) :
    Higham24Eq24_7Execution F c b bound where
  delta1 := 0
  delta2 := 0
  dHat := F.mulVec c
  gHat := F.mulVec b
  d_stage := by simp
  g_stage := by simp
  delta1_bound := by simpa using hbound
  delta2_bound := by simpa using hbound

/-- Equation (24.7) at its honest explicit domain, exposing both computed
vectors, both perturbation matrices, and their (24.6) budgets. -/
theorem higham24_eq24_7_explicitDomain {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℂ} {c b : Fin n → ℂ} {bound : ℝ}
    (execution : Higham24Eq24_7Execution F c b bound) :
    execution.dHat = (F + execution.delta1).mulVec c ∧
      execution.gHat = (F + execution.delta2).mulVec b ∧
      ‖execution.delta1‖ ≤ bound ∧ ‖execution.delta2‖ ≤ bound :=
  ⟨execution.d_stage, execution.g_stage,
    execution.delta1_bound, execution.delta2_bound⟩

/-- The remaining rounded stages of the four-stage circulant solver.  Each
field is a local executable stage equation or a local perturbation budget;
the composed (24.7)--(24.8) formula is derived below. -/
structure Higham24RoundedCirculantSolveExecution {n : ℕ}
    (F FInv DInv : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ)
    (fftBound scalingBound : ℝ) where
  delta2 : Matrix (Fin n) (Fin n) ℂ
  delta3 : Matrix (Fin n) (Fin n) ℂ
  E : Matrix (Fin n) (Fin n) ℂ
  gHat : Fin n → ℂ
  hHat : Fin n → ℂ
  xHat : Fin n → ℂ
  forward_stage : gHat = (F + delta2).mulVec b
  scaling_stage : hHat = ((1 + E) * DInv).mulVec gHat
  inverse_stage : xHat = (FInv + delta3).mulVec hHat
  delta2_bound : ‖delta2‖ ≤ fftBound
  delta3_bound : ‖delta3‖ ≤ fftBound
  scaling_bound : ‖E‖ ≤ scalingBound

/-- The rounded solver contract composes to the exact matrix expression used
as the `xHat` premise in (24.8). -/
theorem higham24_roundedCirculantSolve_composed {n : ℕ}
    {F FInv DInv : Matrix (Fin n) (Fin n) ℂ} {b : Fin n → ℂ}
    {fftBound scalingBound : ℝ}
    (execution : Higham24RoundedCirculantSolveExecution
      F FInv DInv b fftBound scalingBound) :
    execution.xHat =
      ((FInv + execution.delta3) * (1 + execution.E) * DInv *
        (F + execution.delta2)).mulVec b := by
  rw [execution.inverse_stage, execution.scaling_stage,
    execution.forward_stage]
  simp only [Matrix.mulVec_mulVec]
  congr 1
  noncomm_ring

/-- Concrete nonvacuity of the rounded four-stage domain: the exact solver is
obtained by setting every local perturbation to zero. -/
noncomputable def higham24ExactCirculantSolveExecution {n : ℕ}
    (F FInv DInv : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ)
    (fftBound scalingBound : ℝ) (hfft : 0 ≤ fftBound)
    (hscale : 0 ≤ scalingBound) :
    Higham24RoundedCirculantSolveExecution
      F FInv DInv b fftBound scalingBound where
  delta2 := 0
  delta3 := 0
  E := 0
  gHat := F.mulVec b
  hHat := DInv.mulVec (F.mulVec b)
  xHat := FInv.mulVec (DInv.mulVec (F.mulVec b))
  forward_stage := by simp
  scaling_stage := by simp
  inverse_stage := by simp
  delta2_bound := by simpa using hfft
  delta3_bound := by simpa using hfft
  scaling_bound := by simpa using hscale

/-- Local scalar components of the mixed-stability analysis in Theorem 24.3.
The decomposition separates FFT accumulation, the six first-order scalar
roundings, and the genuinely quadratic remainder. -/
structure Higham24MixedStabilityExecutionFamily
    (t : ℕ) (eta : ℝ → ℝ) where
  generatorError : ℝ → ℝ
  rhsError : ℝ → ℝ
  fftContribution : ℝ → ℝ
  scalarContribution : ℝ → ℝ
  remainder : ℝ → ℝ
  radius : ℝ
  radius_pos : 0 < radius
  generator_split : ∀ u, 0 < u → u < radius →
    generatorError u ≤ fftContribution u + scalarContribution u + remainder u
  rhs_split : ∀ u, 0 < u → u < radius →
    rhsError u ≤ fftContribution u + scalarContribution u + remainder u
  fft_bound : ∀ u, 0 < u → u < radius →
    fftContribution u ≤ eta u * t
  scalar_bound : ∀ u, 0 < u → u < radius →
    scalarContribution u ≤ 6 * u
  remainder_bigO : remainder =O[nhdsWithin 0 (Set.Ioi 0)] (fun u : ℝ => u ^ 2)

/-- Theorem 24.3's printed `eta log₂(n) + 6u + O(u²)` conclusion, derived
from the preceding local execution-family decomposition (`t = log₂ n`). -/
theorem higham24_theorem24_3_explicitDomain
    {t : ℕ} {eta : ℝ → ℝ}
    (execution : Higham24MixedStabilityExecutionFamily t eta) :
    execution.remainder =O[nhdsWithin 0 (Set.Ioi 0)] (fun u : ℝ => u ^ 2) ∧
      ∀ u, 0 < u → u < execution.radius →
        execution.generatorError u ≤ eta u * t + 6 * u + execution.remainder u ∧
        execution.rhsError u ≤ eta u * t + 6 * u + execution.remainder u := by
  refine ⟨execution.remainder_bigO, ?_⟩
  intro u hu hur
  have hg := execution.generator_split u hu hur
  have hb := execution.rhs_split u hu hur
  have hf := execution.fft_bound u hu hur
  have hs := execution.scalar_bound u hu hur
  constructor <;> linarith

/-- Nonvacuity witness for the asymptotic contract: the exact family has zero
mixed perturbations and zero quadratic remainder. -/
def higham24ExactMixedStabilityExecutionFamily (t : ℕ) :
    Higham24MixedStabilityExecutionFamily t (fun _ => 0) where
  generatorError := fun _ => 0
  rhsError := fun _ => 0
  fftContribution := fun _ => 0
  scalarContribution := fun _ => 0
  remainder := fun _ => 0
  radius := 1
  radius_pos := by norm_num
  generator_split := by intros; norm_num
  rhs_split := by intros; norm_num
  fft_bound := by intros; norm_num
  scalar_bound := by intro u hu hur; linarith
  remainder_bigO := Asymptotics.isBigO_zero
    (fun u : ℝ => u ^ 2) (nhdsWithin 0 (Set.Ioi 0))

section Equation24_8

variable {n : ℕ}

/-- Exact noncommutative matrix identity underlying equation (24.8).

`FInv` is the inverse DFT, `DInv` the computed inverse diagonal, `EInv` the
inverse diagonal-scaling perturbation, and `QInv` the inverse of
`I + Delta3 F`.  The hypotheses state exactly the inverse identities used in
the printed rearrangement. -/
theorem higham24_eq24_8_matrix_identity
    (F FInv D DInv E EInv Delta2 Delta3 QInv : Matrix (Fin n) (Fin n) ℂ)
    (hFFInv : F * FInv = 1) (hFInvF : FInv * F = 1)
    (hDDInv : D * DInv = 1)
    (hEInvE : EInv * (1 + E) = 1)
    (hQInvQ : QInv * (1 + Delta3 * F) = 1) :
    (FInv * D * EInv * F * QInv) *
        ((FInv + Delta3) * (1 + E) * DInv * (F + Delta2)) =
      1 + FInv * Delta2 := by
  have hleft : FInv + Delta3 = (1 + Delta3 * F) * FInv := by
    calc
      FInv + Delta3 = FInv + Delta3 * (F * FInv) := by rw [hFFInv, mul_one]
      _ = (1 + Delta3 * F) * FInv := by noncomm_ring
  have hright : F + Delta2 = F * (1 + FInv * Delta2) := by
    calc
      F + Delta2 = F + (F * FInv) * Delta2 := by rw [hFFInv, one_mul]
      _ = F * (1 + FInv * Delta2) := by noncomm_ring
  rw [hleft, hright]
  calc
    (FInv * D * EInv * F * QInv) *
          ((1 + Delta3 * F) * FInv * (1 + E) * DInv *
            (F * (1 + FInv * Delta2))) =
        FInv * D * EInv * F * (QInv * (1 + Delta3 * F)) *
          FInv * (1 + E) * DInv * F * (1 + FInv * Delta2) := by
            noncomm_ring
    _ = FInv * D * EInv * F * FInv * (1 + E) * DInv * F *
          (1 + FInv * Delta2) := by rw [hQInvQ]; simp
    _ = FInv * D * EInv * (F * FInv) * (1 + E) * DInv * F *
          (1 + FInv * Delta2) := by noncomm_ring
    _ = FInv * D * EInv * (1 + E) * DInv * F *
          (1 + FInv * Delta2) := by rw [hFFInv]; simp
    _ = FInv * D * (EInv * (1 + E)) * DInv * F *
          (1 + FInv * Delta2) := by noncomm_ring
    _ = FInv * D * DInv * F * (1 + FInv * Delta2) := by
          rw [hEInvE]
          simp
    _ = FInv * (D * DInv) * F * (1 + FInv * Delta2) := by noncomm_ring
    _ = FInv * F * (1 + FInv * Delta2) := by rw [hDDInv]; simp
    _ = 1 + FInv * Delta2 := by rw [hFInvF]; simp

/-- Vector-applied form of equation (24.8). -/
theorem higham24_eq24_8
    (F FInv D DInv E EInv Delta2 Delta3 QInv : Matrix (Fin n) (Fin n) ℂ)
    (b xHat : Fin n → ℂ)
    (hFFInv : F * FInv = 1) (hFInvF : FInv * F = 1)
    (hDDInv : D * DInv = 1)
    (hEInvE : EInv * (1 + E) = 1)
    (hQInvQ : QInv * (1 + Delta3 * F) = 1)
    (hxHat : xHat =
      ((FInv + Delta3) * (1 + E) * DInv * (F + Delta2)).mulVec b) :
    (FInv * D * EInv * F * QInv).mulVec xHat =
      (1 + FInv * Delta2).mulVec b := by
  rw [hxHat, Matrix.mulVec_mulVec,
    higham24_eq24_8_matrix_identity F FInv D DInv E EInv Delta2 Delta3 QInv
      hFFInv hFInvF hDDInv hEInvE hQInvQ]

end Equation24_8

end NumStability
