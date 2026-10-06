import NumStability.Algorithms.LinearSystems.LeastSquares.AugmentedSystem
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.QR.HouseholderQR
import NumStability.Algorithms.LinearSystems.QR.QRSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Absorption
import NumStability.Analysis.Perturbation.LeastSquares.AugmentedSystem
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve

namespace NumStability

/-!
# Higham Chapter 20 — Theorem04

Canonical source correspondence module extracted without change from Higham20Theorem20_4Absorption.
-/

/-- Normalize a nonnegative square witness to Frobenius norm one.  The
one-hot branch makes the definition total when the supplied witness is zero. -/
noncomputable def higham20Theorem20_4NormalizedWitness {m : ℕ}
    (row0 col0 : Fin m) (W : Fin m → Fin m → ℝ) :
    Fin m → Fin m → ℝ :=
  if frobNorm W = 0 then
    lsTheorem20_4OneHotMajorant row0 col0
  else
    fun i j => W i j / frobNorm W
theorem higham20Theorem20_4NormalizedWitness_nonneg {m : ℕ}
    (row0 col0 : Fin m) (W : Fin m → Fin m → ℝ)
    (hW : ∀ i j, 0 ≤ W i j) :
    ∀ i j, 0 ≤ higham20Theorem20_4NormalizedWitness row0 col0 W i j := by
  classical
  intro i j
  by_cases hzero : frobNorm W = 0
  · simp [higham20Theorem20_4NormalizedWitness, hzero,
      lsTheorem20_4OneHotMajorant_nonneg row0 col0 i j]
  · simp only [higham20Theorem20_4NormalizedWitness, hzero, if_false]
    exact div_nonneg (hW i j) (frobNorm_nonneg W)
theorem higham20Theorem20_4NormalizedWitness_frobNorm {m : ℕ}
    (row0 col0 : Fin m) (W : Fin m → Fin m → ℝ) :
    frobNorm (higham20Theorem20_4NormalizedWitness row0 col0 W) = 1 := by
  classical
  by_cases hzero : frobNorm W = 0
  · simp [higham20Theorem20_4NormalizedWitness, hzero,
      lsTheorem20_4OneHotMajorant_frobNorm row0 col0]
  · have hpos : 0 < frobNorm W :=
      lt_of_le_of_ne (frobNorm_nonneg W) (Ne.symm hzero)
    simp only [higham20Theorem20_4NormalizedWitness, hzero, if_false]
    rw [← frobNormRect_eq_frobNormFn]
    have hfun : (fun i j => W i j / frobNorm W) =
        fun i j => (frobNorm W)⁻¹ * W i j := by
      funext i j
      simp [div_eq_mul_inv, mul_comm]
    rw [hfun, frobNormRect_smul, frobNormRect_eq_frobNormFn,
      abs_of_pos (inv_pos.mpr hpos)]
    exact inv_mul_cancel₀ hzero
/-- The unnormalized witness is exactly its Frobenius norm times the normalized
witness, including the zero-witness fallback branch. -/
theorem higham20Theorem20_4_witness_eq_frobNorm_mul_normalized {m : ℕ}
    (row0 col0 : Fin m) (W : Fin m → Fin m → ℝ) (i j : Fin m) :
    W i j = frobNorm W *
      higham20Theorem20_4NormalizedWitness row0 col0 W i j := by
  classical
  by_cases hzero : frobNorm W = 0
  · have hWij : W i j = 0 := (frobNorm_eq_zero_iff W).mp hzero i j
    simp [higham20Theorem20_4NormalizedWitness, hzero, hWij]
  · simp only [higham20Theorem20_4NormalizedWitness, hzero, if_false]
    field_simp
theorem higham20Theorem20_4_le_normalized_of_left_domination
    {m n : ℕ} (row0 col0 : Fin m)
    (A D : Fin m → Fin n → ℝ) (W : Fin m → Fin m → ℝ) (C : ℝ)
    (hW : ∀ i j, 0 ≤ W i j)
    (hWnorm : frobNorm W ≤ C)
    (hdom : ∀ i j,
      |D i j| ≤ matMulRect m m n W (fun r s => |A r s|) i j) :
    ∀ i j,
      |D i j| ≤ C * matMulRect m m n
        (higham20Theorem20_4NormalizedWitness row0 col0 W)
        (fun r s => |A r s|) i j := by
  intro i j
  let G := higham20Theorem20_4NormalizedWitness row0 col0 W
  have hprod_nonneg :
      0 ≤ matMulRect m m n G (fun r s => |A r s|) i j := by
    unfold matMulRect
    exact Finset.sum_nonneg (fun r _ =>
      mul_nonneg
        (higham20Theorem20_4NormalizedWitness_nonneg
          row0 col0 W hW i r)
        (abs_nonneg (A r j)))
  have hscale :
      matMulRect m m n W (fun r s => |A r s|) i j =
        frobNorm W * matMulRect m m n G (fun r s => |A r s|) i j := by
    unfold matMulRect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [higham20Theorem20_4_witness_eq_frobNorm_mul_normalized
      row0 col0 W i r]
    ring
  calc
    |D i j| ≤ matMulRect m m n W (fun r s => |A r s|) i j := hdom i j
    _ = frobNorm W * matMulRect m m n G (fun r s => |A r s|) i j := hscale
    _ ≤ C * matMulRect m m n G (fun r s => |A r s|) i j :=
      mul_le_mul_of_nonneg_right hWnorm hprod_nonneg
/-- Normalize any nonnegative square left witness that already dominates a
rectangular perturbation.  The conclusion has exactly the printed Theorem
20.4 shape: one nonnegative Frobenius-unit matrix multiplying `|A|`, with a
scalar coefficient that can be bounded using dimensions and gamma factors. -/
theorem higham20Theorem20_4_exists_unit_witness_of_left_domination
    {m n : ℕ} (row0 col0 : Fin m)
    (A D : Fin m → Fin n → ℝ) (W : Fin m → Fin m → ℝ) (C : ℝ)
    (hW : ∀ i j, 0 ≤ W i j)
    (hWnorm : frobNorm W ≤ C)
    (hdom : ∀ i j,
      |D i j| ≤ matMulRect m m n W (fun r s => |A r s|) i j) :
    ∃ G : Fin m → Fin m → ℝ,
      (∀ i j, 0 ≤ G i j) ∧
      frobNorm G = 1 ∧
      ∀ i j,
        |D i j| ≤ C * matMulRect m m n G (fun r s => |A r s|) i j := by
  let G := higham20Theorem20_4NormalizedWitness row0 col0 W
  refine ⟨G, higham20Theorem20_4NormalizedWitness_nonneg
    row0 col0 W hW, higham20Theorem20_4NormalizedWitness_frobNorm
    row0 col0 W, ?_⟩
  exact higham20Theorem20_4_le_normalized_of_left_domination
    row0 col0 A D W C hW hWnorm hdom
private theorem higham20Theorem20_4_matMulRect_mono_left {m n : ℕ}
    (L M : Fin m → Fin m → ℝ) (B : Fin m → Fin n → ℝ)
    (hLM : ∀ i j, L i j ≤ M i j) (hB : ∀ i j, 0 ≤ B i j)
    (i : Fin m) (j : Fin n) :
    matMulRect m m n L B i j ≤ matMulRect m m n M B i j := by
  unfold matMulRect
  apply Finset.sum_le_sum
  intro k _hk
  exact mul_le_mul_of_nonneg_right (hLM i k) (hB k j)
/-- Source-shaped augmented-system handoff that deliberately retains the two
exact QR identities needed to absorb the triangular-solve perturbations.  The
older public handoffs discarded these identities after constructing the exact
system, which was the final obstruction to the printed total-matrix bound. -/
theorem LSAsymmetricAugmentedSystem.exists_exact_qr_solution_with_source_bounds_and_qr_relation
    {n k : ℕ} (fp : FPModel)
    (Q : Fin (n + k) → Fin (n + k) → ℝ)
    (A Rhat : Fin (n + k) → Fin n → ℝ)
    (f c_hat : Fin (n + k) → ℝ) (g : Fin n → ℝ)
    (cA cComp cF cFsrc cG : ℝ)
    (H1 H2 H3 : Fin (n + k) → Fin (n + k) → ℝ)
    (hQR : StructuredHouseholderQRPanelHighamBackwardError (n + k) n
      A Q Rhat cA cComp)
    (hRhs : HouseholderQRRhsPanelExplicitBackwardError (n + k) n
      A f Q c_hat cF)
    (hcG : 0 ≤ cG)
    (hH1nonneg : ∀ i j, 0 ≤ H1 i j)
    (hH2nonneg : ∀ i j, 0 ≤ H2 i j)
    (hH3nonneg : ∀ i j, 0 ≤ H3 i j)
    (hH1norm : frobNorm H1 = 1)
    (hH2norm : frobNorm H2 = 1)
    (hH3norm : frobNorm H3 = 1)
    (hDeltafDom :
      let R : Fin n → Fin n → ℝ :=
        fun i j => Rhat (Fin.castAdd k i) j
      let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
      let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
      let rhat : Fin (n + k) → ℝ := matMulVec (n + k) Q (Fin.append h cBot)
      ∀ i : Fin (n + k),
        cF ≤ cFsrc * lsTheorem20_4DeltafMajorant H1 H2 f rhat i)
    (hdiag : ∀ i : Fin n, Rhat (Fin.castAdd k i) i ≠ 0)
    (hgamma : gammaValid fp n) :
    let R : Fin n → Fin n → ℝ :=
      fun i j => Rhat (Fin.castAdd k i) j
    let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
    let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
    let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
    let x : Fin n → ℝ := fl_backSub fp n R (fun i => cTop i - h i)
    let rhat : Fin (n + k) → ℝ := matMulVec (n + k) Q (Fin.append h cBot)
    ∃ DeltaA : Fin (n + k) → Fin n → ℝ,
    ∃ G : Fin (n + k) → Fin (n + k) → ℝ,
    ∃ Deltaf : Fin (n + k) → ℝ,
    ∃ Deltag : Fin n → ℝ,
    ∃ DeltaR1 DeltaR2 : Fin n → Fin n → ℝ,
      frobNorm DeltaA ≤ cA ∧
      (∀ i j, 0 ≤ G i j) ∧
      frobNorm G = 1 ∧
      (∀ i j, |DeltaA i j| ≤
        cComp * matMulRect (n + k) (n + k) n G
          (fun a b => |A a b|) i j) ∧
      (∀ i, |Deltaf i| ≤
        cFsrc * lsTheorem20_4DeltafMajorant H1 H2 f rhat i) ∧
      (∀ j, |Deltag j| ≤
        cG * lsTheorem20_4DeltagMajorant A H3 rhat j) ∧
      (∀ i j, |DeltaR1 i j| ≤ gamma fp n * |R i j|) ∧
      (∀ i j, |DeltaR2 i j| ≤ gamma fp n * |R i j|) ∧
      Rhat = matMulRectLeft (matTranspose Q)
        (fun i j => A i j + DeltaA i j) ∧
      Rhat = lsQRTallBlock (k := k) R ∧
      LSAsymmetricAugmentedSystem
        (fun i j => A i j + DeltaA i j +
          matMulRectLeft Q (lsQRTallBlock DeltaR1) i j)
        (fun i j => A i j + DeltaA i j +
          matMulRectLeft Q (lsQRTallBlock DeltaR2) i j)
        (fun i => f i + Deltaf i) (fun j => g j + Deltag j)
        rhat x := by
  let R : Fin n → Fin n → ℝ := fun i j => Rhat (Fin.castAdd k i) j
  let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
  let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
  let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
  let rhat : Fin (n + k) → ℝ := matMulVec (n + k) Q (Fin.append h cBot)
  obtain ⟨DeltaA, G, hRrep, hDeltaA, hGnonneg, hGnorm, hDeltaAcomp⟩ :=
    hQR.result
  obtain ⟨Deltaf, hfRep, hDeltaf⟩ := hRhs.result
  have hRhatBlock : Rhat = lsQRTallBlock (k := k) R := by
    simpa [R] using lsQRTallBlock_of_upper_trapezoidal
      (n := n) (k := k) Rhat hQR.upper
  have hupperR : ∀ i j : Fin n, j.val < i.val → R i j = 0 := by
    simpa [R] using lsQRTallBlock_top_upper_of_upper_trapezoidal
      (n := n) (k := k) Rhat hQR.upper
  have hdiagR : ∀ i : Fin n, R i i ≠ 0 := by
    intro i
    simpa [R] using hdiag i
  have hRmat : Rhat = matMulRectLeft (matTranspose Q)
      (fun r col => A r col + DeltaA r col) := by
    ext i j
    simpa [matMulRectLeft, matMulRect] using hRrep i j
  have hApert :
      (fun i j => A i j + DeltaA i j) =
        matMulRectLeft Q (lsQRTallBlock R) := by
    have hQRmat : matMulRectLeft Q Rhat =
        (fun i j => A i j + DeltaA i j) := by
      rw [hRmat, ← matMulRectLeft_assoc]
      have hQQT : matMul (n + k) Q (matTranspose Q) = idMatrix (n + k) := by
        ext i j
        exact hQR.orth.right_inv i j
      rw [hQQT, matMulRectLeft_id]
    rw [← hQRmat, hRhatBlock]
  have hd : matMulVec (n + k) (matTranspose Q)
      (fun i => f i + Deltaf i) = Fin.append cTop cBot := by
    ext row
    calc
      matMulVec (n + k) (matTranspose Q) (fun i => f i + Deltaf i) row =
          c_hat row := (hfRep row).symm
      _ = Fin.append cTop cBot row := by
        cases row using Fin.addCases with
        | left row => simp [cTop]
        | right row => simp [cBot]
  have hd0 : matMulVec (n + k) (matTranspose Q)
      (fun i => f i + Deltaf i) =
        Fin.append (fun i : Fin n => cTop i + (fun _ : Fin n => 0) i)
          cBot := by simpa using hd
  rcases LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub
      fp Q (fun i j => A i j + DeltaA i j) R
      (fun i => f i + Deltaf i) cTop (fun _ : Fin n => 0) cBot g
      hQR.orth hApert hd0 hdiagR hupperR hgamma with
    ⟨DeltaR1, DeltaR2, hDeltaR1, hDeltaR2, hsys⟩
  let Deltag : Fin n → ℝ := fun _ => 0
  have hDeltafSrc : ∀ i : Fin (n + k),
      |Deltaf i| ≤ cFsrc * lsTheorem20_4DeltafMajorant H1 H2 f rhat i := by
    intro i
    exact (hDeltaf i).trans (hDeltafDom i)
  have hDeltag : ∀ j : Fin n,
      |Deltag j| ≤ cG * lsTheorem20_4DeltagMajorant A H3 rhat j := by
    intro j
    have hmaj := lsTheorem20_4DeltagMajorant_nonneg A H3 rhat hH3nonneg j
    simpa [Deltag] using mul_nonneg hcG hmaj
  refine ⟨DeltaA, G, Deltaf, Deltag, DeltaR1, DeltaR2,
    hDeltaA, hGnonneg, hGnorm, hDeltaAcomp, hDeltafSrc, hDeltag,
    hDeltaR1, hDeltaR2, hRmat, hRhatBlock, ?_⟩
  simpa [R, cTop, cBot, h, rhat, Deltag] using hsys
/-- Explicit tilde-gamma for the fully absorbed Theorem 20.4 matrix
perturbations.  Its extra terms are dimension-only transport costs for the two
triangular solves; no input-data-dependent coefficient is hidden here. -/
noncomputable def lsTheorem20_4ConcreteGammaTildeTotal (fp : FPModel)
    (m n : ℕ) : ℝ :=
  let g0 := lsTheorem20_4ConcreteGammaTildeSqrtResidual fp m n
  let c := (m : ℝ) * (n : ℝ) * g0
  2 * (g0 + gamma fp n + gamma fp n * c)
/-- Higham, 2nd ed., Theorem 20.4, with both actual total matrix
perturbations absorbed into one common nonnegative Frobenius-unit witness.

The theorem executes the repository's Householder panel/RHS kernels and both
rounded triangular solves.  `gamma_tilde` is explicit and depends only on the
format and dimensions. -/
theorem LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_householderQRPanel_theorem20_4_printed_total_perturbations
    {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ)
    (f : Fin (n + k) → ℝ) (g : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex (n + k)))
    (hdomain : lsTheorem20_4FullRankComputedQRDomain fp A) :
    let gammaTilde :=
      lsTheorem20_4ConcreteGammaTildeTotal fp (n + k) n
    let Q := fl_householderQRPanel_Q fp (n + k) n A
    let Rhat := fl_householderQRPanel_R fp (n + k) n A
    let R : Fin n → Fin n → ℝ := fun i j => Rhat (Fin.castAdd k i) j
    let c_hat := fl_householderQRPanel_rhs fp (n + k) n A f
    let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
    let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
    let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
    let x : Fin n → ℝ := fl_backSub fp n R (fun i => cTop i - h i)
    let rhat : Fin (n + k) → ℝ := matMulVec (n + k) Q (Fin.append h cBot)
    ∃ DeltaA1 DeltaA2 : Fin (n + k) → Fin n → ℝ,
    ∃ G H1 H2 H3 : Fin (n + k) → Fin (n + k) → ℝ,
    ∃ Deltaf : Fin (n + k) → ℝ,
    ∃ Deltag : Fin n → ℝ,
      (∀ i j, 0 ≤ G i j) ∧ frobNorm G = 1 ∧
      (∀ i j, 0 ≤ H1 i j) ∧ frobNorm H1 = 1 ∧
      (∀ i j, 0 ≤ H2 i j) ∧ frobNorm H2 = 1 ∧
      (∀ i j, 0 ≤ H3 i j) ∧ frobNorm H3 = 1 ∧
      (∀ i j, |DeltaA1 i j| ≤
        ((n + k : ℝ) * (n : ℝ) * gammaTilde) *
          matMulRect (n + k) (n + k) n G (fun r s => |A r s|) i j) ∧
      (∀ i j, |DeltaA2 i j| ≤
        ((n + k : ℝ) * (n : ℝ) * gammaTilde) *
          matMulRect (n + k) (n + k) n G (fun r s => |A r s|) i j) ∧
      (∀ i, |Deltaf i| ≤
        (Real.sqrt (n + k : ℝ) * (n : ℝ) * gammaTilde) *
          lsTheorem20_4DeltafMajorant H1 H2 f rhat i) ∧
      (∀ j, |Deltag j| ≤
        (Real.sqrt (n + k : ℝ) * (n : ℝ) * gammaTilde) *
          lsTheorem20_4DeltagMajorant A H3 rhat j) ∧
      LSAsymmetricAugmentedSystem
        (fun i j => A i j + DeltaA1 i j)
        (fun i j => A i j + DeltaA2 i j)
        (fun i => f i + Deltaf i) (fun j => g j + Deltag j)
        rhat x := by
  let m : ℕ := n + k
  let Q : Fin m → Fin m → ℝ := fl_householderQRPanel_Q fp m n A
  let Rhat : Fin m → Fin n → ℝ := fl_householderQRPanel_R fp m n A
  let R : Fin n → Fin n → ℝ := fun i j => Rhat (Fin.castAdd k i) j
  let c_hat : Fin m → ℝ := fl_householderQRPanel_rhs fp m n A f
  let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
  let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
  let rhat : Fin m → ℝ := matMulVec m Q (Fin.append h cBot)
  let Kidx : ℕ := householderConstructApplyGammaIndex m
  let gammaPanel : ℝ := gamma fp (n * Kidx)
  let resCoeff : ℝ := householderQRRhsPanelSqrtResidualGrowthCoeff fp m n
  let g0 : ℝ := lsTheorem20_4ConcreteGammaTildeSqrtResidual fp m n
  let c : ℝ := (m : ℝ) * (n : ℝ) * g0
  let eta : ℝ := gamma fp n
  let gammaTilde : ℝ := lsTheorem20_4ConcreteGammaTildeTotal fp m n
  have hgamma : gammaValid fp n :=
    gammaValid_n_of_householderConstructApplyGammaValid fp m n (by
      simpa [m, Kidx] using hvalid)
  have hn_le_rows : n ≤ m := by simp [m]
  have hsteps : 0 < Nat.min m n := by
    simpa [Nat.min_eq_right hn_le_rows] using hn
  have hQR : StructuredHouseholderQRPanelHighamBackwardError m n A Q Rhat
      (gammaPanel * frobNorm A) ((m : ℝ) * gammaPanel) := by
    have hraw :=
      fl_householderQRPanel_R_higham_backward_error_gammaHigham_of_global_gammaValid
        fp m n A hsteps (by
          simpa [m, Kidx, Nat.min_eq_right hn_le_rows] using hvalid)
    simpa [Q, Rhat, gammaPanel, Kidx, Nat.min_eq_right hn_le_rows] using hraw
  have hK_le_nK : Kidx ≤ n * Kidx := by
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
    simpa using Nat.mul_le_mul_right Kidx hn1
  have hbase_le_K : 11 * m + 23 ≤ Kidx := by
    dsimp [Kidx, householderConstructApplyGammaIndex]
    omega
  have hbase_valid : gammaValid fp (11 * m + 23) :=
    gammaValid_mono fp (le_trans hbase_le_K hK_le_nK) (by
      simpa [m, Kidx] using hvalid)
  have hready : HouseholderQRPanelReady fp m n A :=
    HouseholderQRPanelReady_of_global_gammaValid fp m n m A le_rfl hbase_valid
  have hRhs : HouseholderQRRhsPanelExplicitBackwardError m n A f Q c_hat
      (householderQRRhsPanelSqrtResidualBackwardBound fp m n A f) := by
    simpa [Q, c_hat] using
      fl_householderQRPanel_rhs_explicit_backward_error_sqrt_residual
        fp m n A f hready
  rcases
      householderQRRhsPanelSqrtResidualBackwardBound_uniform_f_source_witness_of_sqrtResidualGrowthCoeff
        fp A f g hn hbase_valid hready with
    ⟨H1, H2, hH1nonneg, hH2nonneg, hH1norm, hH2norm, hDeltafDom⟩
  let row0 : Fin m := ⟨0, by simp [m]; omega⟩
  let H3 : Fin m → Fin m → ℝ := lsTheorem20_4OneHotMajorant row0 row0
  have hH3nonneg : ∀ i j, 0 ≤ H3 i j :=
    lsTheorem20_4OneHotMajorant_nonneg row0 row0
  have hH3norm : frobNorm H3 = 1 :=
    lsTheorem20_4OneHotMajorant_frobNorm row0 row0
  have hcG : 0 ≤ Real.sqrt (m : ℝ) * (n : ℝ) * gammaPanel := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg n))
      (gamma_nonneg fp (by simpa [m, Kidx, gammaPanel] using hvalid))
  rcases LSAsymmetricAugmentedSystem.exists_exact_qr_solution_with_source_bounds_and_qr_relation
      fp Q A Rhat f c_hat g
      (gammaPanel * frobNorm A) ((m : ℝ) * gammaPanel)
      (householderQRRhsPanelSqrtResidualBackwardBound fp m n A f)
      (Real.sqrt (m : ℝ) * resCoeff)
      (Real.sqrt (m : ℝ) * (n : ℝ) * gammaPanel)
      H1 H2 H3 hQR hRhs hcG hH1nonneg hH2nonneg hH3nonneg
      hH1norm hH2norm hH3norm
      (by simpa [Q, Rhat, R, c_hat, cBot, h, rhat, m, resCoeff] using
        hDeltafDom)
      (by simpa [Rhat, m] using hdomain.computedQRNonbreakdown) hgamma with
    ⟨DeltaA, G0, Deltaf, Deltag, DeltaR1, DeltaR2,
      _hDeltaAnorm, hG0nonneg, hG0norm, hDeltaAraw, hDeltaf, hDeltag,
      hDeltaR1, hDeltaR2, hQRrel, hRhatBlock, hsys⟩
  have hg0_nonneg : 0 ≤ g0 := by
    simpa [g0, m] using
      lsTheorem20_4ConcreteGammaTildeSqrtResidual_nonneg fp hn (by
        simpa [m, Kidx] using hvalid)
  have heta_nonneg : 0 ≤ eta := gamma_nonneg fp hgamma
  have hc_nonneg : 0 ≤ c := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))
      hg0_nonneg
  have hpanel_le_g0 : gammaPanel ≤ g0 := by
    simpa [gammaPanel, g0, m, Kidx] using
      gamma_le_lsTheorem20_4ConcreteGammaTildeSqrtResidual fp hn (by
        simpa [m, Kidx] using hvalid)
  have hres_le_g0 : resCoeff ≤ g0 := by
    simpa [resCoeff, g0, m] using
      householderQRRhsPanelSqrtResidualGrowthCoeff_le_lsTheorem20_4ConcreteGammaTildeSqrtResidual
        fp (m := m) (n := n) (by simpa [m, Kidx] using hvalid)
  have hDeltaA : ∀ i j,
      |DeltaA i j| ≤ c * matMulRect m m n G0 (fun r s => |A r s|) i j := by
    intro i j
    have hmaj : 0 ≤ matMulRect m m n G0 (fun r s => |A r s|) i j := by
      unfold matMulRect
      exact Finset.sum_nonneg (fun r _ =>
        mul_nonneg (hG0nonneg i r) (abs_nonneg _))
    have hcoeff : (m : ℝ) * gammaPanel ≤ c := by
      dsimp [c]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
      calc
        (m : ℝ) * gammaPanel ≤ (m : ℝ) * g0 :=
          mul_le_mul_of_nonneg_left hpanel_le_g0 (Nat.cast_nonneg m)
        _ = (m : ℝ) * (1 : ℝ) * g0 := by ring
        _ ≤ (m : ℝ) * (n : ℝ) * g0 := by gcongr
    exact (hDeltaAraw i j).trans (mul_le_mul_of_nonneg_right hcoeff hmaj)
  have hDhat1 : ∀ i j,
      |lsQRTallBlock (k := k) DeltaR1 i j| ≤ eta * |Rhat i j| := by
    intro i j
    rw [hRhatBlock]
    cases i using Fin.addCases with
    | left i => simpa [lsQRTallBlock, eta, R] using hDeltaR1 i j
    | right i => simp [lsQRTallBlock, eta]
  have hDhat2 : ∀ i j,
      |lsQRTallBlock (k := k) DeltaR2 i j| ≤ eta * |Rhat i j| := by
    intro i j
    rw [hRhatBlock]
    cases i using Fin.addCases with
    | left i => simpa [lsQRTallBlock, eta, R] using hDeltaR2 i j
    | right i => simp [lsQRTallBlock, eta]
  have htransport1 := higham20Theorem20_4_transport_domination_of_qr_relation
    Q G0 A DeltaA Rhat (lsQRTallBlock (k := k) DeltaR1) c eta
    hc_nonneg heta_nonneg hG0nonneg hQRrel hDeltaA hDhat1
  have htransport2 := higham20Theorem20_4_transport_domination_of_qr_relation
    Q G0 A DeltaA Rhat (lsQRTallBlock (k := k) DeltaR2) c eta
    hc_nonneg heta_nonneg hG0nonneg hQRrel hDeltaA hDhat2
  let QdR1 : Fin m → Fin n → ℝ := matMulRectLeft Q (lsQRTallBlock DeltaR1)
  let QdR2 : Fin m → Fin n → ℝ := matMulRectLeft Q (lsQRTallBlock DeltaR2)
  let DeltaA1 : Fin m → Fin n → ℝ := fun i j => DeltaA i j + QdR1 i j
  let DeltaA2 : Fin m → Fin n → ℝ := fun i j => DeltaA i j + QdR2 i j
  let W1 := higham20Theorem20_4TotalLeftWitness Q G0 c eta
  let W2 := higham20Theorem20_4TotalLeftWitness Q G0 c eta
  let W : Fin m → Fin m → ℝ := fun i j => W1 i j + W2 i j
  have hW1nonneg : ∀ i j, 0 ≤ W1 i j :=
    higham20Theorem20_4TotalLeftWitness_nonneg Q G0 c eta
      hG0nonneg hc_nonneg heta_nonneg
  have hW2nonneg : ∀ i j, 0 ≤ W2 i j := hW1nonneg
  have hdomW1 : ∀ i j, |DeltaA1 i j| ≤
      matMulRect m m n W1 (fun r s => |A r s|) i j := by
    simpa [DeltaA1, QdR1, W1] using
      higham20Theorem20_4TotalLeftWitness_domination_of_transport
        Q G0 A DeltaA QdR1 c eta hDeltaA htransport1
  have hdomW2 : ∀ i j, |DeltaA2 i j| ≤
      matMulRect m m n W2 (fun r s => |A r s|) i j := by
    simpa [DeltaA2, QdR2, W2] using
      higham20Theorem20_4TotalLeftWitness_domination_of_transport
        Q G0 A DeltaA QdR2 c eta hDeltaA htransport2
  have hWnonneg : ∀ i j, 0 ≤ W i j := by
    intro i j
    exact add_nonneg (hW1nonneg i j) (hW2nonneg i j)
  have hdom1 : ∀ i j, |DeltaA1 i j| ≤
      matMulRect m m n W (fun r s => |A r s|) i j := by
    intro i j
    exact (hdomW1 i j).trans
      (higham20Theorem20_4_matMulRect_mono_left W1 W
        (fun r s => |A r s|)
        (fun r s => le_add_of_nonneg_right (hW2nonneg r s))
        (fun r s => abs_nonneg _) i j)
  have hdom2 : ∀ i j, |DeltaA2 i j| ≤
      matMulRect m m n W (fun r s => |A r s|) i j := by
    intro i j
    exact (hdomW2 i j).trans
      (higham20Theorem20_4_matMulRect_mono_left W2 W
        (fun r s => |A r s|)
        (fun r s => le_add_of_nonneg_left (hW1nonneg r s))
        (fun r s => abs_nonneg _) i j)
  have hW1norm : frobNorm W1 ≤
      c + eta * (m : ℝ) + eta * c * (m : ℝ) := by
    simpa [W1] using higham20Theorem20_4TotalLeftWitness_frobNorm_le
      Q G0 c eta hQR.orth hG0norm hc_nonneg heta_nonneg
  have hW2norm : frobNorm W2 ≤
      c + eta * (m : ℝ) + eta * c * (m : ℝ) := by simpa [W2, W1] using hW1norm
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
  have heta_m_le : eta * (m : ℝ) ≤ eta * (m : ℝ) * (n : ℝ) := by
    calc
      eta * (m : ℝ) = (eta * (m : ℝ)) * 1 := by ring
      _ ≤ (eta * (m : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hn1R
          (mul_nonneg heta_nonneg (Nat.cast_nonneg m))
  have hetac_m_le : eta * c * (m : ℝ) ≤
      eta * c * (m : ℝ) * (n : ℝ) := by
    calc
      eta * c * (m : ℝ) = (eta * c * (m : ℝ)) * 1 := by ring
      _ ≤ (eta * c * (m : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hn1R
          (mul_nonneg (mul_nonneg heta_nonneg hc_nonneg) (Nat.cast_nonneg m))
  have hC : 2 * (c + eta * (m : ℝ) + eta * c * (m : ℝ)) ≤
      (m : ℝ) * (n : ℝ) * gammaTilde := by
    dsimp [gammaTilde, lsTheorem20_4ConcreteGammaTildeTotal]
    dsimp [c]
    calc
      2 * (((m : ℝ) * (n : ℝ) * g0) + eta * (m : ℝ) +
          eta * ((m : ℝ) * (n : ℝ) * g0) * (m : ℝ)) ≤
        2 * (((m : ℝ) * (n : ℝ) * g0) +
          eta * (m : ℝ) * (n : ℝ) +
          eta * ((m : ℝ) * (n : ℝ) * g0) * (m : ℝ) * (n : ℝ)) := by
            gcongr
      _ = (m : ℝ) * (n : ℝ) *
          (2 * (g0 + eta + eta * ((m : ℝ) * (n : ℝ) * g0))) := by ring
  have hWnorm : frobNorm W ≤ (m : ℝ) * (n : ℝ) * gammaTilde := by
    calc
      frobNorm W ≤ frobNorm W1 + frobNorm W2 := by
        simpa [W] using frobNorm_add_le W1 W2
      _ ≤ 2 * (c + eta * (m : ℝ) + eta * c * (m : ℝ)) := by linarith
      _ ≤ (m : ℝ) * (n : ℝ) * gammaTilde := hC
  let G := higham20Theorem20_4NormalizedWitness row0 row0 W
  have hGnonneg : ∀ i j, 0 ≤ G i j :=
    higham20Theorem20_4NormalizedWitness_nonneg row0 row0 W hWnonneg
  have hGnorm : frobNorm G = 1 :=
    higham20Theorem20_4NormalizedWitness_frobNorm row0 row0 W
  have htotal1 : ∀ i j, |DeltaA1 i j| ≤
      ((m : ℝ) * (n : ℝ) * gammaTilde) *
        matMulRect m m n G (fun r s => |A r s|) i j := by
    simpa [G] using higham20Theorem20_4_le_normalized_of_left_domination
      row0 row0 A DeltaA1 W ((m : ℝ) * (n : ℝ) * gammaTilde)
      hWnonneg hWnorm hdom1
  have htotal2 : ∀ i j, |DeltaA2 i j| ≤
      ((m : ℝ) * (n : ℝ) * gammaTilde) *
        matMulRect m m n G (fun r s => |A r s|) i j := by
    simpa [G] using higham20Theorem20_4_le_normalized_of_left_domination
      row0 row0 A DeltaA2 W ((m : ℝ) * (n : ℝ) * gammaTilde)
      hWnonneg hWnorm hdom2
  have hg0_le_total : g0 ≤ gammaTilde := by
    dsimp [gammaTilde, lsTheorem20_4ConcreteGammaTildeTotal]
    have hsum : 0 ≤ g0 + eta + eta * c := by positivity
    nlinarith
  have hDeltafTotal : ∀ i, |Deltaf i| ≤
      (Real.sqrt (m : ℝ) * (n : ℝ) * gammaTilde) *
        lsTheorem20_4DeltafMajorant H1 H2 f rhat i := by
    intro i
    have hmaj := lsTheorem20_4DeltafMajorant_nonneg
      H1 H2 f rhat hH1nonneg hH2nonneg i
    have hcoeff : Real.sqrt (m : ℝ) * resCoeff ≤
        Real.sqrt (m : ℝ) * (n : ℝ) * gammaTilde := by
      have hres : resCoeff ≤ (n : ℝ) * gammaTilde :=
        hres_le_g0.trans <| calc
          g0 = 1 * g0 := by ring
          _ ≤ (n : ℝ) * gammaTilde :=
            mul_le_mul hn1R hg0_le_total hg0_nonneg (by positivity)
      calc
        Real.sqrt (m : ℝ) * resCoeff ≤
            Real.sqrt (m : ℝ) * ((n : ℝ) * gammaTilde) :=
          mul_le_mul_of_nonneg_left hres (Real.sqrt_nonneg _)
        _ = Real.sqrt (m : ℝ) * (n : ℝ) * gammaTilde := by ring
    exact (hDeltaf i).trans (mul_le_mul_of_nonneg_right hcoeff hmaj)
  have hDeltagTotal : ∀ j, |Deltag j| ≤
      (Real.sqrt (m : ℝ) * (n : ℝ) * gammaTilde) *
        lsTheorem20_4DeltagMajorant A H3 rhat j := by
    intro j
    have hmaj := lsTheorem20_4DeltagMajorant_nonneg A H3 rhat hH3nonneg j
    have hcoeff : Real.sqrt (m : ℝ) * (n : ℝ) * gammaPanel ≤
        Real.sqrt (m : ℝ) * (n : ℝ) * gammaTilde := by
      gcongr
      exact hpanel_le_g0.trans hg0_le_total
    exact (hDeltag j).trans (mul_le_mul_of_nonneg_right hcoeff hmaj)
  have htotal1' : ∀ i j, |DeltaA1 i j| ≤
      ((n + k : ℝ) * (n : ℝ) *
        lsTheorem20_4ConcreteGammaTildeTotal fp (n + k) n) *
        matMulRect (n + k) (n + k) n G (fun r s => |A r s|) i j := by
    simpa [m, gammaTilde] using htotal1
  have htotal2' : ∀ i j, |DeltaA2 i j| ≤
      ((n + k : ℝ) * (n : ℝ) *
        lsTheorem20_4ConcreteGammaTildeTotal fp (n + k) n) *
        matMulRect (n + k) (n + k) n G (fun r s => |A r s|) i j := by
    simpa [m, gammaTilde] using htotal2
  have hDeltafTotal' : ∀ i, |Deltaf i| ≤
      (Real.sqrt (n + k : ℝ) * (n : ℝ) *
        lsTheorem20_4ConcreteGammaTildeTotal fp (n + k) n) *
        lsTheorem20_4DeltafMajorant H1 H2 f
          (matMulVec (n + k) (fl_householderQRPanel_Q fp (n + k) n A)
            (Fin.append
              (fl_forwardSub fp n
                (matTranspose (fun i j =>
                  fl_householderQRPanel_R fp (n + k) n A (Fin.castAdd k i) j)) g)
              (fun i =>
                fl_householderQRPanel_rhs fp (n + k) n A f (Fin.natAdd n i)))) i := by
    simpa [m, gammaTilde, rhat, Q, R, c_hat, cBot, h] using hDeltafTotal
  have hDeltagTotal' : ∀ j, |Deltag j| ≤
      (Real.sqrt (n + k : ℝ) * (n : ℝ) *
        lsTheorem20_4ConcreteGammaTildeTotal fp (n + k) n) *
        lsTheorem20_4DeltagMajorant A H3
          (matMulVec (n + k) (fl_householderQRPanel_Q fp (n + k) n A)
            (Fin.append
              (fl_forwardSub fp n
                (matTranspose (fun i j =>
                  fl_householderQRPanel_R fp (n + k) n A (Fin.castAdd k i) j)) g)
              (fun i =>
                fl_householderQRPanel_rhs fp (n + k) n A f (Fin.natAdd n i)))) j := by
    simpa [m, gammaTilde, rhat, Q, R, c_hat, cBot, h] using hDeltagTotal
  refine ⟨DeltaA1, DeltaA2, G, H1, H2, H3, Deltaf, Deltag,
    hGnonneg, hGnorm, hH1nonneg, hH1norm, hH2nonneg, hH2norm,
    hH3nonneg, hH3norm, htotal1', htotal2', hDeltafTotal', hDeltagTotal', ?_⟩
  simpa [m, Q, Rhat, R, c_hat, cBot, h, rhat, DeltaA1, DeltaA2,
    QdR1, QdR2, add_assoc] using hsys

end NumStability
