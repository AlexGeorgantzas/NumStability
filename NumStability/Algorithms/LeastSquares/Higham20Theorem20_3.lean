import NumStability.Algorithms.LeastSquares.LSQRSolve
import NumStability.Algorithms.QR.Higham19

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

namespace Theorem20_3

/-!
# Higham, Chapter 20, Theorem 20.3

This module closes the source-facing Householder-QR least-squares route using
the repository's concrete zero-aware panel implementation.  The matrix
perturbation is the columnwise `(19.11)`/Theorem 19.4 certificate, the
right-hand side is transformed by the same exact orthogonal witness, and the
computed top triangular system is solved by `fl_backSub`.

The RHS implementation currently has a conservative accumulated gamma index.
Accordingly, `gamma_tilde_mn` is an explicit dimension-only envelope rather
than an assertion that the repository's implementation realizes Higham's
hidden sharp constant.
-/

/-- One gamma-validity radius covering the Householder QR panel, its concrete
RHS transform, and rounded `n`-by-`n` back substitution. -/
def gammaIndex (m n : ℕ) : ℕ :=
  Nat.max n
    (Nat.max (n * householderConstructApplyGammaIndex m)
      (Nat.max (11 * m + 23)
        (householderQRRhsPanelGammaClosedGrowthIndex m n)))

/-- The actual computed `n`-by-`n` top block of the concrete tall QR panel. -/
noncomputable def computedR {m n : ℕ} (fp : FPModel)
    (A : Fin m → Fin n → ℝ) (hmn : n ≤ m) : Fin n → Fin n → ℝ :=
  fun i j =>
    fl_householderQRPanel_R fp m n A
      ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j

/-- The actual computed top `n` entries of the concrete Householder RHS
transform. -/
noncomputable def computedC {m n : ℕ} (fp : FPModel)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (hmn : n ≤ m) : Fin n → ℝ :=
  fun i =>
    fl_householderQRPanel_rhs fp m n A b
      ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩

/-- The concrete computed least-squares vector: rounded back substitution on
the computed top `R` block and computed transformed top RHS. -/
noncomputable def computedX {m n : ℕ} (fp : FPModel)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (hmn : n ≤ m) : Fin n → ℝ :=
  fl_backSub fp n (computedR fp A hmn) (computedC fp A b hmn)

/-- Matrix-side coefficient after composing the columnwise QR perturbation
with the componentwise backward error of rounded back substitution. -/
noncomputable def matrixCoeff (fp : FPModel) (m n : ℕ) : ℝ :=
  let η := H19.Theorem19_4.gamma_tilde fp m n
  η + gamma fp n * (1 + η)

/-- Dimension-only RHS coefficient obtained from the verified accumulated
gamma-index bound for the concrete Householder RHS transform. -/
noncomputable def rhsCoeff (fp : FPModel) (m n : ℕ) : ℝ :=
  Real.sqrt (m : ℝ) *
    gamma fp (householderQRRhsPanelGammaClosedGrowthIndex m n)

/-- A single explicit `gamma_tilde_mn` envelope for both perturbations in
Higham's Theorem 20.3 conclusion. -/
noncomputable def gamma_tilde_mn (fp : FPModel) (m n : ℕ) : ℝ :=
  max (matrixCoeff fp m n) (rhsCoeff fp m n)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.3, for the repository's actual
Householder QR least-squares implementation.

Under the public algorithm-domain guards, the returned vector is literally
`fl_backSub` applied to the computed top block of
`fl_householderQRPanel_R` and the computed top part of
`fl_householderQRPanel_rhs`.  It is an exact least-squares minimizer for
perturbed source data, with both the columnwise matrix perturbation and the RHS
perturbation bounded by the same explicit dimension-only coefficient.

The nonzero-diagonal hypothesis is precisely the public domain condition of
triangular back substitution; no stored-loop conditioning, active-pivot, or
source-denominator hypotheses occur. -/
theorem householder_qr_fl_backSub_backward_error
    {m n : ℕ} (fp : FPModel)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hn : 0 < n) (hmn : n ≤ m)
    (hvalid : gammaValid fp (gammaIndex m n))
    (hdiag : ∀ i : Fin n, computedR fp A hmn i i ≠ 0) :
    ∃ (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      (∀ j : Fin n,
        vecNorm2 (fun i : Fin m => ΔA i j) ≤
          gamma_tilde_mn fp m n *
            vecNorm2 (fun i : Fin m => A i j)) ∧
      vecNorm2 Δb ≤ gamma_tilde_mn fp m n * vecNorm2 b ∧
      IsLeastSquaresMinimizer
        (fun i j => A i j + ΔA i j) (fun i => b i + Δb i)
        (fl_backSub fp n (computedR fp A hmn) (computedC fp A b hmn)) := by
  have hvalid_n : gammaValid fp n :=
    gammaValid_mono fp (by simp [gammaIndex]) hvalid
  have hvalid_qr :
      gammaValid fp (n * householderConstructApplyGammaIndex m) :=
    gammaValid_mono fp (by simp [gammaIndex]) hvalid
  have hvalid_base : gammaValid fp (11 * m + 23) :=
    gammaValid_mono fp (by simp [gammaIndex]) hvalid
  have hvalid_rhs :
      gammaValid fp (householderQRRhsPanelGammaClosedGrowthIndex m n) :=
    gammaValid_mono fp (by simp [gammaIndex]) hvalid
  have hsteps : 0 < Nat.min m n := by
    simpa [Nat.min_eq_right hmn] using hn
  have hpanel :=
    fl_householderQRPanel_R_columnwise_backward_error_gammaHigham_of_global_gammaValid
      fp m n A hsteps (by
        simpa [Nat.min_eq_right hmn] using hvalid_qr)
  rcases hpanel.result with ⟨ΔA₀, hAhat, _hΔA_frob, hΔA_cols⟩
  have hready : HouseholderQRPanelReady fp m n A :=
    HouseholderQRPanelReady_of_global_gammaValid fp m n m A le_rfl hvalid_base
  rcases fl_householderQRPanel_rhs_explicit_vecNorm2_perturbation_bound
      fp m n A b hready with
    ⟨Δb₀, hbhat, hΔb_raw⟩
  have hraw_le_inf :
      householderQRRhsPanelBackwardBound fp m n A b ≤
        gamma fp (householderQRRhsPanelGammaClosedGrowthIndex m n) *
          infNormVec b :=
    householderQRRhsPanelBackwardBound_le_gammaClosedGrowthIndex
      fp m n A b hmn hvalid_rhs hready
  have hinf_le_vec : infNormVec b ≤ vecNorm2 b :=
    infNormVec_le_of_abs_le b
      (fun i => abs_coord_le_vecNorm2 b i) (vecNorm2_nonneg b)
  have hgamma_rhs_nonneg :
      0 ≤ gamma fp (householderQRRhsPanelGammaClosedGrowthIndex m n) :=
    gamma_nonneg fp hvalid_rhs
  have hsqrt_nonneg : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hΔb : vecNorm2 Δb₀ ≤ rhsCoeff fp m n * vecNorm2 b := by
    calc
      vecNorm2 Δb₀
          ≤ Real.sqrt (m : ℝ) *
              householderQRRhsPanelBackwardBound fp m n A b := hΔb_raw
      _ ≤ Real.sqrt (m : ℝ) *
            (gamma fp (householderQRRhsPanelGammaClosedGrowthIndex m n) *
              infNormVec b) :=
          mul_le_mul_of_nonneg_left hraw_le_inf hsqrt_nonneg
      _ ≤ Real.sqrt (m : ℝ) *
            (gamma fp (householderQRRhsPanelGammaClosedGrowthIndex m n) *
              vecNorm2 b) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinf_le_vec hgamma_rhs_nonneg)
            hsqrt_nonneg
      _ = rhsCoeff fp m n * vecNorm2 b := by
          simp [rhsCoeff, mul_assoc]
  have hAhat' : ∀ i j,
      fl_householderQRPanel_R fp m n A i j =
        matMulRectLeft
          (matTranspose (fl_householderQRPanel_Q fp m n A))
          (fun a b => A a b + ΔA₀ a b) i j := by
    intro i j
    simpa [matMulRectLeft, matMulRect] using hAhat i j
  have hA_top : ∀ (i : Fin m) (j : Fin n) (hi : i.val < n),
      fl_householderQRPanel_R fp m n A i j =
        computedR fp A hmn ⟨i.val, hi⟩ j := by
    intro i j hi
    dsimp [computedR]
  have hA_bottom : ∀ (i : Fin m) (j : Fin n), n ≤ i.val →
      fl_householderQRPanel_R fp m n A i j = 0 := by
    intro i j hi
    exact hpanel.upper i j (lt_of_lt_of_le j.isLt hi)
  have hb_top : ∀ (i : Fin m) (hi : i.val < n),
      fl_householderQRPanel_rhs fp m n A b i =
        computedC fp A b hmn ⟨i.val, hi⟩ := by
    intro i hi
    dsimp [computedC]
  have hupper : ∀ i j : Fin n, j.val < i.val →
      computedR fp A hmn i j = 0 := by
    intro i j hji
    exact hpanel.upper
      ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j hji
  have hΔA_cols' : ∀ j : Fin n,
      vecNorm2 (fun i : Fin m => ΔA₀ i j) ≤
        H19.Theorem19_4.gamma_tilde fp m n *
          vecNorm2 (fun i : Fin m => A i j) := by
    intro j
    simpa [H19.Theorem19_4.gamma_tilde, Nat.min_eq_right hmn,
      columnFrob_eq_vecNorm2] using hΔA_cols j
  rcases
      exists_perturbed_ls_minimizer_of_commonQ_topBlock_fl_backSub_gamma_bound_columnwise
        fp A ΔA₀ b Δb₀
        (fl_householderQRPanel_R fp m n A)
        (fl_householderQRPanel_rhs fp m n A b)
        (fl_householderQRPanel_Q fp m n A)
        (computedR fp A hmn) (computedC fp A b hmn)
        (fun j => H19.Theorem19_4.gamma_tilde fp m n *
          vecNorm2 (fun i : Fin m => A i j))
        (rhsCoeff fp m n * vecNorm2 b)
        hpanel.orth hAhat' hbhat hA_top hA_bottom hb_top hdiag hupper
        hvalid_n hΔA_cols' hΔb with
    ⟨ΔA, Δb, hΔA_final, hΔb_final, hmin⟩
  refine ⟨ΔA, Δb, ?_, ?_, ?_⟩
  · intro j
    let aNorm : ℝ := vecNorm2 (fun i : Fin m => A i j)
    have haNorm_nonneg : 0 ≤ aNorm := vecNorm2_nonneg _
    calc
      vecNorm2 (fun i : Fin m => ΔA i j)
          ≤ H19.Theorem19_4.gamma_tilde fp m n * aNorm +
              gamma fp n *
                (aNorm + H19.Theorem19_4.gamma_tilde fp m n * aNorm) := by
            simpa [aNorm] using hΔA_final j
      _ = matrixCoeff fp m n * aNorm := by
            simp [matrixCoeff]
            ring
      _ ≤ gamma_tilde_mn fp m n * aNorm :=
            mul_le_mul_of_nonneg_right
              (le_max_left (matrixCoeff fp m n) (rhsCoeff fp m n))
              haNorm_nonneg
  · exact le_trans hΔb_final
      (mul_le_mul_of_nonneg_right
        (le_max_right (matrixCoeff fp m n) (rhsCoeff fp m n))
        (vecNorm2_nonneg b))
  · exact hmin

end Theorem20_3

end NumStability
