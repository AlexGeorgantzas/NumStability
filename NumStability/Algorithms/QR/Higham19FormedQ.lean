-- Algorithms/QR/Higham19FormedQ.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms" (2nd ed.),
-- §19.3, equation (19.13): the FORMED Householder orthogonal factor Q̂.
--
--   ‖Q̂ − Q‖_F ≤ √n · γ̃_{mn}
--
-- Here Q̂ is the explicitly formed product of the computed Householder
-- reflectors, obtained by applying the r rounded reflectors to the identity,
-- and Q is the exact orthogonal factor from the residual-form backward-error
-- factorization.  This file assembles that bound from the repository's
-- existing accumulated-reflector sequence backward-error surfaces
-- (`fl_householder_sequence_backward_error`, HouseholderQR.lean:579) together
-- with the `opNorm2`/Frobenius plumbing in MatrixAlgebra.lean.
--
-- SCOPE (honest).  This file targets ONLY the formed-Q̂ closeness bound of
-- eq (19.13).  It is a DIFFERENT statement from the MGS stored-loop bottleneck
-- `H19.Theorem19_13.mgs_qr_bounds` (Higham19.lean): that one requires a
-- perturbation bridge past the four `rounded_normalized_betaSpec_*_handoff`
-- counterexamples and is Codex's genuinely-open lane.  Nothing here touches it.
-- The (19.35)–(19.37) Stewart/Zha QR sensitivity theory is likewise DEFERRED:
-- it needs perturbation machinery absent from Mathlib.
--
-- CONSTANT (honest).  The printed book constant is `√n · γ̃_{mn}`.  What we
-- prove is `‖Q̂ − Q‖_F ≤ residualAccumBound (householderConstructApplyBound
-- fp n) r · √n`, i.e. the exact higher-order accumulation the book hides inside
-- its generic `γ̃`.  We also give the γ-collapsed corollary
-- `‖Q̂ − Q‖_F ≤ √n · gamma fp (r * (3*(11n+23)))`, matching the `√n · γ̃`
-- shape once the loop accumulation is absorbed into a single Higham `γ` term.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.QR.HouseholderQR

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- opNorm2 / Frobenius plumbing for the formed square factor Q̂
-- ============================================================

/-- The formed orthogonal factor is `m × m` (square), so its 2-norm/Frobenius
    interplay is governed by the square `opNorm2` primitive
    (`MatrixAlgebra.lean:5860`).  This wrapper records the standard
    `‖M‖₂ ≤ ‖M‖_F` bound applied to the *difference* `Q̂ − Q`, which is exactly
    the operator-norm consequence of the Frobenius closeness bound of
    eq (19.13).  It lets a caller stated in the exact l2 operator norm consume
    a Frobenius-form conclusion. -/
theorem opNorm2_matDiff_le_frobNorm {n : ℕ}
    (Qhat Q : Fin n → Fin n → ℝ) :
    opNorm2 (fun i j => Qhat i j - Q i j) ≤
      frobNorm (fun i j => Qhat i j - Q i j) :=
  opNorm2_le_of_opNorm2Le (fun i j => Qhat i j - Q i j)
    (frobNorm_nonneg _)
    (opNorm2Le_of_frobNorm_self (fun i j => Qhat i j - Q i j))

/-- If the Frobenius closeness of eq (19.13) is bounded by `b`, so is the exact
    2-norm distance between the formed factor and the exact orthogonal factor.
    This is the `opNorm2` face of the same bound. -/
theorem opNorm2_matDiff_le_of_frobNorm_le {n : ℕ}
    {Qhat Q : Fin n → Fin n → ℝ} {b : ℝ}
    (hb : frobNorm (fun i j => Qhat i j - Q i j) ≤ b) :
    opNorm2 (fun i j => Qhat i j - Q i j) ≤ b :=
  le_trans (opNorm2_matDiff_le_frobNorm Qhat Q) hb

-- ============================================================
-- §19.3 eq (19.13): formed-Q̂ backward error, core assembly
-- ============================================================

/-- **Formed-Q̂ closeness of a sequence of computed reflectors** (the engine of
    Higham eq (19.13)).

    Feed the residual-form accumulated-reflector backward error with the
    identity as the transformed matrix: applying the `r` rounded Householder
    reflectors to `I` forms `Q̂ := Aseq r`.  The sequence theorem yields an
    orthogonal `Q` and a perturbation `ΔA` with
    `Q̂ = Qᵀ(I + ΔA)`, so `Q̂ − Qᵀ = Qᵀ ΔA`, whence — since `Qᵀ` is orthogonal
    and Frobenius-norm invariant under it —
    `‖Q̂ − Qᵀ‖_F = ‖ΔA‖_F ≤ residualAccumBound c r · ‖I‖_F = √n · residualAccumBound c r`.

    The returned `Qexact` is `matTranspose Q`, which is the orthogonal factor
    the book calls `Q` in eq (19.13).  `Qhat` is any matrix that equals the
    residual-form composite `Qᵀ(I + ΔA)`; the caller supplies it via `hform`. -/
theorem formed_Q_backward_error_of_sequence
    {n : ℕ} (Qhat : Fin n → Fin n → ℝ)
    (c : ℝ) (_hc : 0 ≤ c) (r : ℕ)
    (Q ΔA : Fin n → Fin n → ℝ)
    (hQ : IsOrthogonal n Q)
    (hform : ∀ i j, Qhat i j =
      matMul n (matTranspose Q)
        (fun a b => idMatrix n a b + ΔA a b) i j)
    (hΔA : frobNorm ΔA ≤ residualAccumBound c r * frobNorm (idMatrix n)) :
    ∃ Qexact : Fin n → Fin n → ℝ,
      IsOrthogonal n Qexact ∧
      frobNorm (fun i j => Qhat i j - Qexact i j) ≤
        residualAccumBound c r * Real.sqrt (n : ℝ) := by
  -- The exact orthogonal factor from the residual factorization.
  refine ⟨matTranspose Q, hQ.transpose, ?_⟩
  -- `Qᵀ` is orthogonal, so `frobNorm (matMul n Qᵀ ΔA) = frobNorm ΔA`.
  have hQT : IsOrthogonal n (matTranspose Q) := hQ.transpose
  -- Pointwise: `Q̂ i j − Qᵀ i j = (matMul n Qᵀ ΔA) i j`.
  have hdiff :
      (fun i j => Qhat i j - matTranspose Q i j) =
        matMul n (matTranspose Q) ΔA := by
    funext i j
    have hexpand :
        matMul n (matTranspose Q)
            (fun a b => idMatrix n a b + ΔA a b) i j =
          matMul n (matTranspose Q) (idMatrix n) i j +
            matMul n (matTranspose Q) ΔA i j :=
      congr_fun
        (congr_fun (matMul_add_right n (matTranspose Q) (idMatrix n) ΔA) i) j
    have hid :
        matMul n (matTranspose Q) (idMatrix n) i j = matTranspose Q i j :=
      congr_fun (congr_fun (matMul_id_right n (matTranspose Q)) i) j
    rw [hform i j, hexpand, hid]
    ring
  -- Frobenius norm of the difference equals `frobNorm ΔA`.
  have hnorm :
      frobNorm (fun i j => Qhat i j - matTranspose Q i j) = frobNorm ΔA := by
    rw [hdiff]
    exact frobNorm_orthogonal_left (matTranspose Q) ΔA hQT
  -- `‖I‖_F = √n`.
  have hidNorm : frobNorm (idMatrix n) = Real.sqrt (n : ℝ) :=
    (idMatrix_orthogonal n).frobNorm_eq_sqrt_card
  rw [hnorm]
  calc
    frobNorm ΔA
        ≤ residualAccumBound c r * frobNorm (idMatrix n) := hΔA
    _ = residualAccumBound c r * Real.sqrt (n : ℝ) := by rw [hidNorm]

/-- **Higham Theorem 19.13 / eq (19.13): formed Householder Q̂ backward error.**

    Applying the `r` concrete rounded Householder reflectors — built from the
    nonzero vectors `xseq k` — to the identity forms the explicit orthogonal
    factor `Q̂ := Aseq r`.  It is close in the Frobenius norm to an exact
    orthogonal factor `Q`:

      `‖Q̂ − Q‖_F ≤ residualAccumBound (householderConstructApplyBound fp n) r · √n`.

    This is precisely the `√n · γ̃_{mn}` closeness of eq (19.13), with the exact
    higher-order accumulation kept explicit rather than collapsed into the
    book's generic `γ̃`.  See `H19_eq19_13_formed_Q_backward_error_gamma` for the
    single-`γ` corollary matching the printed constant shape.

    NOTE.  This is the FORMED-Q̂ bound.  It is NOT the MGS stored-loop
    `mgs_qr_bounds` (Higham19.lean, Codex's lane), which is a different and
    genuinely-open statement blocked by the `rounded_normalized_betaSpec_*`
    counterexamples. -/
theorem H19_eq19_13_formed_Q_backward_error
    (fp : FPModel) {n r : ℕ} (hn0 : 0 < n)
    (Aseq : ℕ → Fin n → Fin n → ℝ)
    (xseq : ℕ → Fin n → ℝ)
    (hx : ∀ k : ℕ, k < r → xseq k ≠ 0)
    (hvalid : gammaValid fp (11 * n + 23))
    (hInit : Aseq 0 = idMatrix n)
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_householderApplyMatrix fp n
          (fl_householderNormalizedVector fp hn0 (xseq k)) 1 (Aseq k)) :
    ∃ Q : Fin n → Fin n → ℝ,
      IsOrthogonal n Q ∧
      frobNorm (fun i j => Aseq r i j - Q i j) ≤
        residualAccumBound (householderConstructApplyBound fp n) r *
          Real.sqrt (n : ℝ) := by
  obtain ⟨Q, ΔA, hQ, hrep, hΔA⟩ :=
    fl_householder_sequence_backward_error fp hn0 Aseq xseq hx hvalid hAstep
  refine formed_Q_backward_error_of_sequence (Aseq r)
      (householderConstructApplyBound fp n)
      (householderConstructApplyBound_nonneg fp n hvalid) r Q ΔA hQ ?_ ?_
  · intro i j
    have := hrep i j
    rw [hInit] at this
    exact this
  · rw [hInit] at hΔA
    exact hΔA

/-- **γ-collapsed form of eq (19.13)** matching the printed `√n · γ̃` constant.

    The higher-order loop accumulation `residualAccumBound (…) r` is absorbed
    into a single Higham `γ` term of index `r * (3*(11n+23))`, giving

      `‖Q̂ − Q‖_F ≤ √n · γ_{r·(3(11n+23))}`,

    the concrete `√n · γ̃_{mn}` shape of the book. -/
theorem H19_eq19_13_formed_Q_backward_error_gamma
    (fp : FPModel) {n r : ℕ} (hn0 : 0 < n)
    (Aseq : ℕ → Fin n → Fin n → ℝ)
    (xseq : ℕ → Fin n → ℝ)
    (hx : ∀ k : ℕ, k < r → xseq k ≠ 0)
    (hvalid : gammaValid fp (householderConstructApplyGammaIndex n))
    (hvalidLoop : gammaValid fp (r * householderConstructApplyGammaIndex n))
    (hInit : Aseq 0 = idMatrix n)
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_householderApplyMatrix fp n
          (fl_householderNormalizedVector fp hn0 (xseq k)) 1 (Aseq k)) :
    ∃ Q : Fin n → Fin n → ℝ,
      IsOrthogonal n Q ∧
      frobNorm (fun i j => Aseq r i j - Q i j) ≤
        Real.sqrt (n : ℝ) *
          gamma fp (r * householderConstructApplyGammaIndex n) := by
  -- The per-step Householder coefficient is `≤ γ_k` for `k = 3(11n+23)`.
  have hvalid11 : gammaValid fp (11 * n + 23) :=
    gammaValid_mono fp (by
      dsimp [householderConstructApplyGammaIndex]; omega) hvalid
  obtain ⟨Q, hQ, hbound⟩ :=
    H19_eq19_13_formed_Q_backward_error fp hn0 Aseq xseq hx hvalid11 hInit hAstep
  refine ⟨Q, hQ, ?_⟩
  set k : ℕ := householderConstructApplyGammaIndex n with hk
  set c : ℝ := householderConstructApplyBound fp n with hcdef
  have hc_nonneg : 0 ≤ c := householderConstructApplyBound_nonneg fp n hvalid11
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  -- Step 1: per-step coefficient collapses to `γ_k`.
  have hc_le_gamma : c ≤ gamma fp k :=
    householderConstructApplyBound_le_gamma fp n hvalid
  -- Step 2: monotonicity of the accumulation in the per-step coefficient.
  have hmono :
      residualAccumBound c r ≤ residualAccumBound (gamma fp k) r :=
    residualAccumBound_mono hc_nonneg hc_le_gamma r
  -- Step 3: absorb the `r`-fold accumulation into a single `γ_{r·k}`.
  have hcollapse :
      residualAccumBound (gamma fp k) r ≤ gamma fp (r * k) :=
    residualAccumBound_gamma_le_gamma_mul fp k r hvalidLoop
  have haccum_le : residualAccumBound c r ≤ gamma fp (r * k) :=
    le_trans hmono hcollapse
  -- Assemble: `‖Q̂ − Q‖_F ≤ (residualAccumBound c r)·√n ≤ √n · γ_{r·k}`.
  calc
    frobNorm (fun i j => Aseq r i j - Q i j)
        ≤ residualAccumBound c r * Real.sqrt (n : ℝ) := hbound
    _ ≤ gamma fp (r * k) * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_right haccum_le hsqrt_nonneg
    _ = Real.sqrt (n : ℝ) * gamma fp (r * k) := by ring

end NumStability
