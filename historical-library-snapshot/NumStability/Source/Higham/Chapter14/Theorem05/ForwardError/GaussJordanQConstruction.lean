import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GaussJordanAccumulation
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanStep

/-!
# Chapter14 Theorem05 ForwardError GaussJordanQConstruction

Canonical destination for material split out of
`NumStability.Algorithms.Ch14GaussJordanQConstruction` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators
open NumStability

namespace NumStability

namespace Ch14Ext

/-- **Theorem 14.5 / eq. (14.32): overall GJE forward error, constructed `Q`.**

    As `ch14ext_gje_overall_forward_error_of_accumulation`, but with the
    supplied-`Q` hypothesis discharged by the construction. -/
theorem ch14ext_gjeConstructedQ_overall_forward_error
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat : Fin n → Fin n → ℝ) (b x x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * xseq start j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hxrec : ∀ t : ℕ, (ht : t < n - 1) →
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |V start l k|) * |x_hat k| +
        gje_c₃ fp n * ∑ k : Fin n,
          (∑ k₁ : Fin n, |L_hat j k₁| *
            (∑ k₂ : Fin n,
              |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
                  (ch14ext_gjeConstructedQ n V start) start (n - 1) k₁ k₂| *
                |V start k₂ k|)) * |x_hat k| +
        gje_c₃ fp n * ∑ l : Fin n, |L_hat j l| *
          (∑ k : Fin n,
            |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
                (ch14ext_gjeConstructedQ n V start) start (n - 1) l k| *
              |xseq start k|)) :=
  ch14ext_gje_overall_forward_error_of_accumulation n fp A A_inv L_hat b x x_hat
    (ch14ext_gjeSeqStages n V) V xseq (ch14ext_gjeConstructedQ n V start) start
    hLU hAinv hn hnpos h3 hidx hVfinal hxfinal
    (ch14ext_gjeConstructedQ_isLeftInverse n V start hidx) hy hExact
    (ch14ext_gjeConcrete_hrecM fp n V start h3 hidx hVrec hpiv)
    (ch14ext_gjeConcrete_hrecX fp n V xseq start h3 hidx hxrec hpiv)

/-- **Conditional residual-transfer forward bound, not the printed (14.32).**

    Transferring the single-object `8nu` residual (`ch14ext_gjeConstructedQ_residual_8nu`)
    through `|A⁻¹|` (`ch14ext_forward_transfer`) yields
        `|x − x̂| ≤ ∑ⱼ |A⁻¹ᵢⱼ| · (8nu + ch14ext_residualRem)·S2ⱼ`,
    i.e. the forward error is `O(u)` with the printed-order leading constant on
    the object `|A⁻¹||L̂||X_abs||Û||x̂|`.

    STRUCTURAL RESIDUAL (documented).  This is the accumulation's `3-factor`
    object `|A⁻¹||L̂||X_abs||Û|` (with `X_abs ≈ |Û||Û⁻¹|`), NOT the printed
    two-term split `2nu|A⁻¹||L̂||Û||x̂| + 6nu|Û⁻¹||Û||x̂|` of (14.32): the second
    printed term carries NEITHER `|A⁻¹|` NOR `|L̂|`.  Reaching it requires bounding
    the split `(x−x₀)+(x₀−Û⁻¹ŷ)+(Û⁻¹ŷ−x̂)` of Higham's proof — the last term via
    (14.29) applied DIRECTLY to `Ûx = ŷ` — instead of transferring the whole
    residual through `|A⁻¹|`.  The printed constants themselves are audited in
    §B1 (`ch14ext_gje_forward_first_coeff` `= 2nu`,
    `ch14ext_gje_forward_second_coeff` `= 6nu`). -/
theorem ch14ext_gjeConstructedQ_forward_error_8nu
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat : Fin n → Fin n → ℝ) (b x x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * xseq start j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hxrec : ∀ t : ℕ, (ht : t < n - 1) →
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0)
    (hySharp : ∀ m : Fin n,
      |xseq start m| ≤ ∑ l : Fin n, |V start m l| * |x_hat l|) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (8 * (n : ℝ) * fp.u * ch14ext_gjeS2row n L_hat V x_hat start j +
          ch14ext_residualRem fp n * ch14ext_gjeS2row n L_hat V x_hat start j) := by
  have hres8 := ch14ext_gjeConstructedQ_residual_8nu n fp A L_hat b x_hat V xseq start
    hLU hn hnpos h3 hidx hVfinal hxfinal hy hVrec hxrec hpiv hySharp
  exact ch14ext_forward_transfer n A A_inv b x x_hat
    (fun j => 8 * (n : ℝ) * fp.u * ch14ext_gjeS2row n L_hat V x_hat start j +
      ch14ext_residualRem fp n * ch14ext_gjeS2row n L_hat V x_hat start j)
    hAinv hExact hres8

/-- **Higham Theorem 14.5, equation (14.32), exact stage-envelope split.**

    Let `z` be the exact solution of `Uhat z = yhat`.  The first two terms of
    Higham's split are derived from
    `A(x-z) = DeltaA1*z + DeltaL*yhat`; the last term is the concrete (14.29)
    recurrence bound with its self-substitution made explicit.  Consequently
    the two printed first-order objects remain separate:

    `2*n*u |A^{-1}||Lhat||Uhat||xhat|`
    and
    `6*n*u |X||Uhat||xhat|`.

    All substitutions of `z` by `xhat` occur only in
    `ch14ext_gjeForwardHigherOrder`, which is proved nonnegative and consists
    solely of `gammaRem`, `c3Rem`, `gamma*c3`, and `c3^2` terms.  No final
    forward-error bound or `hySharp` comparison is assumed.  The exact second
    object uses the cumulative-stage envelope `X` from (14.29); replacing it
    by the printed `|Uhat^{-1}|` via `X = Uhat^{-1} + O(u)` is a separate
    identification, not smuggled into this intermediate theorem. -/
theorem ch14ext_gjeConcrete_overall_forward_error_stage_envelope
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat : Fin n → Fin n → ℝ)
    (b x z x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hyStart : xseq start = fl_forwardSub fp n L_hat b)
    (hExact : ∀ i : Fin n, matMulVec n A x i = b i)
    (hUz : ∀ i : Fin n, matMulVec n (V start) z i = xseq start i)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hxrec : ∀ t : ℕ, (ht : t < n - 1) →
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
        2 * (n : ℝ) * fp.u *
          ch14ext_gjeForwardT1 n A_inv L_hat (V start) x_hat i +
        6 * (n : ℝ) * fp.u *
          ch14ext_gjeForwardT2 n
            (ch14ext_absCumProd n (ch14ext_gjeSeqStages n V) start (n - 1))
            (V start) x_hat i +
        ch14ext_gjeForwardHigherOrder n fp A_inv L_hat (V start)
          (ch14ext_absCumProd n (ch14ext_gjeSeqStages n V) start (n - 1))
          z (xseq start) x_hat i := by
  intro i
  let P := ch14ext_absCumProd n (ch14ext_gjeSeqStages n V) start (n - 1)
  have hP : ∀ a j : Fin n, 0 ≤ P a j := by
    intro a j
    exact gje_cumulative_product_abs_nonneg n (ch14ext_gjeSeqStages n V)
      start (start + (n - 1)) a j
  let ΔA₁ : Fin n → Fin n → ℝ := fun a j =>
    matMul n L_hat (V start) a j - A a j
  have hΔA₁ : ∀ a j : Fin n, |ΔA₁ a j| ≤ gamma fp n *
      ∑ k : Fin n, |L_hat a k| * |V start k j| := by
    intro a j
    exact hLU.backward_bound a j
  have hFactor : ∀ a j : Fin n,
      A a j + ΔA₁ a j = matMul n L_hat (V start) a j := by
    intro a j
    unfold ΔA₁
    ring
  obtain ⟨ΔL, hΔL, hForwardRaw⟩ := forwardSub_backward_error fp n L_hat b
    (fun a => by rw [hLU.L_diag a]; norm_num) hLU.L_upper_zero hn
  have hForward : ∀ a : Fin n,
      matMulVec n L_hat (xseq start) a + matMulVec n ΔL (xseq start) a = b a := by
    intro a
    have h := hForwardRaw a
    rw [← hyStart] at h
    simpa [matMulVec, Finset.sum_add_distrib, add_mul] using h
  have hErr : ∀ a : Fin n, |z a - x_hat a| ≤
      gje_c₃ fp n * ch14ext_gjeForwardRaw n P (V start) z (xseq start) a := by
    intro a
    have h := ch14ext_gjeConcrete_stage2_forward_error fp n V xseq z start
      hnpos h3 hidx hVfinal hUz hVrec hxrec hpiv a
    rw [← hxfinal a] at h
    simpa [P, ch14ext_gjeForwardRaw, ch14ext_gjeForwardEnvelope] using h
  have hFirst := ch14ext_gje_first_stage_forward_split n A A_inv L_hat (V start)
    ΔA₁ ΔL b x z (xseq start) x_hat (gamma fp n) (gje_c₃ fp n)
    (gamma_nonneg fp hn) hAinv hExact hFactor hForward hUz hΔA₁ hΔL P hErr i
  have hSecond := ch14ext_gje_stage2_forward_split n (V start) P z (xseq start)
    x_hat (gje_c₃ fp n) (gje_c3_nonneg fp n hnpos h3) hP hUz hErr i
  have htri : |x i - x_hat i| ≤ |x i - z i| + |z i - x_hat i| := by
    have heq : x i - x_hat i = (x i - z i) + (z i - x_hat i) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hCombined : |x i - x_hat i| ≤
      2 * gamma fp n * ch14ext_gjeForwardT1 n A_inv L_hat (V start) x_hat i +
      2 * gje_c₃ fp n * ch14ext_gjeForwardT2 n P (V start) x_hat i +
      2 * gamma fp n * gje_c₃ fp n *
        ch14ext_gjeForwardQ1 n A_inv L_hat (V start) P z (xseq start) i +
      2 * gje_c₃ fp n * gje_c₃ fp n *
        ch14ext_gjeForwardQ2 n P (V start) z (xseq start) i := by
    linarith
  have hT1nn := ch14ext_gjeForwardT1_nonneg n A_inv L_hat (V start) x_hat i
  have hT2nn := ch14ext_gjeForwardT2_nonneg n P (V start) x_hat i hP
  have hGammaTerm :
      2 * gamma fp n * ch14ext_gjeForwardT1 n A_inv L_hat (V start) x_hat i =
        2 * (n : ℝ) * fp.u *
            ch14ext_gjeForwardT1 n A_inv L_hat (V start) x_hat i +
          2 * ch14ext_gammaRem fp n *
            ch14ext_gjeForwardT1 n A_inv L_hat (V start) x_hat i := by
    rw [ch14ext_gamma_split fp n hn]
    ring
  have hCcoeff : 2 * gje_c₃ fp n ≤
      6 * (n : ℝ) * fp.u + 2 * gje_c3_quadratic_remainder fp n := by
    have h := ch14ext_gje_forward_second_coeff fp n h3
    nlinarith
  have hCterm := mul_le_mul_of_nonneg_right hCcoeff hT2nn
  unfold ch14ext_gjeForwardHigherOrder
  nlinarith [hCombined, hGammaTerm, hCterm]

/-- **Higham Theorem 14.5, literal equation (14.32).**

    The second printed first-order object is now exactly
    `|Uhat⁻¹||Uhat||xhat|`.  No comparison or asymptotic hypothesis is assumed:
    upper triangularity of the concrete rounded loop gives
    `absCumProd = |signedCumProd|`, and (14.27) then yields

    `absCumProd ≤ |Uhat⁻¹| + c₃ absCumProd |Uhat| |Uhat⁻¹|`.

    The resulting correction carries the explicit coefficient `6*n*u*c₃` and
    is included in `ch14ext_gjeForwardLiteralHigherOrder`, whose nonnegativity
    is proved separately above. -/
theorem ch14ext_gjeConcrete_overall_forward_error_14_32
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_inv : Fin n → Fin n → ℝ)
    (b x z x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hUinv : IsRightInverse n (V start) U_inv)
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hyStart : xseq start = fl_forwardSub fp n L_hat b)
    (hExact : ∀ i : Fin n, matMulVec n A x i = b i)
    (hUz : ∀ i : Fin n, matMulVec n (V start) z i = xseq start i)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hxrec : ∀ t : ℕ, (ht : t < n - 1) →
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
        2 * (n : ℝ) * fp.u *
          ch14ext_gjeForwardT1 n A_inv L_hat (V start) x_hat i +
        6 * (n : ℝ) * fp.u *
          ch14ext_gjeForwardT2 n (absMatrix n U_inv) (V start) x_hat i +
        ch14ext_gjeForwardLiteralHigherOrder n fp A_inv L_hat (V start)
          (ch14ext_absCumProd n (ch14ext_gjeSeqStages n V) start (n - 1))
          U_inv z (xseq start) x_hat i := by
  intro i
  let X := ch14ext_absCumProd n (ch14ext_gjeSeqStages n V) start (n - 1)
  let S := gje_cumulative_product n (ch14ext_gjeSeqStages n V)
    start (start + (n - 1))
  have hStage : |x i - x_hat i| ≤
      2 * (n : ℝ) * fp.u *
        ch14ext_gjeForwardT1 n A_inv L_hat (V start) x_hat i +
      6 * (n : ℝ) * fp.u *
        ch14ext_gjeForwardT2 n X (V start) x_hat i +
      ch14ext_gjeForwardHigherOrder n fp A_inv L_hat (V start) X
        z (xseq start) x_hat i := by
    simpa [X] using
      ch14ext_gjeConcrete_overall_forward_error_stage_envelope n fp
        A A_inv L_hat b x z x_hat V xseq start hLU hAinv hn hnpos h3 hidx
        hVfinal hxfinal hyStart hExact hUz hVrec hxrec hpiv i
  have hUpper : ∀ t : ℕ, t ≤ n - 1 →
      ∀ a j : Fin n, j.val < a.val → V (start + t) a j = 0 :=
    ch14ext_gjeSeq_upper_triangular fp n V start hidx hLU.U_lower_zero hVrec hpiv
  have hXeq : ∀ a j : Fin n, X a j = |S a j| := by
    intro a j
    simpa [X, S] using
      ch14ext_gje_absCumProd_eq_abs_signed n V start (n - 1) hidx hUpper a j
  have hAccum := ch14ext_gjeConcrete_matrixAccumulation fp n V start hnpos h3
    hidx hVrec hpiv
  have hResidual : ∀ a j : Fin n,
      |idMatrix n a j - matMul n S (V start) a j| ≤
        gje_c₃ fp n * matMul n X (absMatrix n (V start)) a j := by
    intro a j
    have h := hAccum a j
    rw [hVfinal] at h
    simpa [S, X, ch14ext_boundObj] using h
  have hCompare : ∀ a j : Fin n,
      X a j ≤ |U_inv a j| +
        gje_c₃ fp n *
          matMul n (matMul n X (absMatrix n (V start)))
            (absMatrix n U_inv) a j :=
    ch14ext_abs_signed_le_abs_rightInverse_add n S X (V start) U_inv
      (gje_c₃ fp n) hXeq hUinv hResidual
  have hT2 := ch14ext_gjeForwardT2_le_printed_add_correction n X (V start)
    U_inv x_hat (gje_c₃ fp n) hCompare i
  have hLeadNonneg : 0 ≤ 6 * (n : ℝ) * fp.u :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  have hScaled := mul_le_mul_of_nonneg_left hT2 hLeadNonneg
  have hFinal : |x i - x_hat i| ≤
      2 * (n : ℝ) * fp.u *
        ch14ext_gjeForwardT1 n A_inv L_hat (V start) x_hat i +
      6 * (n : ℝ) * fp.u *
        ch14ext_gjeForwardT2 n (absMatrix n U_inv) (V start) x_hat i +
      (ch14ext_gjeForwardHigherOrder n fp A_inv L_hat (V start) X
          z (xseq start) x_hat i +
        6 * (n : ℝ) * fp.u * gje_c₃ fp n *
          ch14ext_gjeForwardUinvCorrection n X (V start) U_inv x_hat i) := by
    calc
      |x i - x_hat i| ≤
          2 * (n : ℝ) * fp.u *
              ch14ext_gjeForwardT1 n A_inv L_hat (V start) x_hat i +
            6 * (n : ℝ) * fp.u *
              ch14ext_gjeForwardT2 n X (V start) x_hat i +
            ch14ext_gjeForwardHigherOrder n fp A_inv L_hat (V start) X
              z (xseq start) x_hat i := hStage
      _ ≤ 2 * (n : ℝ) * fp.u *
              ch14ext_gjeForwardT1 n A_inv L_hat (V start) x_hat i +
            6 * (n : ℝ) * fp.u *
              (ch14ext_gjeForwardT2 n (absMatrix n U_inv) (V start) x_hat i +
                gje_c₃ fp n *
                  ch14ext_gjeForwardUinvCorrection n X (V start) U_inv x_hat i) +
            ch14ext_gjeForwardHigherOrder n fp A_inv L_hat (V start) X
              z (xseq start) x_hat i := by
          nlinarith [hScaled]
      _ = _ := by ring
  simpa [X, ch14ext_gjeForwardLiteralHigherOrder] using hFinal

end Ch14Ext
end NumStability
