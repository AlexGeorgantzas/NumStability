/-
# Higham, 2nd ed., Chapter 14.4, Corollary 14.6: exact finite GJE endpoint

This companion wires the concrete Theorem 14.5 recurrences into the SPD
specialization.  In particular, neither the residual nor the forward-error
endpoint is accepted as a hypothesis.  Fixed-model higher-order terms remain
explicit; no fixed floating-point datum is mislabeled as an asymptotic family.
-/

import NumStability.Algorithms.Ch14GaussJordanQConstruction
import NumStability.Algorithms.Ch14GaussJordanSPDCorollary

namespace NumStability.Ch14Ext

open scoped BigOperators
open NumStability

set_option maxHeartbeats 1000000

/-- Positive diagonal scaling identifies the source first-stage absolute
product with the absolute Cholesky product exactly. -/
theorem ch14ext_cor146_absLU_eq_absRT_absR
    (n : ℕ) (L_hat U_hat : Fin n → Fin n → ℝ)
    (hpiv : ∀ i : Fin n, 0 < U_hat i i)
    (hsym : ∀ i j : Fin n, U_hat i j = U_hat i i * L_hat j i) :
    matMul n (absMatrix n L_hat) (absMatrix n U_hat) =
      matMul n
        (fun i j => |ch14ext_cor146_scaledUpper n U_hat j i|)
        (fun i j => |ch14ext_cor146_scaledUpper n U_hat i j|) := by
  rcases ch14ext_cor146_positivePivot_scaledUpper_relations
      n L_hat U_hat hpiv hsym with ⟨hU, hR⟩
  funext i j
  simp only [matMul, absMatrix]
  apply Finset.sum_congr rfl
  intro k _
  have hdpos : 0 < ch14ext_cor146_pivotScale n U_hat k :=
    Real.sqrt_pos.2 (hpiv k)
  have hdne : ch14ext_cor146_pivotScale n U_hat k ≠ 0 := ne_of_gt hdpos
  have hL : L_hat i k =
      ch14ext_cor146_scaledUpper n U_hat k i /
        ch14ext_cor146_pivotScale n U_hat k := by
    apply (eq_div_iff hdne).2
    rw [mul_comm]
    exact hR k i |>.symm
  rw [hL, hU k j, abs_div, abs_mul, abs_of_pos hdpos]
  field_simp

/-- The componentwise LU backward certificate gives an operator-2 certificate
for the actual factorization perturbation. -/
theorem ch14ext_cor146_luDelta_opNorm2Le
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (c : ℝ)
    (hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n U_hat)) c) :
    opNorm2Le
      (fun i j => matMul n L_hat U_hat i j - A i j)
      (gamma fp n * c) := by
  apply opNorm2Le_of_abs_le n _
    (fun i j => gamma fp n *
      matMul n (absMatrix n L_hat) (absMatrix n U_hat) i j)
  · intro i j
    simpa [matMul, absMatrix] using hLU.backward_bound i j
  · exact opNorm2Le_smul n _ _ (gamma fp n) (gamma_nonneg fp hn) hAbsLU

/-- The LU absolute-product budget used by Corollary 14.6 is derived rather
than assumed.  This is Higham's exact finite counterpart of
`(1 - n*gamma_n)⁻¹ = 1 + O(u)`:

`|| |L_hat||U_hat| ||_2 <= n (1-n*gamma_n)⁻¹ ||A||_2`.
-/
theorem ch14ext_cor146_absLU_budget
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hpiv : ∀ i : Fin n, 0 < U_hat i i)
    (hsym : ∀ i j : Fin n, U_hat i j = U_hat i i * L_hat j i)
    (hn : gammaValid fp n)
    (hsmall : (n : ℝ) * gamma fp n < 1) :
    opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
      ((n : ℝ) * (1 - (n : ℝ) * gamma fp n)⁻¹ * opNorm2 A) := by
  let R := ch14ext_cor146_scaledUpper n U_hat
  let M := matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  let delta := fun i j => matMul n L_hat U_hat i j - A i j
  have hM_eq : M = matMul n (fun i j => |R j i|) (fun i j => |R i j|) := by
    simpa [M, R] using ch14ext_cor146_absLU_eq_absRT_absR
      n L_hat U_hat hpiv hsym
  have hMbase : opNorm2Le M ((n : ℝ) * opNorm2 R ^ 2) := by
    rw [hM_eq]
    exact higham10_7_absRT_absR_opNorm2Le n R (opNorm2 R)
      (opNorm2_nonneg R) (opNorm2Le_opNorm2 R)
  have hDelta : opNorm2Le delta
      (gamma fp n * ((n : ℝ) * opNorm2 R ^ 2)) := by
    simpa [delta, M] using ch14ext_cor146_luDelta_opNorm2Le
      n fp A L_hat U_hat hLU hn ((n : ℝ) * opNorm2 R ^ 2) hMbase
  have hprod : matMul n L_hat U_hat = matMul n (fun i j => R j i) R := by
    rcases ch14ext_cor146_positivePivot_scaledUpper_relations
        n L_hat U_hat hpiv hsym with ⟨hU, hR⟩
    exact ch14ext_cor146_diagScaled_lu_product_eq_cholesky
      n L_hat U_hat R (ch14ext_cor146_pivotScale n U_hat) hU hR
  have hadd : (fun i j => A i j + delta i j) = matMul n (fun i j => R j i) R := by
    funext i j
    simp only [delta]
    rw [← congrFun (congrFun hprod i) j]
    ring
  have hRnorm : opNorm2 R ^ 2 ≤
      opNorm2 A + gamma fp n * ((n : ℝ) * opNorm2 R ^ 2) := by
    have hdeltaNonneg :
        0 ≤ gamma fp n * ((n : ℝ) * opNorm2 R ^ 2) :=
      mul_nonneg (gamma_nonneg fp hn)
        (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
    have hsum : opNorm2 (fun i j => A i j + delta i j) ≤
        opNorm2 A + gamma fp n * ((n : ℝ) * opNorm2 R ^ 2) := by
      apply opNorm2_le_of_opNorm2Le _
        (add_nonneg (opNorm2_nonneg A) hdeltaNonneg)
      intro x
      rw [matMulVec_add_left]
      calc
        vecNorm2 (fun i => matMulVec n A x i + matMulVec n delta x i) ≤
            vecNorm2 (matMulVec n A x) + vecNorm2 (matMulVec n delta x) :=
          vecNorm2_add_le _ _
        _ ≤ opNorm2 A * vecNorm2 x +
            (gamma fp n * ((n : ℝ) * opNorm2 R ^ 2)) * vecNorm2 x :=
          add_le_add (opNorm2Le_opNorm2 A x) (hDelta x)
        _ = (opNorm2 A + gamma fp n * ((n : ℝ) * opNorm2 R ^ 2)) *
            vecNorm2 x := by ring
    calc
      opNorm2 R ^ 2 = opNorm2 (matMul n (fun i j => R j i) R) :=
        (ch14ext_opNorm2_transpose_mul_self_eq n R).symm
      _ = opNorm2 (fun i j => A i j + delta i j) := congrArg opNorm2 hadd.symm
      _ ≤ _ := hsum
  have hden : 0 < 1 - (n : ℝ) * gamma fp n := by linarith
  have hRbudget : opNorm2 R ^ 2 ≤
      (1 - (n : ℝ) * gamma fp n)⁻¹ * opNorm2 A := by
    have hdiv : opNorm2 R ^ 2 ≤
        opNorm2 A / (1 - (n : ℝ) * gamma fp n) :=
      (le_div_iff₀ hden).2 (by nlinarith [hRnorm])
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  intro x
  calc
    vecNorm2 (matMulVec n M x) ≤
        ((n : ℝ) * opNorm2 R ^ 2) * vecNorm2 x := hMbase x
    _ ≤ ((n : ℝ) *
          ((1 - (n : ℝ) * gamma fp n)⁻¹ * opNorm2 A)) * vecNorm2 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRbudget (Nat.cast_nonneg n))
        (vecNorm2_nonneg x)
    _ = ((n : ℝ) * (1 - (n : ℝ) * gamma fp n)⁻¹ * opNorm2 A) *
          vecNorm2 x := by ring

/-- Exact nonnegative matrix driving the concrete (14.31) first-order term. -/
noncomputable def ch14ext_cor146ConcreteResidualEnvelope
    (n : ℕ) (L_hat : Fin n → Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (start : ℕ) :
    Fin n → Fin n → ℝ :=
  let X := ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
    (ch14ext_gjeConstructedQ n V start) start (n - 1)
  matMul n (absMatrix n L_hat)
    (matMul n (absMatrix n X) (absMatrix n (V start)))

/-- The explicit fixed-model higher-order residual vector from concrete
Theorem 14.5. -/
noncomputable def ch14ext_cor146ConcreteResidualRemainder
    (n : ℕ) (fp : FPModel) (L_hat : Fin n → Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ)
    (x_hat : Fin n → ℝ) (start : ℕ) : Fin n → ℝ :=
  let X := ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
    (ch14ext_gjeConstructedQ n V start) start (n - 1)
  fun i => ch14ext_gjeResidualHigherOrder n fp L_hat X (V start)
    (xseq start) x_hat i

/-- Concrete (14.31), reduced to an exact operator-2 leading term with its
higher-order vector retained.  All LU, forward-substitution, and GJE errors
come from the algorithmic certificates; no residual conclusion is assumed. -/
theorem ch14ext_cor146_concrete_residual_norm2
    (n : ℕ) (fp : FPModel)
    (A L_hat : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hyStart : xseq start = fl_forwardSub fp n L_hat b)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hxrec : ∀ t : ℕ, (ht : t < n - 1) →
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpivLoop : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    vecNorm2 (fun i : Fin n => b i - matMulVec n A x_hat i) ≤
      8 * (n : ℝ) * fp.u *
          opNorm2 (ch14ext_cor146ConcreteResidualEnvelope n L_hat V start) *
          vecNorm2 x_hat +
        vecNorm2 (ch14ext_cor146ConcreteResidualRemainder
          n fp L_hat V xseq x_hat start) := by
  let X := ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
    (ch14ext_gjeConstructedQ n V start) start (n - 1)
  let s : Fin n → ℝ := fun i =>
    ch14ext_gjeResidualS2 n L_hat X (V start) x_hat i
  let rho : Fin n → ℝ := ch14ext_cor146ConcreteResidualRemainder
    n fp L_hat V xseq x_hat start
  let M := ch14ext_cor146ConcreteResidualEnvelope n L_hat V start
  let c : ℝ := 8 * (n : ℝ) * fp.u
  have hConcrete := ch14ext_gjeConcrete_overall_residual_14_31
    n fp A L_hat b x_hat V xseq start hLU hn hnpos h3 hidx hVfinal hxfinal
      hyStart hVrec hxrec hpivLoop
  have hEntry : ∀ i : Fin n,
      |b i - matMulVec n A x_hat i| ≤ c * s i + rho i := by
    intro i
    simpa [c, s, rho, X, ch14ext_cor146ConcreteResidualRemainder] using
      hConcrete i
  have hNorm := vecNorm2_le_of_abs_le
    (fun i : Fin n => b i - matMulVec n A x_hat i)
    (fun i => c * s i + rho i) hEntry
  have hMS : matMulVec n M (absVec n x_hat) = s := by
    funext i
    simp only [M, s, X, ch14ext_cor146ConcreteResidualEnvelope,
      ch14ext_gjeResidualS2]
    rw [matMulVec_matMul n (absMatrix n L_hat)
      (matMul n
        (absMatrix n (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
          (ch14ext_gjeConstructedQ n V start) start (n - 1)))
        (absMatrix n (V start))) (absVec n x_hat) i]
    congr 1
    funext k
    exact matMulVec_matMul n
      (absMatrix n (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
        (ch14ext_gjeConstructedQ n V start) start (n - 1)))
      (absMatrix n (V start)) (absVec n x_hat) k
  have hsNorm : vecNorm2 s ≤ opNorm2 M * vecNorm2 x_hat := by
    rw [← hMS]
    calc
      vecNorm2 (matMulVec n M (absVec n x_hat)) ≤
          opNorm2 M * vecNorm2 (absVec n x_hat) := opNorm2Le_opNorm2 M _
      _ = opNorm2 M * vecNorm2 x_hat := by
        rw [show vecNorm2 (absVec n x_hat) = vecNorm2 x_hat by
          simpa [absVec] using vecNorm2_abs x_hat]
  have hc : 0 ≤ c :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  calc
    vecNorm2 (fun i : Fin n => b i - matMulVec n A x_hat i) ≤
        vecNorm2 (fun i => c * s i + rho i) := hNorm
    _ ≤ vecNorm2 (fun i => c * s i) + vecNorm2 rho :=
      vecNorm2_add_le _ _
    _ = c * vecNorm2 s + vecNorm2 rho := by
      rw [vecNorm2_smul, abs_of_nonneg hc]
    _ ≤ c * (opNorm2 M * vecNorm2 x_hat) + vecNorm2 rho :=
      add_le_add (mul_le_mul_of_nonneg_left hsNorm hc) (le_refl _)
    _ = 8 * (n : ℝ) * fp.u *
          opNorm2 (ch14ext_cor146ConcreteResidualEnvelope n L_hat V start) *
          vecNorm2 x_hat +
        vecNorm2 (ch14ext_cor146ConcreteResidualRemainder
          n fp L_hat V xseq x_hat start) := by
      simp only [c, M, rho]
      ring

/-- Relative residual form of `ch14ext_cor146_concrete_residual_norm2`.
The unresolved finite bridge to Higham's printed `8 n^3` coefficient is now
isolated to the norm of `ch14ext_cor146ConcreteResidualEnvelope`; the concrete
residual itself and its higher-order term are fully discharged. -/
theorem ch14ext_cor146_concrete_relative_residual_norm2
    (n : ℕ) (fp : FPModel)
    (A L_hat : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hyStart : xseq start = fl_forwardSub fp n L_hat b)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hxrec : ∀ t : ℕ, (ht : t < n - 1) →
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpivLoop : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0)
    (hApos : 0 < opNorm2 A) (hxhatPos : 0 < vecNorm2 x_hat) :
    vecNorm2 (fun i : Fin n => b i - matMulVec n A x_hat i) /
        (opNorm2 A * vecNorm2 x_hat) ≤
      (8 * (n : ℝ) * fp.u *
          opNorm2 (ch14ext_cor146ConcreteResidualEnvelope n L_hat V start) *
          vecNorm2 x_hat +
        vecNorm2 (ch14ext_cor146ConcreteResidualRemainder
          n fp L_hat V xseq x_hat start)) /
        (opNorm2 A * vecNorm2 x_hat) := by
  exact div_le_div_of_nonneg_right
    (ch14ext_cor146_concrete_residual_norm2 n fp A L_hat b x_hat V xseq start
      hLU hn hnpos h3 hidx hVfinal hxfinal hyStart hVrec hxrec hpivLoop)
    (le_of_lt (mul_pos hApos hxhatPos))

/-- The explicit fixed-model higher-order forward-error vector from the
literal concrete (14.32) theorem. -/
noncomputable def ch14ext_cor146ConcreteForwardRemainder
    (n : ℕ) (fp : FPModel)
    (A_inv L_hat U_inv : Fin n → Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ)
    (z x_hat : Fin n → ℝ) (start : ℕ) : Fin n → ℝ :=
  let P := ch14ext_absCumProd n (ch14ext_gjeSeqStages n V) start (n - 1)
  fun i => ch14ext_gjeForwardLiteralHigherOrder n fp A_inv L_hat (V start)
    P U_inv z (xseq start) x_hat i

/-- **Concrete source-facing Corollary 14.6 forward endpoint.**

The concrete (14.32) recurrence supplies both first-order terms.  Positive
pivots and symmetry give the exact Cholesky condition factor, while
`ch14ext_cor146_absLU_budget` supplies the first-stage
`(1-n*gamma_n)⁻¹` factor.  The remaining fixed-model terms are the explicit
nonnegative vector `ch14ext_cor146ConcreteForwardRemainder`; neither a final
forward bound nor an `O(u^2)` assertion is assumed. -/
theorem ch14ext_cor146_concrete_forward_norm2
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_inv R_inv : Fin n → Fin n → ℝ)
    (b x z x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hpiv : ∀ i : Fin n, 0 < V start i i)
    (hsym : ∀ i j : Fin n, V start i j = V start i i * L_hat j i)
    (hAinv : IsLeftInverse n A A_inv)
    (hUInv : IsInverse n (V start) U_inv)
    (hRInv : IsInverse n (ch14ext_cor146_scaledUpper n (V start)) R_inv)
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hsmall : (n : ℝ) * gamma fp n < 1)
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
    (hpivLoop : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    vecNorm2 (fun i : Fin n => x i - x_hat i) ≤
      2 * (n : ℝ) * fp.u *
        ((n : ℝ) * Real.sqrt n *
            (1 - (n : ℝ) * gamma fp n)⁻¹ * kappa2 A A_inv +
          3 * (n : ℝ) *
            Real.sqrt
              (kappa2
                (fun i j => A i j +
                  ch14ext_cor146_symmetricGEDelta n A L_hat (V start) i j)
                (nonsingInv n (fun i j => A i j +
                  ch14ext_cor146_symmetricGEDelta n A L_hat (V start) i j)))) *
        vecNorm2 x_hat +
      vecNorm2 (ch14ext_cor146ConcreteForwardRemainder
        n fp A_inv L_hat U_inv V xseq z x_hat start) := by
  let U := V start
  let R := ch14ext_cor146_scaledUpper n U
  let factor := (1 - (n : ℝ) * gamma fp n)⁻¹
  let P := ch14ext_absCumProd n (ch14ext_gjeSeqStages n V) start (n - 1)
  let t1 : Fin n → ℝ := fun i =>
    ch14ext_gjeForwardT1 n A_inv L_hat U x_hat i
  let t2 : Fin n → ℝ := fun i =>
    ch14ext_gjeForwardT2 n (absMatrix n U_inv) U x_hat i
  let lead : Fin n → ℝ := fun i =>
    2 * (n : ℝ) * fp.u * (t1 i + 3 * t2 i)
  let rho : Fin n → ℝ := ch14ext_cor146ConcreteForwardRemainder
    n fp A_inv L_hat U_inv V xseq z x_hat start
  have hden : 0 < 1 - (n : ℝ) * gamma fp n := by linarith
  have hfactor : 0 ≤ factor := le_of_lt (inv_pos.mpr hden)
  have hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n U))
      ((n : ℝ) * factor * opNorm2 A) := by
    simpa [U, factor] using ch14ext_cor146_absLU_budget
      n fp A L_hat (V start) hLU hpiv hsym hn hsmall
  have hCond : opNorm2Le
      (matMul n (absMatrix n U_inv) (absMatrix n U))
      ((n : ℝ) * kappa2 R R_inv) := by
    simpa [U, R] using ch14ext_cor146_positivePivot_condU_opNorm2Le
      n L_hat (V start) U_inv R_inv hpiv hsym hRInv hUInv
  have ht1form : ∀ i : Fin n,
      matMulVec n
          (matMul n (absMatrix n A_inv)
            (matMul n (absMatrix n L_hat) (absMatrix n U)))
          (absVec n x_hat) i = t1 i := by
    intro i
    rw [matMulVec_matMul n (absMatrix n A_inv)
      (matMul n (absMatrix n L_hat) (absMatrix n U)) (absVec n x_hat) i]
    congr 1
    funext k
    exact matMulVec_matMul n (absMatrix n L_hat) (absMatrix n U)
      (absVec n x_hat) k
  have ht2form : ∀ i : Fin n,
      matMulVec n (matMul n (absMatrix n U_inv) (absMatrix n U))
        (absVec n x_hat) i = t2 i := by
    intro i
    simpa [t2, ch14ext_gjeForwardT2] using
      matMulVec_matMul n (absMatrix n U_inv) (absMatrix n U)
        (absVec n x_hat) i
  have hlead : ∀ i : Fin n, 0 ≤ lead i := by
    intro i
    have h1 := ch14ext_gjeForwardT1_nonneg n A_inv L_hat U x_hat i
    have h2 := ch14ext_gjeForwardT2_nonneg n (absMatrix n U_inv) U x_hat i
      (fun a j => abs_nonneg (U_inv a j))
    dsimp [lead]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg)
      (add_nonneg h1 (mul_nonneg (by norm_num) h2))
  have hFake : ∀ i : Fin n,
      |(x_hat i + lead i) - x_hat i| ≤
        2 * (n : ℝ) * fp.u *
          (matMulVec n
              (matMul n (absMatrix n A_inv)
                (matMul n (absMatrix n L_hat) (absMatrix n U)))
              (absVec n x_hat) i +
            3 * matMulVec n
              (matMul n (absMatrix n U_inv) (absMatrix n U))
              (absVec n x_hat) i) := by
    intro i
    rw [show (x_hat i + lead i) - x_hat i = lead i by ring,
      abs_of_nonneg (hlead i), ht1form i, ht2form i]
  have hLeadNorm : vecNorm2 lead ≤
      2 * (n : ℝ) * fp.u *
        ((n : ℝ) * Real.sqrt n * factor * kappa2 A A_inv +
          3 * (n : ℝ) * kappa2 R R_inv) * vecNorm2 x_hat := by
    have h := ch14ext_cor146_forward_twoFactor_of_cond_bound
      n fp A A_inv L_hat U U_inv (fun i => x_hat i + lead i) x_hat
      factor (kappa2 R R_inv) hfactor hAbsLU hCond hFake
    simpa using h
  have hConcrete := ch14ext_gjeConcrete_overall_forward_error_14_32
    n fp A A_inv L_hat U_inv b x z x_hat V xseq start hLU hAinv hUInv.2
      hn hnpos h3 hidx hVfinal hxfinal hyStart hExact hUz hVrec hxrec hpivLoop
  have hEntry : ∀ i : Fin n, |x i - x_hat i| ≤ lead i + rho i := by
    intro i
    calc
      |x i - x_hat i| ≤
          2 * (n : ℝ) * fp.u * t1 i +
          6 * (n : ℝ) * fp.u * t2 i + rho i := by
        simpa [t1, t2, rho, U, P,
          ch14ext_cor146ConcreteForwardRemainder] using hConcrete i
      _ = lead i + rho i := by
        dsimp [lead]
        ring
  have hNorm := vecNorm2_le_of_abs_le
    (fun i : Fin n => x i - x_hat i) (fun i => lead i + rho i) hEntry
  have hstruct := ch14ext_cor146_positivePivot_cholesky_backward_error
    n fp A L_hat U hSPD (by simpa [U] using hLU)
      (by simpa [U] using hpiv) (by simpa [U] using hsym)
  have hGram :
      matMul n (fun i j => R j i) R =
        (fun i j => A i j +
          ch14ext_cor146_symmetricGEDelta n A L_hat U i j) := by
    funext i j
    exact (hstruct.2.1 i j).symm
  have hkappa := ch14ext_cor146_kappa2_eq_sqrt_kappa2_gram n R R_inv
    (by simpa [R, U] using hRInv)
  have hkappa' : kappa2 R R_inv =
      Real.sqrt
        (kappa2
          (fun i j => A i j +
            ch14ext_cor146_symmetricGEDelta n A L_hat U i j)
          (nonsingInv n (fun i j => A i j +
            ch14ext_cor146_symmetricGEDelta n A L_hat U i j))) := by
    simpa only [hGram] using hkappa
  rw [hkappa'] at hLeadNorm
  calc
    vecNorm2 (fun i : Fin n => x i - x_hat i) ≤
        vecNorm2 (fun i => lead i + rho i) := hNorm
    _ ≤ vecNorm2 lead + vecNorm2 rho := vecNorm2_add_le _ _
    _ ≤ 2 * (n : ℝ) * fp.u *
          ((n : ℝ) * Real.sqrt n * factor * kappa2 A A_inv +
            3 * (n : ℝ) *
              Real.sqrt
                (kappa2
                  (fun i j => A i j +
                    ch14ext_cor146_symmetricGEDelta n A L_hat U i j)
                  (nonsingInv n (fun i j => A i j +
                    ch14ext_cor146_symmetricGEDelta n A L_hat U i j)))) *
          vecNorm2 x_hat + vecNorm2 rho :=
      add_le_add hLeadNorm (le_refl _)
    _ = _ := by
      simp only [U, factor, rho]

/-- Relative-2-norm form of the concrete Corollary 14.6 forward endpoint.
The factor `||x_hat||_2 / ||x||_2` and the normalized explicit remainder are
kept visible instead of being absorbed into an unproved fixed-model `O(u^2)`.
-/
theorem ch14ext_cor146_concrete_forward_relative_norm2
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_inv R_inv : Fin n → Fin n → ℝ)
    (b x z x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hpiv : ∀ i : Fin n, 0 < V start i i)
    (hsym : ∀ i j : Fin n, V start i j = V start i i * L_hat j i)
    (hAinv : IsLeftInverse n A A_inv)
    (hUInv : IsInverse n (V start) U_inv)
    (hRInv : IsInverse n (ch14ext_cor146_scaledUpper n (V start)) R_inv)
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hsmall : (n : ℝ) * gamma fp n < 1)
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
    (hpivLoop : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0)
    (hxpos : 0 < vecNorm2 x) :
    vecNorm2 (fun i : Fin n => x i - x_hat i) / vecNorm2 x ≤
      2 * (n : ℝ) * fp.u *
        ((n : ℝ) * Real.sqrt n *
            (1 - (n : ℝ) * gamma fp n)⁻¹ * kappa2 A A_inv +
          3 * (n : ℝ) *
            Real.sqrt
              (kappa2
                (fun i j => A i j +
                  ch14ext_cor146_symmetricGEDelta n A L_hat (V start) i j)
                (nonsingInv n (fun i j => A i j +
                  ch14ext_cor146_symmetricGEDelta n A L_hat (V start) i j)))) *
        (vecNorm2 x_hat / vecNorm2 x) +
      vecNorm2 (ch14ext_cor146ConcreteForwardRemainder
        n fp A_inv L_hat U_inv V xseq z x_hat start) / vecNorm2 x := by
  have habs := ch14ext_cor146_concrete_forward_norm2
    n fp A A_inv L_hat U_inv R_inv b x z x_hat V xseq start hSPD hLU hpiv hsym
      hAinv hUInv hRInv hn hnpos h3 hsmall hidx hVfinal hxfinal hyStart hExact
      hUz hVrec hxrec hpivLoop
  calc
    vecNorm2 (fun i : Fin n => x i - x_hat i) / vecNorm2 x ≤
        (2 * (n : ℝ) * fp.u *
            ((n : ℝ) * Real.sqrt n *
                (1 - (n : ℝ) * gamma fp n)⁻¹ * kappa2 A A_inv +
              3 * (n : ℝ) *
                Real.sqrt
                  (kappa2
                    (fun i j => A i j +
                      ch14ext_cor146_symmetricGEDelta n A L_hat (V start) i j)
                    (nonsingInv n (fun i j => A i j +
                      ch14ext_cor146_symmetricGEDelta n A L_hat (V start) i j)))) *
            vecNorm2 x_hat +
          vecNorm2 (ch14ext_cor146ConcreteForwardRemainder
            n fp A_inv L_hat U_inv V xseq z x_hat start)) / vecNorm2 x :=
      div_le_div_of_nonneg_right habs (le_of_lt hxpos)
    _ = _ := by
      rw [add_div, mul_div_assoc]

/-!
## Exact scope

The two primary results above are the explicit-remainder theorems
`ch14ext_cor146_concrete_relative_residual_norm2` and
`ch14ext_cor146_concrete_forward_relative_norm2`.  They are exact statements
for one `FPModel`.

They do not by themselves close the source's terminal `O(u^2)` clauses.  Such
a closure requires a genuine family indexed by a roundoff parameter tending
to zero, with uniform control of the algorithm data.  In particular, the
family proof must establish the second-order size of the explicit remainder
vectors and the first-order replacements of `(1-n*gamma_n)⁻¹`,
`sqrt(kappa2(A+DeltaA))`, and `||x_hat||_2/||x||_2`.  The residual constant also
requires a family-level comparison between
`ch14ext_cor146ConcreteResidualEnvelope` and Higham's
`|L_hat||U_hat||U_hat⁻¹||U_hat|` object.  No fixed-`u` existential constant is
used here as asymptotic evidence.
-/

end NumStability.Ch14Ext
