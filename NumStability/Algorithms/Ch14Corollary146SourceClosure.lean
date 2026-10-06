-- Algorithms/Ch14Corollary146SourceClosure.lean
--
-- Source-active closure of Higham Corollary 14.6. The GJE stage is the
-- recursively executed masked Algorithm 14.4 trace beginning at stage 1.

import NumStability.Algorithms.Ch14Corollary146Closure
import NumStability.Algorithms.Ch14GJETheorem145SourceClosure

namespace NumStability.Ch14Ext

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

set_option maxHeartbeats 1000000

/-! ## Source-active fixed-run endpoints -/

/-- The source-active cumulative envelope satisfies the fixed-model
Corollary 14.6 comparison with `|U_hat| |U_hat^-1|`. -/
theorem ch14ext_cor146Source_envelope_le_printed_add_correction {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n)
    (U_inv : Fin n -> Fin n -> Real)
    (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hfinal : ch14ext_gjeSourceTraceMatrix fp 1 s n = idMatrix n)
    (hpiv : forall q : Nat, (hq : q < n - 1) ->
      ch14ext_gjeSourceTraceMatrix fp 1 s (1 + q)
        ⟨1 + q, by omega⟩ ⟨1 + q, by omega⟩ = 0 -> False)
    (hUinv : IsRightInverse n s.matrix U_inv) :
    forall i j : Fin n,
      ch14ext_gjeSourceXabs fp s i j <=
        matMul n (absMatrix n s.matrix) (absMatrix n U_inv) i j +
          2 * gje_c₃ fp n *
            matMul n
              (matMul n (ch14ext_gjeSourceXabs fp s)
                (absMatrix n s.matrix))
              (absMatrix n U_inv) i j := by
  let Q := ch14ext_gjeSourceQ fp s
  let P := ch14ext_gjeSourcePabs fp s
  let X := ch14ext_gjeSourceXabs fp s
  let U := s.matrix
  let c := gje_c₃ fp n
  have hXdef : X = matMul n (absMatrix n Q) P := by
    rfl
  have hPcompare : forall i j : Fin n,
      P i j <= |U_inv i j| +
        c * matMul n (matMul n P (absMatrix n U))
          (absMatrix n U_inv) i j := by
    intro i j
    simpa [P, U, c] using
      ch14ext_gjeSource_Pabs_le_abs_Uinv_add fp s U_inv hnpos h3 hUpper
        hfinal hpiv hUinv i j
  have hQcompare : forall i j : Fin n,
      |Q i j| <= |U i j| + c * matMul n X (absMatrix n U) i j := by
    intro i j
    have hsub := ch14ext_gjeSource_constructedQ_sub_U_bound fp s hnpos h3
      hUpper hfinal hpiv i j
    calc
      |Q i j| = |(Q i j - U i j) + U i j| := by congr 1 <;> ring
      _ <= |Q i j - U i j| + |U i j| := abs_add_le _ _
      _ <= c * matMul n X (absMatrix n U) i j + |U i j| := by
        exact add_le_add (by simpa [Q, X, U, c] using hsub) (le_refl _)
      _ = |U i j| + c * matMul n X (absMatrix n U) i j := by ring
  simpa [X, U, c] using
    ch14ext_cor146_envelope_le_printed_add_correction
      n Q P X U U_inv c hXdef hPcompare hQcompare

/-- Source-active (14.31) with Higham's SPD printed envelope and an explicit
fixed-run remainder. -/
theorem ch14ext_cor146Source_residual_printed_with_explicit_remainder {n : Nat}
    (fp : FPModel) (A L_hat U_inv : Fin n -> Fin n -> Real)
    (b x_hat : Fin n -> Real) (s : Ch14GJEState n)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hUinv : IsRightInverse n s.matrix U_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hfinal : ch14ext_gjeSourceTraceMatrix fp 1 s n = idMatrix n)
    (hxfinal : forall i : Fin n,
      x_hat i = ch14ext_gjeSourceTraceRhs fp 1 s n i)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hpiv : forall q : Nat, (hq : q < n - 1) ->
      ch14ext_gjeSourceTraceMatrix fp 1 s (1 + q)
        ⟨1 + q, by omega⟩ ⟨1 + q, by omega⟩ = 0 -> False) :
    forall i : Fin n,
      |b i - matMulVec n A x_hat i| <=
        8 * (n : Real) * fp.u *
          ch14ext_cor146PrintedResidualObject
            n L_hat s.matrix U_inv x_hat i +
        ch14ext_cor146ResidualClosureRemainder n fp L_hat
          (ch14ext_gjeSourceXabs fp s) s.matrix U_inv s.rhs x_hat i := by
  intro i
  let X := ch14ext_gjeSourceXabs fp s
  have hX : forall a j : Fin n, 0 <= X a j := by
    intro a j
    exact ch14ext_gjeXabs_nonneg n (ch14ext_gjeSourceStages fp s)
      (ch14ext_gjeSourceQ fp s) 1 (n - 1) a j
  have hEnvelope := ch14ext_cor146Source_envelope_le_printed_add_correction
    fp s U_inv hnpos h3 hLU.U_lower_zero hfinal hpiv hUinv
  have hS2 := ch14ext_cor146_gjeResidualS2_le_printed_add_correction
    n L_hat X s.matrix U_inv x_hat (gje_c₃ fp n) hX
      (by simpa [X] using hEnvelope) i
  have hBase := ch14ext_gjeSourceTrace_overall_residual_14_31
    fp A L_hat b x_hat s hLU hn hnpos h3 hfinal hxfinal hyStart hpiv i
  have hlead : 0 <= 8 * (n : Real) * fp.u :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  calc
    |b i - matMulVec n A x_hat i| <=
        8 * (n : Real) * fp.u *
            ch14ext_gjeResidualS2 n L_hat X s.matrix x_hat i +
          ch14ext_gjeResidualHigherOrder n fp L_hat X
            s.matrix s.rhs x_hat i := by
      simpa [X] using hBase
    _ <= 8 * (n : Real) * fp.u *
          (ch14ext_cor146PrintedResidualObject
              n L_hat s.matrix U_inv x_hat i +
            2 * gje_c₃ fp n *
              ch14ext_cor146ResidualBridgeCorrection
                n L_hat X s.matrix U_inv x_hat i) +
          ch14ext_gjeResidualHigherOrder n fp L_hat X
            s.matrix s.rhs x_hat i := by
      exact add_le_add (mul_le_mul_of_nonneg_left hS2 hlead) (le_refl _)
    _ = 8 * (n : Real) * fp.u *
          ch14ext_cor146PrintedResidualObject
            n L_hat s.matrix U_inv x_hat i +
        ch14ext_cor146ResidualClosureRemainder n fp L_hat X
          s.matrix U_inv s.rhs x_hat i := by
      unfold ch14ext_cor146ResidualClosureRemainder
      ring
    _ = _ := by rfl

/-- Source-active normwise residual endpoint before replacing the perturbed
condition number by the source condition number. -/
theorem ch14ext_cor146Source_residual_norm2_with_explicit_remainder {n : Nat}
    (fp : FPModel)
    (A L_hat U_inv R_inv : Fin n -> Fin n -> Real)
    (b x_hat : Fin n -> Real) (s : Ch14GJEState n)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hpivPos : forall i : Fin n, 0 < s.matrix i i)
    (hsym : forall i j : Fin n,
      s.matrix i j = s.matrix i i * L_hat j i)
    (hUInv : IsInverse n s.matrix U_inv)
    (hRInv : IsInverse n (ch14ext_cor146_scaledUpper n s.matrix) R_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hsmall : (n : Real) * gamma fp n < 1)
    (hfinal : ch14ext_gjeSourceTraceMatrix fp 1 s n = idMatrix n)
    (hxfinal : forall i : Fin n,
      x_hat i = ch14ext_gjeSourceTraceRhs fp 1 s n i)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hpiv : forall q : Nat, (hq : q < n - 1) ->
      ch14ext_gjeSourceTraceMatrix fp 1 s (1 + q)
        ⟨1 + q, by omega⟩ ⟨1 + q, by omega⟩ = 0 -> False) :
    vecNorm2 (fun i : Fin n => b i - matMulVec n A x_hat i) <=
      8 * (n : Real) ^ 3 * fp.u *
          (1 - (n : Real) * gamma fp n)⁻¹ *
          Real.sqrt
            (kappa2
              (fun i j => A i j +
                ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)
              (nonsingInv n (fun i j => A i j +
                ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j))) *
          opNorm2 A * vecNorm2 x_hat +
        vecNorm2 (fun i =>
          ch14ext_cor146ResidualClosureRemainder n fp L_hat
            (ch14ext_gjeSourceXabs fp s) s.matrix U_inv s.rhs x_hat i) := by
  let X := ch14ext_gjeSourceXabs fp s
  let factor := (1 - (n : Real) * gamma fp n)⁻¹
  let lead : Fin n -> Real := fun i =>
    8 * (n : Real) * fp.u *
      ch14ext_cor146PrintedResidualObject n L_hat s.matrix U_inv x_hat i
  let rho : Fin n -> Real := fun i =>
    ch14ext_cor146ResidualClosureRemainder
      n fp L_hat X s.matrix U_inv s.rhs x_hat i
  have hden : 0 < 1 - (n : Real) * gamma fp n := by linarith
  have hfactor : 0 <= factor := le_of_lt (inv_pos.mpr hden)
  have hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n s.matrix))
      ((n : Real) * factor * opNorm2 A) := by
    simpa [factor] using ch14ext_cor146_absLU_budget
      n fp A L_hat s.matrix hLU hpivPos hsym hn hsmall
  have hlead : forall i : Fin n, 0 <= lead i := by
    intro i
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg)
      (ch14ext_cor146PrintedResidualObject_nonneg
        n L_hat s.matrix U_inv x_hat i)
  let bLead : Fin n -> Real := fun i => matMulVec n A x_hat i + lead i
  have hLeadResidual : forall i : Fin n,
      |bLead i - matMulVec n A x_hat i| <=
        8 * (n : Real) * fp.u *
          ch14ext_cor146PrintedResidualObject
            n L_hat s.matrix U_inv x_hat i := by
    intro i
    change |matMulVec n A x_hat i + lead i - matMulVec n A x_hat i| <= _
    rw [show matMulVec n A x_hat i + lead i - matMulVec n A x_hat i =
      lead i by ring, abs_of_nonneg (hlead i)]
  have hLeadNormRaw :=
    ch14ext_cor146_residual_positivePivot_exactGram_of_theorem14_5
      n fp A L_hat s.matrix U_inv R_inv bLead x_hat factor
      hSPD hLU hpivPos hsym hUInv hRInv hfactor hAbsLU hLeadResidual
  have hLeadVector :
      (fun i : Fin n => bLead i - ∑ j : Fin n, A i j * x_hat j) = lead := by
    funext i
    change matMulVec n A x_hat i + lead i - matMulVec n A x_hat i = lead i
    ring
  have hLeadNorm : vecNorm2 lead <=
      8 * (n : Real) ^ 3 * fp.u * factor *
          Real.sqrt
            (kappa2
              (fun i j => A i j +
                ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)
              (nonsingInv n (fun i j => A i j +
                ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j))) *
          opNorm2 A * vecNorm2 x_hat := by
    rw [hLeadVector] at hLeadNormRaw
    exact hLeadNormRaw
  have hEntry : forall i : Fin n,
      |b i - matMulVec n A x_hat i| <= lead i + rho i := by
    intro i
    simpa [lead, rho, X] using
      ch14ext_cor146Source_residual_printed_with_explicit_remainder
        fp A L_hat U_inv b x_hat s hLU hUInv.2 hn hnpos h3 hfinal
          hxfinal hyStart hpiv i
  have hNorm := vecNorm2_le_of_abs_le
    (fun i : Fin n => b i - matMulVec n A x_hat i)
    (fun i => lead i + rho i) hEntry
  calc
    vecNorm2 (fun i : Fin n => b i - matMulVec n A x_hat i) <=
        vecNorm2 (fun i => lead i + rho i) := hNorm
    _ <= vecNorm2 lead + vecNorm2 rho := vecNorm2_add_le lead rho
    _ <= (8 * (n : Real) ^ 3 * fp.u * factor *
          Real.sqrt
            (kappa2
              (fun i j => A i j +
                ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)
              (nonsingInv n (fun i j => A i j +
                ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j))) *
          opNorm2 A * vecNorm2 x_hat) + vecNorm2 rho :=
      add_le_add hLeadNorm (le_refl _)
    _ = _ := by rfl

/-- The explicit higher-order vector in the source-active forward endpoint. -/
noncomputable def ch14ext_cor146SourceForwardRemainder {n : Nat}
    (fp : FPModel) (A_inv L_hat U_inv : Fin n -> Fin n -> Real)
    (s : Ch14GJEState n) (z x_hat : Fin n -> Real) : Fin n -> Real :=
  fun i => ch14ext_gjeForwardLiteralHigherOrder n fp A_inv L_hat s.matrix
    (ch14ext_gjeSourcePabs fp s) U_inv z s.rhs x_hat i

/-- Source-active normwise forward endpoint before replacing the perturbed
condition number by the source condition number. -/
theorem ch14ext_cor146Source_forward_norm2 {n : Nat}
    (fp : FPModel)
    (A A_inv L_hat U_inv R_inv : Fin n -> Fin n -> Real)
    (b x z x_hat : Fin n -> Real) (s : Ch14GJEState n)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hpivPos : forall i : Fin n, 0 < s.matrix i i)
    (hsym : forall i j : Fin n,
      s.matrix i j = s.matrix i i * L_hat j i)
    (hAinv : IsLeftInverse n A A_inv)
    (hUInv : IsInverse n s.matrix U_inv)
    (hRInv : IsInverse n (ch14ext_cor146_scaledUpper n s.matrix) R_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hsmall : (n : Real) * gamma fp n < 1)
    (hfinal : ch14ext_gjeSourceTraceMatrix fp 1 s n = idMatrix n)
    (hxfinal : forall i : Fin n,
      x_hat i = ch14ext_gjeSourceTraceRhs fp 1 s n i)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hExact : forall i : Fin n, matMulVec n A x i = b i)
    (hUz : forall i : Fin n, matMulVec n s.matrix z i = s.rhs i)
    (hpiv : forall q : Nat, (hq : q < n - 1) ->
      ch14ext_gjeSourceTraceMatrix fp 1 s (1 + q)
        ⟨1 + q, by omega⟩ ⟨1 + q, by omega⟩ = 0 -> False) :
    vecNorm2 (fun i : Fin n => x i - x_hat i) <=
      2 * (n : Real) * fp.u *
        ((n : Real) * Real.sqrt n *
            (1 - (n : Real) * gamma fp n)⁻¹ * kappa2 A A_inv +
          3 * (n : Real) *
            Real.sqrt
              (kappa2
                (fun i j => A i j +
                  ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)
                (nonsingInv n (fun i j => A i j +
                  ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)))) *
        vecNorm2 x_hat +
      vecNorm2
        (ch14ext_cor146SourceForwardRemainder fp A_inv L_hat U_inv s z x_hat) := by
  let U := s.matrix
  let R := ch14ext_cor146_scaledUpper n U
  let factor := (1 - (n : Real) * gamma fp n)⁻¹
  let P := ch14ext_gjeSourcePabs fp s
  let t1 : Fin n -> Real := fun i =>
    ch14ext_gjeForwardT1 n A_inv L_hat U x_hat i
  let t2 : Fin n -> Real := fun i =>
    ch14ext_gjeForwardT2 n (absMatrix n U_inv) U x_hat i
  let lead : Fin n -> Real := fun i =>
    2 * (n : Real) * fp.u * (t1 i + 3 * t2 i)
  let rho : Fin n -> Real :=
    ch14ext_cor146SourceForwardRemainder fp A_inv L_hat U_inv s z x_hat
  have hden : 0 < 1 - (n : Real) * gamma fp n := by linarith
  have hfactor : 0 <= factor := le_of_lt (inv_pos.mpr hden)
  have hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n U))
      ((n : Real) * factor * opNorm2 A) := by
    simpa [U, factor] using ch14ext_cor146_absLU_budget
      n fp A L_hat s.matrix hLU hpivPos hsym hn hsmall
  have hCond : opNorm2Le
      (matMul n (absMatrix n U_inv) (absMatrix n U))
      ((n : Real) * kappa2 R R_inv) := by
    simpa [U, R] using ch14ext_cor146_positivePivot_condU_opNorm2Le
      n L_hat s.matrix U_inv R_inv hpivPos hsym hRInv hUInv
  have ht1form : forall i : Fin n,
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
  have ht2form : forall i : Fin n,
      matMulVec n (matMul n (absMatrix n U_inv) (absMatrix n U))
        (absVec n x_hat) i = t2 i := by
    intro i
    simpa [t2, ch14ext_gjeForwardT2] using
      matMulVec_matMul n (absMatrix n U_inv) (absMatrix n U)
        (absVec n x_hat) i
  have hlead : forall i : Fin n, 0 <= lead i := by
    intro i
    have h1 := ch14ext_gjeForwardT1_nonneg n A_inv L_hat U x_hat i
    have h2 := ch14ext_gjeForwardT2_nonneg n (absMatrix n U_inv) U x_hat i
      (fun a j => abs_nonneg (U_inv a j))
    dsimp [lead]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg)
      (add_nonneg h1 (mul_nonneg (by norm_num) h2))
  have hFake : forall i : Fin n,
      |(x_hat i + lead i) - x_hat i| <=
        2 * (n : Real) * fp.u *
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
  have hLeadNorm : vecNorm2 lead <=
      2 * (n : Real) * fp.u *
        ((n : Real) * Real.sqrt n * factor * kappa2 A A_inv +
          3 * (n : Real) * kappa2 R R_inv) * vecNorm2 x_hat := by
    have h := ch14ext_cor146_forward_twoFactor_of_cond_bound
      n fp A A_inv L_hat U U_inv (fun i => x_hat i + lead i) x_hat
      factor (kappa2 R R_inv) hfactor hAbsLU hCond hFake
    simpa using h
  have hConcrete := ch14ext_gjeSourceTrace_overall_forward_14_32
    fp A A_inv L_hat U_inv b x z x_hat s hLU hAinv hUInv.2 hn hnpos h3
      hfinal hxfinal hyStart hExact hUz hpiv
  have hEntry : forall i : Fin n, |x i - x_hat i| <= lead i + rho i := by
    intro i
    calc
      |x i - x_hat i| <=
          2 * (n : Real) * fp.u * (t1 i + 3 * t2 i) + rho i := by
        simpa [t1, t2, rho, U, P, ch14ext_cor146SourceForwardRemainder]
          using hConcrete i
      _ = lead i + rho i := by
        dsimp [lead]
  have hNorm := vecNorm2_le_of_abs_le
    (fun i : Fin n => x i - x_hat i) (fun i => lead i + rho i) hEntry
  have hstruct := ch14ext_cor146_positivePivot_cholesky_backward_error
    n fp A L_hat U hSPD (by simpa [U] using hLU)
      (by simpa [U] using hpivPos) (by simpa [U] using hsym)
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
    vecNorm2 (fun i : Fin n => x i - x_hat i) <=
        vecNorm2 (fun i => lead i + rho i) := hNorm
    _ <= vecNorm2 lead + vecNorm2 rho := vecNorm2_add_le _ _
    _ <= 2 * (n : Real) * fp.u *
          ((n : Real) * Real.sqrt n * factor * kappa2 A A_inv +
            3 * (n : Real) *
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

/-! ## Successful source-trace families -/

/-- A vanishing-roundoff family for Corollary 14.6 whose second stage is the
actual masked Algorithm 14.4 source trace. -/
structure Ch14Cor146SourceRunFamily
    (I : Type*) (l : Filter I) (n : Nat)
    (A A_inv : Fin n -> Fin n -> Real)
    (b x : Fin n -> Real) where
  gje : Ch14GJETheorem145SourceFamily I l n A b
  U_inv : I -> Fin n -> Fin n -> Real
  R_inv : I -> Fin n -> Fin n -> Real
  z : I -> Fin n -> Real
  spd : IsSymPosDef n A
  exact_solution_nonzero : 0 < vecNorm2 x
  computed_pivots_pos : forall t i, 0 < (gje.state t).matrix i i
  symmetric_factor_relation : forall t i j,
    (gje.state t).matrix i j = (gje.state t).matrix i i * gje.L_hat t j i
  upper_inverse : forall t, IsInverse n (gje.state t).matrix (U_inv t)
  scaled_upper_inverse : forall t,
    IsInverse n (ch14ext_cor146_scaledUpper n (gje.state t).matrix) (R_inv t)
  gamma_small : forall t, (n : Real) * gamma (gje.model t) n < 1
  exact_solution : forall i, matMulVec n A x i = b i
  exact_upper_solve : forall t i,
    matMulVec n (gje.state t).matrix (z t) i = (gje.state t).rhs i
  U_inv_isBigO_one : MatrixFamilyIsBigOOne l U_inv
  z_isBigO_one : VectorFamilyIsBigOOne l z
  uniform_inverse : Ch14Cor146UniformInverseRegularity l n A A_inv
    gje.model gje.L_hat (fun t => (gje.state t).matrix)

noncomputable def ch14ext_cor146SourceRunV
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x)
    (t : I) : Nat -> Fin n -> Fin n -> Real :=
  ch14ext_gjeSourceV (F.gje.model t) (F.gje.state t)

noncomputable def ch14ext_cor146SourceRunXseq
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x)
    (t : I) : Nat -> Fin n -> Real :=
  ch14ext_gjeSourceXseq (F.gje.model t) (F.gje.state t)

@[simp] theorem ch14ext_cor146SourceRunV_one
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x) (t : I) :
    ch14ext_cor146SourceRunV F t 1 = (F.gje.state t).matrix := by
  simp [ch14ext_cor146SourceRunV, ch14ext_gjeSourceV,
    ch14ext_gjeSourceTraceMatrix, ch14ext_gjeSourceTrace]

@[simp] theorem ch14ext_cor146SourceRunXseq_one
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x) (t : I) :
    ch14ext_cor146SourceRunXseq F t 1 = (F.gje.state t).rhs := by
  simp [ch14ext_cor146SourceRunXseq, ch14ext_gjeSourceXseq,
    ch14ext_gjeSourceTraceRhs, ch14ext_gjeSourceTrace]

noncomputable def ch14ext_cor146SourceResidualRemainder
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x) (t : I) : Real :=
  ch14ext_cor146ResidualSourceRemainder n F.gje.model A A_inv F.gje.L_hat
    F.U_inv (ch14ext_cor146SourceRunV F) (ch14ext_cor146SourceRunXseq F)
    F.gje.x_hat 1 t

noncomputable def ch14ext_cor146SourceForwardAbsoluteRemainder
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x) (t : I) : Real :=
  ch14ext_cor146ForwardAbsoluteSourceRemainder n F.gje.model A A_inv
    F.gje.L_hat F.U_inv (ch14ext_cor146SourceRunV F)
    (ch14ext_cor146SourceRunXseq F) F.z F.gje.x_hat 1 t

noncomputable def ch14ext_cor146SourceForwardRelativeRemainder
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x) (t : I) : Real :=
  ch14ext_cor146ForwardRelativeSourceRemainder n F.gje.model A A_inv
    F.gje.L_hat F.U_inv (ch14ext_cor146SourceRunV F)
    (ch14ext_cor146SourceRunXseq F) F.z F.gje.x_hat x 1 t

theorem ch14ext_cor146Source_closureX_isBigO_one
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x) :
    Ch14Cor146ClosureMatrixFamilyIsBigOOne l
      (ch14ext_cor146ClosureX n (ch14ext_cor146SourceRunV F) 1) := by
  simpa [ch14ext_cor146ClosureX, ch14ext_cor146SourceRunV,
    ch14ext_gjeSourceXabs, ch14ext_gjeSourceStages, ch14ext_gjeSourceQ]
    using ch14ext_gjeSourceFamilyXabs_isBigOOne F.gje

theorem ch14ext_cor146Source_closureP_isBigO_one
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x) :
    Ch14Cor146ClosureMatrixFamilyIsBigOOne l
      (ch14ext_cor146ClosureP n (ch14ext_cor146SourceRunV F) 1) := by
  simpa [ch14ext_cor146ClosureP, ch14ext_cor146SourceRunV,
    ch14ext_gjeSourcePabs, ch14ext_gjeSourceStages]
    using ch14ext_gjeSourceFamilyPabs_isBigOOne F.gje

theorem ch14ext_cor146Source_y_isBigO_one
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x) :
    Ch14Cor146ClosureVectorFamilyIsBigOOne l
      (fun t => ch14ext_cor146SourceRunXseq F t 1) := by
  simpa using F.gje.y_isBigO_one

theorem ch14ext_cor146Source_residualRemainder_isBigO_u_sq
    {I : Type*} {l : Filter I} [NeBot l] {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x) :
    (fun t => ch14ext_cor146SourceResidualRemainder F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  have hn : Filter.Eventually (fun t => gammaValid (F.gje.model t) n) l :=
    Filter.Eventually.of_forall F.gje.valid_n
  have hsmall : Filter.Eventually
      (fun t => (n : Real) * gamma (F.gje.model t) n < 1) l :=
    Filter.Eventually.of_forall F.gamma_small
  unfold ch14ext_cor146SourceResidualRemainder
  exact ch14ext_cor146ResidualSourceRemainder_family_isBigO_u_sq
    n F.gje.model A A_inv F.gje.L_hat F.U_inv
      (ch14ext_cor146SourceRunV F) (ch14ext_cor146SourceRunXseq F)
      F.gje.x_hat 1 F.gje.unit_tendsto_zero F.gje.dimension_pos hn hsmall
      F.gje.L_hat_isBigO_one (ch14ext_cor146Source_closureX_isBigO_one F)
      (by simpa using F.gje.U_hat_isBigO_one) F.U_inv_isBigO_one
      (ch14ext_cor146Source_y_isBigO_one F) F.gje.x_hat_isBigO_one
      F.uniform_inverse

theorem ch14ext_cor146Source_forwardRelativeRemainder_isBigO_u_sq
    {I : Type*} {l : Filter I} [NeBot l] {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x) :
    (fun t => ch14ext_cor146SourceForwardRelativeRemainder F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2) := by
  have hn : Filter.Eventually (fun t => gammaValid (F.gje.model t) n) l :=
    Filter.Eventually.of_forall F.gje.valid_n
  have hsmall : Filter.Eventually
      (fun t => (n : Real) * gamma (F.gje.model t) n < 1) l :=
    Filter.Eventually.of_forall F.gamma_small
  unfold ch14ext_cor146SourceForwardRelativeRemainder
  exact ch14ext_cor146ForwardRelativeSourceRemainder_family_isBigO_u_sq
    n F.gje.model A A_inv F.gje.L_hat F.U_inv
      (ch14ext_cor146SourceRunV F) (ch14ext_cor146SourceRunXseq F)
      F.z F.gje.x_hat x 1 F.gje.unit_tendsto_zero F.gje.dimension_pos hn
      hsmall F.gje.L_hat_isBigO_one
      (by simpa using F.gje.U_hat_isBigO_one)
      (ch14ext_cor146Source_closureP_isBigO_one F) F.U_inv_isBigO_one
      F.z_isBigO_one (ch14ext_cor146Source_y_isBigO_one F)
      F.gje.x_hat_isBigO_one F.uniform_inverse

/-! ## Printed Corollary 14.6 constants -/

/-- Source-active Corollary 14.6 residual with the exact printed source
constant and an explicit `O(u^2)`-ready remainder. -/
theorem ch14ext_cor146Source_residual_source_literal
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x) (t : I) :
    vecNorm2 (fun i : Fin n => b i - matMulVec n A (F.gje.x_hat t) i) <=
      8 * (n : Real) ^ 3 * (F.gje.model t).u *
          Real.sqrt (kappa2 A A_inv) * opNorm2 A * vecNorm2 (F.gje.x_hat t) +
        ch14ext_cor146SourceResidualRemainder F t := by
  let factor := (1 - (n : Real) * gamma (F.gje.model t) n)⁻¹
  let khat := ch14ext_cor146ClosureSqrtKappa n A F.gje.L_hat
    (fun s => (F.gje.state s).matrix) t
  let ksrc := Real.sqrt (kappa2 A A_inv)
  let C := 8 * (n : Real) ^ 3 * (F.gje.model t).u *
    opNorm2 A * vecNorm2 (F.gje.x_hat t)
  let rho := vecNorm2 (fun i =>
    ch14ext_cor146ResidualClosureRemainder n (F.gje.model t)
      (F.gje.L_hat t) (ch14ext_gjeSourceXabs (F.gje.model t) (F.gje.state t))
      (F.gje.state t).matrix (F.U_inv t) (F.gje.state t).rhs
      (F.gje.x_hat t) i)
  have hbase := ch14ext_cor146Source_residual_norm2_with_explicit_remainder
    (F.gje.model t) A (F.gje.L_hat t) (F.U_inv t) (F.R_inv t) b
      (F.gje.x_hat t) (F.gje.state t) F.spd (F.gje.lu_certificate t)
      (F.computed_pivots_pos t) (F.symmetric_factor_relation t)
      (F.upper_inverse t) (F.scaled_upper_inverse t) (F.gje.valid_n t)
      F.gje.dimension_pos (F.gje.valid_three t) (F.gamma_small t)
      (F.gje.final_matrix t) (F.gje.final_vector t)
      (F.gje.forward_start t) (F.gje.pivots_nonzero t)
  have hAhat : ch14ext_cor146ClosureAhat n A F.gje.L_hat
      (fun s => (F.gje.state s).matrix) t =
      (fun i j => A i j + ch14ext_cor146_symmetricGEDelta n A
        (F.gje.L_hat t) (F.gje.state t).matrix i j) := rfl
  have hspectral : factor * khat <= ksrc + |factor * khat - ksrc| := by
    linarith [le_abs_self (factor * khat - ksrc)]
  have hC0 : 0 <= C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (F.gje.model t).u_nonneg)
        (opNorm2_nonneg A))
      (vecNorm2_nonneg (F.gje.x_hat t))
  have hbase' :
      vecNorm2 (fun i : Fin n => b i - matMulVec n A (F.gje.x_hat t) i) <=
        C * (factor * khat) + rho := by
    convert hbase using 1 <;>
      simp [C, factor, khat, rho, ch14ext_cor146ClosureSqrtKappa,
        hAhat] <;> ring
  have hVone : (fun s => ch14ext_cor146SourceRunV F s 1) =
      (fun s => (F.gje.state s).matrix) := by
    funext s
    exact ch14ext_cor146SourceRunV_one F s
  have hX : ch14ext_cor146ClosureX n (ch14ext_cor146SourceRunV F) 1 t =
      ch14ext_gjeSourceXabs (F.gje.model t) (F.gje.state t) := by
    rfl
  calc
    vecNorm2 (fun i : Fin n => b i - matMulVec n A (F.gje.x_hat t) i) <=
        C * (factor * khat) + rho := hbase'
    _ <= C * (ksrc + |factor * khat - ksrc|) + rho :=
      add_le_add (mul_le_mul_of_nonneg_left hspectral hC0) (le_refl rho)
    _ = 8 * (n : Real) ^ 3 * (F.gje.model t).u *
          Real.sqrt (kappa2 A A_inv) * opNorm2 A *
            vecNorm2 (F.gje.x_hat t) +
        ch14ext_cor146SourceResidualRemainder F t := by
      simp only [ch14ext_cor146SourceResidualRemainder,
        ch14ext_cor146ResidualSourceRemainder,
        ch14ext_cor146ResidualSpectralCorrection, C, factor, khat, ksrc, rho]
      rw [hVone, hX]
      simp only [ch14ext_cor146SourceRunV_one,
        ch14ext_cor146SourceRunXseq_one]
      ring

/-- Source-active Corollary 14.6 absolute forward error with the exact printed
coefficient. -/
theorem ch14ext_cor146Source_forward_absolute_source_literal
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x) (t : I) :
    vecNorm2 (fun i : Fin n => x i - F.gje.x_hat t i) <=
      8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
          kappa2 A A_inv * vecNorm2 (F.gje.x_hat t) +
        ch14ext_cor146SourceForwardAbsoluteRemainder F t := by
  let factor := (1 - (n : Real) * gamma (F.gje.model t) n)⁻¹
  let khat := ch14ext_cor146ClosureSqrtKappa n A F.gje.L_hat
    (fun s => (F.gje.state s).matrix) t
  let ksrc := Real.sqrt (kappa2 A A_inv)
  let kap := kappa2 A A_inv
  let a := 2 * (n : Real) ^ 2 * Real.sqrt n * kap
  let d := 6 * (n : Real) ^ 2
  let raw := a * factor + d * khat
  let printed := 8 * (n : Real) ^ 2 * Real.sqrt n * kap
  let corr := ch14ext_cor146ForwardCoefficientCorrection n F.gje.model A A_inv
    F.gje.L_hat (fun s => (F.gje.state s).matrix) t
  let rho := vecNorm2 (ch14ext_cor146SourceForwardRemainder
    (F.gje.model t) A_inv (F.gje.L_hat t) (F.U_inv t) (F.gje.state t)
    (F.z t) (F.gje.x_hat t))
  have hbase := ch14ext_cor146Source_forward_norm2
    (F.gje.model t) A A_inv (F.gje.L_hat t) (F.U_inv t) (F.R_inv t)
      b x (F.z t) (F.gje.x_hat t) (F.gje.state t) F.spd
      (F.gje.lu_certificate t) (F.computed_pivots_pos t)
      (F.symmetric_factor_relation t) F.uniform_inverse.source_inverse.1
      (F.upper_inverse t) (F.scaled_upper_inverse t) (F.gje.valid_n t)
      F.gje.dimension_pos (F.gje.valid_three t) (F.gamma_small t)
      (F.gje.final_matrix t) (F.gje.final_vector t)
      (F.gje.forward_start t) F.exact_solution (F.exact_upper_solve t)
      (F.gje.pivots_nonzero t)
  have hAhat : ch14ext_cor146ClosureAhat n A F.gje.L_hat
      (fun s => (F.gje.state s).matrix) t =
      (fun i j => A i j + ch14ext_cor146_symmetricGEDelta n A
        (F.gje.L_hat t) (F.gje.state t).matrix i j) := rfl
  have hkap1 := ch14ext_cor146_one_le_kappa2_of_isInverse
    n A A_inv F.gje.dimension_pos F.uniform_inverse.source_inverse
  have hkap0 : 0 <= kap := by simpa [kap] using le_trans (by norm_num) hkap1
  have hksrc : ksrc <= kap := by
    simpa [ksrc, kap] using
      ch14ext_cor146_sqrt_kappa2_le_kappa2_of_isInverse
        n A A_inv F.gje.dimension_pos F.uniform_inverse.source_inverse
  have hnR : (1 : Real) <= (n : Real) := by
    exact_mod_cast F.gje.dimension_pos
  have hsqrtn : (1 : Real) <= Real.sqrt n := by
    have h := Real.sqrt_le_sqrt hnR
    simpa using h
  have hksrcScaled : ksrc <= Real.sqrt n * kap := by
    calc
      ksrc <= kap := hksrc
      _ = 1 * kap := by ring
      _ <= Real.sqrt n * kap := mul_le_mul_of_nonneg_right hsqrtn hkap0
  have ha0 : 0 <= a := by
    dsimp [a]
    exact mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg n)) hkap0
  have hd0 : 0 <= d := by dsimp [d]; positivity
  have hfactor : factor <= 1 + |factor - 1| := by
    linarith [le_abs_self (factor - 1)]
  have hkhat : khat <= ksrc + |khat - ksrc| := by
    linarith [le_abs_self (khat - ksrc)]
  have hperturbed :
      raw <= a * (1 + |factor - 1|) + d * (ksrc + |khat - ksrc|) := by
    dsimp [raw]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hfactor ha0)
      (mul_le_mul_of_nonneg_left hkhat hd0)
  have hsecond : d * ksrc <= d * (Real.sqrt n * kap) :=
    mul_le_mul_of_nonneg_left hksrcScaled hd0
  have hbaseline : a + d * ksrc <= printed := by
    calc
      a + d * ksrc <= a + d * (Real.sqrt n * kap) :=
        add_le_add (le_refl a) hsecond
      _ = printed := by dsimp [a, d, printed]; ring
  have hcorr : corr = a * |factor - 1| + d * |khat - ksrc| := by
    dsimp [corr, a, d, factor, khat, ksrc, kap]
    rfl
  have hraw : raw <= printed + corr := by
    calc
      raw <= a * (1 + |factor - 1|) +
          d * (ksrc + |khat - ksrc|) := hperturbed
      _ = (a + d * ksrc) +
          (a * |factor - 1| + d * |khat - ksrc|) := by ring
      _ <= printed + (a * |factor - 1| + d * |khat - ksrc|) :=
        add_le_add hbaseline (le_refl _)
      _ = printed + corr := by rw [hcorr]
  have hbase' :
      vecNorm2 (fun i : Fin n => x i - F.gje.x_hat t i) <=
        raw * ((F.gje.model t).u * vecNorm2 (F.gje.x_hat t)) + rho := by
    convert hbase using 1 <;>
      simp [raw, a, d, factor, khat, kap, rho,
        ch14ext_cor146ClosureSqrtKappa, hAhat] <;> ring
  have hmult0 : 0 <= (F.gje.model t).u * vecNorm2 (F.gje.x_hat t) :=
    mul_nonneg (F.gje.model t).u_nonneg (vecNorm2_nonneg (F.gje.x_hat t))
  have hVone : (fun s => ch14ext_cor146SourceRunV F s 1) =
      (fun s => (F.gje.state s).matrix) := by
    funext s
    exact ch14ext_cor146SourceRunV_one F s
  have hrho : ch14ext_cor146ConcreteForwardRemainder n (F.gje.model t)
      A_inv (F.gje.L_hat t) (F.U_inv t) (ch14ext_cor146SourceRunV F t)
      (ch14ext_cor146SourceRunXseq F t) (F.z t) (F.gje.x_hat t) 1 =
      ch14ext_cor146SourceForwardRemainder (F.gje.model t) A_inv
        (F.gje.L_hat t) (F.U_inv t) (F.gje.state t) (F.z t)
        (F.gje.x_hat t) := by
    funext i
    unfold ch14ext_cor146ConcreteForwardRemainder
      ch14ext_cor146SourceForwardRemainder
    simp only [ch14ext_cor146SourceRunV_one,
      ch14ext_cor146SourceRunXseq_one]
    rfl
  calc
    vecNorm2 (fun i : Fin n => x i - F.gje.x_hat t i) <=
        raw * ((F.gje.model t).u * vecNorm2 (F.gje.x_hat t)) + rho := hbase'
    _ <= (printed + corr) *
          ((F.gje.model t).u * vecNorm2 (F.gje.x_hat t)) + rho :=
      add_le_add (mul_le_mul_of_nonneg_right hraw hmult0) (le_refl rho)
    _ = 8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
          kappa2 A A_inv * vecNorm2 (F.gje.x_hat t) +
        ch14ext_cor146SourceForwardAbsoluteRemainder F t := by
      simp only [ch14ext_cor146SourceForwardAbsoluteRemainder,
        ch14ext_cor146ForwardAbsoluteSourceRemainder, printed, corr, rho, kap]
      rw [hVone, hrho]
      ring

/-- Source-active relative forward endpoint. The computed/exact norm ratio is
removed by the standard eventual first-order bootstrap. -/
theorem ch14ext_cor146Source_forward_relative_source_literal
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x) (t : I)
    (hbootstrap :
      8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
        kappa2 A A_inv < 1) :
    vecNorm2 (fun i : Fin n => x i - F.gje.x_hat t i) / vecNorm2 x <=
      8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
          kappa2 A A_inv +
        ch14ext_cor146SourceForwardRelativeRemainder F t := by
  let e := vecNorm2 (fun i : Fin n => x i - F.gje.x_hat t i)
  let xn := vecNorm2 x
  let xhn := vecNorm2 (F.gje.x_hat t)
  let c := ch14ext_cor146ForwardPrintedCoefficient n A A_inv
  let q := c * (F.gje.model t).u
  let r := ch14ext_cor146SourceForwardAbsoluteRemainder F t
  have habs := ch14ext_cor146Source_forward_absolute_source_literal F t
  have habs' : e <= q * xhn + r := by
    dsimp [e, xhn, r]
    calc
      vecNorm2 (fun i : Fin n => x i - F.gje.x_hat t i) <=
          8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
              kappa2 A A_inv * vecNorm2 (F.gje.x_hat t) +
            ch14ext_cor146SourceForwardAbsoluteRemainder F t := habs
      _ = q * vecNorm2 (F.gje.x_hat t) +
          ch14ext_cor146SourceForwardAbsoluteRemainder F t := by
        dsimp [q, c, ch14ext_cor146ForwardPrintedCoefficient]
        ring
  have hxhat : xhn <= xn + e := by
    calc
      xhn = vecNorm2 (fun i : Fin n => x i + (F.gje.x_hat t i - x i)) := by
        dsimp [xhn]
        apply congrArg vecNorm2
        funext i
        ring
      _ <= vecNorm2 x + vecNorm2 (fun i : Fin n => F.gje.x_hat t i - x i) :=
        vecNorm2_add_le x (fun i : Fin n => F.gje.x_hat t i - x i)
      _ = xn + e := by
        dsimp [xn, e]
        rw [vecNorm2_sub_comm]
  have hkap1 := ch14ext_cor146_one_le_kappa2_of_isInverse
    n A A_inv F.gje.dimension_pos F.uniform_inverse.source_inverse
  have hkap0 : 0 <= kappa2 A A_inv := le_trans (by norm_num) hkap1
  have hc0 : 0 <= c := by
    dsimp [c, ch14ext_cor146ForwardPrintedCoefficient]
    positivity
  have hq0 : 0 <= q := mul_nonneg hc0 (F.gje.model t).u_nonneg
  have hq1 : q < 1 := by
    dsimp [q, c, ch14ext_cor146ForwardPrintedCoefficient]
    convert hbootstrap using 1 <;> ring
  have hself : e <= q * (xn + e) + r := by
    exact le_trans habs'
      (add_le_add (mul_le_mul_of_nonneg_left hxhat hq0) (le_refl r))
  have hlinear : e * (1 - q) <= q * xn + r := by
    nlinarith
  have hden : 0 < 1 - q := by linarith
  have hsolve : e <= (q * xn + r) / (1 - q) := by
    rw [le_div_iff₀ hden]
    exact hlinear
  have hrelative :
      e / xn <= ((q * xn + r) / (1 - q)) / xn :=
    div_le_div_of_nonneg_right hsolve F.exact_solution_nonzero.le
  have hxn : xn = 0 -> False := by
    dsimp [xn]
    exact F.exact_solution_nonzero.ne'
  calc
    vecNorm2 (fun i : Fin n => x i - F.gje.x_hat t i) / vecNorm2 x =
        e / xn := rfl
    _ <= ((q * xn + r) / (1 - q)) / xn := hrelative
    _ = q + (q ^ 2 * (1 - q)⁻¹ + r * (1 - q)⁻¹ * xn⁻¹) := by
      field_simp [hden.ne', hxn]
      ring
    _ = 8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
          kappa2 A A_inv +
        ch14ext_cor146SourceForwardRelativeRemainder F t := by
      simp only [ch14ext_cor146SourceForwardRelativeRemainder,
        ch14ext_cor146ForwardRelativeSourceRemainder, c, q, r, xn,
        ch14ext_cor146ForwardPrintedCoefficient,
        ch14ext_cor146SourceForwardAbsoluteRemainder]
      ring

/-- **Complete source-active Corollary 14.6 family closure.**

The residual coefficient is exactly `8*n^3*u*sqrt(kappa2(A))`; the relative
forward coefficient is exactly `8*n^2*sqrt(n)*u*kappa2(A)`. Both explicit
remainders are genuine `O(u^2)` statements on a nonbottom filter. -/
theorem ch14ext_cor146Source_vanishing_family_endpoint
    {I : Type*} {l : Filter I} [NeBot l] {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146SourceRunFamily I l n A A_inv b x) :
    (forall t,
      vecNorm2 (fun i : Fin n => b i - matMulVec n A (F.gje.x_hat t) i) <=
        8 * (n : Real) ^ 3 * (F.gje.model t).u *
            Real.sqrt (kappa2 A A_inv) * opNorm2 A *
              vecNorm2 (F.gje.x_hat t) +
          ch14ext_cor146SourceResidualRemainder F t) /\
    ((fun t => ch14ext_cor146SourceResidualRemainder F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2)) /\
    (Filter.Eventually (fun t =>
      vecNorm2 (fun i : Fin n => x i - F.gje.x_hat t i) / vecNorm2 x <=
        8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
            kappa2 A A_inv +
          ch14ext_cor146SourceForwardRelativeRemainder F t) l) /\
    ((fun t => ch14ext_cor146SourceForwardRelativeRemainder F t)
      =O[l] (fun t => (F.gje.model t).u ^ 2)) := by
  let c := ch14ext_cor146ForwardPrintedCoefficient n A A_inv
  have hqZero : Tendsto (fun t => c * (F.gje.model t).u) l (nhds 0) := by
    simpa only [mul_zero] using F.gje.unit_tendsto_zero.const_mul c
  have hqSmall : Filter.Eventually (fun t => c * (F.gje.model t).u < 1) l :=
    (tendsto_order.1 hqZero).2 1 zero_lt_one
  have hbootstrap : Filter.Eventually (fun t =>
      8 * (n : Real) ^ 2 * Real.sqrt n * (F.gje.model t).u *
        kappa2 A A_inv < 1) l := by
    filter_upwards [hqSmall] with t ht
    dsimp [c, ch14ext_cor146ForwardPrintedCoefficient] at ht
    convert ht using 1 <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ch14ext_cor146Source_residual_source_literal F
  · exact ch14ext_cor146Source_residualRemainder_isBigO_u_sq F
  · filter_upwards [hbootstrap] with t ht
    exact ch14ext_cor146Source_forward_relative_source_literal F t ht
  · exact ch14ext_cor146Source_forwardRelativeRemainder_isBigO_u_sq F

end NumStability.Ch14Ext
