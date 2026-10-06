-- Algorithms/Ch14Corollary147SourceClosure.lean
--
-- Strict source closure for Higham Corollary 14.7.  The second stage is the
-- recursively executed, source-active Algorithm 14.4 trace beginning at 1.

import NumStability.Algorithms.Ch14GJESourceAccumulationBridge
import NumStability.Algorithms.Ch14Corollary147WeakFamily

namespace NumStability.Ch14Ext

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

/-! ## Source-run family -/

/-- A vanishing-roundoff family of successful Algorithm 14.4 executions.

The fields are operational LU, forward-substitution, source-trace, inverse,
and solve certificates together with local boundedness of the varying state.
In particular, this contract contains no factor-proximity, `Xabs`-consistency,
residual, forward-error, or final-remainder hypothesis. -/
structure Ch14Cor147SourceFamily
    (ι : Type*) (l : Filter ι) (n : Nat)
    (A : Fin n -> Fin n -> Real) (b : Fin n -> Real) where
  model : ι -> FPModel
  L_hat : ι -> Fin n -> Fin n -> Real
  initial : ι -> Ch14GJEState n
  x_hat : ι -> Fin n -> Real
  U_hat_inv : ι -> Fin n -> Fin n -> Real
  z : ι -> Fin n -> Real
  unit_tendsto_zero : Tendsto (fun t => (model t).u) l (𝓝 0)
  lu_certificate : forall t,
    LUBackwardError n A (L_hat t) (initial t).matrix (gamma (model t) n)
  valid_n : forall t, gammaValid (model t) n
  dimension_pos : 1 <= n
  valid_three : forall t, gammaValid (model t) 3
  final_matrix : forall t,
    ch14ext_gjeSourceTraceMatrix (model t) 1 (initial t) n = idMatrix n
  final_vector : forall t i,
    x_hat t i = ch14ext_gjeSourceTraceRhs (model t) 1 (initial t) n i
  forward_start : forall t,
    (initial t).rhs = fl_forwardSub (model t) n (L_hat t) b
  pivots_nonzero : forall t q, (hq : q < n - 1) ->
    ch14ext_gjeSourceTraceMatrix (model t) 1 (initial t) (1 + q)
        ⟨1 + q, by omega⟩ ⟨1 + q, by omega⟩ ≠ 0
  computed_upper_inverse : forall t,
    IsInverse n (initial t).matrix (U_hat_inv t)
  upper_solve : forall t i,
    matMulVec n (initial t).matrix (z t) i = (initial t).rhs i
  L_hat_isBigO_one : MatrixFamilyIsBigOOne l L_hat
  U_hat_isBigO_one : MatrixFamilyIsBigOOne l (fun t => (initial t).matrix)
  P_abs_isBigO_one : MatrixFamilyIsBigOOne l (fun t =>
    ch14ext_absCumProd n
      (ch14ext_gjeSeqStages n
        (ch14ext_gjeSourceTraceMatrix (model t) 1 (initial t))) 1 (n - 1))
  X_abs_isBigO_one : MatrixFamilyIsBigOOne l (fun t =>
    ch14ext_gjeXabs n
      (ch14ext_gjeSeqStages n
        (ch14ext_gjeSourceTraceMatrix (model t) 1 (initial t)))
      (ch14ext_gjeConstructedQ n
        (ch14ext_gjeSourceTraceMatrix (model t) 1 (initial t)) 1)
      1 (n - 1))
  y_isBigO_one : VectorFamilyIsBigOOne l (fun t => (initial t).rhs)
  x_hat_isBigO_one : VectorFamilyIsBigOOne l x_hat
  U_hat_inv_isBigO_one : MatrixFamilyIsBigOOne l U_hat_inv
  z_isBigO_one : VectorFamilyIsBigOOne l z

noncomputable def ch14ext_cor147SourceV
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) :
    Nat -> Fin n -> Fin n -> Real :=
  ch14ext_gjeSourceTraceMatrix (F.model t) 1 (F.initial t)

noncomputable def ch14ext_cor147SourceXseq
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) :
    Nat -> Fin n -> Real :=
  ch14ext_gjeSourceTraceRhs (F.model t) 1 (F.initial t)

noncomputable def ch14ext_cor147SourceQ
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) :
    Fin n -> Fin n -> Real :=
  ch14ext_gjeConstructedQ n (ch14ext_cor147SourceV F t) 1

noncomputable def ch14ext_cor147SourcePabs
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) :
    Fin n -> Fin n -> Real :=
  ch14ext_absCumProd n
    (ch14ext_gjeSeqStages n (ch14ext_cor147SourceV F t)) 1 (n - 1)

noncomputable def ch14ext_cor147SourceXabs
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) :
    Fin n -> Fin n -> Real :=
  ch14ext_gjeXabs n
    (ch14ext_gjeSeqStages n (ch14ext_cor147SourceV F t))
    (ch14ext_cor147SourceQ F t) 1 (n - 1)

@[simp] theorem ch14ext_cor147SourceV_one
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) :
    ch14ext_cor147SourceV F t 1 = (F.initial t).matrix := by
  simp [ch14ext_cor147SourceV, ch14ext_gjeSourceTraceMatrix,
    ch14ext_gjeSourceTrace]

@[simp] theorem ch14ext_cor147SourceXseq_one
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) :
    ch14ext_cor147SourceXseq F t 1 = (F.initial t).rhs := by
  simp [ch14ext_cor147SourceXseq, ch14ext_gjeSourceTraceRhs,
    ch14ext_gjeSourceTrace]

theorem ch14ext_cor147Source_index_valid {n : Nat} :
    forall q : Nat, q < n - 1 -> 1 + q < n := by
  omega

theorem ch14ext_cor147Source_upper
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) :
    forall q : Nat, q <= n - 1 -> forall i j : Fin n,
      j.val < i.val -> ch14ext_cor147SourceV F t (1 + q) i j = 0 := by
  let V := ch14ext_cor147SourceV F t
  have hidx := ch14ext_cor147Source_index_valid (n := n)
  have hV0 : forall i j : Fin n, j.val < i.val -> V 1 i j = 0 := by
    intro i j hji
    simpa [V] using (F.lu_certificate t).U_lower_zero i j hji
  have hVrec : forall q : Nat, (hq : q < n - 1) ->
      V (1 + (q + 1)) =
        ch14ext_gjeSourceStepMatrix (F.model t) n (V (1 + q))
          ⟨1 + q, hidx q hq⟩ := by
    intro q hq
    simpa [V, ch14ext_cor147SourceV] using
      ch14ext_gjeSourceTraceMatrix_rec (F.model t) 1 (F.initial t) q
        (hidx q hq)
  exact ch14ext_gjeSourceSeq_upper (F.model t) V 1 (n - 1)
    hidx hV0 hVrec

/-! ## Source accumulation adapters -/

/-- The accumulated (14.30a-c) equation for the actual masked source trace. -/
theorem ch14ext_cor147Source_stage2_backward_error
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) :
    ∃ ΔU : Fin n -> Fin n -> Real, ∃ Δy : Fin n -> Real,
      (forall i : Fin n,
        ∑ j : Fin n, ((F.initial t).matrix i j + ΔU i j) * F.x_hat t j =
          (F.initial t).rhs i + Δy i) ∧
      (forall i j : Fin n, |ΔU i j| <= gje_c₃ (F.model t) n *
        ∑ k : Fin n, |ch14ext_cor147SourceXabs F t i k| *
          |(F.initial t).matrix k j|) ∧
      (forall i : Fin n, |Δy i| <= gje_c₃ (F.model t) n *
        ∑ j : Fin n, |ch14ext_cor147SourceXabs F t i j| *
          |(F.initial t).rhs j|) := by
  let V := ch14ext_cor147SourceV F t
  let xseq := ch14ext_cor147SourceXseq F t
  let N := ch14ext_gjeSeqStages n V
  let Q := ch14ext_cor147SourceQ F t
  have hidx := ch14ext_cor147Source_index_valid (n := n)
  have hrec := ch14ext_gjeSourceTrace_recurrence_bounds_14_25b_14_26
    (F.model t) (F.initial t) hidx (F.lu_certificate t).U_lower_zero
    (F.pivots_nonzero t) (F.valid_three t)
  have hsum : 1 + (n - 1) = n := by
    have hn := F.dimension_pos
    omega
  have hfinal : V (1 + (n - 1)) = idMatrix n := by
    rw [hsum]
    simpa [V, ch14ext_cor147SourceV] using F.final_matrix t
  have hxfinal : forall i : Fin n,
      F.x_hat t i = xseq (1 + (n - 1)) i := by
    intro i
    rw [hsum]
    simpa [xseq, ch14ext_cor147SourceXseq] using F.final_vector t i
  have hQP : matMul n Q
      (gje_cumulative_product n N 1 (1 + (n - 1))) = idMatrix n := by
    simpa [Q, N, ch14ext_cor147SourceQ] using
      ch14ext_gjeConstructedQ_isLeftInverse n V 1 hidx
  simpa [V, xseq, N, Q, ch14ext_cor147SourceXabs,
    ch14ext_cor147SourceQ] using
      ch14ext_gje_stage2_backward_error_of_accumulation n (F.model t)
        (F.x_hat t) N V xseq Q 1 F.dimension_pos (F.valid_three t)
        hidx hfinal hxfinal hQP hrec.1 hrec.2

/-- The constructed source `Q` differs from the computed upper factor by the
accumulated matrix error; the right side is operational and locally bounded. -/
theorem ch14ext_cor147Source_Q_sub_U_bound
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) (i j : Fin n) :
    |ch14ext_cor147SourceQ F t i j - (F.initial t).matrix i j| <=
      gje_c₃ (F.model t) n *
        matMul n (ch14ext_cor147SourceXabs F t)
          (absMatrix n (F.initial t).matrix) i j := by
  let V := ch14ext_cor147SourceV F t
  let N := ch14ext_gjeSeqStages n V
  let Q := ch14ext_cor147SourceQ F t
  let P := gje_cumulative_product n N 1 (1 + (n - 1))
  let E : Fin n -> Fin n -> Real := fun a k =>
    V (1 + (n - 1)) a k - matMul n P (V 1) a k
  have hidx := ch14ext_cor147Source_index_valid (n := n)
  have hrec := ch14ext_gjeSourceTrace_recurrence_bounds_14_25b_14_26
    (F.model t) (F.initial t) hidx (F.lu_certificate t).U_lower_zero
    (F.pivots_nonzero t) (F.valid_three t)
  have hE : forall a k : Fin n, |E a k| <=
      gje_c₃ (F.model t) n * ch14ext_boundObj n N (V 1) 1 (n - 1) a k := by
    intro a k
    simpa [E, P] using ch14ext_matrixAccumulation_c3 n (F.model t) N V 1
      F.dimension_pos (F.valid_three t) hidx hrec.1 a k
  have hQP : matMul n Q P = idMatrix n := by
    simpa [Q, P, N, ch14ext_cor147SourceQ] using
      ch14ext_gjeConstructedQ_isLeftInverse n V 1 hidx
  have hsum : 1 + (n - 1) = n := by
    have hn := F.dimension_pos
    omega
  have hfinalQ : matMul n Q (V (1 + (n - 1))) = Q := by
    rw [hsum]
    have hfin : V n = idMatrix n := by
      simpa [V, ch14ext_cor147SourceV] using F.final_matrix t
    rw [hfin, matMul_id_right]
  have hproductQ : matMul n Q (matMul n P (V 1)) = V 1 := by
    rw [← matMul_assoc, hQP, matMul_id_left]
  have hkey : matMul n Q E = fun a k => Q a k - V 1 a k := by
    funext a k
    have hexpand : matMul n Q E a k =
        matMul n Q (V (1 + (n - 1))) a k -
          matMul n Q (matMul n P (V 1)) a k := by
      show (∑ q : Fin n, Q a q * E q k) =
        (∑ q : Fin n, Q a q * V (1 + (n - 1)) q k) -
          ∑ q : Fin n, Q a q * matMul n P (V 1) q k
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun q _ => by
        show Q a q * (V (1 + (n - 1)) q k - matMul n P (V 1) q k) = _
        ring)
    rw [hexpand, hfinalQ, hproductQ]
  have hbound := ch14ext_matMul_abs_bound n Q E
    (ch14ext_boundObj n N (V 1) 1 (n - 1)) (gje_c₃ (F.model t) n) hE i j
  have hreassoc :
      matMul n (absMatrix n Q) (ch14ext_boundObj n N (V 1) 1 (n - 1)) =
        matMul n (ch14ext_cor147SourceXabs F t) (absMatrix n (V 1)) := by
    show matMul n (absMatrix n Q)
        (matMul n (ch14ext_absCumProd n N 1 (n - 1)) (absMatrix n (V 1))) = _
    rw [← matMul_assoc]
    rfl
  rw [hreassoc, hkey] at hbound
  simpa [Q, V, ch14ext_cor147SourceQ] using hbound

/-- The absolute source-stage product is bounded by a genuine right inverse
of the computed upper factor plus the retained accumulated residual term. -/
theorem ch14ext_cor147Source_Pabs_le_abs_Uinv_add
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (t : ι) (U_inv : Fin n -> Fin n -> Real)
    (hUinv : IsRightInverse n (F.initial t).matrix U_inv)
    (i j : Fin n) :
    ch14ext_cor147SourcePabs F t i j <= |U_inv i j| +
      gje_c₃ (F.model t) n *
        matMul n
          (matMul n (ch14ext_cor147SourcePabs F t)
            (absMatrix n (F.initial t).matrix))
          (absMatrix n U_inv) i j := by
  let V := ch14ext_cor147SourceV F t
  let N := ch14ext_gjeSeqStages n V
  let X := ch14ext_cor147SourcePabs F t
  let S := gje_cumulative_product n N 1 (1 + (n - 1))
  have hidx := ch14ext_cor147Source_index_valid (n := n)
  have hUpper : forall q : Nat, q <= n - 1 -> forall a k : Fin n,
      k.val < a.val -> V (1 + q) a k = 0 := by
    simpa [V] using ch14ext_cor147Source_upper F t
  have hX : forall a k : Fin n, X a k = |S a k| := by
    intro a k
    simpa [X, S, N, ch14ext_cor147SourcePabs] using
      ch14ext_gje_absCumProd_eq_abs_signed n V 1 (n - 1) hidx hUpper a k
  have hrec := ch14ext_gjeSourceTrace_recurrence_bounds_14_25b_14_26
    (F.model t) (F.initial t) hidx (F.lu_certificate t).U_lower_zero
    (F.pivots_nonzero t) (F.valid_three t)
  have hAccum := ch14ext_matrixAccumulation_c3 n (F.model t) N V 1
    F.dimension_pos (F.valid_three t) hidx hrec.1
  have hsum : 1 + (n - 1) = n := by
    have hn := F.dimension_pos
    omega
  have hResidual : forall a k : Fin n,
      |idMatrix n a k - matMul n S (F.initial t).matrix a k| <=
        gje_c₃ (F.model t) n *
          matMul n X (absMatrix n (F.initial t).matrix) a k := by
    intro a k
    have h := hAccum a k
    have hfin : V (1 + (n - 1)) = idMatrix n := by
      rw [hsum]
      simpa [V, ch14ext_cor147SourceV] using F.final_matrix t
    rw [hfin] at h
    simpa [S, X, N, V, ch14ext_cor147SourcePabs,
      ch14ext_boundObj] using h
  simpa [X] using
    ch14ext_abs_signed_le_abs_rightInverse_add n S X (F.initial t).matrix
      U_inv (gje_c₃ (F.model t) n) hX hUinv hResidual i j

/-! ## Literal source forms of Theorem 14.5 -/

/-- Equation (14.31) for the recursively executed source-active trace. -/
theorem ch14ext_cor147Source_overall_residual_14_31
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) :
    forall i : Fin n,
      |b i - matMulVec n A (F.x_hat t) i| <=
        8 * (n : Real) * (F.model t).u *
          ch14ext_gjeResidualS2 n (F.L_hat t)
            (ch14ext_cor147SourceXabs F t) (F.initial t).matrix
            (F.x_hat t) i +
        ch14ext_gjeResidualHigherOrder n (F.model t) (F.L_hat t)
          (ch14ext_cor147SourceXabs F t) (F.initial t).matrix
          (F.initial t).rhs (F.x_hat t) i := by
  intro i
  let X := ch14ext_cor147SourceXabs F t
  let ΔA₁ : Fin n -> Fin n -> Real := fun a j =>
    matMul n (F.L_hat t) (F.initial t).matrix a j - A a j
  have hΔA₁ : forall a j : Fin n, |ΔA₁ a j| <= gamma (F.model t) n *
      ∑ k : Fin n, |F.L_hat t a k| * |(F.initial t).matrix k j| := by
    intro a j
    exact (F.lu_certificate t).backward_bound a j
  have hFactor : forall a j : Fin n,
      A a j + ΔA₁ a j = matMul n (F.L_hat t) (F.initial t).matrix a j := by
    intro a j
    unfold ΔA₁
    ring
  obtain ⟨ΔL, hΔL, hForwardRaw⟩ := forwardSub_backward_error
    (F.model t) n (F.L_hat t) b
    (fun a => by rw [(F.lu_certificate t).L_diag a]; norm_num)
    (F.lu_certificate t).L_upper_zero (F.valid_n t)
  have hForward : forall a : Fin n,
      matMulVec n (F.L_hat t) (F.initial t).rhs a +
          matMulVec n ΔL (F.initial t).rhs a = b a := by
    intro a
    have h := hForwardRaw a
    rw [← F.forward_start t] at h
    simpa [matMulVec, Finset.sum_add_distrib, add_mul] using h
  obtain ⟨ΔU, Δy, hStageRaw, hΔUraw, hΔyraw⟩ :=
    ch14ext_cor147Source_stage2_backward_error F t
  have hStage : forall a : Fin n,
      matMulVec n (F.initial t).matrix (F.x_hat t) a +
          matMulVec n ΔU (F.x_hat t) a = (F.initial t).rhs a + Δy a := by
    intro a
    have h := hStageRaw a
    simpa [matMulVec, Finset.sum_add_distrib, add_mul] using h
  have hΔU : forall a j : Fin n, |ΔU a j| <= gje_c₃ (F.model t) n *
      ∑ k : Fin n, |X a k| * |(F.initial t).matrix k j| := by
    intro a j
    simpa [X] using hΔUraw a j
  have hΔy : forall a : Fin n, |Δy a| <= gje_c₃ (F.model t) n *
      ∑ j : Fin n, |X a j| * |(F.initial t).rhs j| := by
    intro a
    simpa [X] using hΔyraw a
  have hResidual := ch14ext_gje_residual_decomposition_14_33 n A
    (F.L_hat t) (F.initial t).matrix ΔA₁ ΔL ΔU b (F.initial t).rhs
    (F.x_hat t) Δy hFactor hForward hStage
  have hR := ch14ext_gjeResidual1433_bound_corrected n (F.L_hat t)
    (F.initial t).matrix X ΔA₁ ΔL ΔU (F.initial t).rhs (F.x_hat t) Δy
    (gamma (F.model t) n) (gje_c₃ (F.model t) n)
    (gamma_nonneg (F.model t) (F.valid_n t))
    (gje_c3_nonneg (F.model t) n F.dimension_pos (F.valid_three t))
    hΔA₁ hΔL hΔU hΔy hStage i
  have hidx := ch14ext_cor147Source_index_valid (n := n)
  have hdiag : forall k : Fin n, 1 <= X k k := by
    intro k
    simpa [X, ch14ext_cor147SourceXabs, ch14ext_cor147SourceQ] using
      ch14ext_gjeXabs_diag_ge_one n
        (ch14ext_gjeSeqStages n (ch14ext_cor147SourceV F t))
        (ch14ext_gjeConstructedQ n (ch14ext_cor147SourceV F t) 1)
        1 (n - 1) hidx
        (ch14ext_gjeConstructedQ_isLeftInverse n
          (ch14ext_cor147SourceV F t) 1 hidx) k
  have hS12 := ch14ext_gjeResidualS1_le_S2 n (F.L_hat t) X
    (F.initial t).matrix (F.x_hat t) i hdiag
  have hS2nn := ch14ext_gjeResidualS2_nonneg n (F.L_hat t) X
    (F.initial t).matrix (F.x_hat t) i
  have hAbsorb :
      2 * gamma (F.model t) n *
          ch14ext_gjeResidualS1 n (F.L_hat t) (F.initial t).matrix
            (F.x_hat t) i <=
        2 * gamma (F.model t) n *
          ch14ext_gjeResidualS2 n (F.L_hat t) X (F.initial t).matrix
            (F.x_hat t) i :=
    mul_le_mul_of_nonneg_left hS12
      (mul_nonneg (by norm_num) (gamma_nonneg (F.model t) (F.valid_n t)))
  have hCoeff := ch14ext_gje_residual_coeff_budget_corrected
    (F.model t) n (F.valid_n t) (F.valid_three t)
  have hCoeffS2 := mul_le_mul_of_nonneg_right hCoeff hS2nn
  have hresEq : b i - matMulVec n A (F.x_hat t) i =
      ch14ext_gjeResidual1433 n (F.L_hat t) (F.initial t).matrix
        ΔA₁ ΔL ΔU (F.x_hat t) Δy i := by
    linarith [hResidual i]
  rw [hresEq]
  have hFinal :
      |ch14ext_gjeResidual1433 n (F.L_hat t) (F.initial t).matrix
          ΔA₁ ΔL ΔU (F.x_hat t) Δy i| <=
        8 * (n : Real) * (F.model t).u *
          ch14ext_gjeResidualS2 n (F.L_hat t) X (F.initial t).matrix
            (F.x_hat t) i +
        ch14ext_gjeResidualHigherOrder n (F.model t) (F.L_hat t) X
          (F.initial t).matrix (F.initial t).rhs (F.x_hat t) i := by
    unfold ch14ext_gjeResidualHigherOrder
    nlinarith [hR, hAbsorb, hCoeffS2]
  simpa [X] using hFinal

/-- The stage-envelope form of (14.32), with its second-stage error supplied
by `ch14ext_gjeSourceTrace_stage2_forward_error_14_29`. -/
theorem ch14ext_cor147Source_overall_forward_stage_envelope
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι)
    (A_inv : Fin n -> Fin n -> Real) (x : Fin n -> Real)
    (hAinv : IsLeftInverse n A A_inv)
    (hExact : forall i : Fin n, matMulVec n A x i = b i) :
    forall i : Fin n,
      |x i - F.x_hat t i| <=
        2 * (n : Real) * (F.model t).u *
          ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
            (F.x_hat t) i +
        6 * (n : Real) * (F.model t).u *
          ch14ext_gjeForwardT2 n (ch14ext_cor147SourcePabs F t)
            (F.initial t).matrix (F.x_hat t) i +
        ch14ext_gjeForwardHigherOrder n (F.model t) A_inv (F.L_hat t)
          (F.initial t).matrix (ch14ext_cor147SourcePabs F t)
          (F.z t) (F.initial t).rhs (F.x_hat t) i := by
  intro i
  let P := ch14ext_cor147SourcePabs F t
  have hP : forall a j : Fin n, 0 <= P a j := by
    intro a j
    exact gje_cumulative_product_abs_nonneg n
      (ch14ext_gjeSeqStages n (ch14ext_cor147SourceV F t))
      1 (1 + (n - 1)) a j
  let ΔA₁ : Fin n -> Fin n -> Real := fun a j =>
    matMul n (F.L_hat t) (F.initial t).matrix a j - A a j
  have hΔA₁ : forall a j : Fin n, |ΔA₁ a j| <= gamma (F.model t) n *
      ∑ k : Fin n, |F.L_hat t a k| * |(F.initial t).matrix k j| := by
    intro a j
    exact (F.lu_certificate t).backward_bound a j
  have hFactor : forall a j : Fin n,
      A a j + ΔA₁ a j = matMul n (F.L_hat t) (F.initial t).matrix a j := by
    intro a j
    unfold ΔA₁
    ring
  obtain ⟨ΔL, hΔL, hForwardRaw⟩ := forwardSub_backward_error
    (F.model t) n (F.L_hat t) b
    (fun a => by rw [(F.lu_certificate t).L_diag a]; norm_num)
    (F.lu_certificate t).L_upper_zero (F.valid_n t)
  have hForward : forall a : Fin n,
      matMulVec n (F.L_hat t) (F.initial t).rhs a +
          matMulVec n ΔL (F.initial t).rhs a = b a := by
    intro a
    have h := hForwardRaw a
    rw [← F.forward_start t] at h
    simpa [matMulVec, Finset.sum_add_distrib, add_mul] using h
  have hErr : forall a : Fin n, |F.z t a - F.x_hat t a| <=
      gje_c₃ (F.model t) n *
        ch14ext_gjeForwardRaw n P (F.initial t).matrix (F.z t)
          (F.initial t).rhs a := by
    intro a
    have h := ch14ext_gjeSourceTrace_stage2_forward_error_14_29
      (F.model t) (F.initial t) (F.z t) F.dimension_pos (F.valid_three t)
      (F.lu_certificate t).U_lower_zero (F.final_matrix t)
      (F.upper_solve t) (F.pivots_nonzero t) a
    rw [← F.final_vector t a] at h
    simpa [P, ch14ext_cor147SourcePabs, ch14ext_cor147SourceV,
      ch14ext_gjeForwardRaw, ch14ext_gjeForwardEnvelope] using h
  have hFirst := ch14ext_gje_first_stage_forward_split n A A_inv
    (F.L_hat t) (F.initial t).matrix ΔA₁ ΔL b x (F.z t)
    (F.initial t).rhs (F.x_hat t) (gamma (F.model t) n)
    (gje_c₃ (F.model t) n) (gamma_nonneg (F.model t) (F.valid_n t))
    hAinv hExact hFactor hForward (F.upper_solve t) hΔA₁ hΔL P hErr i
  have hSecond := ch14ext_gje_stage2_forward_split n (F.initial t).matrix P
    (F.z t) (F.initial t).rhs (F.x_hat t) (gje_c₃ (F.model t) n)
    (gje_c3_nonneg (F.model t) n F.dimension_pos (F.valid_three t)) hP
    (F.upper_solve t) hErr i
  have htri : |x i - F.x_hat t i| <=
      |x i - F.z t i| + |F.z t i - F.x_hat t i| := by
    have heq : x i - F.x_hat t i =
        (x i - F.z t i) + (F.z t i - F.x_hat t i) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hCombined : |x i - F.x_hat t i| <=
      2 * gamma (F.model t) n *
          ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
            (F.x_hat t) i +
      2 * gje_c₃ (F.model t) n *
          ch14ext_gjeForwardT2 n P (F.initial t).matrix (F.x_hat t) i +
      2 * gamma (F.model t) n * gje_c₃ (F.model t) n *
          ch14ext_gjeForwardQ1 n A_inv (F.L_hat t) (F.initial t).matrix P
            (F.z t) (F.initial t).rhs i +
      2 * gje_c₃ (F.model t) n * gje_c₃ (F.model t) n *
          ch14ext_gjeForwardQ2 n P (F.initial t).matrix
            (F.z t) (F.initial t).rhs i := by
    linarith
  have hT1nn := ch14ext_gjeForwardT1_nonneg n A_inv (F.L_hat t)
    (F.initial t).matrix (F.x_hat t) i
  have hT2nn := ch14ext_gjeForwardT2_nonneg n P (F.initial t).matrix
    (F.x_hat t) i hP
  have hGammaTerm :
      2 * gamma (F.model t) n *
          ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
            (F.x_hat t) i =
        2 * (n : Real) * (F.model t).u *
            ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
              (F.x_hat t) i +
          2 * ch14ext_gammaRem (F.model t) n *
            ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
              (F.x_hat t) i := by
    rw [ch14ext_gamma_split (F.model t) n (F.valid_n t)]
    ring
  have hCcoeff : 2 * gje_c₃ (F.model t) n <=
      6 * (n : Real) * (F.model t).u +
        2 * gje_c3_quadratic_remainder (F.model t) n := by
    have h := ch14ext_gje_forward_second_coeff
      (F.model t) n (F.valid_three t)
    nlinarith
  have hCterm := mul_le_mul_of_nonneg_right hCcoeff hT2nn
  unfold ch14ext_gjeForwardHigherOrder
  nlinarith [hCombined, hGammaTerm, hCterm]

/-- Literal equation (14.32) for the source trace, with the cumulative-stage
envelope replaced by the actual computed upper inverse. -/
theorem ch14ext_cor147Source_overall_forward_14_32
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι)
    (A_inv : Fin n -> Fin n -> Real) (x : Fin n -> Real)
    (hAinv : IsLeftInverse n A A_inv)
    (hExact : forall i : Fin n, matMulVec n A x i = b i) :
    forall i : Fin n,
      |x i - F.x_hat t i| <=
        2 * (n : Real) * (F.model t).u *
          ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
            (F.x_hat t) i +
        6 * (n : Real) * (F.model t).u *
          ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
            (F.initial t).matrix (F.x_hat t) i +
        ch14ext_gjeForwardLiteralHigherOrder n (F.model t) A_inv
          (F.L_hat t) (F.initial t).matrix (ch14ext_cor147SourcePabs F t)
          (F.U_hat_inv t) (F.z t) (F.initial t).rhs (F.x_hat t) i := by
  intro i
  let P := ch14ext_cor147SourcePabs F t
  have hStage := ch14ext_cor147Source_overall_forward_stage_envelope F t
    A_inv x hAinv hExact i
  have hCompare : forall a j : Fin n,
      P a j <= |F.U_hat_inv t a j| +
        gje_c₃ (F.model t) n *
          matMul n (matMul n P (absMatrix n (F.initial t).matrix))
            (absMatrix n (F.U_hat_inv t)) a j := by
    intro a j
    simpa [P] using ch14ext_cor147Source_Pabs_le_abs_Uinv_add
      F t (F.U_hat_inv t) (F.computed_upper_inverse t).2 a j
  have hT2 := ch14ext_gjeForwardT2_le_printed_add_correction n P
    (F.initial t).matrix (F.U_hat_inv t) (F.x_hat t)
    (gje_c₃ (F.model t) n) hCompare i
  have hLeadNonneg : 0 <= 6 * (n : Real) * (F.model t).u :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
      (F.model t).u_nonneg
  have hScaled := mul_le_mul_of_nonneg_left hT2 hLeadNonneg
  have hFinal : |x i - F.x_hat t i| <=
      2 * (n : Real) * (F.model t).u *
          ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
            (F.x_hat t) i +
      6 * (n : Real) * (F.model t).u *
          ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
            (F.initial t).matrix (F.x_hat t) i +
      (ch14ext_gjeForwardHigherOrder n (F.model t) A_inv (F.L_hat t)
          (F.initial t).matrix P (F.z t) (F.initial t).rhs (F.x_hat t) i +
        6 * (n : Real) * (F.model t).u * gje_c₃ (F.model t) n *
          ch14ext_gjeForwardUinvCorrection n P (F.initial t).matrix
            (F.U_hat_inv t) (F.x_hat t) i) := by
    calc
      |x i - F.x_hat t i| <=
          2 * (n : Real) * (F.model t).u *
              ch14ext_gjeForwardT1 n A_inv (F.L_hat t)
                (F.initial t).matrix (F.x_hat t) i +
            6 * (n : Real) * (F.model t).u *
              ch14ext_gjeForwardT2 n P (F.initial t).matrix
                (F.x_hat t) i +
            ch14ext_gjeForwardHigherOrder n (F.model t) A_inv (F.L_hat t)
              (F.initial t).matrix P (F.z t) (F.initial t).rhs
              (F.x_hat t) i := by simpa [P] using hStage
      _ <= 2 * (n : Real) * (F.model t).u *
              ch14ext_gjeForwardT1 n A_inv (F.L_hat t)
                (F.initial t).matrix (F.x_hat t) i +
            6 * (n : Real) * (F.model t).u *
              (ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
                  (F.initial t).matrix (F.x_hat t) i +
                gje_c₃ (F.model t) n *
                  ch14ext_gjeForwardUinvCorrection n P
                    (F.initial t).matrix (F.U_hat_inv t) (F.x_hat t) i) +
            ch14ext_gjeForwardHigherOrder n (F.model t) A_inv (F.L_hat t)
              (F.initial t).matrix P (F.z t) (F.initial t).rhs
              (F.x_hat t) i := by nlinarith [hScaled]
      _ = _ := by ring
  simpa [P, ch14ext_gjeForwardLiteralHigherOrder] using hFinal

/-! ## Vanishing-roundoff source endpoints -/

theorem ch14ext_cor147Source_residual_14_31_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) :
    (forall t i,
      |b i - matMulVec n A (F.x_hat t) i| <=
        8 * (n : Real) * (F.model t).u *
          ch14ext_gjeResidualS2 n (F.L_hat t)
            (ch14ext_cor147SourceXabs F t) (F.initial t).matrix
            (F.x_hat t) i +
        ch14ext_gjeResidualHigherOrder n (F.model t) (F.L_hat t)
          (ch14ext_cor147SourceXabs F t) (F.initial t).matrix
          (F.initial t).rhs (F.x_hat t) i) ∧
      forall i,
        (fun t => ch14ext_gjeResidualHigherOrder n (F.model t) (F.L_hat t)
          (ch14ext_cor147SourceXabs F t) (F.initial t).matrix
          (F.initial t).rhs (F.x_hat t) i) =O[l]
            (fun t => (F.model t).u ^ 2) := by
  constructor
  · exact ch14ext_cor147Source_overall_residual_14_31 F
  · intro i
    exact ch14ext_gjeResidualHigherOrder_family_isBigO n F.model F.L_hat
      (ch14ext_cor147SourceXabs F) (fun t => (F.initial t).matrix)
      (fun t => (F.initial t).rhs) F.x_hat F.unit_tendsto_zero
      F.L_hat_isBigO_one (by simpa [ch14ext_cor147SourceXabs,
        ch14ext_cor147SourceQ, ch14ext_cor147SourceV] using F.X_abs_isBigO_one)
      F.U_hat_isBigO_one F.y_isBigO_one F.x_hat_isBigO_one i

theorem ch14ext_cor147Source_forward_14_32_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv : Fin n -> Fin n -> Real) (x : Fin n -> Real)
    (hAinv : IsLeftInverse n A A_inv)
    (hExact : forall i : Fin n, matMulVec n A x i = b i) :
    (forall t i,
      |x i - F.x_hat t i| <=
        2 * (n : Real) * (F.model t).u *
          ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
            (F.x_hat t) i +
        6 * (n : Real) * (F.model t).u *
          ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
            (F.initial t).matrix (F.x_hat t) i +
        ch14ext_gjeForwardLiteralHigherOrder n (F.model t) A_inv
          (F.L_hat t) (F.initial t).matrix (ch14ext_cor147SourcePabs F t)
          (F.U_hat_inv t) (F.z t) (F.initial t).rhs (F.x_hat t) i) ∧
      forall i,
        (fun t => ch14ext_gjeForwardLiteralHigherOrder n (F.model t) A_inv
          (F.L_hat t) (F.initial t).matrix (ch14ext_cor147SourcePabs F t)
          (F.U_hat_inv t) (F.z t) (F.initial t).rhs (F.x_hat t) i) =O[l]
            (fun t => (F.model t).u ^ 2) := by
  constructor
  · intro t
    exact ch14ext_cor147Source_overall_forward_14_32 F t A_inv x hAinv hExact
  · intro i
    exact ch14ext_gjeForwardLiteralHigherOrder_family_isBigO n F.model
      (fun _ => A_inv) F.L_hat (fun t => (F.initial t).matrix)
      (ch14ext_cor147SourcePabs F) F.U_hat_inv F.z
      (fun t => (F.initial t).rhs) F.x_hat F.unit_tendsto_zero
      (ch14ext_fixedMatrix_family_isBigOOne l A_inv) F.L_hat_isBigO_one
      F.U_hat_isBigO_one (by simpa [ch14ext_cor147SourcePabs,
        ch14ext_cor147SourceV] using F.P_abs_isBigO_one)
      F.U_hat_inv_isBigO_one F.z_isBigO_one F.y_isBigO_one
      F.x_hat_isBigO_one i

/-! ## Factor proximity derived from the LU backward certificate -/

/-- The componentwise LU backward residual is `O(u)` when the computed
factors are locally bounded. -/
theorem ch14ext_luBackward_productResidual_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    (fp : ι -> FPModel) (A : Fin n -> Fin n -> Real)
    (L_hat U_hat : ι -> Fin n -> Fin n -> Real)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (hLU : forall t,
      LUBackwardError n A (L_hat t) (U_hat t) (gamma (fp t) n))
    (hvalid : forall t, gammaValid (fp t) n)
    (hLone : MatrixFamilyIsBigOOne l L_hat)
    (hUone : MatrixFamilyIsBigOOne l U_hat) :
    Ch14MatrixFamilyIsBigO l
      (fun t i j => matMul n (L_hat t) (U_hat t) i j - A i j)
      (fun t => (fp t).u) := by
  intro i j
  let W : ι -> Real := fun t =>
    ∑ k : Fin n, |L_hat t i k| * |U_hat t k j|
  have hW : W =O[l] (fun _ : ι => (1 : Real)) := by
    dsimp [W]
    simpa only [one_mul, Real.norm_eq_abs] using
      (Asymptotics.IsBigO.sum (s := Finset.univ) (fun k _ =>
        (hLone i k).norm_left.mul (hUone k j).norm_left))
  have hdom :
      (fun t => matMul n (L_hat t) (U_hat t) i j - A i j) =O[l]
        (fun t => gamma (fp t) n * W t) := by
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards [] with t
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (gamma_nonneg (fp t) (hvalid t))
        (Finset.sum_nonneg (fun k _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))))]
    simpa [W, matMul] using (hLU t).backward_bound i j
  have hgamma := ch14ext_gamma_family_isBigO_unit n fp hu
  exact hdom.trans (by
    simpa only [mul_one] using hgamma.mul hW)

/-- Product split used by the upper Doolittle dependency. -/
theorem ch14ext_matMul_eq_prefix_add_upper {n : Nat}
    (L U : Fin n -> Fin n -> Real)
    (hdiag : forall k : Fin n, L k k = 1)
    (hupper : forall i j : Fin n, i.val < j.val -> L i j = 0)
    (k j : Fin n) (hkj : k.val <= j.val) :
    matMul n L U k j = higham9_2_rectPrefixDot L U k j k + U k j := by
  simpa [matMul, rectMatMul, higham9_2_rectRow] using
    higham9_2_rectMatMul_eq_prefix_add_upper
      (m := n) (n := n) (hmn := Nat.le_refl n) hdiag hupper k j hkj

/-- Product split used by the lower Doolittle dependency. -/
theorem ch14ext_matMul_eq_prefix_add_lower {n : Nat}
    (L U : Fin n -> Fin n -> Real)
    (hlower : forall i j : Fin n, j.val < i.val -> U i j = 0)
    (i k : Fin n) :
    matMul n L U i k = higham9_2_rectPrefixDot L U i k k + L i k * U k k := by
  simpa [matMul, rectMatMul] using
    higham9_2_rectMatMul_eq_prefix_add_lower hlower i k

/-- If all factor entries used before pivot `k` are already `O(u)` close,
then their Doolittle prefix products are `O(u)` close as well. -/
theorem ch14ext_luPrefix_difference_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    (L U : Fin n -> Fin n -> Real)
    (L_hat U_hat : ι -> Fin n -> Fin n -> Real)
    (u : ι -> Real) (i j k : Fin n)
    (hLprev : forall s : Fin n, s.val < k.val ->
      (fun t => L_hat t i s - L i s) =O[l] u)
    (hUprev : forall s : Fin n, s.val < k.val ->
      (fun t => U_hat t s j - U s j) =O[l] u)
    (hUone : MatrixFamilyIsBigOOne l U_hat) :
    (fun t => higham9_2_rectPrefixDot (L_hat t) (U_hat t) i j k -
      higham9_2_rectPrefixDot L U i j k) =O[l] u := by
  have hsum :
      (fun t => ∑ s : Fin n,
        ((if s.val < k.val then L_hat t i s * U_hat t s j else 0) -
          (if s.val < k.val then L i s * U s j else 0))) =O[l] u := by
    apply Asymptotics.IsBigO.sum
    intro s _
    by_cases hs : s.val < k.val
    · have h1 : (fun t => (L_hat t i s - L i s) * U_hat t s j) =O[l] u := by
        simpa only [mul_one] using (hLprev s hs).mul (hUone s j)
      have h2 : (fun t => L i s * (U_hat t s j - U s j)) =O[l] u :=
        (hUprev s hs).const_mul_left (L i s)
      have h := h1.add h2
      simpa only [if_pos hs] using (show
        (fun t => L_hat t i s * U_hat t s j - L i s * U s j) =O[l] u by
          convert h using 1
          funext t
          ring)
    · simp only [if_neg hs, sub_self]
      exact Asymptotics.isBigO_zero _ _
  simpa only [higham9_2_rectPrefixDot, ← Finset.sum_sub_distrib] using hsum

/-- Fixed-dimensional Doolittle induction turns the operational LU backward
certificate into first-order proximity to the exact no-pivot factors.  The
only divisions are by the exact pivots, whose nonvanishing is explicit. -/
theorem ch14ext_luBackward_factorProximity_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    (fp : ι -> FPModel) (A L U : Fin n -> Fin n -> Real)
    (L_hat U_hat : ι -> Fin n -> Fin n -> Real)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (hComputed : forall t,
      LUBackwardError n A (L_hat t) (U_hat t) (gamma (fp t) n))
    (hvalid : forall t, gammaValid (fp t) n)
    (hLone : MatrixFamilyIsBigOOne l L_hat)
    (hUone : MatrixFamilyIsBigOOne l U_hat)
    (hExact : LUFactSpec n A L U)
    (hpiv : forall k : Fin n, U k k ≠ 0) :
    Ch14MatrixFamilyIsBigO l
        (fun t i j => L_hat t i j - L i j) (fun t => (fp t).u) ∧
      Ch14MatrixFamilyIsBigO l
        (fun t i j => U_hat t i j - U i j) (fun t => (fp t).u) := by
  let unit : ι -> Real := fun t => (fp t).u
  have hres := ch14ext_luBackward_productResidual_isBigO fp A L_hat U_hat
    hu hComputed hvalid hLone hUone
  have hstage : forall m : Nat, m <= n ->
      (forall k : Fin n, k.val < m -> forall j : Fin n,
        (fun t => U_hat t k j - U k j) =O[l] unit) ∧
      (forall k : Fin n, k.val < m -> forall i : Fin n,
        (fun t => L_hat t i k - L i k) =O[l] unit) := by
    intro m
    induction m with
    | zero =>
        intro _
        constructor <;> intro k hk
        · exact (Nat.not_lt_zero k.val hk).elim
        · exact (Nat.not_lt_zero k.val hk).elim
    | succ m ih =>
        intro hm
        have hprev := ih (by omega)
        have hUcurrent : forall k : Fin n, k.val < m + 1 -> forall j : Fin n,
            (fun t => U_hat t k j - U k j) =O[l] unit := by
          intro k hk j
          by_cases hkm : k.val < m
          · exact hprev.1 k hkm j
          · have hk_eq : k.val = m := by omega
            by_cases hkj : k.val <= j.val
            · have hprefix := ch14ext_luPrefix_difference_isBigO L U L_hat U_hat
                unit k j k
                (fun s hs => hprev.2 s (by omega) k)
                (fun s hs => hprev.1 s (by omega) j) hUone
              have h := (hres k j).sub hprefix
              convert h using 1
              funext t
              have hhat := ch14ext_matMul_eq_prefix_add_upper
                (L_hat t) (U_hat t) (hComputed t).L_diag
                (hComputed t).L_upper_zero k j hkj
              have hexact := ch14ext_matMul_eq_prefix_add_upper L U
                hExact.L_diag hExact.L_upper_zero k j hkj
              have hA : matMul n L U k j = A k j := by
                simpa [matMul] using hExact.product_eq k j
              change U_hat t k j - U k j =
                (matMul n (L_hat t) (U_hat t) k j - A k j) -
                  (higham9_2_rectPrefixDot (L_hat t) (U_hat t) k j k -
                    higham9_2_rectPrefixDot L U k j k)
              rw [hhat, ← hA, hexact]
              ring
            · have hjk : j.val < k.val := by omega
              have heq : (fun t => U_hat t k j - U k j) =
                  (fun _ : ι => (0 : Real)) := by
                funext t
                rw [(hComputed t).U_lower_zero k j hjk,
                  hExact.U_lower_zero k j hjk]
                ring
              rw [heq]
              exact Asymptotics.isBigO_zero _ _
        have hLcurrent : forall k : Fin n, k.val < m + 1 -> forall i : Fin n,
            (fun t => L_hat t i k - L i k) =O[l] unit := by
          intro k hk i
          by_cases hkm : k.val < m
          · exact hprev.2 k hkm i
          · have hk_eq : k.val = m := by omega
            have hprefix := ch14ext_luPrefix_difference_isBigO L U L_hat U_hat
              unit i k k
              (fun s hs => hprev.2 s (by omega) i)
              (fun s hs => hprev.1 s (by omega) k) hUone
            have hUkk := hUcurrent k hk k
            have hterm :
                (fun t => L_hat t i k * (U_hat t k k - U k k)) =O[l] unit := by
              simpa only [one_mul] using (hLone i k).mul hUkk
            have hnum := ((hres i k).sub hprefix).sub hterm
            have hscaled := hnum.const_mul_left (U k k)⁻¹
            convert hscaled using 1
            funext t
            have hhat := ch14ext_matMul_eq_prefix_add_lower
              (L_hat t) (U_hat t) (hComputed t).U_lower_zero i k
            have hexact := ch14ext_matMul_eq_prefix_add_lower L U
              hExact.U_lower_zero i k
            have hA : matMul n L U i k = A i k := by
              simpa [matMul] using hExact.product_eq i k
            change L_hat t i k - L i k = (U k k)⁻¹ *
              ((matMul n (L_hat t) (U_hat t) i k - A i k) -
                (higham9_2_rectPrefixDot (L_hat t) (U_hat t) i k k -
                  higham9_2_rectPrefixDot L U i k k) -
                L_hat t i k * (U_hat t k k - U k k))
            rw [hhat, ← hA, hexact]
            field_simp [hpiv k]
            ring
        exact ⟨hUcurrent, hLcurrent⟩
  have hall := hstage n (Nat.le_refl n)
  constructor
  · intro i j
    exact hall.2 j j.isLt i
  · intro i j
    exact hall.1 i i.isLt j

/-- Specialization of the operational factor-proximity theorem to the source
family. -/
theorem ch14ext_cor147Source_factorProximity_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0) :
    Ch14MatrixFamilyIsBigO l
        (fun t i j => F.L_hat t i j - L i j) (fun t => (F.model t).u) ∧
      Ch14MatrixFamilyIsBigO l
        (fun t i j => (F.initial t).matrix i j - U i j)
          (fun t => (F.model t).u) := by
  apply ch14ext_luBackward_factorProximity_isBigO F.model A L U F.L_hat
    (fun t => (F.initial t).matrix) F.unit_tendsto_zero F.lu_certificate
    F.valid_n F.L_hat_isBigO_one F.U_hat_isBigO_one hLU
  exact (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdet)

/-- Computed inverse proximity follows from upper-factor proximity and the
exact inverse identity; it is not a source-family field. -/
theorem ch14ext_cor147Source_inverseProximity_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (U U_inv : Fin n -> Fin n -> Real)
    (hUprox : Ch14MatrixFamilyIsBigO l
      (fun t i j => (F.initial t).matrix i j - U i j)
      (fun t => (F.model t).u))
    (hUinv : IsInverse n U U_inv) :
    Ch14MatrixFamilyIsBigO l
      (fun t i j => F.U_hat_inv t i j - U_inv i j)
      (fun t => (F.model t).u) := by
  let unit : ι -> Real := fun t => (F.model t).u
  have hfirst : Ch14MatrixFamilyIsBigO l
      (fun t => matMul n (F.U_hat_inv t)
        (fun i j => (F.initial t).matrix i j - U i j)) unit := by
    have h := ch14ext_matrixFamily_mul_isBigO
      (M := F.U_hat_inv)
      (N := fun t i j => (F.initial t).matrix i j - U i j)
      (f := fun _ : ι => (1 : Real)) (g := unit)
      F.U_hat_inv_isBigO_one hUprox
    simpa only [one_mul] using h
  have htriple : Ch14MatrixFamilyIsBigO l
      (fun t => matMul n
        (matMul n (F.U_hat_inv t)
          (fun i j => (F.initial t).matrix i j - U i j)) U_inv) unit := by
    have hfixed : Ch14MatrixFamilyIsBigO l
        (fun _ : ι => U_inv) (fun _ : ι => (1 : Real)) :=
      ch14ext_fixedMatrix_isBigOOne U_inv
    have h := ch14ext_matrixFamily_mul_isBigO
      (M := fun t => matMul n (F.U_hat_inv t)
        (fun i j => (F.initial t).matrix i j - U i j))
      (N := fun _ : ι => U_inv) (f := unit)
      (g := fun _ : ι => (1 : Real)) hfirst hfixed
    simpa only [mul_one] using h
  intro i j
  have hneg := (htriple i j).neg_left
  convert hneg using 1
  funext t
  exact congrFun (congrFun
    (ch14ext_inverseDifference_identity n (F.initial t).matrix U
      (F.U_hat_inv t) U_inv (F.computed_upper_inverse t).1 hUinv.2) i) j

noncomputable def ch14ext_cor147SourcePrintedX
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) :
    Fin n -> Fin n -> Real :=
  matMul n (absMatrix n (F.initial t).matrix)
    (absMatrix n (F.U_hat_inv t))

/-- The computed printed inverse product is `O(u)` close to its exact
counterpart, with both factor and inverse proximity already derived. -/
theorem ch14ext_cor147Source_printedX_difference_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) :
    Ch14MatrixFamilyIsBigO l
      (fun t i j => ch14ext_cor147SourcePrintedX F t i j -
        ch14ext_cor147WeakExactX n U U_inv i j)
      (fun t => (F.model t).u) := by
  have hprox := ch14ext_cor147Source_factorProximity_isBigO F L U hLU hdet
  have hInv := ch14ext_cor147Source_inverseProximity_isBigO F U U_inv
    hprox.2 hUinv
  have hUabs := ch14ext_matrixFamily_absDifference_isBigO U hprox.2
  have hInvabs := ch14ext_matrixFamily_absDifference_isBigO U_inv hInv
  have h := ch14ext_matrixFamily_productDifference_isBigO
    (M := fun t i j => |(F.initial t).matrix i j|)
    (N := fun t i j => |F.U_hat_inv t i j|)
    (absMatrix n U) (absMatrix n U_inv)
    (by simpa only [absMatrix] using hUabs)
    (by simpa only [absMatrix] using hInvabs)
    (matrixFamily_abs_isBigOOne F.U_hat_inv_isBigO_one)
  simpa only [ch14ext_cor147SourcePrintedX, ch14ext_cor147WeakExactX,
    absMatrix] using h

/-! ## Derived replacement of the source `Xabs` state -/

/-- Explicit source-accumulation correction in
`Xabs <= |Uhat||Uhat^-1| + c3 * correction`. -/
noncomputable def ch14ext_cor147SourceXCorrection
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) :
    Fin n -> Fin n -> Real :=
  let P := ch14ext_cor147SourcePabs F t
  let X := ch14ext_cor147SourceXabs F t
  let AU := absMatrix n (F.initial t).matrix
  let AUi := absMatrix n (F.U_hat_inv t)
  fun i j =>
    matMul n AU (matMul n (matMul n P AU) AUi) i j +
      matMul n (matMul n X AU) P i j

theorem ch14ext_cor147SourceXCorrection_nonneg
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) (i j : Fin n) :
    0 <= ch14ext_cor147SourceXCorrection F t i j := by
  have hP : forall a b : Fin n, 0 <= ch14ext_cor147SourcePabs F t a b := by
    intro a b
    exact gje_cumulative_product_abs_nonneg n
      (ch14ext_gjeSeqStages n (ch14ext_cor147SourceV F t))
      1 (1 + (n - 1)) a b
  have hX : forall a b : Fin n, 0 <= ch14ext_cor147SourceXabs F t a b := by
    intro a b
    exact ch14ext_gjeXabs_nonneg n
      (ch14ext_gjeSeqStages n (ch14ext_cor147SourceV F t))
      (ch14ext_cor147SourceQ F t) 1 (n - 1) a b
  have hmm : forall (M N : Fin n -> Fin n -> Real),
      (forall a b : Fin n, 0 <= M a b) ->
      (forall a b : Fin n, 0 <= N a b) ->
      forall a b : Fin n, 0 <= matMul n M N a b := by
    intro M N hM hN a b
    unfold matMul
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hM a k) (hN k b)
  have hAU : forall a b : Fin n, 0 <= absMatrix n (F.initial t).matrix a b :=
    fun a b => abs_nonneg _
  have hAUi : forall a b : Fin n, 0 <= absMatrix n (F.U_hat_inv t) a b :=
    fun a b => abs_nonneg _
  unfold ch14ext_cor147SourceXCorrection
  exact add_nonneg
    (hmm _ _ hAU (hmm _ _ (hmm _ _ hP hAU) hAUi) i j)
    (hmm _ _ (hmm _ _ hX hAU) hP i j)

/-- The internal `Xabs` replacement is derived from the two actual source
accumulation residuals.  No consistency premise is used. -/
theorem ch14ext_cor147Source_Xabs_le_printed_add_correction
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) (i j : Fin n) :
    ch14ext_cor147SourceXabs F t i j <=
      ch14ext_cor147SourcePrintedX F t i j +
        gje_c₃ (F.model t) n * ch14ext_cor147SourceXCorrection F t i j := by
  let P := ch14ext_cor147SourcePabs F t
  let Q := ch14ext_cor147SourceQ F t
  let X := ch14ext_cor147SourceXabs F t
  let AU := absMatrix n (F.initial t).matrix
  let AUi := absMatrix n (F.U_hat_inv t)
  let c := gje_c₃ (F.model t) n
  have hc : 0 <= c :=
    gje_c3_nonneg (F.model t) n F.dimension_pos (F.valid_three t)
  have hPcompare : forall a b : Fin n,
      P a b <= AUi a b + c * matMul n (matMul n P AU) AUi a b := by
    intro a b
    simpa [P, AU, AUi, c] using
      ch14ext_cor147Source_Pabs_le_abs_Uinv_add F t (F.U_hat_inv t)
        (F.computed_upper_inverse t).2 a b
  have hQcompare : forall a b : Fin n,
      |Q a b| <= AU a b + c * matMul n X AU a b := by
    intro a b
    have htri : |Q a b| <= |(F.initial t).matrix a b| +
        |Q a b - (F.initial t).matrix a b| := by
      calc
        |Q a b| = |(F.initial t).matrix a b +
            (Q a b - (F.initial t).matrix a b)| := by congr 1; ring
        _ <= _ := abs_add_le _ _
    have hq := ch14ext_cor147Source_Q_sub_U_bound F t a b
    simpa [Q, X, AU, c] using
      le_trans htri (add_le_add (le_refl |(F.initial t).matrix a b|) hq)
  have hXfirst : X i j <= matMul n AU P i j +
      c * matMul n (matMul n X AU) P i j := by
    unfold X ch14ext_cor147SourceXabs ch14ext_gjeXabs matMul absMatrix
    calc
      ∑ k : Fin n, |Q i k| * P k j <=
          ∑ k : Fin n, (AU i k + c * matMul n X AU i k) * P k j := by
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_right (hQcompare i k)
        exact gje_cumulative_product_abs_nonneg n
          (ch14ext_gjeSeqStages n (ch14ext_cor147SourceV F t))
          1 (1 + (n - 1)) k j
      _ = matMul n AU P i j + c * matMul n (matMul n X AU) P i j := by
        simp only [add_mul, Finset.sum_add_distrib]
        congr 1
        unfold matMul
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hAU_P : matMul n AU P i j <= matMul n AU AUi i j +
      c * matMul n AU (matMul n (matMul n P AU) AUi) i j := by
    unfold matMul
    calc
      ∑ k : Fin n, AU i k * P k j <=
          ∑ k : Fin n, AU i k *
            (AUi k j + c * matMul n (matMul n P AU) AUi k j) := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hPcompare k j) (abs_nonneg _)
      _ = (∑ k : Fin n, AU i k * AUi k j) +
          c * ∑ k : Fin n, AU i k * matMul n (matMul n P AU) AUi k j := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  unfold ch14ext_cor147SourceXCorrection ch14ext_cor147SourcePrintedX
  change X i j <= matMul n AU AUi i j +
    c * (matMul n AU (matMul n (matMul n P AU) AUi) i j +
      matMul n (matMul n X AU) P i j)
  nlinarith [hXfirst, hAU_P]

theorem ch14ext_cor147SourceXCorrection_isBigOOne
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) :
    MatrixFamilyIsBigOOne l (ch14ext_cor147SourceXCorrection F) := by
  have hP : MatrixFamilyIsBigOOne l (ch14ext_cor147SourcePabs F) := by
    simpa [ch14ext_cor147SourcePabs, ch14ext_cor147SourceV] using
      F.P_abs_isBigO_one
  have hX : MatrixFamilyIsBigOOne l (ch14ext_cor147SourceXabs F) := by
    simpa [ch14ext_cor147SourceXabs, ch14ext_cor147SourceQ,
      ch14ext_cor147SourceV] using F.X_abs_isBigO_one
  have hAU := matrixFamily_abs_isBigOOne F.U_hat_isBigO_one
  have hAUi := matrixFamily_abs_isBigOOne F.U_hat_inv_isBigO_one
  have hfirst := ch14ext_matrixFamily_mul_family_isBigOOne hAU
    (ch14ext_matrixFamily_mul_family_isBigOOne
      (ch14ext_matrixFamily_mul_family_isBigOOne hP hAU) hAUi)
  have hsecond := ch14ext_matrixFamily_mul_family_isBigOOne
    (ch14ext_matrixFamily_mul_family_isBigOOne hX hAU) hP
  intro i j
  simpa only [ch14ext_cor147SourceXCorrection] using (hfirst i j).add (hsecond i j)

/-- Action of the retained `Xabs` replacement correction on the residual
leading vector. -/
noncomputable def ch14ext_cor147SourceResidualEnvelopeCorrection
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) (i : Fin n) : Real :=
  matMulVec n (absMatrix n (F.L_hat t))
    (matMulVec n (ch14ext_cor147SourceXCorrection F t)
      (matMulVec n (absMatrix n (F.initial t).matrix)
        (absVec n (F.x_hat t)))) i

theorem ch14ext_cor147SourceResidualEnvelopeCorrection_isBigOOne
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) :
    VectorFamilyIsBigOOne l (ch14ext_cor147SourceResidualEnvelopeCorrection F) := by
  have hx := ch14ext_vectorFamily_abs_isBigOOne F.x_hat_isBigO_one
  have hU := matrixFamily_abs_isBigOOne F.U_hat_isBigO_one
  have hL := matrixFamily_abs_isBigOOne F.L_hat_isBigO_one
  have hUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hU hx
  have hCorr := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (ch14ext_cor147SourceXCorrection_isBigOOne F) hUx
  have hfinal := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hL hCorr
  simpa only [ch14ext_cor147SourceResidualEnvelopeCorrection] using hfinal

/-- One-sided replacement of the source residual leading object by the
computed printed inverse product. -/
theorem ch14ext_cor147Source_residualS2_le_printed_add_correction
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) (t : ι) (i : Fin n) :
    ch14ext_gjeResidualS2 n (F.L_hat t) (ch14ext_cor147SourceXabs F t)
        (F.initial t).matrix (F.x_hat t) i <=
      ch14ext_gjeResidualS2 n (F.L_hat t) (ch14ext_cor147SourcePrintedX F t)
        (F.initial t).matrix (F.x_hat t) i +
      gje_c₃ (F.model t) n *
        ch14ext_cor147SourceResidualEnvelopeCorrection F t i := by
  let X := ch14ext_cor147SourceXabs F t
  let PX := ch14ext_cor147SourcePrintedX F t
  let C := ch14ext_cor147SourceXCorrection F t
  let w := matMulVec n (absMatrix n (F.initial t).matrix) (absVec n (F.x_hat t))
  let c := gje_c₃ (F.model t) n
  have hw : forall j : Fin n, 0 <= w j := by
    intro j
    unfold w matMulVec absMatrix absVec
    exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hmid : forall a : Fin n,
      matMulVec n X w a <= matMulVec n PX w a + c * matMulVec n C w a := by
    intro a
    unfold matMulVec
    calc
      ∑ k : Fin n, X a k * w k <=
          ∑ k : Fin n, (PX a k + c * C a k) * w k := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right
          (ch14ext_cor147Source_Xabs_le_printed_add_correction F t a k)
          (hw k)
      _ = (∑ k : Fin n, PX a k * w k) +
          c * ∑ k : Fin n, C a k * w k := by
        simp only [add_mul, Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hLnonneg : forall a k : Fin n, 0 <= absMatrix n (F.L_hat t) a k :=
    fun a k => abs_nonneg _
  have houter := ch14ext_matMulVec_mono_nonneg n
    (absMatrix n (F.L_hat t)) (matMulVec n X w)
    (fun a => matMulVec n PX w a + c * matMulVec n C w a)
    hLnonneg hmid i
  have hXabs : absMatrix n X = X := by
    funext a k
    exact abs_of_nonneg (ch14ext_gjeXabs_nonneg n
      (ch14ext_gjeSeqStages n (ch14ext_cor147SourceV F t))
      (ch14ext_cor147SourceQ F t) 1 (n - 1) a k)
  have hPXnonneg : forall a k : Fin n, 0 <= PX a k := by
    intro a k
    unfold PX ch14ext_cor147SourcePrintedX matMul absMatrix
    exact Finset.sum_nonneg fun q _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hPXabs : absMatrix n PX = PX := by
    funext a k
    exact abs_of_nonneg (hPXnonneg a k)
  change matMulVec n (absMatrix n (F.L_hat t))
      (matMulVec n (absMatrix n X) w) i <=
    matMulVec n (absMatrix n (F.L_hat t))
        (matMulVec n (absMatrix n PX) w) i +
      c * ch14ext_cor147SourceResidualEnvelopeCorrection F t i
  rw [hXabs, hPXabs]
  calc
    matMulVec n (absMatrix n (F.L_hat t)) (matMulVec n X w) i <=
        matMulVec n (absMatrix n (F.L_hat t))
          (fun a => matMulVec n PX w a + c * matMulVec n C w a) i := houter
    _ = matMulVec n (absMatrix n (F.L_hat t)) (matMulVec n PX w) i +
        c * ch14ext_cor147SourceResidualEnvelopeCorrection F t i := by
      unfold matMulVec ch14ext_cor147SourceResidualEnvelopeCorrection
      change (∑ k : Fin n, absMatrix n (F.L_hat t) i k *
          ((∑ q : Fin n, PX k q * w q) + c * (∑ q : Fin n, C k q * w q))) =
        (∑ k : Fin n, absMatrix n (F.L_hat t) i k *
          (∑ q : Fin n, PX k q * w q)) +
        c * ∑ k : Fin n, absMatrix n (F.L_hat t) i k *
          (∑ q : Fin n, C k q * w q)
      calc
        _ = ∑ k : Fin n,
            (absMatrix n (F.L_hat t) i k * (∑ q : Fin n, PX k q * w q) +
              c * (absMatrix n (F.L_hat t) i k *
                (∑ q : Fin n, C k q * w q))) := by
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The residual object formed with the computed printed inverse product is
`O(u)` close to the exact row-dominant object. -/
theorem ch14ext_cor147Source_printedResidualLeading_difference_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        ch14ext_gjeResidualS2 n (F.L_hat t) (ch14ext_cor147SourcePrintedX F t)
            (F.initial t).matrix (F.x_hat t) i -
          ch14ext_gjeResidualS2 n L (ch14ext_cor147WeakExactX n U U_inv)
            U (F.x_hat t) i)
      (fun t => (F.model t).u) := by
  let unit : ι -> Real := fun t => (F.model t).u
  have hprox := ch14ext_cor147Source_factorProximity_isBigO F L U hLU hdet
  have hPXdiff := ch14ext_cor147Source_printedX_difference_isBigO
    F L U U_inv hLU hdet hUinv
  have hxabs := ch14ext_vectorFamily_abs_isBigOOne F.x_hat_isBigO_one
  have hUabsOne := matrixFamily_abs_isBigOOne F.U_hat_isBigO_one
  have hUabsDiff := ch14ext_matrixFamily_absDifference_isBigO U hprox.2
  have hUactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |(F.initial t).matrix i j|)
        (fun i => |F.x_hat t i|)) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hUabsOne hxabs
  have hUactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |(F.initial t).matrix a j|)
            (fun j => |F.x_hat t j|) i -
          matMulVec n (absMatrix n U) (fun j => |F.x_hat t j|) i) unit :=
    ch14ext_matrixVectorFamily_actionDifference_isBigO
      (M := fun t i j => |(F.initial t).matrix i j|) (absMatrix n U)
      (by simpa only [absMatrix] using hUabsDiff) hxabs
  have hPXOne : MatrixFamilyIsBigOOne l
      (ch14ext_cor147SourcePrintedX F) :=
    ch14ext_matrixFamily_mul_family_isBigOOne
      (matrixFamily_abs_isBigOOne F.U_hat_isBigO_one)
      (matrixFamily_abs_isBigOOne F.U_hat_inv_isBigO_one)
  have hPXabsDiff := ch14ext_matrixFamily_absDifference_isBigO
    (ch14ext_cor147WeakExactX n U U_inv) hPXdiff
  have hPXactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n
        (fun i j => |ch14ext_cor147SourcePrintedX F t i j|)
        (matMulVec n (fun i j => |(F.initial t).matrix i j|)
          (fun i => |F.x_hat t i|))) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne
      (matrixFamily_abs_isBigOOne hPXOne) hUactionOne
  have hPXactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |ch14ext_cor147SourcePrintedX F t a j|)
            (matMulVec n (fun a j => |(F.initial t).matrix a j|)
              (fun j => |F.x_hat t j|)) i -
          matMulVec n (absMatrix n (ch14ext_cor147WeakExactX n U U_inv))
            (matMulVec n (absMatrix n U) (fun j => |F.x_hat t j|)) i) unit :=
    ch14ext_matrixVectorFamily_productDifference_isBigO
      (M := fun t i j => |ch14ext_cor147SourcePrintedX F t i j|)
      (A := absMatrix n (ch14ext_cor147WeakExactX n U U_inv))
      (x := fun t => matMulVec n (fun i j => |(F.initial t).matrix i j|)
        (fun i => |F.x_hat t i|))
      (y := fun t => matMulVec n (absMatrix n U) (fun i => |F.x_hat t i|))
      (by simpa only [absMatrix] using hPXabsDiff) hUactionDiff hUactionOne
  have hLabsDiff := ch14ext_matrixFamily_absDifference_isBigO L hprox.1
  have hfinal := ch14ext_matrixVectorFamily_productDifference_isBigO
    (M := fun t i j => |F.L_hat t i j|) (A := absMatrix n L)
    (x := fun t => matMulVec n
      (fun i j => |ch14ext_cor147SourcePrintedX F t i j|)
      (matMulVec n (fun i j => |(F.initial t).matrix i j|)
        (fun i => |F.x_hat t i|)))
    (y := fun t => matMulVec n
      (absMatrix n (ch14ext_cor147WeakExactX n U U_inv))
      (matMulVec n (absMatrix n U) (fun i => |F.x_hat t i|)))
    (by simpa only [absMatrix] using hLabsDiff) hPXactionDiff hPXactionOne
  simpa only [ch14ext_gjeResidualS2, absMatrix, absVec] using hfinal

noncomputable def ch14ext_cor147SourceResidualLeadingCorrection
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real) (t : ι) (i : Fin n) : Real :=
  |ch14ext_gjeResidualS2 n (F.L_hat t) (ch14ext_cor147SourcePrintedX F t)
      (F.initial t).matrix (F.x_hat t) i -
    ch14ext_gjeResidualS2 n L (ch14ext_cor147WeakExactX n U U_inv)
      U (F.x_hat t) i| +
    gje_c₃ (F.model t) n * ch14ext_cor147SourceResidualEnvelopeCorrection F t i

theorem ch14ext_cor147SourceResidualLeadingCorrection_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) (i : Fin n) :
    (fun t => ch14ext_cor147SourceResidualLeadingCorrection F L U U_inv t i)
      =O[l] (fun t => (F.model t).u) := by
  have hdiff := (ch14ext_cor147Source_printedResidualLeading_difference_isBigO
    F L U U_inv hLU hdet hUinv i).norm_left
  have hc3 := ch14ext_gje_c3_family_isBigO_unit n F.model F.unit_tendsto_zero
  have henv := ch14ext_cor147SourceResidualEnvelopeCorrection_isBigOOne F i
  have hcorr : (fun t => gje_c₃ (F.model t) n *
      ch14ext_cor147SourceResidualEnvelopeCorrection F t i) =O[l]
        (fun t => (F.model t).u) := by
    simpa only [mul_one] using hc3.mul henv
  simpa only [ch14ext_cor147SourceResidualLeadingCorrection,
    Real.norm_eq_abs] using hdiff.add hcorr

theorem ch14ext_cor147Source_residualS2_le_exact_add_correction
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real) (t : ι) (i : Fin n) :
    ch14ext_gjeResidualS2 n (F.L_hat t) (ch14ext_cor147SourceXabs F t)
        (F.initial t).matrix (F.x_hat t) i <=
      ch14ext_gjeResidualS2 n L (ch14ext_cor147WeakExactX n U U_inv)
          U (F.x_hat t) i +
        ch14ext_cor147SourceResidualLeadingCorrection F L U U_inv t i := by
  have hsource := ch14ext_cor147Source_residualS2_le_printed_add_correction F t i
  have habs := le_abs_self
    (ch14ext_gjeResidualS2 n (F.L_hat t) (ch14ext_cor147SourcePrintedX F t)
        (F.initial t).matrix (F.x_hat t) i -
      ch14ext_gjeResidualS2 n L (ch14ext_cor147WeakExactX n U U_inv)
        U (F.x_hat t) i)
  unfold ch14ext_cor147SourceResidualLeadingCorrection
  linarith

/-! ## Source-facing Corollary 14.7 residual closure -/

noncomputable def ch14ext_cor147SourceResidualRemainder
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real) (t : ι) (i : Fin n) : Real :=
  8 * (n : Real) * (F.model t).u *
      ch14ext_cor147SourceResidualLeadingCorrection F L U U_inv t i +
    ch14ext_gjeResidualHigherOrder n (F.model t) (F.L_hat t)
      (ch14ext_cor147SourceXabs F t) (F.initial t).matrix
      (F.initial t).rhs (F.x_hat t) i

theorem ch14ext_cor147SourceResidualRemainder_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) (i : Fin n) :
    (fun t => ch14ext_cor147SourceResidualRemainder F L U U_inv t i)
      =O[l] (fun t => (F.model t).u ^ 2) := by
  let unit : ι -> Real := fun t => (F.model t).u
  have hu : unit =O[l] unit := Asymptotics.isBigO_refl _ l
  have hlead := ch14ext_cor147SourceResidualLeadingCorrection_isBigO
    F L U U_inv hLU hdet hUinv i
  have hscaled :
      (fun t => 8 * (n : Real) * unit t *
        ch14ext_cor147SourceResidualLeadingCorrection F L U U_inv t i)
        =O[l] (fun t => unit t ^ 2) := by
    simpa only [pow_two, mul_assoc] using
      (hu.mul hlead).const_mul_left (8 * (n : Real))
  have hhigher := ch14ext_gjeResidualHigherOrder_family_isBigO n F.model
    F.L_hat (ch14ext_cor147SourceXabs F) (fun t => (F.initial t).matrix)
    (fun t => (F.initial t).rhs) F.x_hat F.unit_tendsto_zero
    F.L_hat_isBigO_one (by simpa [ch14ext_cor147SourceXabs,
      ch14ext_cor147SourceQ, ch14ext_cor147SourceV] using F.X_abs_isBigO_one)
    F.U_hat_isBigO_one F.y_isBigO_one F.x_hat_isBigO_one i
  simpa only [ch14ext_cor147SourceResidualRemainder, unit] using
    hscaled.add hhigher

theorem ch14ext_cor147Source_residual_bound
    {ι : Type*} {l : Filter ι} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hUinv : IsInverse n U U_inv) :
    forall t i,
      |b i - matMulVec n A (F.x_hat t) i| <=
        32 * (n : Real) ^ 2 * (F.model t).u *
            Finset.sum Finset.univ (fun j : Fin n => |A i j|) *
            Finset.sum Finset.univ (fun j : Fin n => |F.x_hat t j|) +
          ch14ext_cor147SourceResidualRemainder F L U U_inv t i := by
  intro t i
  have hsource := ch14ext_cor147Source_overall_residual_14_31 F t i
  have hreplace := ch14ext_cor147Source_residualS2_le_exact_add_correction
    F L U U_inv t i
  have hcoef : 0 <= 8 * (n : Real) * (F.model t).u :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
      (F.model t).u_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hreplace hcoef
  have hURow := ch14ext_exactNoPivotLU_upper_higham8_8 A L U hRow hdet hLU
  have hlead := ch14ext_cor147_residual_leading_object_le
    n (F.model t) A L U U_inv (F.x_hat t) hLU hURow hUinv i
  calc
    |b i - matMulVec n A (F.x_hat t) i| <=
        8 * (n : Real) * (F.model t).u *
            ch14ext_gjeResidualS2 n (F.L_hat t)
              (ch14ext_cor147SourceXabs F t) (F.initial t).matrix
              (F.x_hat t) i +
          ch14ext_gjeResidualHigherOrder n (F.model t) (F.L_hat t)
            (ch14ext_cor147SourceXabs F t) (F.initial t).matrix
            (F.initial t).rhs (F.x_hat t) i := hsource
    _ <= 8 * (n : Real) * (F.model t).u *
          (ch14ext_gjeResidualS2 n L (ch14ext_cor147WeakExactX n U U_inv)
              U (F.x_hat t) i +
            ch14ext_cor147SourceResidualLeadingCorrection F L U U_inv t i) +
            ch14ext_gjeResidualHigherOrder n (F.model t) (F.L_hat t)
            (ch14ext_cor147SourceXabs F t) (F.initial t).matrix
            (F.initial t).rhs (F.x_hat t) i := by
      exact add_le_add hscaled (le_refl _)
    _ = 8 * (n : Real) * (F.model t).u *
          ch14ext_gjeResidualS2 n L (ch14ext_cor147WeakExactX n U U_inv)
            U (F.x_hat t) i +
          ch14ext_cor147SourceResidualRemainder F L U U_inv t i := by
      unfold ch14ext_cor147SourceResidualRemainder
      ring
    _ <= 32 * (n : Real) ^ 2 * (F.model t).u *
            Finset.sum Finset.univ (fun j : Fin n => |A i j|) *
            Finset.sum Finset.univ (fun j : Fin n => |F.x_hat t j|) +
          ch14ext_cor147SourceResidualRemainder F L U U_inv t i := by
      simpa only [ch14ext_cor147WeakExactX, add_comm] using
        add_le_add_right hlead
          (ch14ext_cor147SourceResidualRemainder F L U U_inv t i)

theorem ch14ext_cor147Source_residual_vanishing_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hUinv : IsInverse n U U_inv) :
    (forall t i,
      |b i - matMulVec n A (F.x_hat t) i| <=
        32 * (n : Real) ^ 2 * (F.model t).u *
            Finset.sum Finset.univ (fun j : Fin n => |A i j|) *
            Finset.sum Finset.univ (fun j : Fin n => |F.x_hat t j|) +
          ch14ext_cor147SourceResidualRemainder F L U U_inv t i) ∧
      forall i,
        (fun t => ch14ext_cor147SourceResidualRemainder F L U U_inv t i)
          =O[l] (fun t => (F.model t).u ^ 2) := by
  constructor
  · exact ch14ext_cor147Source_residual_bound F L U U_inv
      hRow hdet hLU hUinv
  · exact ch14ext_cor147SourceResidualRemainder_isBigO
      F L U U_inv hLU hdet hUinv

/-! ## Computed versus exact forward leading objects -/

theorem ch14ext_cor147Source_forwardT1_difference_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
            (F.x_hat t) i -
          ch14ext_gjeForwardT1 n A_inv L U (F.x_hat t) i)
      (fun t => (F.model t).u) := by
  let unit : ι -> Real := fun t => (F.model t).u
  have hprox := ch14ext_cor147Source_factorProximity_isBigO F L U hLU hdet
  have hxabs := ch14ext_vectorFamily_abs_isBigOOne F.x_hat_isBigO_one
  have hUabsOne := matrixFamily_abs_isBigOOne F.U_hat_isBigO_one
  have hUabsDiff := ch14ext_matrixFamily_absDifference_isBigO U hprox.2
  have hUactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |(F.initial t).matrix i j|)
        (fun i => |F.x_hat t i|)) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hUabsOne hxabs
  have hUactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |(F.initial t).matrix a j|)
            (fun j => |F.x_hat t j|) i -
          matMulVec n (absMatrix n U) (fun j => |F.x_hat t j|) i) unit :=
    ch14ext_matrixVectorFamily_actionDifference_isBigO
      (M := fun t i j => |(F.initial t).matrix i j|) (absMatrix n U)
      (by simpa only [absMatrix] using hUabsDiff) hxabs
  have hLabsOne := matrixFamily_abs_isBigOOne F.L_hat_isBigO_one
  have hLabsDiff := ch14ext_matrixFamily_absDifference_isBigO L hprox.1
  have hLactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |F.L_hat t i j|)
        (matMulVec n (fun i j => |(F.initial t).matrix i j|)
          (fun i => |F.x_hat t i|))) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hLabsOne hUactionOne
  have hLactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |F.L_hat t a j|)
            (matMulVec n (fun a j => |(F.initial t).matrix a j|)
              (fun j => |F.x_hat t j|)) i -
          matMulVec n (absMatrix n L)
            (matMulVec n (absMatrix n U) (fun j => |F.x_hat t j|)) i) unit :=
    ch14ext_matrixVectorFamily_productDifference_isBigO
      (M := fun t i j => |F.L_hat t i j|) (A := absMatrix n L)
      (x := fun t => matMulVec n (fun i j => |(F.initial t).matrix i j|)
        (fun i => |F.x_hat t i|))
      (y := fun t => matMulVec n (absMatrix n U) (fun i => |F.x_hat t i|))
      (by simpa only [absMatrix] using hLabsDiff) hUactionDiff hUactionOne
  have hfinal := ch14ext_fixedMatrix_vectorDifference_isBigO
    (absMatrix n A_inv) hLactionDiff
  simpa only [ch14ext_gjeForwardT1, absMatrix, absVec] using hfinal

theorem ch14ext_cor147Source_forwardT2_difference_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
            (F.initial t).matrix (F.x_hat t) i -
          ch14ext_gjeForwardT2 n (absMatrix n U_inv) U (F.x_hat t) i)
      (fun t => (F.model t).u) := by
  let unit : ι -> Real := fun t => (F.model t).u
  have hprox := ch14ext_cor147Source_factorProximity_isBigO F L U hLU hdet
  have hInv := ch14ext_cor147Source_inverseProximity_isBigO F U U_inv
    hprox.2 hUinv
  have hxabs := ch14ext_vectorFamily_abs_isBigOOne F.x_hat_isBigO_one
  have hUabsOne := matrixFamily_abs_isBigOOne F.U_hat_isBigO_one
  have hUabsDiff := ch14ext_matrixFamily_absDifference_isBigO U hprox.2
  have hUactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |(F.initial t).matrix i j|)
        (fun i => |F.x_hat t i|)) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hUabsOne hxabs
  have hUactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |(F.initial t).matrix a j|)
            (fun j => |F.x_hat t j|) i -
          matMulVec n (absMatrix n U) (fun j => |F.x_hat t j|) i) unit :=
    ch14ext_matrixVectorFamily_actionDifference_isBigO
      (M := fun t i j => |(F.initial t).matrix i j|) (absMatrix n U)
      (by simpa only [absMatrix] using hUabsDiff) hxabs
  have hInvAbsDiff := ch14ext_matrixFamily_absDifference_isBigO U_inv hInv
  have hfinal := ch14ext_matrixVectorFamily_productDifference_isBigO
    (M := fun t i j => |F.U_hat_inv t i j|) (A := absMatrix n U_inv)
    (x := fun t => matMulVec n (fun i j => |(F.initial t).matrix i j|)
      (fun i => |F.x_hat t i|))
    (y := fun t => matMulVec n (absMatrix n U) (fun i => |F.x_hat t i|))
    (by simpa only [absMatrix] using hInvAbsDiff) hUactionDiff hUactionOne
  simpa only [ch14ext_gjeForwardT2, absMatrix, absVec] using hfinal

theorem ch14ext_cor147Source_forwardCore_difference_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        (ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
            (F.x_hat t) i +
          3 * ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
            (F.initial t).matrix (F.x_hat t) i) -
        (ch14ext_gjeForwardT1 n A_inv L U (F.x_hat t) i +
          3 * ch14ext_gjeForwardT2 n (absMatrix n U_inv) U
            (F.x_hat t) i))
      (fun t => (F.model t).u) := by
  intro i
  have h1 := ch14ext_cor147Source_forwardT1_difference_isBigO
    F A_inv L U hLU hdet i
  have h2 := ch14ext_cor147Source_forwardT2_difference_isBigO
    F L U U_inv hLU hdet hUinv i
  have h := h1.add (h2.const_mul_left (3 : Real))
  convert h using 1
  funext t
  ring

/-! ## Explicit quadratic forward remainders -/

noncomputable def ch14ext_cor147SourceForwardVectorRemainder
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real) (t : ι) (i : Fin n) : Real :=
  (2 * (n : Real) * (F.model t).u *
        ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
          (F.x_hat t) i +
      6 * (n : Real) * (F.model t).u *
        ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
          (F.initial t).matrix (F.x_hat t) i) -
    (2 * (n : Real) * (F.model t).u *
        ch14ext_gjeForwardT1 n A_inv L U (F.x_hat t) i +
      6 * (n : Real) * (F.model t).u *
        ch14ext_gjeForwardT2 n (absMatrix n U_inv) U (F.x_hat t) i) +
    ch14ext_gjeForwardLiteralHigherOrder n (F.model t) A_inv
      (F.L_hat t) (F.initial t).matrix (ch14ext_cor147SourcePabs F t)
      (F.U_hat_inv t) (F.z t) (F.initial t).rhs (F.x_hat t) i

theorem ch14ext_cor147SourceForwardVectorRemainder_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) :
    Ch14VectorFamilyIsBigO l
      (fun t i => ch14ext_cor147SourceForwardVectorRemainder
        F A_inv L U U_inv t i)
      (fun t => (F.model t).u ^ 2) := by
  let unit : ι -> Real := fun t => (F.model t).u
  have hu : unit =O[l] unit := Asymptotics.isBigO_refl _ l
  have hcore := ch14ext_cor147Source_forwardCore_difference_isBigO
    F A_inv L U U_inv hLU hdet hUinv
  intro i
  have hscaled := (hu.mul (hcore i)).const_mul_left (2 * (n : Real))
  have hlead :
      (fun t =>
        (2 * (n : Real) * unit t *
              ch14ext_gjeForwardT1 n A_inv (F.L_hat t)
                (F.initial t).matrix (F.x_hat t) i +
            6 * (n : Real) * unit t *
              ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
                (F.initial t).matrix (F.x_hat t) i) -
          (2 * (n : Real) * unit t *
              ch14ext_gjeForwardT1 n A_inv L U (F.x_hat t) i +
            6 * (n : Real) * unit t *
              ch14ext_gjeForwardT2 n (absMatrix n U_inv) U
                (F.x_hat t) i)) =O[l] (fun t => unit t ^ 2) := by
    convert hscaled using 1 <;> funext t <;> ring
  have hhigher := ch14ext_gjeForwardLiteralHigherOrder_family_isBigO n
    F.model (fun _ : ι => A_inv) F.L_hat (fun t => (F.initial t).matrix)
    (ch14ext_cor147SourcePabs F) F.U_hat_inv F.z
    (fun t => (F.initial t).rhs) F.x_hat F.unit_tendsto_zero
    (ch14ext_fixedMatrix_family_isBigOOne l A_inv) F.L_hat_isBigO_one
    F.U_hat_isBigO_one (by simpa [ch14ext_cor147SourcePabs,
      ch14ext_cor147SourceV] using F.P_abs_isBigO_one)
    F.U_hat_inv_isBigO_one F.z_isBigO_one F.y_isBigO_one
    F.x_hat_isBigO_one i
  simpa only [ch14ext_cor147SourceForwardVectorRemainder, unit] using
    hlead.add hhigher

noncomputable def ch14ext_cor147SourceForwardRelativeRemainder
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real)
    (x : Fin n -> Real) (t : ι) : Real :=
  infNormVec (fun i =>
    ch14ext_cor147SourceForwardVectorRemainder F A_inv L U U_inv t i) /
      infNormVec x

theorem ch14ext_cor147SourceForwardRelativeRemainder_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real)
    (x : Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) :
    (fun t => ch14ext_cor147SourceForwardRelativeRemainder
      F A_inv L U U_inv x t) =O[l] (fun t => (F.model t).u ^ 2) := by
  have hvec := ch14ext_cor147SourceForwardVectorRemainder_isBigO
    F A_inv L U U_inv hLU hdet hUinv
  have hnorm := ch14ext_vectorFamily_infNorm_isBigO hvec
  have hscaled := hnorm.const_mul_left (infNormVec x)⁻¹
  simpa only [ch14ext_cor147SourceForwardRelativeRemainder,
    div_eq_mul_inv, mul_comm] using hscaled

noncomputable def ch14ext_cor147SourceForwardLeadingCoefficient
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv : Fin n -> Fin n -> Real) (t : ι) : Real :=
  4 * (n : Real) ^ 3 * (F.model t).u *
    (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.dimension_pos) A A_inv + 3)

theorem ch14ext_cor147SourceForwardLeadingCoefficient_tendsto_zero
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv : Fin n -> Fin n -> Real) :
    Tendsto (ch14ext_cor147SourceForwardLeadingCoefficient F A_inv) l (𝓝 0) := by
  let K : Real := 4 * (n : Real) ^ 3 *
    (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.dimension_pos) A A_inv + 3)
  have h := F.unit_tendsto_zero.const_mul K
  convert h using 1
  · funext t
    dsimp [ch14ext_cor147SourceForwardLeadingCoefficient, K]
    ring
  · simp

theorem ch14ext_cor147SourceForwardLeadingCoefficient_nonneg
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv : Fin n -> Fin n -> Real) (t : ι) :
    0 <= ch14ext_cor147SourceForwardLeadingCoefficient F A_inv t := by
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one F.dimension_pos
  have hk := kappaInf_nonneg n hn A A_inv
  have hu := (F.model t).u_nonneg
  unfold ch14ext_cor147SourceForwardLeadingCoefficient
  positivity

noncomputable def ch14ext_cor147SourceForwardPrintedRemainder
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real)
    (x : Fin n -> Real) (t : ι) : Real :=
  let C := ch14ext_cor147SourceForwardLeadingCoefficient F A_inv t
  C ^ 2 / (1 - C) +
    ch14ext_cor147SourceForwardRelativeRemainder F A_inv L U U_inv x t /
      (1 - C)

theorem ch14ext_cor147SourceForwardPrintedRemainder_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real)
    (x : Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) :
    (fun t => ch14ext_cor147SourceForwardPrintedRemainder
      F A_inv L U U_inv x t) =O[l] (fun t => (F.model t).u ^ 2) := by
  let unit : ι -> Real := fun t => (F.model t).u
  let C : ι -> Real := ch14ext_cor147SourceForwardLeadingCoefficient F A_inv
  let rho : ι -> Real := fun t =>
    ch14ext_cor147SourceForwardRelativeRemainder F A_inv L U U_inv x t
  let K : Real := 4 * (n : Real) ^ 3 *
    (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.dimension_pos) A A_inv + 3)
  have hCeq : C = fun t => K * unit t := by
    funext t
    dsimp [C, K, unit, ch14ext_cor147SourceForwardLeadingCoefficient]
    ring
  have hunit : unit =O[l] unit := Asymptotics.isBigO_refl _ l
  have hC : C =O[l] unit := by
    rw [hCeq]
    exact hunit.const_mul_left K
  have hCsq : (fun t => C t ^ 2) =O[l] (fun t => unit t ^ 2) := by
    simpa only [pow_two] using hC.mul hC
  have hCzero : Tendsto C l (𝓝 0) := by
    simpa only [C] using
      ch14ext_cor147SourceForwardLeadingCoefficient_tendsto_zero F A_inv
  have hden : Tendsto (fun t => 1 - C t) l (𝓝 1) := by
    simpa using hCzero.const_sub 1
  have hinvOne : (fun t => (1 - C t)⁻¹) =O[l]
      (fun _ : ι => (1 : Real)) := by
    have hinv : Tendsto (fun t => (1 - C t)⁻¹) l (𝓝 (1 : Real)) := by
      simpa using hden.inv₀ one_ne_zero
    exact hinv.isBigO_one Real
  have hterm1 : (fun t => C t ^ 2 / (1 - C t)) =O[l]
      (fun t => unit t ^ 2) := by
    simpa only [div_eq_mul_inv, mul_one] using hCsq.mul hinvOne
  have hrho : rho =O[l] (fun t => unit t ^ 2) := by
    simpa only [rho, unit] using
      ch14ext_cor147SourceForwardRelativeRemainder_isBigO
        F A_inv L U U_inv x hLU hdet hUinv
  have hterm2 : (fun t => rho t / (1 - C t)) =O[l]
      (fun t => unit t ^ 2) := by
    simpa only [div_eq_mul_inv, mul_one] using hrho.mul hinvOne
  simpa only [ch14ext_cor147SourceForwardPrintedRemainder, C, rho, unit] using
    hterm1.add hterm2

/-! ## Source-facing Corollary 14.7 forward closure -/

/-- Intermediate relative bound with the computed-solution norm ratio. -/
theorem ch14ext_cor147Source_forward_bound
    {ι : Type*} {l : Filter ι} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real) (x : Fin n -> Real)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hAinv : IsInverse n A A_inv)
    (hUinv : IsInverse n U U_inv)
    (hExact : forall i, matMulVec n A x i = b i)
    (hxpos : 0 < infNormVec x) :
    forall t,
      infNormVec (fun i => x i - F.x_hat t i) / infNormVec x <=
        4 * (n : Real) ^ 3 * (F.model t).u *
            (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.dimension_pos)
              A A_inv + 3) *
            (infNormVec (F.x_hat t) / infNormVec x) +
          ch14ext_cor147SourceForwardRelativeRemainder
            F A_inv L U U_inv x t := by
  intro t
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one F.dimension_pos
  have hconcrete := ch14ext_cor147Source_overall_forward_14_32
    F t A_inv x hAinv.1 hExact
  have hURow := ch14ext_exactNoPivotLU_upper_higham8_8 A L U hRow hdet hLU
  have hFactProduct : LUFactSpec n
      (ch14ext_cor147ComputedProduct n L U) L U := by
    exact {
      L_diag := hLU.L_diag
      L_upper_zero := hLU.L_upper_zero
      U_lower_zero := hLU.U_lower_zero
      product_eq := by intro i j; rfl
    }
  have hProductEq : ch14ext_cor147ComputedProduct n L U = A := by
    funext i j
    simpa only [ch14ext_cor147ComputedProduct, matMul] using hLU.product_eq i j
  have hProductNorm :
      infNorm (ch14ext_cor147ComputedProduct n L U) <= infNorm A / (1 : Real) := by
    rw [hProductEq, div_one]
  have hExactLead := ch14ext_cor147_forward_leading_infNorm_le
    n (F.model t) hn A A_inv L U U_inv (F.x_hat t)
    hFactProduct hURow hUinv (1 : Real) zero_lt_one hProductNorm
  let exactLead : Fin n -> Real := fun i =>
    2 * (n : Real) * (F.model t).u *
        ch14ext_gjeForwardT1 n A_inv L U (F.x_hat t) i +
      6 * (n : Real) * (F.model t).u *
        ch14ext_gjeForwardT2 n (absMatrix n U_inv) U (F.x_hat t) i
  let rem : Fin n -> Real := fun i =>
    ch14ext_cor147SourceForwardVectorRemainder F A_inv L U U_inv t i
  have hpoint : forall i, |x i - F.x_hat t i| <= exactLead i + rem i := by
    intro i
    calc
      |x i - F.x_hat t i| <=
          2 * (n : Real) * (F.model t).u *
              ch14ext_gjeForwardT1 n A_inv (F.L_hat t)
                (F.initial t).matrix (F.x_hat t) i +
            6 * (n : Real) * (F.model t).u *
              ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
                (F.initial t).matrix (F.x_hat t) i +
            ch14ext_gjeForwardLiteralHigherOrder n (F.model t) A_inv
              (F.L_hat t) (F.initial t).matrix (ch14ext_cor147SourcePabs F t)
              (F.U_hat_inv t) (F.z t) (F.initial t).rhs (F.x_hat t) i :=
        hconcrete i
      _ = exactLead i + rem i := by
        dsimp [exactLead, rem]
        unfold ch14ext_cor147SourceForwardVectorRemainder
        ring
  have hnormSplit : infNormVec (fun i => x i - F.x_hat t i) <=
      infNormVec exactLead + infNormVec rem := by
    apply infNormVec_le_of_abs_le
    · intro i
      calc
        |x i - F.x_hat t i| <= exactLead i + rem i := hpoint i
        _ <= |exactLead i| + |rem i| :=
          add_le_add (le_abs_self _) (le_abs_self _)
        _ <= infNormVec exactLead + infNormVec rem :=
          add_le_add (abs_le_infNormVec exactLead i) (abs_le_infNormVec rem i)
    · exact add_nonneg (infNormVec_nonneg exactLead) (infNormVec_nonneg rem)
  have hlead : infNormVec exactLead <=
      4 * (n : Real) ^ 3 * (F.model t).u *
        (kappaInf n hn A A_inv + 3) * infNormVec (F.x_hat t) := by
    simpa only [exactLead, div_one] using hExactLead
  have hnorm : infNormVec (fun i => x i - F.x_hat t i) <=
      4 * (n : Real) ^ 3 * (F.model t).u *
          (kappaInf n hn A A_inv + 3) * infNormVec (F.x_hat t) +
        infNormVec rem :=
    le_trans hnormSplit (add_le_add hlead (le_refl _))
  calc
    infNormVec (fun i => x i - F.x_hat t i) / infNormVec x <=
        (4 * (n : Real) ^ 3 * (F.model t).u *
            (kappaInf n hn A A_inv + 3) * infNormVec (F.x_hat t) +
          infNormVec rem) / infNormVec x :=
      div_le_div_of_nonneg_right hnorm hxpos.le
    _ = 4 * (n : Real) ^ 3 * (F.model t).u *
            (kappaInf n hn A A_inv + 3) *
            (infNormVec (F.x_hat t) / infNormVec x) +
          ch14ext_cor147SourceForwardRelativeRemainder
            F A_inv L U U_inv x t := by
      rw [add_div]
      unfold ch14ext_cor147SourceForwardRelativeRemainder
      dsimp [rem]
      ring

theorem ch14ext_cor147Source_forward_printed_bound_of_coefficient_lt_one
    {ι : Type*} {l : Filter ι} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real) (x : Fin n -> Real)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hAinv : IsInverse n A A_inv)
    (hUinv : IsInverse n U U_inv)
    (hExact : forall i, matMulVec n A x i = b i)
    (hxpos : 0 < infNormVec x) (t : ι)
    (hsmall : ch14ext_cor147SourceForwardLeadingCoefficient F A_inv t < 1) :
    infNormVec (fun i => x i - F.x_hat t i) / infNormVec x <=
      4 * (n : Real) ^ 3 * (F.model t).u *
          (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.dimension_pos)
            A A_inv + 3) +
        ch14ext_cor147SourceForwardPrintedRemainder
          F A_inv L U U_inv x t := by
  let e : Real := infNormVec (fun i => x i - F.x_hat t i) / infNormVec x
  let ratio : Real := infNormVec (F.x_hat t) / infNormVec x
  let rho : Real :=
    ch14ext_cor147SourceForwardRelativeRemainder F A_inv L U U_inv x t
  let C : Real := ch14ext_cor147SourceForwardLeadingCoefficient F A_inv t
  have hbase : e <= C * ratio + rho := by
    simpa only [e, ratio, rho, C,
      ch14ext_cor147SourceForwardLeadingCoefficient] using
      ch14ext_cor147Source_forward_bound F A_inv L U U_inv x hRow hdet
        hLU hAinv hUinv hExact hxpos t
  have hratio : ratio <= 1 + e := by
    dsimp only [ratio, e]
    apply (div_le_iff₀ hxpos).2
    calc
      infNormVec (F.x_hat t) <=
          infNormVec x + infNormVec (fun i => x i - F.x_hat t i) :=
        ch14ext_infNormVec_approx_le_exact_add_error x (F.x_hat t)
      _ = (1 + infNormVec (fun i => x i - F.x_hat t i) / infNormVec x) *
          infNormVec x := by
        field_simp [hxpos.ne']
  have hCnonneg : 0 <= C :=
    ch14ext_cor147SourceForwardLeadingCoefficient_nonneg F A_inv t
  have hraw : e <= C * (1 + e) + rho :=
    le_trans hbase (add_le_add
      (mul_le_mul_of_nonneg_left hratio hCnonneg) (le_refl rho))
  have hdenpos : 0 < 1 - C := sub_pos.mpr hsmall
  have hmult : e * (1 - C) <= C + rho := by
    nlinarith [hraw]
  have hdiv : e <= (C + rho) / (1 - C) :=
    (le_div_iff₀ hdenpos).2 hmult
  have hdecomp : (C + rho) / (1 - C) =
      C + (C ^ 2 / (1 - C) + rho / (1 - C)) := by
    field_simp [ne_of_gt hdenpos]
    ring
  calc
    infNormVec (fun i => x i - F.x_hat t i) / infNormVec x = e := rfl
    _ <= (C + rho) / (1 - C) := hdiv
    _ = C + (C ^ 2 / (1 - C) + rho / (1 - C)) := hdecomp
    _ = 4 * (n : Real) ^ 3 * (F.model t).u *
          (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.dimension_pos)
            A A_inv + 3) +
        ch14ext_cor147SourceForwardPrintedRemainder
          F A_inv L U U_inv x t := by rfl

theorem ch14ext_cor147Source_forward_printed_eventually
    {ι : Type*} {l : Filter ι} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real) (x : Fin n -> Real)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hAinv : IsInverse n A A_inv)
    (hUinv : IsInverse n U U_inv)
    (hExact : forall i, matMulVec n A x i = b i)
    (hxpos : 0 < infNormVec x) :
    ∀ᶠ t in l,
      infNormVec (fun i => x i - F.x_hat t i) / infNormVec x <=
        4 * (n : Real) ^ 3 * (F.model t).u *
            (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.dimension_pos)
              A A_inv + 3) +
          ch14ext_cor147SourceForwardPrintedRemainder
            F A_inv L U U_inv x t := by
  have hzero := ch14ext_cor147SourceForwardLeadingCoefficient_tendsto_zero
    F A_inv
  have hsmall : ∀ᶠ t in l,
      ch14ext_cor147SourceForwardLeadingCoefficient F A_inv t < 1 :=
    (tendsto_order.1 hzero).2 1 zero_lt_one
  filter_upwards [hsmall] with t ht
  exact ch14ext_cor147Source_forward_printed_bound_of_coefficient_lt_one
    F A_inv L U U_inv x hRow hdet hLU hAinv hUinv hExact hxpos t ht

theorem ch14ext_cor147Source_forward_vanishing_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real) (x : Fin n -> Real)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hAinv : IsInverse n A A_inv)
    (hUinv : IsInverse n U U_inv)
    (hExact : forall i, matMulVec n A x i = b i)
    (hxpos : 0 < infNormVec x) :
    (∀ᶠ t in l,
      infNormVec (fun i => x i - F.x_hat t i) / infNormVec x <=
        4 * (n : Real) ^ 3 * (F.model t).u *
            (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.dimension_pos)
              A A_inv + 3) +
          ch14ext_cor147SourceForwardPrintedRemainder
            F A_inv L U U_inv x t) ∧
      (fun t => ch14ext_cor147SourceForwardPrintedRemainder
        F A_inv L U U_inv x t) =O[l] (fun t => (F.model t).u ^ 2) := by
  constructor
  · exact ch14ext_cor147Source_forward_printed_eventually
      F A_inv L U U_inv x hRow hdet hLU hAinv hUinv hExact hxpos
  · exact ch14ext_cor147SourceForwardPrintedRemainder_isBigO
      F A_inv L U U_inv x hLU hdet hUinv

/-- **Higham Corollary 14.7, strict source-facing family endpoint.**

The source-active Algorithm 14.4 trace supplies all second-stage recurrence
bounds.  Factor proximity and the `Xabs` replacement are derived above from
the operational certificates.  The nontrivial-filter instance is explicit,
so neither eventual statement nor any `O(u^2)` claim can be vacuous. -/
theorem ch14ext_cor147Source_vanishing_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real) (x : Fin n -> Real)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hAinv : IsInverse n A A_inv)
    (hUinv : IsInverse n U U_inv)
    (hExact : forall i, matMulVec n A x i = b i)
    (hxpos : 0 < infNormVec x) :
    ((forall t i,
      |b i - matMulVec n A (F.x_hat t) i| <=
        32 * (n : Real) ^ 2 * (F.model t).u *
            Finset.sum Finset.univ (fun j : Fin n => |A i j|) *
            Finset.sum Finset.univ (fun j : Fin n => |F.x_hat t j|) +
          ch14ext_cor147SourceResidualRemainder F L U U_inv t i) ∧
      (forall i,
        (fun t => ch14ext_cor147SourceResidualRemainder F L U U_inv t i)
          =O[l] (fun t => (F.model t).u ^ 2))) ∧
    ((∀ᶠ t in l,
      infNormVec (fun i => x i - F.x_hat t i) / infNormVec x <=
        4 * (n : Real) ^ 3 * (F.model t).u *
            (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.dimension_pos)
              A A_inv + 3) +
          ch14ext_cor147SourceForwardPrintedRemainder
            F A_inv L U U_inv x t) ∧
      (fun t => ch14ext_cor147SourceForwardPrintedRemainder
        F A_inv L U U_inv x t) =O[l] (fun t => (F.model t).u ^ 2)) := by
  constructor
  · exact ch14ext_cor147Source_residual_vanishing_family_endpoint
      F L U U_inv hRow hdet hLU hUinv
  · exact ch14ext_cor147Source_forward_vanishing_family_endpoint
      F A_inv L U U_inv x hRow hdet hLU hAinv hUinv hExact hxpos

end NumStability.Ch14Ext
