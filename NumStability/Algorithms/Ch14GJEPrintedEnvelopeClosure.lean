-- Algorithms/Ch14GJEPrintedEnvelopeClosure.lean
--
-- Printed-envelope closure for Higham (14.30b-c) and (14.31).
-- The concrete GJE analysis naturally produces |Q| Pabs.  Higham prints
-- |Uhat| |Uhat^-1| after using Q = Uhat + O(u) and
-- Pabs = |Uhat^-1| + O(u).  This module performs that replacement over an
-- arbitrary vanishing-roundoff family and retains every discarded term in
-- an explicit quadratic remainder.

import NumStability.Algorithms.Ch14GJEAsymptoticFamilies

namespace NumStability.Ch14Ext

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

/-! ## Structural proximity data -/

/-- Structural data behind Higham's replacement of the exact GJE envelope
`|Q| Pabs` by the printed first-order envelope `|Uhat| |Uhat^-1|`.

The two proximity fields concern the factors separately.  They neither assume
the printed product envelope nor any final error inequality. -/
structure Ch14GJEPrintedEnvelopeFamily (ι : Type*) (l : Filter ι) (n : ℕ) where
  model : ι → FPModel
  U_hat : ι → Fin n → Fin n → ℝ
  Q : ι → Fin n → Fin n → ℝ
  Pabs : ι → Fin n → Fin n → ℝ
  U_inv : ι → Fin n → Fin n → ℝ
  Q_error : ι → Fin n → Fin n → ℝ
  P_error : ι → Fin n → Fin n → ℝ
  unit_tendsto_zero : Tendsto (fun t => (model t).u) l (𝓝 0)
  dimension_pos : 1 ≤ n
  valid_three : ∀ t, gammaValid (model t) 3
  inverse_certificate : ∀ t, IsRightInverse n (U_hat t) (U_inv t)
  Pabs_nonneg : ∀ t i j, 0 ≤ Pabs t i j
  Q_error_nonneg : ∀ t i j, 0 ≤ Q_error t i j
  P_error_nonneg : ∀ t i j, 0 ≤ P_error t i j
  Q_proximity : ∀ t i j,
    |Q t i j - U_hat t i j| ≤ gje_c₃ (model t) n * Q_error t i j
  P_upper : ∀ t i j,
    Pabs t i j ≤ |U_inv t i j| + gje_c₃ (model t) n * P_error t i j
  U_hat_isBigO_one : MatrixFamilyIsBigOOne l U_hat
  U_inv_isBigO_one : MatrixFamilyIsBigOOne l U_inv
  Q_error_isBigO_one : MatrixFamilyIsBigOOne l Q_error
  P_error_isBigO_one : MatrixFamilyIsBigOOne l P_error
  exact_envelope_isBigO_one : MatrixFamilyIsBigOOne l
    (fun t => matMul n (absMatrix n (Q t)) (Pabs t))

/-- The exact, pre-replacement envelope `|Q| Pabs`.  `Q` and `Pabs` remain
separate data throughout the closure. -/
noncomputable def ch14ext_gjeExactQPEnvelope
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) :
    Fin n → Fin n → ℝ :=
  matMul n (absMatrix n (F.Q t)) (F.Pabs t)

/-- Higham's printed first-order middle factor `|Uhat| |Uhat^-1|`. -/
noncomputable def ch14ext_gjePrintedUinvEnvelope
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) :
    Fin n → Fin n → ℝ :=
  matMul n (absMatrix n (F.U_hat t)) (absMatrix n (F.U_inv t))

/-- The coefficient of `c3` in the product replacement
`|Q| Pabs ≤ |Uhat| |Uhat^-1| + c3*C`.  The last summand retains the product of
the two first-order factor errors. -/
noncomputable def ch14ext_gjePrintedEnvelopeCorrection
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) :
    Fin n → Fin n → ℝ :=
  fun i j =>
      matMul n (F.Q_error t) (absMatrix n (F.U_inv t)) i j +
      matMul n (absMatrix n (F.U_hat t)) (F.P_error t) i j +
      gje_c₃ (F.model t) n * matMul n (F.Q_error t) (F.P_error t) i j

theorem ch14ext_gjePrintedEnvelopeCorrection_nonneg
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) (i j : Fin n) :
    0 ≤ ch14ext_gjePrintedEnvelopeCorrection F t i j := by
  have h₁ : 0 ≤ matMul n (F.Q_error t) (absMatrix n (F.U_inv t)) i j := by
    unfold matMul absMatrix
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (F.Q_error_nonneg t i k) (abs_nonneg _)
  have h₂ : 0 ≤ matMul n (absMatrix n (F.U_hat t)) (F.P_error t) i j := by
    unfold matMul absMatrix
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (abs_nonneg _) (F.P_error_nonneg t k j)
  have h₃ : 0 ≤ matMul n (F.Q_error t) (F.P_error t) i j := by
    unfold matMul
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (F.Q_error_nonneg t i k) (F.P_error_nonneg t k j)
  unfold ch14ext_gjePrintedEnvelopeCorrection
  exact add_nonneg (add_nonneg h₁ h₂)
    (mul_nonneg (gje_c3_nonneg (F.model t) n F.dimension_pos (F.valid_three t)) h₃)

theorem ch14ext_gjeExactQPEnvelope_nonneg
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) (i j : Fin n) :
    0 ≤ ch14ext_gjeExactQPEnvelope F t i j := by
  unfold ch14ext_gjeExactQPEnvelope matMul absMatrix
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (abs_nonneg _) (F.Pabs_nonneg t k j)

theorem ch14ext_gjePrintedUinvEnvelope_nonneg
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) (i j : Fin n) :
    0 ≤ ch14ext_gjePrintedUinvEnvelope F t i j := by
  unfold ch14ext_gjePrintedUinvEnvelope matMul absMatrix
  positivity

private theorem ch14ext_gje_Q_abs_le
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) (i j : Fin n) :
    |F.Q t i j| ≤ |F.U_hat t i j| +
      gje_c₃ (F.model t) n * F.Q_error t i j := by
  calc
    |F.Q t i j| = |(F.Q t i j - F.U_hat t i j) + F.U_hat t i j| := by
      congr 1
      ring
    _ ≤ |F.Q t i j - F.U_hat t i j| + |F.U_hat t i j| := abs_add_le _ _
    _ ≤ gje_c₃ (F.model t) n * F.Q_error t i j + |F.U_hat t i j| := by
      gcongr
      exact F.Q_proximity t i j
    _ = |F.U_hat t i j| + gje_c₃ (F.model t) n * F.Q_error t i j := by ring

private theorem ch14ext_gje_Pabs_le
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) (i j : Fin n) :
    F.Pabs t i j ≤ |F.U_inv t i j| +
      gje_c₃ (F.model t) n * F.P_error t i j :=
  F.P_upper t i j

/-- The factorwise proximity contracts imply the exact pointwise product
replacement.  In particular, no hypothesis mentions the target product
envelope. -/
theorem ch14ext_gjeExactQPEnvelope_le_printed_add_correction
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) (i j : Fin n) :
    ch14ext_gjeExactQPEnvelope F t i j ≤
      ch14ext_gjePrintedUinvEnvelope F t i j +
        gje_c₃ (F.model t) n * ch14ext_gjePrintedEnvelopeCorrection F t i j := by
  unfold ch14ext_gjeExactQPEnvelope ch14ext_gjePrintedUinvEnvelope
    ch14ext_gjePrintedEnvelopeCorrection matMul absMatrix
  calc
    ∑ k : Fin n, |F.Q t i k| * F.Pabs t k j ≤
        ∑ k : Fin n,
          (|F.U_hat t i k| + gje_c₃ (F.model t) n * F.Q_error t i k) *
            (|F.U_inv t k j| + gje_c₃ (F.model t) n * F.P_error t k j) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul (ch14ext_gje_Q_abs_le F t i k)
        (ch14ext_gje_Pabs_le F t k j) (F.Pabs_nonneg t k j)
        (add_nonneg (abs_nonneg _)
          (mul_nonneg
            (gje_c3_nonneg (F.model t) n F.dimension_pos (F.valid_three t))
            (F.Q_error_nonneg t i k)))
    _ = (∑ k : Fin n, |F.U_hat t i k| * |F.U_inv t k j|) +
        gje_c₃ (F.model t) n *
          ((∑ k : Fin n, F.Q_error t i k * |F.U_inv t k j|) +
            (∑ k : Fin n, |F.U_hat t i k| * F.P_error t k j) +
            gje_c₃ (F.model t) n *
              ∑ k : Fin n, F.Q_error t i k * F.P_error t k j) := by
      calc
        ∑ k : Fin n,
            (|F.U_hat t i k| + gje_c₃ (F.model t) n * F.Q_error t i k) *
              (|F.U_inv t k j| + gje_c₃ (F.model t) n * F.P_error t k j) =
            ∑ k : Fin n,
              (|F.U_hat t i k| * |F.U_inv t k j| +
                gje_c₃ (F.model t) n *
                  (F.Q_error t i k * |F.U_inv t k j| +
                    |F.U_hat t i k| * F.P_error t k j +
                    gje_c₃ (F.model t) n *
                      (F.Q_error t i k * F.P_error t k j))) := by
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = (∑ k : Fin n, |F.U_hat t i k| * |F.U_inv t k j|) +
            gje_c₃ (F.model t) n *
              ∑ k : Fin n,
                (F.Q_error t i k * |F.U_inv t k j| +
                  |F.U_hat t i k| * F.P_error t k j +
                  gje_c₃ (F.model t) n *
                    (F.Q_error t i k * F.P_error t k j)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = (∑ k : Fin n, |F.U_hat t i k| * |F.U_inv t k j|) +
            gje_c₃ (F.model t) n *
              ((∑ k : Fin n, F.Q_error t i k * |F.U_inv t k j|) +
                (∑ k : Fin n, |F.U_hat t i k| * F.P_error t k j) +
                gje_c₃ (F.model t) n *
                  ∑ k : Fin n, F.Q_error t i k * F.P_error t k j) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-! ## Discharge from the concrete rounded GJE run -/

/-- For the actual constructed left inverse, the accumulated matrix error
proves `Q = Uhat + O(c3)` componentwise.  The proximity is derived here from
the rounded recurrence, final `D = I` normalization, and the proved identity
`Q * signedCumProd = I`. -/
theorem ch14ext_gjeConcrete_constructedQ_sub_U_bound
    {ι : Type*} {l : Filter ι} {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ} {start : ℕ}
    (R : Ch14GJEConcreteFamily ι l n A b start) (t : ι) (i j : Fin n) :
    |ch14ext_gjeConstructedQ n (R.V t) start i j - R.V t start i j| ≤
      gje_c₃ (R.model t) n *
        matMul n (ch14ext_gjeConcreteFamilyXabs R t)
          (absMatrix n (R.V t start)) i j := by
  let N := ch14ext_gjeSeqStages n (R.V t)
  let Q := ch14ext_gjeConstructedQ n (R.V t) start
  let P := gje_cumulative_product n N start (start + (n - 1))
  let E : Fin n → Fin n → ℝ := fun a k =>
    R.V t (start + (n - 1)) a k - matMul n P (R.V t start) a k
  have hE : ∀ a k : Fin n, |E a k| ≤
      gje_c₃ (R.model t) n *
        ch14ext_boundObj n N (R.V t start) start (n - 1) a k := by
    intro a k
    simpa [E, P, N] using
      ch14ext_gjeConcrete_matrixAccumulation (R.model t) n (R.V t) start
        R.dimension_pos (R.valid_three t) R.index_valid
        (R.matrix_recurrence t) (R.pivots_nonzero t) a k
  have hQP : matMul n Q P = idMatrix n := by
    simpa [Q, P, N] using
      ch14ext_gjeConstructedQ_isLeftInverse n (R.V t) start R.index_valid
  have hfinalQ : matMul n Q (R.V t (start + (n - 1))) = Q := by
    rw [R.final_matrix t, matMul_id_right]
  have hproductQ : matMul n Q (matMul n P (R.V t start)) = R.V t start := by
    rw [← matMul_assoc, hQP, matMul_id_left]
  have hkey : matMul n Q E = fun a k => Q a k - R.V t start a k := by
    funext a k
    have hexpand : matMul n Q E a k =
        matMul n Q (R.V t (start + (n - 1))) a k -
          matMul n Q (matMul n P (R.V t start)) a k := by
      show (∑ q : Fin n, Q a q * E q k) =
        (∑ q : Fin n, Q a q * R.V t (start + (n - 1)) q k) -
          ∑ q : Fin n, Q a q * matMul n P (R.V t start) q k
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun q _ => by
        show Q a q *
          (R.V t (start + (n - 1)) q k - matMul n P (R.V t start) q k) = _
        ring)
    rw [hexpand, hfinalQ, hproductQ]
  have hbound := ch14ext_matMul_abs_bound n Q E
    (ch14ext_boundObj n N (R.V t start) start (n - 1))
    (gje_c₃ (R.model t) n) hE i j
  have hreassoc :
      matMul n (absMatrix n Q)
          (ch14ext_boundObj n N (R.V t start) start (n - 1)) =
        matMul n (ch14ext_gjeConcreteFamilyXabs R t)
          (absMatrix n (R.V t start)) := by
    show matMul n (absMatrix n Q)
        (matMul n (ch14ext_absCumProd n N start (n - 1))
          (absMatrix n (R.V t start))) = _
    rw [← matMul_assoc]
    rfl
  rw [hreassoc, hkey] at hbound
  simpa [Q] using hbound

/-- For the actual absolute cumulative product, upper triangularity identifies
it with the absolute signed product.  The accumulated residual and a genuine
right inverse of `Uhat` then prove Higham's one-sided inverse comparison. -/
theorem ch14ext_gjeConcrete_Pabs_le_abs_Uinv_add
    {ι : Type*} {l : Filter ι} {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ} {start : ℕ}
    (R : Ch14GJEConcreteFamily ι l n A b start)
    (U_inv : ι → Fin n → Fin n → ℝ)
    (hUinv : ∀ t, IsRightInverse n (R.V t start) (U_inv t))
    (t : ι) (i j : Fin n) :
    ch14ext_gjeConcreteFamilyPabs R t i j ≤ |U_inv t i j| +
      gje_c₃ (R.model t) n *
        matMul n
          (matMul n (ch14ext_gjeConcreteFamilyPabs R t)
            (absMatrix n (R.V t start)))
          (absMatrix n (U_inv t)) i j := by
  let X := ch14ext_gjeConcreteFamilyPabs R t
  let S := gje_cumulative_product n (ch14ext_gjeSeqStages n (R.V t))
    start (start + (n - 1))
  have hUpper : ∀ q : ℕ, q ≤ n - 1 →
      ∀ a k : Fin n, k.val < a.val → R.V t (start + q) a k = 0 :=
    ch14ext_gjeSeq_upper_triangular (R.model t) n (R.V t) start
      R.index_valid (R.lu_certificate t).U_lower_zero
      (R.matrix_recurrence t) (R.pivots_nonzero t)
  have hX : ∀ a k : Fin n, X a k = |S a k| := by
    intro a k
    simpa [X, S, ch14ext_gjeConcreteFamilyPabs] using
      ch14ext_gje_absCumProd_eq_abs_signed n (R.V t) start (n - 1)
        R.index_valid hUpper a k
  have hAccum := ch14ext_gjeConcrete_matrixAccumulation (R.model t) n
    (R.V t) start R.dimension_pos (R.valid_three t) R.index_valid
    (R.matrix_recurrence t) (R.pivots_nonzero t)
  have hResidual : ∀ a k : Fin n,
      |idMatrix n a k - matMul n S (R.V t start) a k| ≤
        gje_c₃ (R.model t) n *
          matMul n X (absMatrix n (R.V t start)) a k := by
    intro a k
    have h := hAccum a k
    rw [R.final_matrix t] at h
    simpa [S, X, ch14ext_gjeConcreteFamilyPabs, ch14ext_boundObj] using h
  simpa [X] using
    ch14ext_abs_signed_le_abs_rightInverse_add n S X (R.V t start)
      (U_inv t) (gje_c₃ (R.model t) n) hX (hUinv t) hResidual i j

private theorem ch14ext_matMul_upper_triangular
    (n : ℕ) (A B : Fin n → Fin n → ℝ)
    (hA : ∀ i j : Fin n, j.val < i.val → A i j = 0)
    (hB : ∀ i j : Fin n, j.val < i.val → B i j = 0) :
    ∀ i j : Fin n, j.val < i.val → matMul n A B i j = 0 := by
  intro i j hji
  unfold matMul
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : k.val < i.val
  · rw [hA i k hki, zero_mul]
  · have hik : i.val ≤ k.val := Nat.le_of_not_gt hki
    rw [hB k j (lt_of_lt_of_le hji hik), mul_zero]

private theorem ch14ext_matMul_diag_one_of_unit_upper
    (n : ℕ) (A B : Fin n → Fin n → ℝ)
    (hA : ∀ i j : Fin n, j.val < i.val → A i j = 0)
    (hB : ∀ i j : Fin n, j.val < i.val → B i j = 0)
    (hAd : ∀ i : Fin n, A i i = 1)
    (hBd : ∀ i : Fin n, B i i = 1) (i : Fin n) :
    matMul n A B i i = 1 := by
  unfold matMul
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hoff : ∑ k ∈ Finset.univ.erase i, A i k * B k i = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    by_cases hlt : k.val < i.val
    · rw [hA i k hlt, zero_mul]
    · have hgt : i.val < k.val := by
        have hne : k.val ≠ i.val := fun h => hki (Fin.ext h)
        omega
      rw [hB k i hgt, mul_zero]
  rw [hoff, add_zero, hAd i, hBd i, one_mul]

private theorem ch14ext_gjeInvStageMatrix_upper_triangular
    (n : ℕ) (U : Fin n → Fin n → ℝ) (k : Fin n)
    (hU : ∀ i j : Fin n, j.val < i.val → U i j = 0) :
    ∀ i j : Fin n, j.val < i.val →
      ch14ext_gjeInvStageMatrix n U k i j = 0 := by
  intro i j hji
  have hij : i ≠ j := fun h => by subst j; omega
  by_cases hjk : j = k
  · subst j
    have hki : k.val ≤ i.val := Nat.le_of_lt hji
    simp [ch14ext_gjeInvStageMatrix, hij,
      ch14ext_gjeMultVec_zero_of_upper n U k i hU hki]
  · simp [ch14ext_gjeInvStageMatrix, hij, hjk]

private theorem ch14ext_gjeInvStageMatrix_diag_one
    (n : ℕ) (U : Fin n → Fin n → ℝ) (k i : Fin n) :
    ch14ext_gjeInvStageMatrix n U k i i = 1 := by
  by_cases hik : i = k
  · subst i
    simp [ch14ext_gjeInvStageMatrix, ch14ext_gjeMultVec_self]
  · simp [ch14ext_gjeInvStageMatrix, hik]

private theorem ch14ext_gjeInvCumProd_unit_upper
    (n : ℕ) (Ninv : Fin n → Fin n → Fin n → ℝ) (start : ℕ) :
    ∀ steps : ℕ, (hidx : ∀ q : ℕ, q < steps → start + q < n) →
      (∀ q : ℕ, (hq : q < steps) →
        ∀ i j : Fin n, j.val < i.val →
          Ninv ⟨start + q, hidx q hq⟩ i j = 0) →
      (∀ q : ℕ, (hq : q < steps) → ∀ i : Fin n,
        Ninv ⟨start + q, hidx q hq⟩ i i = 1) →
      (∀ i j : Fin n, j.val < i.val →
        ch14ext_gjeInvCumProd n Ninv start (start + steps) i j = 0) ∧
      (∀ i : Fin n,
        ch14ext_gjeInvCumProd n Ninv start (start + steps) i i = 1) := by
  intro steps
  induction steps with
  | zero =>
      intro _ _ _
      rw [Nat.add_zero, ch14ext_gjeInvCumProd_base n Ninv (le_refl start)]
      constructor
      · intro i j hji
        simp [idMatrix, show i ≠ j from fun h => by subst j; omega]
      · intro i
        simp [idMatrix]
  | succ steps ih =>
      intro hidx hUpper hDiag
      have htop : start + steps < n := hidx steps (Nat.lt_succ_self steps)
      have hstep : start < start + (steps + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos steps)
      have hfinEq : start + (steps + 1) - 1 = start + steps := by omega
      have hfinLt : start + (steps + 1) - 1 < n := by simpa [hfinEq] using htop
      have hfin : (⟨start + (steps + 1) - 1, hfinLt⟩ : Fin n) =
          ⟨start + steps, htop⟩ := by
        apply Fin.ext
        simp [hfinEq]
      have hidxPrev : ∀ q : ℕ, q < steps → start + q < n :=
        fun q hq => hidx q (Nat.lt_trans hq (Nat.lt_succ_self steps))
      have hUpperPrev : ∀ q : ℕ, (hq : q < steps) →
          ∀ i j : Fin n, j.val < i.val →
            Ninv ⟨start + q, hidxPrev q hq⟩ i j = 0 := by
        intro q hq
        simpa using hUpper q (Nat.lt_trans hq (Nat.lt_succ_self steps))
      have hDiagPrev : ∀ q : ℕ, (hq : q < steps) → ∀ i : Fin n,
          Ninv ⟨start + q, hidxPrev q hq⟩ i i = 1 := by
        intro q hq
        simpa using hDiag q (Nat.lt_trans hq (Nat.lt_succ_self steps))
      obtain ⟨hPrevUpper, hPrevDiag⟩ := ih hidxPrev hUpperPrev hDiagPrev
      have hTopUpper : ∀ i j : Fin n, j.val < i.val →
          Ninv ⟨start + steps, htop⟩ i j = 0 := by
        simpa using hUpper steps (Nat.lt_succ_self steps)
      have hTopDiag : ∀ i : Fin n, Ninv ⟨start + steps, htop⟩ i i = 1 := by
        simpa using hDiag steps (Nat.lt_succ_self steps)
      rw [ch14ext_gjeInvCumProd_step n Ninv hstep hfinLt, hfin, hfinEq]
      constructor
      · exact ch14ext_matMul_upper_triangular n _ _ hPrevUpper hTopUpper
      · intro i
        exact ch14ext_matMul_diag_one_of_unit_upper n _ _ hPrevUpper hTopUpper
          hPrevDiag hTopDiag i

/-- The concrete constructed inverse is unit upper triangular.  Only the
already-proved upper-triangular invariant of the rounded iterates is used. -/
theorem ch14ext_gjeConcrete_constructedQ_diag_one
    {ι : Type*} {l : Filter ι} {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ} {start : ℕ}
    (R : Ch14GJEConcreteFamily ι l n A b start) (t : ι) (i : Fin n) :
    ch14ext_gjeConstructedQ n (R.V t) start i i = 1 := by
  have hUpper : ∀ q : ℕ, q ≤ n - 1 →
      ∀ a k : Fin n, k.val < a.val → R.V t (start + q) a k = 0 :=
    ch14ext_gjeSeq_upper_triangular (R.model t) n (R.V t) start
      R.index_valid (R.lu_certificate t).U_lower_zero
      (R.matrix_recurrence t) (R.pivots_nonzero t)
  have hInvUpper : ∀ q : ℕ, (hq : q < n - 1) →
      ∀ a k : Fin n, k.val < a.val →
        ch14ext_gjeSeqStagesInv n (R.V t) ⟨start + q, R.index_valid q hq⟩ a k = 0 := by
    intro q hq a k hka
    exact ch14ext_gjeInvStageMatrix_upper_triangular n (R.V t (start + q))
      ⟨start + q, R.index_valid q hq⟩ (hUpper q (Nat.le_of_lt hq)) a k hka
  have hInvDiag : ∀ q : ℕ, (hq : q < n - 1) → ∀ a : Fin n,
      ch14ext_gjeSeqStagesInv n (R.V t) ⟨start + q, R.index_valid q hq⟩ a a = 1 := by
    intro q hq a
    exact ch14ext_gjeInvStageMatrix_diag_one n (R.V t (start + q))
      ⟨start + q, R.index_valid q hq⟩ a
  exact (ch14ext_gjeInvCumProd_unit_upper n
    (ch14ext_gjeSeqStagesInv n (R.V t)) start (n - 1) R.index_valid
    hInvUpper hInvDiag).2 i

/-- The exact `|Q| Pabs` envelope dominates `Pabs` itself because the
constructed `Q` has unit diagonal. -/
theorem ch14ext_gjeConcreteFamilyPabs_le_Xabs
    {ι : Type*} {l : Filter ι} {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ} {start : ℕ}
    (R : Ch14GJEConcreteFamily ι l n A b start) (t : ι) (i j : Fin n) :
    ch14ext_gjeConcreteFamilyPabs R t i j ≤
      ch14ext_gjeConcreteFamilyXabs R t i j := by
  have hPnonneg : ∀ a k : Fin n,
      0 ≤ ch14ext_gjeConcreteFamilyPabs R t a k := by
    intro a k
    exact gje_cumulative_product_abs_nonneg n (ch14ext_gjeSeqStages n (R.V t))
      start (start + (n - 1)) a k
  have hQdiag := ch14ext_gjeConcrete_constructedQ_diag_one R t i
  unfold ch14ext_gjeConcreteFamilyXabs ch14ext_gjeXabs matMul absMatrix
  calc
    ch14ext_gjeConcreteFamilyPabs R t i j =
        |ch14ext_gjeConstructedQ n (R.V t) start i i| *
          ch14ext_gjeConcreteFamilyPabs R t i j := by rw [hQdiag]; simp
    _ ≤ ∑ k : Fin n, |ch14ext_gjeConstructedQ n (R.V t) start i k| *
          ch14ext_gjeConcreteFamilyPabs R t k j :=
      Finset.single_le_sum
        (fun k _ => mul_nonneg (abs_nonneg _) (hPnonneg k j))
        (Finset.mem_univ i)

/-- The absolute cumulative-product family is locally bounded because it is
entrywise dominated by the already-bounded exact envelope `|Q| Pabs`. -/
theorem ch14ext_gjeConcreteFamilyPabs_isBigOOne
    {ι : Type*} {l : Filter ι} {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ} {start : ℕ}
    (R : Ch14GJEConcreteFamily ι l n A b start) :
    MatrixFamilyIsBigOOne l (ch14ext_gjeConcreteFamilyPabs R) := by
  intro i j
  have hdom :
      (fun t => ch14ext_gjeConcreteFamilyPabs R t i j)
        =O[l] (fun t => ch14ext_gjeConcreteFamilyXabs R t i j) := by
    apply Asymptotics.IsBigO.of_norm_le
    intro t
    have hp : 0 ≤ ch14ext_gjeConcreteFamilyPabs R t i j := by
      unfold ch14ext_gjeConcreteFamilyPabs ch14ext_absCumProd
      exact gje_cumulative_product_abs_nonneg n (ch14ext_gjeSeqStages n (R.V t))
        start (start + (n - 1)) i j
    change |ch14ext_gjeConcreteFamilyPabs R t i j| ≤
      ch14ext_gjeConcreteFamilyXabs R t i j
    rw [abs_of_nonneg hp]
    exact ch14ext_gjeConcreteFamilyPabs_le_Xabs R t i j
  exact hdom.trans (R.X_abs_isBigO_one i j)

/-- Instantiate the abstract replacement data with the actual rounded GJE
objects.  The only additional regularity assumption is local boundedness of
the exact right inverse; boundedness of `Pabs` is derived from the concrete
constructed envelope. -/
noncomputable def ch14ext_gjeConcretePrintedEnvelopeFamily
    {ι : Type*} {l : Filter ι} {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ} {start : ℕ}
    (R : Ch14GJEConcreteFamily ι l n A b start)
    (U_inv : ι → Fin n → Fin n → ℝ)
    (hUinv : ∀ t, IsRightInverse n (R.V t start) (U_inv t))
    (hUinv_one : MatrixFamilyIsBigOOne l U_inv) :
    Ch14GJEPrintedEnvelopeFamily ι l n where
  model := R.model
  U_hat := fun t => R.V t start
  Q := fun t => ch14ext_gjeConstructedQ n (R.V t) start
  Pabs := ch14ext_gjeConcreteFamilyPabs R
  U_inv := U_inv
  Q_error := fun t =>
    matMul n (ch14ext_gjeConcreteFamilyXabs R t) (absMatrix n (R.V t start))
  P_error := fun t =>
    matMul n
      (matMul n (ch14ext_gjeConcreteFamilyPabs R t) (absMatrix n (R.V t start)))
      (absMatrix n (U_inv t))
  unit_tendsto_zero := R.unit_tendsto_zero
  dimension_pos := R.dimension_pos
  valid_three := R.valid_three
  inverse_certificate := hUinv
  Pabs_nonneg := by
    intro t i j
    exact gje_cumulative_product_abs_nonneg n (ch14ext_gjeSeqStages n (R.V t))
      start (start + (n - 1)) i j
  Q_error_nonneg := by
    intro t i j
    unfold matMul absMatrix
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg
        (ch14ext_gjeXabs_nonneg n (ch14ext_gjeSeqStages n (R.V t))
          (ch14ext_gjeConstructedQ n (R.V t) start) start (n - 1) i k)
        (abs_nonneg _)
  P_error_nonneg := by
    intro t i j
    unfold matMul absMatrix
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg
    · exact Finset.sum_nonneg fun q _ =>
        mul_nonneg
          (gje_cumulative_product_abs_nonneg n (ch14ext_gjeSeqStages n (R.V t))
            start (start + (n - 1)) i q)
          (abs_nonneg _)
    · exact abs_nonneg _
  Q_proximity := ch14ext_gjeConcrete_constructedQ_sub_U_bound R
  P_upper := ch14ext_gjeConcrete_Pabs_le_abs_Uinv_add R U_inv hUinv
  U_hat_isBigO_one := R.U_hat_isBigO_one
  U_inv_isBigO_one := hUinv_one
  Q_error_isBigO_one := by
    exact ch14ext_matrixFamily_mul_family_isBigOOne R.X_abs_isBigO_one
      (matrixFamily_abs_isBigOOne R.U_hat_isBigO_one)
  P_error_isBigO_one := by
    exact ch14ext_matrixFamily_mul_family_isBigOOne
      (ch14ext_matrixFamily_mul_family_isBigOOne
        (ch14ext_gjeConcreteFamilyPabs_isBigOOne R)
        (matrixFamily_abs_isBigOOne R.U_hat_isBigO_one))
      (matrixFamily_abs_isBigOOne hUinv_one)
  exact_envelope_isBigO_one := by
    simpa [ch14ext_gjeConcreteFamilyXabs, ch14ext_gjeConcreteFamilyPabs,
      ch14ext_gjeXabs] using R.X_abs_isBigO_one

/-! ## Uniform closure of the replacement correction -/

theorem ch14ext_gjePrintedEnvelopeCorrection_isBigOOne
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) :
    MatrixFamilyIsBigOOne l (ch14ext_gjePrintedEnvelopeCorrection F) := by
  have hQU := ch14ext_matrixFamily_mul_family_isBigOOne
    F.Q_error_isBigO_one (matrixFamily_abs_isBigOOne F.U_inv_isBigO_one)
  have hUP := ch14ext_matrixFamily_mul_family_isBigOOne
    (matrixFamily_abs_isBigOOne F.U_hat_isBigO_one) F.P_error_isBigO_one
  have hQP := ch14ext_matrixFamily_mul_family_isBigOOne
    F.Q_error_isBigO_one F.P_error_isBigO_one
  have hc3u := ch14ext_gje_c3_family_isBigO_unit n F.model F.unit_tendsto_zero
  have hu1 : (fun t => (F.model t).u) =O[l] (fun _ : ι => (1 : ℝ)) :=
    F.unit_tendsto_zero.isBigO_one ℝ
  have hc31 : (fun t => gje_c₃ (F.model t) n) =O[l] (fun _ : ι => (1 : ℝ)) :=
    hc3u.trans hu1
  intro i j
  have hthird :
      (fun t => gje_c₃ (F.model t) n *
        matMul n (F.Q_error t) (F.P_error t) i j)
        =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa only [one_mul] using hc31.mul (hQP i j)
  simpa only [ch14ext_gjePrintedEnvelopeCorrection] using
    ((hQU i j).add (hUP i j)).add hthird

/-- The product replacement remains valid after multiplication by any
componentwise nonnegative matrix on the right. -/
theorem ch14ext_gjeExactQPEnvelope_matMul_le_printed_add_correction
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι)
    (B : Fin n → Fin n → ℝ) (hB : ∀ i j, 0 ≤ B i j) (i j : Fin n) :
    matMul n (ch14ext_gjeExactQPEnvelope F t) B i j ≤
      matMul n (ch14ext_gjePrintedUinvEnvelope F t) B i j +
        gje_c₃ (F.model t) n *
          matMul n (ch14ext_gjePrintedEnvelopeCorrection F t) B i j := by
  unfold matMul
  calc
    ∑ k : Fin n, ch14ext_gjeExactQPEnvelope F t i k * B k j ≤
        ∑ k : Fin n,
          (ch14ext_gjePrintedUinvEnvelope F t i k +
            gje_c₃ (F.model t) n *
              ch14ext_gjePrintedEnvelopeCorrection F t i k) * B k j := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right
        (ch14ext_gjeExactQPEnvelope_le_printed_add_correction F t i k) (hB k j)
    _ = (∑ k : Fin n, ch14ext_gjePrintedUinvEnvelope F t i k * B k j) +
        gje_c₃ (F.model t) n *
          ∑ k : Fin n, ch14ext_gjePrintedEnvelopeCorrection F t i k * B k j := by
      calc
        ∑ k : Fin n,
            (ch14ext_gjePrintedUinvEnvelope F t i k +
              gje_c₃ (F.model t) n *
                ch14ext_gjePrintedEnvelopeCorrection F t i k) * B k j =
            ∑ k : Fin n,
              (ch14ext_gjePrintedUinvEnvelope F t i k * B k j +
                gje_c₃ (F.model t) n *
                  (ch14ext_gjePrintedEnvelopeCorrection F t i k * B k j)) := by
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The product replacement remains valid when applied to a nonnegative
vector. -/
theorem ch14ext_gjeExactQPEnvelope_matMulVec_le_printed_add_correction
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι)
    (v : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (i : Fin n) :
    matMulVec n (ch14ext_gjeExactQPEnvelope F t) v i ≤
      matMulVec n (ch14ext_gjePrintedUinvEnvelope F t) v i +
        gje_c₃ (F.model t) n *
          matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t) v i := by
  unfold matMulVec
  calc
    ∑ k : Fin n, ch14ext_gjeExactQPEnvelope F t i k * v k ≤
        ∑ k : Fin n,
          (ch14ext_gjePrintedUinvEnvelope F t i k +
            gje_c₃ (F.model t) n *
              ch14ext_gjePrintedEnvelopeCorrection F t i k) * v k := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right
        (ch14ext_gjeExactQPEnvelope_le_printed_add_correction F t i k) (hv k)
    _ = (∑ k : Fin n, ch14ext_gjePrintedUinvEnvelope F t i k * v k) +
        gje_c₃ (F.model t) n *
          ∑ k : Fin n, ch14ext_gjePrintedEnvelopeCorrection F t i k * v k := by
      calc
        ∑ k : Fin n,
            (ch14ext_gjePrintedUinvEnvelope F t i k +
              gje_c₃ (F.model t) n *
                ch14ext_gjePrintedEnvelopeCorrection F t i k) * v k =
            ∑ k : Fin n,
              (ch14ext_gjePrintedUinvEnvelope F t i k * v k +
                gje_c₃ (F.model t) n *
                  (ch14ext_gjePrintedEnvelopeCorrection F t i k * v k)) := by
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

/-! ## Printed equations (14.30b-c) -/

/-- The explicit correction left after replacing `|Q| Pabs` in (14.30b).
Its coefficient is `c3^2`; the matrix factor contains no hidden asymptotic
notation. -/
noncomputable def ch14ext_gje1430bPrintedRemainder
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) (i j : Fin n) : ℝ :=
  gje_c₃ (F.model t) n * gje_c₃ (F.model t) n *
    matMul n (ch14ext_gjePrintedEnvelopeCorrection F t)
      (absMatrix n (F.U_hat t)) i j

/-- The explicit correction left after replacing `|Q| Pabs` in (14.30c). -/
noncomputable def ch14ext_gje1430cPrintedRemainder
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n)
    (y : ι → Fin n → ℝ) (t : ι) (i : Fin n) : ℝ :=
  gje_c₃ (F.model t) n * gje_c₃ (F.model t) n *
    matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t) (absVec n (y t)) i

theorem ch14ext_gje1430bPrintedRemainder_isBigO_unit_sq
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (i j : Fin n) :
    (fun t => ch14ext_gje1430bPrintedRemainder F t i j)
      =O[l] (fun t => (F.model t).u ^ 2) := by
  have hc3 := ch14ext_gje_c3_family_isBigO_unit n F.model F.unit_tendsto_zero
  have hc3sq :
      (fun t => gje_c₃ (F.model t) n * gje_c₃ (F.model t) n)
        =O[l] (fun t => (F.model t).u ^ 2) := by
    simpa only [pow_two] using hc3.mul hc3
  have haction := ch14ext_matrixFamily_mul_family_isBigOOne
    (ch14ext_gjePrintedEnvelopeCorrection_isBigOOne F)
    (matrixFamily_abs_isBigOOne F.U_hat_isBigO_one)
  simpa only [ch14ext_gje1430bPrintedRemainder, mul_one] using
    hc3sq.mul (haction i j)

theorem ch14ext_gje1430cPrintedRemainder_isBigO_unit_sq
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n)
    (y : ι → Fin n → ℝ) (hy : VectorFamilyIsBigOOne l y) (i : Fin n) :
    (fun t => ch14ext_gje1430cPrintedRemainder F y t i)
      =O[l] (fun t => (F.model t).u ^ 2) := by
  have hc3 := ch14ext_gje_c3_family_isBigO_unit n F.model F.unit_tendsto_zero
  have hc3sq :
      (fun t => gje_c₃ (F.model t) n * gje_c₃ (F.model t) n)
        =O[l] (fun t => (F.model t).u ^ 2) := by
    simpa only [pow_two] using hc3.mul hc3
  have haction := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (ch14ext_gjePrintedEnvelopeCorrection_isBigOOne F)
    (ch14ext_vectorFamily_abs_isBigOOne hy)
  simpa only [ch14ext_gje1430cPrintedRemainder, mul_one] using
    hc3sq.mul (haction i)

/-- **Higham (14.30a-c), actual rounded GJE, printed envelopes.**

The witnesses come from the concrete rounded recurrences.  The middle factor
in both bounds is literally `|Uhat| |Uhat^-1|`; the difference from the exact
`|Q| Pabs` envelope is retained in the named remainders and proved uniformly
`O(u^2)` on a nontrivial filter. -/
theorem ch14ext_gjeConcrete_14_30bc_printed_vanishing_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ} {start : ℕ}
    (R : Ch14GJEConcreteFamily ι l n A b start)
    (U_inv : ι → Fin n → Fin n → ℝ)
    (hUinv : ∀ t, IsRightInverse n (R.V t start) (U_inv t))
    (hUinv_one : MatrixFamilyIsBigOOne l U_inv) :
    ∃ ΔU : ι → Fin n → Fin n → ℝ, ∃ Δy : ι → Fin n → ℝ,
      (∀ t i,
        ∑ j : Fin n, (R.V t start i j + ΔU t i j) * R.x_hat t j =
          R.xseq t start i + Δy t i) ∧
      (∀ t i j, |ΔU t i j| ≤
        gje_c₃ (R.model t) n *
          matMul n
            (ch14ext_gjePrintedUinvEnvelope
              (ch14ext_gjeConcretePrintedEnvelopeFamily R U_inv hUinv
                hUinv_one) t)
            (absMatrix n (R.V t start)) i j +
          ch14ext_gje1430bPrintedRemainder
            (ch14ext_gjeConcretePrintedEnvelopeFamily R U_inv hUinv
              hUinv_one) t i j) ∧
      (∀ t i, |Δy t i| ≤
        gje_c₃ (R.model t) n *
          matMulVec n
            (ch14ext_gjePrintedUinvEnvelope
              (ch14ext_gjeConcretePrintedEnvelopeFamily R U_inv hUinv
                hUinv_one) t)
            (absVec n (R.xseq t start)) i +
          ch14ext_gje1430cPrintedRemainder
            (ch14ext_gjeConcretePrintedEnvelopeFamily R U_inv hUinv
              hUinv_one) (fun q => R.xseq q start) t i) ∧
      (∀ i j,
        (fun t => ch14ext_gje1430bPrintedRemainder
          (ch14ext_gjeConcretePrintedEnvelopeFamily R U_inv hUinv
            hUinv_one) t i j)
          =O[l] (fun t => (R.model t).u ^ 2)) ∧
      (∀ i,
        (fun t => ch14ext_gje1430cPrintedRemainder
          (ch14ext_gjeConcretePrintedEnvelopeFamily R U_inv hUinv
            hUinv_one) (fun q => R.xseq q start) t i)
          =O[l] (fun t => (R.model t).u ^ 2)) := by
  let F := ch14ext_gjeConcretePrintedEnvelopeFamily R U_inv hUinv
    hUinv_one
  have hwitness : ∀ t, ∃ ΔU : Fin n → Fin n → ℝ, ∃ Δy : Fin n → ℝ,
      (∀ i : Fin n,
        ∑ j : Fin n, (R.V t start i j + ΔU i j) * R.x_hat t j =
          R.xseq t start i + Δy i) ∧
      (∀ i j : Fin n, |ΔU i j| ≤ gje_c₃ (R.model t) n *
        ∑ k : Fin n,
          |ch14ext_gjeConcreteFamilyXabs R t i k| * |R.V t start k j|) ∧
      (∀ i : Fin n, |Δy i| ≤ gje_c₃ (R.model t) n *
        ∑ j : Fin n,
          |ch14ext_gjeConcreteFamilyXabs R t i j| * |R.xseq t start j|) := by
    intro t
    simpa only [ch14ext_gjeConcreteFamilyXabs] using
      ch14ext_gjeConcrete_stage2_backward_error n (R.model t) (R.x_hat t)
        (R.V t) (R.xseq t) start R.dimension_pos (R.valid_three t)
        R.index_valid (R.final_matrix t) (R.final_vector t)
        (R.matrix_recurrence t) (R.vector_recurrence t) (R.pivots_nonzero t)
  choose ΔU Δy hEq hΔU hΔy using hwitness
  refine ⟨ΔU, Δy, hEq, ?_, ?_, ?_, ?_⟩
  · intro t i j
    have hraw : |ΔU t i j| ≤ gje_c₃ (R.model t) n *
        matMul n (ch14ext_gjeExactQPEnvelope F t)
          (absMatrix n (R.V t start)) i j := by
      have hEnvelope : ch14ext_gjeExactQPEnvelope F t =
          ch14ext_gjeConcreteFamilyXabs R t := by
        rfl
      calc
        |ΔU t i j| ≤ gje_c₃ (R.model t) n *
            ∑ k : Fin n,
              |ch14ext_gjeConcreteFamilyXabs R t i k| *
                |R.V t start k j| := hΔU t i j
        _ = gje_c₃ (R.model t) n *
            matMul n (ch14ext_gjeExactQPEnvelope F t)
              (absMatrix n (R.V t start)) i j := by
          rw [hEnvelope]
          unfold matMul absMatrix
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          rw [abs_of_nonneg]
          exact ch14ext_gjeXabs_nonneg n
            (ch14ext_gjeSeqStages n (R.V t))
            (ch14ext_gjeConstructedQ n (R.V t) start)
            start (n - 1) i k
    have hreplace :=
      ch14ext_gjeExactQPEnvelope_matMul_le_printed_add_correction F t
        (absMatrix n (R.V t start)) (fun _ _ => abs_nonneg _) i j
    have hc := gje_c3_nonneg (R.model t) n R.dimension_pos (R.valid_three t)
    calc
      |ΔU t i j| ≤ gje_c₃ (R.model t) n *
          matMul n (ch14ext_gjeExactQPEnvelope F t)
            (absMatrix n (R.V t start)) i j := hraw
      _ ≤ gje_c₃ (R.model t) n *
          (matMul n (ch14ext_gjePrintedUinvEnvelope F t)
              (absMatrix n (R.V t start)) i j +
            gje_c₃ (R.model t) n *
              matMul n (ch14ext_gjePrintedEnvelopeCorrection F t)
                (absMatrix n (R.V t start)) i j) :=
        mul_le_mul_of_nonneg_left hreplace hc
      _ = gje_c₃ (R.model t) n *
          matMul n (ch14ext_gjePrintedUinvEnvelope F t)
            (absMatrix n (R.V t start)) i j +
          ch14ext_gje1430bPrintedRemainder F t i j := by
        unfold ch14ext_gje1430bPrintedRemainder
        dsimp only [F, ch14ext_gjeConcretePrintedEnvelopeFamily]
        ring
  · intro t i
    have hraw : |Δy t i| ≤ gje_c₃ (R.model t) n *
        matMulVec n (ch14ext_gjeExactQPEnvelope F t)
          (absVec n (R.xseq t start)) i := by
      have hEnvelope : ch14ext_gjeExactQPEnvelope F t =
          ch14ext_gjeConcreteFamilyXabs R t := by
        rfl
      calc
        |Δy t i| ≤ gje_c₃ (R.model t) n *
            ∑ j : Fin n,
              |ch14ext_gjeConcreteFamilyXabs R t i j| *
                |R.xseq t start j| := hΔy t i
        _ = gje_c₃ (R.model t) n *
            matMulVec n (ch14ext_gjeExactQPEnvelope F t)
              (absVec n (R.xseq t start)) i := by
          rw [hEnvelope]
          unfold matMulVec absVec
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_of_nonneg]
          exact ch14ext_gjeXabs_nonneg n
            (ch14ext_gjeSeqStages n (R.V t))
            (ch14ext_gjeConstructedQ n (R.V t) start)
            start (n - 1) i j
    have hreplace :=
      ch14ext_gjeExactQPEnvelope_matMulVec_le_printed_add_correction F t
        (absVec n (R.xseq t start)) (fun _ => abs_nonneg _) i
    have hc := gje_c3_nonneg (R.model t) n R.dimension_pos (R.valid_three t)
    calc
      |Δy t i| ≤ gje_c₃ (R.model t) n *
          matMulVec n (ch14ext_gjeExactQPEnvelope F t)
            (absVec n (R.xseq t start)) i := hraw
      _ ≤ gje_c₃ (R.model t) n *
          (matMulVec n (ch14ext_gjePrintedUinvEnvelope F t)
              (absVec n (R.xseq t start)) i +
            gje_c₃ (R.model t) n *
              matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t)
                (absVec n (R.xseq t start)) i) :=
        mul_le_mul_of_nonneg_left hreplace hc
      _ = gje_c₃ (R.model t) n *
          matMulVec n (ch14ext_gjePrintedUinvEnvelope F t)
            (absVec n (R.xseq t start)) i +
          ch14ext_gje1430cPrintedRemainder F (fun q => R.xseq q start) t i := by
        unfold ch14ext_gje1430cPrintedRemainder
        dsimp only [F, ch14ext_gjeConcretePrintedEnvelopeFamily]
        ring
  · intro i j
    exact ch14ext_gje1430bPrintedRemainder_isBigO_unit_sq F i j
  · intro i
    exact ch14ext_gje1430cPrintedRemainder_isBigO_unit_sq F
      (fun q => R.xseq q start) R.y_isBigO_one i

/-! ## Printed equation (14.31) -/

/-- The literal first-order object printed in (14.31):
`|Lhat| |Uhat| |Uhat^-1| |Uhat| |xhat|`. -/
noncomputable def ch14ext_gje1431PrintedLeading
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n)
    (L : ι → Fin n → Fin n → ℝ) (x_hat : ι → Fin n → ℝ)
    (t : ι) (i : Fin n) : ℝ :=
  matMulVec n (absMatrix n (L t))
    (matMulVec n (absMatrix n (F.U_hat t))
      (matMulVec n (absMatrix n (F.U_inv t))
        (matMulVec n (absMatrix n (F.U_hat t))
          (absVec n (x_hat t))))) i

/-- The bounded action multiplying the extra `c3` generated by replacing
`|Q| Pabs` with `|Uhat| |Uhat^-1|` in (14.31). -/
noncomputable def ch14ext_gje1431EnvelopeCorrectionAction
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n)
    (L : ι → Fin n → Fin n → ℝ) (x_hat : ι → Fin n → ℝ)
    (t : ι) (i : Fin n) : ℝ :=
  matMulVec n (absMatrix n (L t))
    (matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t)
      (matMulVec n (absMatrix n (F.U_hat t))
        (absVec n (x_hat t)))) i

/-- The exact second-stage residual source object is bounded by the literal
printed (14.31) object plus the explicit product-replacement correction. -/
theorem ch14ext_gjeResidualS2_le_1431PrintedLeading_add_correction
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n)
    (L : ι → Fin n → Fin n → ℝ) (x_hat : ι → Fin n → ℝ)
    (t : ι) (i : Fin n) :
    ch14ext_gjeResidualS2 n (L t) (ch14ext_gjeExactQPEnvelope F t)
        (F.U_hat t) (x_hat t) i ≤
      ch14ext_gje1431PrintedLeading F L x_hat t i +
        gje_c₃ (F.model t) n *
          ch14ext_gje1431EnvelopeCorrectionAction F L x_hat t i := by
  let w := matMulVec n (absMatrix n (F.U_hat t)) (absVec n (x_hat t))
  have hw : ∀ j : Fin n, 0 ≤ w j := by
    intro j
    exact ch14ext_absMatrix_action_nonneg n (F.U_hat t)
      (absVec n (x_hat t)) (fun k => abs_nonneg (x_hat t k)) j
  have hinner : ∀ a : Fin n,
      matMulVec n (ch14ext_gjeExactQPEnvelope F t) w a ≤
        matMulVec n (ch14ext_gjePrintedUinvEnvelope F t) w a +
          gje_c₃ (F.model t) n *
            matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t) w a := by
    intro a
    exact ch14ext_gjeExactQPEnvelope_matMulVec_le_printed_add_correction
      F t w hw a
  have houter := ch14ext_matMulVec_mono_nonneg n (absMatrix n (L t))
    (matMulVec n (ch14ext_gjeExactQPEnvelope F t) w)
    (fun a =>
      matMulVec n (ch14ext_gjePrintedUinvEnvelope F t) w a +
        gje_c₃ (F.model t) n *
          matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t) w a)
    (fun a j => abs_nonneg (L t a j)) hinner i
  have hlinear :
      matMulVec n (absMatrix n (L t))
          (fun a =>
            matMulVec n (ch14ext_gjePrintedUinvEnvelope F t) w a +
              gje_c₃ (F.model t) n *
                matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t) w a) i =
        matMulVec n (absMatrix n (L t))
            (matMulVec n (ch14ext_gjePrintedUinvEnvelope F t) w) i +
          gje_c₃ (F.model t) n *
            matMulVec n (absMatrix n (L t))
              (matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t) w) i := by
    unfold matMulVec
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hPrintedAction :
      matMulVec n (ch14ext_gjePrintedUinvEnvelope F t) w =
        matMulVec n (absMatrix n (F.U_hat t))
          (matMulVec n (absMatrix n (F.U_inv t)) w) := by
    funext a
    simpa only [ch14ext_gjePrintedUinvEnvelope] using
      matMulVec_matMul n (absMatrix n (F.U_hat t))
        (absMatrix n (F.U_inv t)) w a
  have hExactAbs : absMatrix n (ch14ext_gjeExactQPEnvelope F t) =
      ch14ext_gjeExactQPEnvelope F t := by
    funext a j
    exact abs_of_nonneg (ch14ext_gjeExactQPEnvelope_nonneg F t a j)
  unfold ch14ext_gjeResidualS2
  change matMulVec n (absMatrix n (L t))
      (matMulVec n (absMatrix n (ch14ext_gjeExactQPEnvelope F t)) w) i ≤ _
  rw [hExactAbs]
  rw [hlinear] at houter
  rw [hPrintedAction] at houter
  simpa only [ch14ext_gje1431PrintedLeading,
    ch14ext_gje1431EnvelopeCorrectionAction, w] using houter

theorem ch14ext_gje1431EnvelopeCorrectionAction_isBigOOne
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n)
    (L : ι → Fin n → Fin n → ℝ) (x_hat : ι → Fin n → ℝ)
    (hL : MatrixFamilyIsBigOOne l L)
    (hx : VectorFamilyIsBigOOne l x_hat) (i : Fin n) :
    (fun t => ch14ext_gje1431EnvelopeCorrectionAction F L x_hat t i)
      =O[l] (fun _ : ι => (1 : ℝ)) := by
  have hUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne F.U_hat_isBigO_one)
    (ch14ext_vectorFamily_abs_isBigOOne hx)
  have hCorrectionUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (ch14ext_gjePrintedEnvelopeCorrection_isBigOOne F) hUx
  have hLCorrectionUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hL) hCorrectionUx
  simpa only [ch14ext_gje1431EnvelopeCorrectionAction] using
    hLCorrectionUx i

/-- The complete explicit remainder in the printed (14.31) endpoint.  Its
first summand is the concrete accumulation theorem's higher-order term; its
second summand records exactly the envelope replacement. -/
noncomputable def ch14ext_gje1431PrintedRemainder
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n)
    (L : ι → Fin n → Fin n → ℝ) (y x_hat : ι → Fin n → ℝ)
    (t : ι) (i : Fin n) : ℝ :=
  ch14ext_gjeResidualHigherOrder n (F.model t) (L t)
      (ch14ext_gjeExactQPEnvelope F t) (F.U_hat t) (y t) (x_hat t) i +
    8 * (n : ℝ) * (F.model t).u * gje_c₃ (F.model t) n *
      ch14ext_gje1431EnvelopeCorrectionAction F L x_hat t i

theorem ch14ext_gje1431PrintedRemainder_isBigO_unit_sq
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n)
    (L : ι → Fin n → Fin n → ℝ) (y x_hat : ι → Fin n → ℝ)
    (hL : MatrixFamilyIsBigOOne l L)
    (hy : VectorFamilyIsBigOOne l y)
    (hx : VectorFamilyIsBigOOne l x_hat) (i : Fin n) :
    (fun t => ch14ext_gje1431PrintedRemainder F L y x_hat t i)
      =O[l] (fun t => (F.model t).u ^ 2) := by
  have hHigher := ch14ext_gjeResidualHigherOrder_family_isBigO n F.model L
    (ch14ext_gjeExactQPEnvelope F) F.U_hat y x_hat F.unit_tendsto_zero
    hL F.exact_envelope_isBigO_one F.U_hat_isBigO_one hy hx i
  have hu : (fun t => (F.model t).u) =O[l]
      (fun t => (F.model t).u) :=
    Asymptotics.isBigO_refl (fun t => (F.model t).u) l
  have hc3 := ch14ext_gje_c3_family_isBigO_unit n F.model
    F.unit_tendsto_zero
  have hcoefficient :
      (fun t => 8 * (n : ℝ) * (F.model t).u * gje_c₃ (F.model t) n)
        =O[l] (fun t => (F.model t).u ^ 2) := by
    simpa only [pow_two, mul_assoc] using
      (hu.mul hc3).const_mul_left (8 * (n : ℝ))
  have hCorrection :=
    ch14ext_gje1431EnvelopeCorrectionAction_isBigOOne F L x_hat hL hx i
  have hReplacement :
      (fun t =>
        8 * (n : ℝ) * (F.model t).u * gje_c₃ (F.model t) n *
          ch14ext_gje1431EnvelopeCorrectionAction F L x_hat t i)
        =O[l] (fun t => (F.model t).u ^ 2) := by
    simpa only [mul_one] using hcoefficient.mul hCorrection
  simpa only [ch14ext_gje1431PrintedRemainder] using
    hHigher.add hReplacement

/-- **Higham (14.31), actual rounded GJE, printed envelope.**

The exact accumulation object is replaced by the literal printed chain
`|Lhat| |Uhat| |Uhat^-1| |Uhat| |xhat|`.  The difference is retained in an
explicit remainder proved `O(u^2)` over a nontrivial filter. -/
theorem ch14ext_gjeConcrete_14_31_printed_vanishing_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ} {start : ℕ}
    (R : Ch14GJEConcreteFamily ι l n A b start)
    (U_inv : ι → Fin n → Fin n → ℝ)
    (hUinv : ∀ t, IsRightInverse n (R.V t start) (U_inv t))
    (hUinv_one : MatrixFamilyIsBigOOne l U_inv) :
    (∀ t i,
      |b i - matMulVec n A (R.x_hat t) i| ≤
        8 * (n : ℝ) * (R.model t).u *
          ch14ext_gje1431PrintedLeading
            (ch14ext_gjeConcretePrintedEnvelopeFamily R U_inv hUinv
              hUinv_one) R.L_hat R.x_hat t i +
        ch14ext_gje1431PrintedRemainder
          (ch14ext_gjeConcretePrintedEnvelopeFamily R U_inv hUinv
            hUinv_one) R.L_hat (fun q => R.xseq q start) R.x_hat t i) ∧
      ∀ i,
        (fun t => ch14ext_gje1431PrintedRemainder
          (ch14ext_gjeConcretePrintedEnvelopeFamily R U_inv hUinv
            hUinv_one) R.L_hat (fun q => R.xseq q start) R.x_hat t i)
          =O[l] (fun t => (R.model t).u ^ 2) := by
  let F := ch14ext_gjeConcretePrintedEnvelopeFamily R U_inv hUinv
    hUinv_one
  have hbase := ch14ext_gjeConcrete_residual_14_31_vanishing_family_endpoint
    n A b start R
  constructor
  · intro t i
    have hEnvelope : ch14ext_gjeExactQPEnvelope F t =
        ch14ext_gjeConcreteFamilyXabs R t := by
      rfl
    have hraw : |b i - matMulVec n A (R.x_hat t) i| ≤
        8 * (n : ℝ) * (F.model t).u *
          ch14ext_gjeResidualS2 n (R.L_hat t)
            (ch14ext_gjeExactQPEnvelope F t) (F.U_hat t)
            (R.x_hat t) i +
        ch14ext_gjeResidualHigherOrder n (F.model t) (R.L_hat t)
          (ch14ext_gjeExactQPEnvelope F t) (F.U_hat t)
          (R.xseq t start) (R.x_hat t) i := by
      rw [hEnvelope]
      exact hbase.1 t i
    have hreplace :=
      ch14ext_gjeResidualS2_le_1431PrintedLeading_add_correction
        F R.L_hat R.x_hat t i
    have hcoefficient : 0 ≤ 8 * (n : ℝ) * (F.model t).u :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
        (F.model t).u_nonneg
    have hscaled := mul_le_mul_of_nonneg_left hreplace hcoefficient
    calc
      |b i - matMulVec n A (R.x_hat t) i| ≤
          8 * (n : ℝ) * (F.model t).u *
            ch14ext_gjeResidualS2 n (R.L_hat t)
              (ch14ext_gjeExactQPEnvelope F t) (F.U_hat t)
              (R.x_hat t) i +
          ch14ext_gjeResidualHigherOrder n (F.model t) (R.L_hat t)
            (ch14ext_gjeExactQPEnvelope F t) (F.U_hat t)
            (R.xseq t start) (R.x_hat t) i := hraw
      _ ≤ 8 * (n : ℝ) * (F.model t).u *
            (ch14ext_gje1431PrintedLeading F R.L_hat R.x_hat t i +
              gje_c₃ (F.model t) n *
                ch14ext_gje1431EnvelopeCorrectionAction
                  F R.L_hat R.x_hat t i) +
          ch14ext_gjeResidualHigherOrder n (F.model t) (R.L_hat t)
            (ch14ext_gjeExactQPEnvelope F t) (F.U_hat t)
            (R.xseq t start) (R.x_hat t) i :=
        add_le_add hscaled (le_refl _)
      _ = 8 * (n : ℝ) * (R.model t).u *
            ch14ext_gje1431PrintedLeading F R.L_hat R.x_hat t i +
          ch14ext_gje1431PrintedRemainder F R.L_hat
            (fun q => R.xseq q start) R.x_hat t i := by
        unfold ch14ext_gje1431PrintedRemainder
        dsimp only [F, ch14ext_gjeConcretePrintedEnvelopeFamily]
        ring
  · intro i
    exact ch14ext_gje1431PrintedRemainder_isBigO_unit_sq F R.L_hat
      (fun q => R.xseq q start) R.x_hat R.L_hat_isBigO_one
      R.y_isBigO_one R.x_hat_isBigO_one i

end NumStability.Ch14Ext
