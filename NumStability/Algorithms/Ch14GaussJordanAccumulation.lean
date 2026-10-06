-- Algorithms/Ch14GaussJordanAccumulation.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 14 ("Matrix Inversion"), §14.4 ("Gauss-Jordan Elimination"),
-- equations (14.27)-(14.33) and Theorem 14.5, pp. 274-276.
--
-- PURPOSE.  `Ch14GaussJordanStep.lean` (wave 2) DERIVED the EXACT per-step
-- backward equations of the GJE second stage from the floating-point model:
--     Û_{k+1} = N̂ₖ Ûₖ + Δ_k ,  |Δ_k| ≤ γ₃ |N̂ₖ| |Ûₖ|        (14.25a/b)
--     x̂_{k+1} = N̂ₖ x̂ₖ + f_k ,  |f_k| ≤ γ₃ |N̂ₖ| |x̂ₖ|        (14.26)
-- (`ch14ext_gje_stage2_matrix_backward_eq`, `..._rhs_backward_eq`).
--
-- THIS MODULE performs the MULTI-STAGE ACCUMULATION (14.27)-(14.30) that wave 2
-- explicitly left open: it telescopes the `steps = n-1` stages into
--     V_final = (∏ N̂) · V_start + E ,        E := V_final − (∏ N̂) V_start
-- and DERIVES, UNCONDITIONALLY, the cumulative componentwise bounds
--     |V_k| ≤ (1+γ₃)^k · (|N̂|···|N̂|) |V_start|                      (growth)
--     |E|  ≤ ((1+γ₃)^{steps} − 1) · (|N̂|···|N̂|) |V_start|
--          ≤ c₃ · |X| |U|,   c₃ = (n−1)γ₃(1+γ₃)^{n−2}              (14.27)-tail
-- via the Duhamel recurrence E_{m+1} = N̂ₘ E_m + Δ_m together with the
-- (1+γ₃) growth envelope.  Both the matrix form (for |ΔU_total|) and the
-- vector form (for |Δy_total|) are proved.
--
-- The abstract accumulation is stated over ANY stage sequence obeying the
-- per-step γ₃ bound (exactly wave 2's output shape), so `ch14ext_gjeStepMatrix`
-- / `ch14ext_gjeStepVec` discharge the hypotheses verbatim.
--
-- These accumulated ΔU_total / Δy_total bounds are then fed into Codex's
-- `gje_overall_residual` / `gje_overall_forward_error` sockets to expose the
-- Theorem 14.5 endpoints (14.31)/(14.32).  The honest structural facts used are
-- (i) Higham's own WLOG normalization D = I (the final reduced matrix is the
-- identity — "negligible effect on the final bounds", p. 274) and (ii) a given
-- left inverse Q of the cumulative product (the file already gives A⁻¹ as data
-- in `gje_overall_forward_error`).  See the socket-feeding docstrings.
--
-- Import-only companion; does not modify `GaussJordan.lean` or
-- `Ch14GaussJordanStep.lean`.

import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.GaussJordan
import NumStability.Algorithms.Ch14GaussJordanStep

namespace NumStability.Ch14Ext

open scoped BigOperators
open NumStability

-- ══════════════════════════════════════════════════════════════════════
-- §1  Accumulation bound object |N̂|···|N̂| · |V_start|
-- ══════════════════════════════════════════════════════════════════════

/-- Absolute cumulative product `|N̂_{start+steps-1}| ··· |N̂_start|` of the GJE
    stage matrices — the `|X|` envelope of (14.27). -/
noncomputable def ch14ext_absCumProd (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (start steps : ℕ) : Fin n → Fin n → ℝ :=
  gje_cumulative_product n (fun k a b => |N_hat k a b|) start (start + steps)

/-- The Chapter-14 accumulation envelope `(|N̂|···|N̂|) · |V_start|` bounding both
    the running iterate `|V_k|` and the accumulated error `|E_k|`. -/
noncomputable def ch14ext_boundObj (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (V0 : Fin n → Fin n → ℝ)
    (start steps : ℕ) : Fin n → Fin n → ℝ :=
  matMul n (ch14ext_absCumProd n N_hat start steps) (absMatrix n V0)

/-- The bound object is entrywise nonnegative. -/
theorem ch14ext_boundObj_nonneg (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (V0 : Fin n → Fin n → ℝ)
    (start steps : ℕ) (i j : Fin n) :
    0 ≤ ch14ext_boundObj n N_hat V0 start steps i j := by
  unfold ch14ext_boundObj matMul
  exact Finset.sum_nonneg fun l _ =>
    mul_nonneg
      (gje_cumulative_product_abs_nonneg n N_hat start (start + steps) i l)
      (abs_nonneg _)

/-- Base case of the accumulation envelope: zero stages give `|V_start|`. -/
theorem ch14ext_boundObj_zero (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (V0 : Fin n → Fin n → ℝ)
    (start : ℕ) (i j : Fin n) :
    ch14ext_boundObj n N_hat V0 start 0 i j = |V0 i j| := by
  unfold ch14ext_boundObj ch14ext_absCumProd
  rw [Nat.add_zero,
    gje_cumulative_product_base n (fun k a b => |N_hat k a b|) (le_refl start),
    matMul_id_left]
  rfl

/-- Duhamel/step recurrence for the accumulation envelope:
    `boundObj (steps+1) = |N̂_{start+steps}| · boundObj steps`. -/
theorem ch14ext_boundObj_succ (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (V0 : Fin n → Fin n → ℝ)
    (start steps : ℕ) (h : start + steps < n) (i j : Fin n) :
    ch14ext_boundObj n N_hat V0 start (steps + 1) i j =
      ∑ l : Fin n, |N_hat ⟨start + steps, h⟩ i l| *
        ch14ext_boundObj n N_hat V0 start steps l j := by
  have hstep : start < start + (steps + 1) :=
    Nat.lt_add_of_pos_right (Nat.succ_pos steps)
  have hfin_eq : start + (steps + 1) - 1 = start + steps := by simp
  have hidx : start + (steps + 1) - 1 < n := by rw [hfin_eq]; exact h
  have hfin : (⟨start + (steps + 1) - 1, hidx⟩ : Fin n) =
      ⟨start + steps, h⟩ := by apply Fin.ext; simp
  have hcp_prev :
      gje_cumulative_product n (fun k a b => |N_hat k a b|)
          start (start + (steps + 1) - 1) =
        gje_cumulative_product n (fun k a b => |N_hat k a b|)
          start (start + steps) := by rw [hfin_eq]
  have hcp :
      gje_cumulative_product n (fun k a b => |N_hat k a b|)
          start (start + (steps + 1)) =
        matMul n (fun a b => |N_hat ⟨start + steps, h⟩ a b|)
          (gje_cumulative_product n (fun k a b => |N_hat k a b|)
            start (start + steps)) := by
    rw [gje_cumulative_product_step n (fun k a b => |N_hat k a b|) hstep hidx,
      hfin, hcp_prev]
  -- boundObj (steps+1) = matMul (|N̂| · absCumProd steps) absV0
  --                    = matMul |N̂| (matMul absCumProd steps absV0)
  unfold ch14ext_boundObj ch14ext_absCumProd
  rw [hcp, matMul_assoc]
  rfl

-- ══════════════════════════════════════════════════════════════════════
-- §2  (14.27)-tail growth:  |V_k| ≤ (1+γ₃)^k · boundObj
-- ══════════════════════════════════════════════════════════════════════

/-- **Higham (14.27) growth envelope — DERIVED.**

    From the per-step bound `|V_{k+1} − N̂ₖ Vₖ| ≤ γ₃ |N̂ₖ| |Vₖ|` alone, the
    running computed iterate satisfies the componentwise growth
        `|V_{start+steps}| ≤ (1+γ₃)^{steps} · (|N̂|···|N̂|) |V_start|`.
    This is the `(1+γ₃)` amplification per stage that underlies the cumulative
    `(1+γ₃)^{n−2}` factor of `c₃`. -/
theorem ch14ext_stageGrowth (n : ℕ) (fp : FPModel)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (V : ℕ → Fin n → Fin n → ℝ)
    (start steps : ℕ) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < steps → start + t < n)
    (hrec : ∀ t : ℕ, (ht : t < steps) → ∀ i j : Fin n,
      |V (start + (t + 1)) i j -
          ∑ l : Fin n, N_hat ⟨start + t, hidx t ht⟩ i l * V (start + t) l j| ≤
        gamma fp 3 *
          ∑ l : Fin n, |N_hat ⟨start + t, hidx t ht⟩ i l| * |V (start + t) l j|) :
    ∀ i j : Fin n,
      |V (start + steps) i j| ≤
        (1 + gamma fp 3) ^ steps *
          ch14ext_boundObj n N_hat (V start) start steps i j := by
  have hg : 0 ≤ gamma fp 3 := gamma_nonneg fp h3
  induction steps with
  | zero =>
      intro i j
      rw [Nat.add_zero, pow_zero, one_mul, ch14ext_boundObj_zero]
  | succ steps ih =>
      intro i j
      have hidx_prev : ∀ t : ℕ, t < steps → start + t < n :=
        fun t ht => hidx t (Nat.lt_trans ht (Nat.lt_succ_self steps))
      have hrec_prev : ∀ t : ℕ, (ht : t < steps) → ∀ i j : Fin n,
          |V (start + (t + 1)) i j -
              ∑ l : Fin n, N_hat ⟨start + t, hidx_prev t ht⟩ i l *
                V (start + t) l j| ≤
            gamma fp 3 * ∑ l : Fin n,
              |N_hat ⟨start + t, hidx_prev t ht⟩ i l| * |V (start + t) l j| := by
        intro t ht i j
        simpa using hrec t (Nat.lt_trans ht (Nat.lt_succ_self steps)) i j
      have ih' := ih hidx_prev hrec_prev
      have hlt : steps < steps + 1 := Nat.lt_succ_self steps
      have htop : start + steps < n := hidx steps hlt
      -- per-step at t = steps
      have hstepbnd := hrec steps hlt i j
      set S : ℝ := ∑ l : Fin n, N_hat ⟨start + steps, htop⟩ i l * V (start + steps) l j
        with hS
      set T : ℝ := ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| * |V (start + steps) l j|
        with hT
      -- |V_{steps+1}| ≤ (1+γ₃) · T
      have habs_sum : |S| ≤ T := by
        rw [hS, hT]
        calc |∑ l : Fin n, N_hat ⟨start + steps, htop⟩ i l * V (start + steps) l j|
            ≤ ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l * V (start + steps) l j| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| * |V (start + steps) l j| :=
              Finset.sum_congr rfl (fun l _ => abs_mul _ _)
      have hrow : |V (start + (steps + 1)) i j| ≤ (1 + gamma fp 3) * T := by
        have htri : |V (start + (steps + 1)) i j| ≤
            |V (start + (steps + 1)) i j - S| + |S| := by
          calc |V (start + (steps + 1)) i j|
              = |(V (start + (steps + 1)) i j - S) + S| := by ring_nf
            _ ≤ |V (start + (steps + 1)) i j - S| + |S| := abs_add_le _ _
        calc |V (start + (steps + 1)) i j|
            ≤ |V (start + (steps + 1)) i j - S| + |S| := htri
          _ ≤ gamma fp 3 * T + T := by linarith [hstepbnd, habs_sum]
          _ = (1 + gamma fp 3) * T := by ring
      -- bound the row-sum via the growth IH on |V_steps l j|
      have hgrow_row :
          T ≤ (1 + gamma fp 3) ^ steps *
              ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| *
                ch14ext_boundObj n N_hat (V start) start steps l j := by
        rw [hT, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro l _
        have hIHl := ih' l j
        calc |N_hat ⟨start + steps, htop⟩ i l| * |V (start + steps) l j|
            ≤ |N_hat ⟨start + steps, htop⟩ i l| *
                ((1 + gamma fp 3) ^ steps *
                  ch14ext_boundObj n N_hat (V start) start steps l j) :=
              mul_le_mul_of_nonneg_left hIHl (abs_nonneg _)
          _ = (1 + gamma fp 3) ^ steps *
                (|N_hat ⟨start + steps, htop⟩ i l| *
                  ch14ext_boundObj n N_hat (V start) start steps l j) := by ring
      -- assemble
      have hbase_nonneg : 0 ≤ 1 + gamma fp 3 := by linarith
      have hsucc :
          ch14ext_boundObj n N_hat (V start) start (steps + 1) i j =
            ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| *
              ch14ext_boundObj n N_hat (V start) start steps l j :=
        ch14ext_boundObj_succ n N_hat (V start) start steps htop i j
      calc |V (start + (steps + 1)) i j|
          ≤ (1 + gamma fp 3) * T := hrow
        _ ≤ (1 + gamma fp 3) *
              ((1 + gamma fp 3) ^ steps *
                ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| *
                  ch14ext_boundObj n N_hat (V start) start steps l j) :=
            mul_le_mul_of_nonneg_left hgrow_row hbase_nonneg
        _ = (1 + gamma fp 3) ^ (steps + 1) *
              ch14ext_boundObj n N_hat (V start) start (steps + 1) i j := by
            rw [hsucc, pow_succ]; ring

-- ══════════════════════════════════════════════════════════════════════
-- §3  (14.27) accumulation:  |V_final − (∏N̂) V_start| ≤ ((1+γ₃)^steps−1)·envelope
-- ══════════════════════════════════════════════════════════════════════

/-- **Higham (14.27) matrix accumulation — DERIVED.**

    Telescoping the `steps` per-step backward equations
    `V_{k+1} = N̂ₖ Vₖ + Δ_k` (`|Δ_k| ≤ γ₃|N̂ₖ||Vₖ|`) via the Duhamel recurrence
    `E_{k+1} = N̂ₖ E_k + Δ_k`, the accumulated error
    `E := V_{start+steps} − (∏ N̂) V_start` satisfies the componentwise bound
        `|E| ≤ ((1+γ₃)^{steps} − 1) · (|N̂|···|N̂|) |V_start|`.
    This is exactly the source line
    `|∑Δ_k| ≤ (n−1)γ₃(1+γ₃)^{n−2}|X||U|` before folding the scalar envelope. -/
theorem ch14ext_matrixAccumulation (n : ℕ) (fp : FPModel)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (V : ℕ → Fin n → Fin n → ℝ)
    (start steps : ℕ) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < steps → start + t < n)
    (hrec : ∀ t : ℕ, (ht : t < steps) → ∀ i j : Fin n,
      |V (start + (t + 1)) i j -
          ∑ l : Fin n, N_hat ⟨start + t, hidx t ht⟩ i l * V (start + t) l j| ≤
        gamma fp 3 *
          ∑ l : Fin n, |N_hat ⟨start + t, hidx t ht⟩ i l| * |V (start + t) l j|) :
    ∀ i j : Fin n,
      |V (start + steps) i j -
          matMul n (gje_cumulative_product n N_hat start (start + steps))
            (V start) i j| ≤
        ((1 + gamma fp 3) ^ steps - 1) *
          ch14ext_boundObj n N_hat (V start) start steps i j := by
  have hg : 0 ≤ gamma fp 3 := gamma_nonneg fp h3
  have hbase_nonneg : 0 ≤ 1 + gamma fp 3 := by linarith
  induction steps with
  | zero =>
      intro i j
      rw [Nat.add_zero,
        gje_cumulative_product_base n N_hat (le_refl start), matMul_id_left,
        pow_zero]
      simp
  | succ m ih =>
      intro i j
      have hidx_prev : ∀ t : ℕ, t < m → start + t < n :=
        fun t ht => hidx t (Nat.lt_trans ht (Nat.lt_succ_self m))
      have hrec_prev : ∀ t : ℕ, (ht : t < m) → ∀ i j : Fin n,
          |V (start + (t + 1)) i j -
              ∑ l : Fin n, N_hat ⟨start + t, hidx_prev t ht⟩ i l *
                V (start + t) l j| ≤
            gamma fp 3 * ∑ l : Fin n,
              |N_hat ⟨start + t, hidx_prev t ht⟩ i l| * |V (start + t) l j| := by
        intro t ht i j
        simpa using hrec t (Nat.lt_trans ht (Nat.lt_succ_self m)) i j
      have ih' := ih hidx_prev hrec_prev
      have hlt : m < m + 1 := Nat.lt_succ_self m
      have htop : start + m < n := hidx m hlt
      -- P_{m+1} = N̂_m · P_m
      have hstep : start < start + (m + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos m)
      have hfin_eq : start + (m + 1) - 1 = start + m := by simp
      have hidxP : start + (m + 1) - 1 < n := by rw [hfin_eq]; exact htop
      have hfin : (⟨start + (m + 1) - 1, hidxP⟩ : Fin n) = ⟨start + m, htop⟩ := by
        apply Fin.ext; simp
      have hcp_prev :
          gje_cumulative_product n N_hat start (start + (m + 1) - 1) =
            gje_cumulative_product n N_hat start (start + m) := by rw [hfin_eq]
      have hPstep :
          gje_cumulative_product n N_hat start (start + (m + 1)) =
            matMul n (N_hat ⟨start + m, htop⟩)
              (gje_cumulative_product n N_hat start (start + m)) := by
        rw [gje_cumulative_product_step n N_hat hstep hidxP, hfin, hcp_prev]
      -- rewrite the accumulated one-step target
      have hBmat :
          matMul n (gje_cumulative_product n N_hat start (start + (m + 1)))
              (V start) i j =
            ∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l *
              matMul n (gje_cumulative_product n N_hat start (start + m))
                (V start) l j := by
        rw [hPstep, matMul_assoc]; rfl
      -- growth of V at level m
      have hgrowth := ch14ext_stageGrowth n fp N_hat V start m h3 hidx_prev hrec_prev
      -- per-step at level m
      have hstepbnd := hrec m hlt i j
      -- R := boundObj_{m+1} i j = ∑_l |N̂_m i l| boundObj_m l j
      have hRsucc :
          ch14ext_boundObj n N_hat (V start) start (m + 1) i j =
            ∑ l : Fin n, |N_hat ⟨start + m, htop⟩ i l| *
              ch14ext_boundObj n N_hat (V start) start m l j :=
        ch14ext_boundObj_succ n N_hat (V start) start m htop i j
      have hpowm_nonneg : 0 ≤ (1 + gamma fp 3) ^ m := pow_nonneg hbase_nonneg _
      have hR_nonneg : ∀ l : Fin n,
          0 ≤ ch14ext_boundObj n N_hat (V start) start m l j :=
        fun l => ch14ext_boundObj_nonneg n N_hat (V start) start m l j
      -- |A − B| ≤ ((1+γ₃)^m − 1) · boundObj_{m+1}
      have hAB :
          |(∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l * V (start + m) l j) -
              (∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l *
                matMul n (gje_cumulative_product n N_hat start (start + m))
                  (V start) l j)| ≤
            ((1 + gamma fp 3) ^ m - 1) *
              ch14ext_boundObj n N_hat (V start) start (m + 1) i j := by
        have heq :
            (∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l * V (start + m) l j) -
                (∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l *
                  matMul n (gje_cumulative_product n N_hat start (start + m))
                    (V start) l j) =
              ∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l *
                (V (start + m) l j -
                  matMul n (gje_cumulative_product n N_hat start (start + m))
                    (V start) l j) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun l _ => by ring)
        rw [heq, hRsucc, Finset.mul_sum]
        calc |∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l *
                (V (start + m) l j -
                  matMul n (gje_cumulative_product n N_hat start (start + m))
                    (V start) l j)|
            ≤ ∑ l : Fin n, |N_hat ⟨start + m, htop⟩ i l| *
                |V (start + m) l j -
                  matMul n (gje_cumulative_product n N_hat start (start + m))
                    (V start) l j| := by
                refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
                exact le_of_eq (Finset.sum_congr rfl (fun l _ => abs_mul _ _))
          _ ≤ ∑ l : Fin n, ((1 + gamma fp 3) ^ m - 1) *
                (|N_hat ⟨start + m, htop⟩ i l| *
                  ch14ext_boundObj n N_hat (V start) start m l j) := by
                apply Finset.sum_le_sum
                intro l _
                have hIHl := ih' l j
                calc |N_hat ⟨start + m, htop⟩ i l| *
                      |V (start + m) l j -
                        matMul n (gje_cumulative_product n N_hat start (start + m))
                          (V start) l j|
                    ≤ |N_hat ⟨start + m, htop⟩ i l| *
                        (((1 + gamma fp 3) ^ m - 1) *
                          ch14ext_boundObj n N_hat (V start) start m l j) :=
                      mul_le_mul_of_nonneg_left hIHl (abs_nonneg _)
                  _ = ((1 + gamma fp 3) ^ m - 1) *
                        (|N_hat ⟨start + m, htop⟩ i l| *
                          ch14ext_boundObj n N_hat (V start) start m l j) := by ring
      -- γ₃·∑|N̂||V_m| ≤ γ₃·(1+γ₃)^m · boundObj_{m+1}
      have hGrow :
          gamma fp 3 *
              (∑ l : Fin n, |N_hat ⟨start + m, htop⟩ i l| * |V (start + m) l j|) ≤
            gamma fp 3 * ((1 + gamma fp 3) ^ m *
              ch14ext_boundObj n N_hat (V start) start (m + 1) i j) := by
        apply mul_le_mul_of_nonneg_left _ hg
        rw [hRsucc, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro l _
        have hgl := hgrowth l j
        calc |N_hat ⟨start + m, htop⟩ i l| * |V (start + m) l j|
            ≤ |N_hat ⟨start + m, htop⟩ i l| *
                ((1 + gamma fp 3) ^ m *
                  ch14ext_boundObj n N_hat (V start) start m l j) :=
              mul_le_mul_of_nonneg_left hgl (abs_nonneg _)
          _ = (1 + gamma fp 3) ^ m *
                (|N_hat ⟨start + m, htop⟩ i l| *
                  ch14ext_boundObj n N_hat (V start) start m l j) := by ring
      -- assemble the telescoped error at level m+1
      set R : ℝ := ch14ext_boundObj n N_hat (V start) start (m + 1) i j with hRdef
      have hRnn : 0 ≤ R := ch14ext_boundObj_nonneg n N_hat (V start) start (m + 1) i j
      have htri :
          |V (start + (m + 1)) i j -
              matMul n (gje_cumulative_product n N_hat start (start + (m + 1)))
                (V start) i j| ≤
            gamma fp 3 *
              (∑ l : Fin n, |N_hat ⟨start + m, htop⟩ i l| * |V (start + m) l j|) +
            ((1 + gamma fp 3) ^ m - 1) * R := by
        rw [hBmat]
        set A : ℝ := ∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l * V (start + m) l j
          with hAdef
        set B : ℝ := ∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l *
          matMul n (gje_cumulative_product n N_hat start (start + m)) (V start) l j
          with hBdef
        have hsplit :
            V (start + (m + 1)) i j - B =
              (V (start + (m + 1)) i j - A) + (A - B) := by ring
        calc |V (start + (m + 1)) i j - B|
            = |(V (start + (m + 1)) i j - A) + (A - B)| := by rw [hsplit]
          _ ≤ |V (start + (m + 1)) i j - A| + |A - B| := abs_add_le _ _
          _ ≤ gamma fp 3 *
                (∑ l : Fin n, |N_hat ⟨start + m, htop⟩ i l| * |V (start + m) l j|) +
              ((1 + gamma fp 3) ^ m - 1) * R := by
                exact add_le_add hstepbnd hAB
      -- fold (γ₃(1+γ₃)^m + (1+γ₃)^m − 1)·R = ((1+γ₃)^{m+1} − 1)·R
      calc |V (start + (m + 1)) i j -
              matMul n (gje_cumulative_product n N_hat start (start + (m + 1)))
                (V start) i j|
          ≤ gamma fp 3 *
              (∑ l : Fin n, |N_hat ⟨start + m, htop⟩ i l| * |V (start + m) l j|) +
            ((1 + gamma fp 3) ^ m - 1) * R := htri
        _ ≤ gamma fp 3 * ((1 + gamma fp 3) ^ m * R) +
              ((1 + gamma fp 3) ^ m - 1) * R := by
              exact add_le_add hGrow (le_refl _)
        _ = ((1 + gamma fp 3) ^ (m + 1) - 1) * R := by rw [pow_succ]; ring

-- ══════════════════════════════════════════════════════════════════════
-- §4  (14.28) right-hand-side accumulation (vector form)
-- ══════════════════════════════════════════════════════════════════════

/-- Vector analogue of `ch14ext_boundObj`: the envelope `(|N̂|···|N̂|)·|v_start|`
    bounding the running RHS iterate `|x_k|` and the RHS error `|g_k|`. -/
noncomputable def ch14ext_boundVec (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (v0 : Fin n → ℝ)
    (start steps : ℕ) : Fin n → ℝ :=
  matMulVec n (ch14ext_absCumProd n N_hat start steps) (absVec n v0)

theorem ch14ext_boundVec_nonneg (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (v0 : Fin n → ℝ)
    (start steps : ℕ) (i : Fin n) :
    0 ≤ ch14ext_boundVec n N_hat v0 start steps i := by
  unfold ch14ext_boundVec matMulVec
  exact Finset.sum_nonneg fun l _ =>
    mul_nonneg
      (gje_cumulative_product_abs_nonneg n N_hat start (start + steps) i l)
      (abs_nonneg _)

theorem ch14ext_boundVec_zero (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (v0 : Fin n → ℝ)
    (start : ℕ) (i : Fin n) :
    ch14ext_boundVec n N_hat v0 start 0 i = |v0 i| := by
  unfold ch14ext_boundVec ch14ext_absCumProd
  rw [Nat.add_zero,
    gje_cumulative_product_base n (fun k a b => |N_hat k a b|) (le_refl start),
    matMulVec_id]
  rfl

theorem ch14ext_boundVec_succ (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (v0 : Fin n → ℝ)
    (start steps : ℕ) (h : start + steps < n) (i : Fin n) :
    ch14ext_boundVec n N_hat v0 start (steps + 1) i =
      ∑ l : Fin n, |N_hat ⟨start + steps, h⟩ i l| *
        ch14ext_boundVec n N_hat v0 start steps l := by
  have hstep : start < start + (steps + 1) :=
    Nat.lt_add_of_pos_right (Nat.succ_pos steps)
  have hfin_eq : start + (steps + 1) - 1 = start + steps := by simp
  have hidx : start + (steps + 1) - 1 < n := by rw [hfin_eq]; exact h
  have hfin : (⟨start + (steps + 1) - 1, hidx⟩ : Fin n) =
      ⟨start + steps, h⟩ := by apply Fin.ext; simp
  have hcp_prev :
      gje_cumulative_product n (fun k a b => |N_hat k a b|)
          start (start + (steps + 1) - 1) =
        gje_cumulative_product n (fun k a b => |N_hat k a b|)
          start (start + steps) := by rw [hfin_eq]
  have hcp :
      gje_cumulative_product n (fun k a b => |N_hat k a b|)
          start (start + (steps + 1)) =
        matMul n (fun a b => |N_hat ⟨start + steps, h⟩ a b|)
          (gje_cumulative_product n (fun k a b => |N_hat k a b|)
            start (start + steps)) := by
    rw [gje_cumulative_product_step n (fun k a b => |N_hat k a b|) hstep hidx,
      hfin, hcp_prev]
  unfold ch14ext_boundVec ch14ext_absCumProd
  rw [hcp, matMulVec_matMul]
  rfl

/-- **Higham (14.28) RHS growth envelope — DERIVED.** -/
theorem ch14ext_stageGrowthVec (n : ℕ) (fp : FPModel)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (start steps : ℕ) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < steps → start + t < n)
    (hrec : ∀ t : ℕ, (ht : t < steps) → ∀ i : Fin n,
      |x (start + (t + 1)) i -
          ∑ l : Fin n, N_hat ⟨start + t, hidx t ht⟩ i l * x (start + t) l| ≤
        gamma fp 3 *
          ∑ l : Fin n, |N_hat ⟨start + t, hidx t ht⟩ i l| * |x (start + t) l|) :
    ∀ i : Fin n,
      |x (start + steps) i| ≤
        (1 + gamma fp 3) ^ steps *
          ch14ext_boundVec n N_hat (x start) start steps i := by
  have hg : 0 ≤ gamma fp 3 := gamma_nonneg fp h3
  induction steps with
  | zero =>
      intro i
      rw [Nat.add_zero, pow_zero, one_mul, ch14ext_boundVec_zero]
  | succ steps ih =>
      intro i
      have hidx_prev : ∀ t : ℕ, t < steps → start + t < n :=
        fun t ht => hidx t (Nat.lt_trans ht (Nat.lt_succ_self steps))
      have hrec_prev : ∀ t : ℕ, (ht : t < steps) → ∀ i : Fin n,
          |x (start + (t + 1)) i -
              ∑ l : Fin n, N_hat ⟨start + t, hidx_prev t ht⟩ i l * x (start + t) l| ≤
            gamma fp 3 * ∑ l : Fin n,
              |N_hat ⟨start + t, hidx_prev t ht⟩ i l| * |x (start + t) l| := by
        intro t ht i
        simpa using hrec t (Nat.lt_trans ht (Nat.lt_succ_self steps)) i
      have ih' := ih hidx_prev hrec_prev
      have hlt : steps < steps + 1 := Nat.lt_succ_self steps
      have htop : start + steps < n := hidx steps hlt
      have hstepbnd := hrec steps hlt i
      set S : ℝ := ∑ l : Fin n, N_hat ⟨start + steps, htop⟩ i l * x (start + steps) l
        with hS
      set T : ℝ := ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| * |x (start + steps) l|
        with hT
      have habs_sum : |S| ≤ T := by
        rw [hS, hT]
        calc |∑ l : Fin n, N_hat ⟨start + steps, htop⟩ i l * x (start + steps) l|
            ≤ ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l * x (start + steps) l| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| * |x (start + steps) l| :=
              Finset.sum_congr rfl (fun l _ => abs_mul _ _)
      have hrow : |x (start + (steps + 1)) i| ≤ (1 + gamma fp 3) * T := by
        have htri : |x (start + (steps + 1)) i| ≤
            |x (start + (steps + 1)) i - S| + |S| := by
          calc |x (start + (steps + 1)) i|
              = |(x (start + (steps + 1)) i - S) + S| := by ring_nf
            _ ≤ |x (start + (steps + 1)) i - S| + |S| := abs_add_le _ _
        calc |x (start + (steps + 1)) i|
            ≤ |x (start + (steps + 1)) i - S| + |S| := htri
          _ ≤ gamma fp 3 * T + T := by linarith [hstepbnd, habs_sum]
          _ = (1 + gamma fp 3) * T := by ring
      have hgrow_row :
          T ≤ (1 + gamma fp 3) ^ steps *
              ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| *
                ch14ext_boundVec n N_hat (x start) start steps l := by
        rw [hT, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro l _
        have hIHl := ih' l
        calc |N_hat ⟨start + steps, htop⟩ i l| * |x (start + steps) l|
            ≤ |N_hat ⟨start + steps, htop⟩ i l| *
                ((1 + gamma fp 3) ^ steps *
                  ch14ext_boundVec n N_hat (x start) start steps l) :=
              mul_le_mul_of_nonneg_left hIHl (abs_nonneg _)
          _ = (1 + gamma fp 3) ^ steps *
                (|N_hat ⟨start + steps, htop⟩ i l| *
                  ch14ext_boundVec n N_hat (x start) start steps l) := by ring
      have hbase_nonneg : 0 ≤ 1 + gamma fp 3 := by linarith
      have hsucc :
          ch14ext_boundVec n N_hat (x start) start (steps + 1) i =
            ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| *
              ch14ext_boundVec n N_hat (x start) start steps l :=
        ch14ext_boundVec_succ n N_hat (x start) start steps htop i
      calc |x (start + (steps + 1)) i|
          ≤ (1 + gamma fp 3) * T := hrow
        _ ≤ (1 + gamma fp 3) *
              ((1 + gamma fp 3) ^ steps *
                ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| *
                  ch14ext_boundVec n N_hat (x start) start steps l) :=
            mul_le_mul_of_nonneg_left hgrow_row hbase_nonneg
        _ = (1 + gamma fp 3) ^ (steps + 1) *
              ch14ext_boundVec n N_hat (x start) start (steps + 1) i := by
            rw [hsucc, pow_succ]; ring

/-- **Higham (14.28) RHS accumulation — DERIVED.**
    `|x_{start+steps} − (∏N̂) x_start| ≤ ((1+γ₃)^{steps} − 1)·(|N̂|···|N̂|)|x_start|`. -/
theorem ch14ext_rhsAccumulation (n : ℕ) (fp : FPModel)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (start steps : ℕ) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < steps → start + t < n)
    (hrec : ∀ t : ℕ, (ht : t < steps) → ∀ i : Fin n,
      |x (start + (t + 1)) i -
          ∑ l : Fin n, N_hat ⟨start + t, hidx t ht⟩ i l * x (start + t) l| ≤
        gamma fp 3 *
          ∑ l : Fin n, |N_hat ⟨start + t, hidx t ht⟩ i l| * |x (start + t) l|) :
    ∀ i : Fin n,
      |x (start + steps) i -
          matMulVec n (gje_cumulative_product n N_hat start (start + steps))
            (x start) i| ≤
        ((1 + gamma fp 3) ^ steps - 1) *
          ch14ext_boundVec n N_hat (x start) start steps i := by
  have hg : 0 ≤ gamma fp 3 := gamma_nonneg fp h3
  have hbase_nonneg : 0 ≤ 1 + gamma fp 3 := by linarith
  induction steps with
  | zero =>
      intro i
      rw [Nat.add_zero,
        gje_cumulative_product_base n N_hat (le_refl start), matMulVec_id,
        pow_zero]
      simp
  | succ m ih =>
      intro i
      have hidx_prev : ∀ t : ℕ, t < m → start + t < n :=
        fun t ht => hidx t (Nat.lt_trans ht (Nat.lt_succ_self m))
      have hrec_prev : ∀ t : ℕ, (ht : t < m) → ∀ i : Fin n,
          |x (start + (t + 1)) i -
              ∑ l : Fin n, N_hat ⟨start + t, hidx_prev t ht⟩ i l * x (start + t) l| ≤
            gamma fp 3 * ∑ l : Fin n,
              |N_hat ⟨start + t, hidx_prev t ht⟩ i l| * |x (start + t) l| := by
        intro t ht i
        simpa using hrec t (Nat.lt_trans ht (Nat.lt_succ_self m)) i
      have ih' := ih hidx_prev hrec_prev
      have hlt : m < m + 1 := Nat.lt_succ_self m
      have htop : start + m < n := hidx m hlt
      have hstep : start < start + (m + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos m)
      have hfin_eq : start + (m + 1) - 1 = start + m := by simp
      have hidxP : start + (m + 1) - 1 < n := by rw [hfin_eq]; exact htop
      have hfin : (⟨start + (m + 1) - 1, hidxP⟩ : Fin n) = ⟨start + m, htop⟩ := by
        apply Fin.ext; simp
      have hcp_prev :
          gje_cumulative_product n N_hat start (start + (m + 1) - 1) =
            gje_cumulative_product n N_hat start (start + m) := by rw [hfin_eq]
      have hPstep :
          gje_cumulative_product n N_hat start (start + (m + 1)) =
            matMul n (N_hat ⟨start + m, htop⟩)
              (gje_cumulative_product n N_hat start (start + m)) := by
        rw [gje_cumulative_product_step n N_hat hstep hidxP, hfin, hcp_prev]
      have hBvec :
          matMulVec n (gje_cumulative_product n N_hat start (start + (m + 1)))
              (x start) i =
            ∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l *
              matMulVec n (gje_cumulative_product n N_hat start (start + m))
                (x start) l := by
        rw [hPstep, matMulVec_matMul]; rfl
      have hgrowth := ch14ext_stageGrowthVec n fp N_hat x start m h3 hidx_prev hrec_prev
      have hstepbnd := hrec m hlt i
      have hRsucc :
          ch14ext_boundVec n N_hat (x start) start (m + 1) i =
            ∑ l : Fin n, |N_hat ⟨start + m, htop⟩ i l| *
              ch14ext_boundVec n N_hat (x start) start m l :=
        ch14ext_boundVec_succ n N_hat (x start) start m htop i
      have hpowm_nonneg : 0 ≤ (1 + gamma fp 3) ^ m := pow_nonneg hbase_nonneg _
      have hAB :
          |(∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l * x (start + m) l) -
              (∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l *
                matMulVec n (gje_cumulative_product n N_hat start (start + m))
                  (x start) l)| ≤
            ((1 + gamma fp 3) ^ m - 1) *
              ch14ext_boundVec n N_hat (x start) start (m + 1) i := by
        have heq :
            (∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l * x (start + m) l) -
                (∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l *
                  matMulVec n (gje_cumulative_product n N_hat start (start + m))
                    (x start) l) =
              ∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l *
                (x (start + m) l -
                  matMulVec n (gje_cumulative_product n N_hat start (start + m))
                    (x start) l) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun l _ => by ring)
        rw [heq, hRsucc, Finset.mul_sum]
        calc |∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l *
                (x (start + m) l -
                  matMulVec n (gje_cumulative_product n N_hat start (start + m))
                    (x start) l)|
            ≤ ∑ l : Fin n, |N_hat ⟨start + m, htop⟩ i l| *
                |x (start + m) l -
                  matMulVec n (gje_cumulative_product n N_hat start (start + m))
                    (x start) l| := by
                refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
                exact le_of_eq (Finset.sum_congr rfl (fun l _ => abs_mul _ _))
          _ ≤ ∑ l : Fin n, ((1 + gamma fp 3) ^ m - 1) *
                (|N_hat ⟨start + m, htop⟩ i l| *
                  ch14ext_boundVec n N_hat (x start) start m l) := by
                apply Finset.sum_le_sum
                intro l _
                have hIHl := ih' l
                calc |N_hat ⟨start + m, htop⟩ i l| *
                      |x (start + m) l -
                        matMulVec n (gje_cumulative_product n N_hat start (start + m))
                          (x start) l|
                    ≤ |N_hat ⟨start + m, htop⟩ i l| *
                        (((1 + gamma fp 3) ^ m - 1) *
                          ch14ext_boundVec n N_hat (x start) start m l) :=
                      mul_le_mul_of_nonneg_left hIHl (abs_nonneg _)
                  _ = ((1 + gamma fp 3) ^ m - 1) *
                        (|N_hat ⟨start + m, htop⟩ i l| *
                          ch14ext_boundVec n N_hat (x start) start m l) := by ring
      have hGrow :
          gamma fp 3 *
              (∑ l : Fin n, |N_hat ⟨start + m, htop⟩ i l| * |x (start + m) l|) ≤
            gamma fp 3 * ((1 + gamma fp 3) ^ m *
              ch14ext_boundVec n N_hat (x start) start (m + 1) i) := by
        apply mul_le_mul_of_nonneg_left _ hg
        rw [hRsucc, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro l _
        have hgl := hgrowth l
        calc |N_hat ⟨start + m, htop⟩ i l| * |x (start + m) l|
            ≤ |N_hat ⟨start + m, htop⟩ i l| *
                ((1 + gamma fp 3) ^ m *
                  ch14ext_boundVec n N_hat (x start) start m l) :=
              mul_le_mul_of_nonneg_left hgl (abs_nonneg _)
          _ = (1 + gamma fp 3) ^ m *
                (|N_hat ⟨start + m, htop⟩ i l| *
                  ch14ext_boundVec n N_hat (x start) start m l) := by ring
      set R : ℝ := ch14ext_boundVec n N_hat (x start) start (m + 1) i with hRdef
      have htri :
          |x (start + (m + 1)) i -
              matMulVec n (gje_cumulative_product n N_hat start (start + (m + 1)))
                (x start) i| ≤
            gamma fp 3 *
              (∑ l : Fin n, |N_hat ⟨start + m, htop⟩ i l| * |x (start + m) l|) +
            ((1 + gamma fp 3) ^ m - 1) * R := by
        rw [hBvec]
        set A : ℝ := ∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l * x (start + m) l
          with hAdef
        set B : ℝ := ∑ l : Fin n, N_hat ⟨start + m, htop⟩ i l *
          matMulVec n (gje_cumulative_product n N_hat start (start + m)) (x start) l
          with hBdef
        have hsplit :
            x (start + (m + 1)) i - B =
              (x (start + (m + 1)) i - A) + (A - B) := by ring
        calc |x (start + (m + 1)) i - B|
            = |(x (start + (m + 1)) i - A) + (A - B)| := by rw [hsplit]
          _ ≤ |x (start + (m + 1)) i - A| + |A - B| := abs_add_le _ _
          _ ≤ gamma fp 3 *
                (∑ l : Fin n, |N_hat ⟨start + m, htop⟩ i l| * |x (start + m) l|) +
              ((1 + gamma fp 3) ^ m - 1) * R := add_le_add hstepbnd hAB
      calc |x (start + (m + 1)) i -
              matMulVec n (gje_cumulative_product n N_hat start (start + (m + 1)))
                (x start) i|
          ≤ gamma fp 3 *
              (∑ l : Fin n, |N_hat ⟨start + m, htop⟩ i l| * |x (start + m) l|) +
            ((1 + gamma fp 3) ^ m - 1) * R := htri
        _ ≤ gamma fp 3 * ((1 + gamma fp 3) ^ m * R) +
              ((1 + gamma fp 3) ^ m - 1) * R := add_le_add hGrow (le_refl _)
        _ = ((1 + gamma fp 3) ^ (m + 1) - 1) * R := by rw [pow_succ]; ring

-- ══════════════════════════════════════════════════════════════════════
-- §5  Fold to the printed c₃ = (n−1)γ₃(1+γ₃)^{n−2} coefficient
-- ══════════════════════════════════════════════════════════════════════

/-- **Higham (14.27) matrix accumulation, printed `c₃` form.**
    `|V_final − (∏N̂) V_start| ≤ c₃ · (|N̂|···|N̂|) |V_start|`,
    `c₃ = (n−1)γ₃(1+γ₃)^{n−2}` — the exact cumulative coefficient of (14.27). -/
theorem ch14ext_matrixAccumulation_c3 (n : ℕ) (fp : FPModel)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (V : ℕ → Fin n → Fin n → ℝ)
    (start : ℕ) (hn : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hrec : ∀ t : ℕ, (ht : t < n - 1) → ∀ i j : Fin n,
      |V (start + (t + 1)) i j -
          ∑ l : Fin n, N_hat ⟨start + t, hidx t ht⟩ i l * V (start + t) l j| ≤
        gamma fp 3 *
          ∑ l : Fin n, |N_hat ⟨start + t, hidx t ht⟩ i l| * |V (start + t) l j|) :
    ∀ i j : Fin n,
      |V (start + (n - 1)) i j -
          matMul n (gje_cumulative_product n N_hat start (start + (n - 1)))
            (V start) i j| ≤
        gje_c₃ fp n *
          ch14ext_boundObj n N_hat (V start) start (n - 1) i j := by
  intro i j
  have hacc := ch14ext_matrixAccumulation n fp N_hat V start (n - 1) h3 hidx hrec i j
  have hfold : (1 + gamma fp 3) ^ (n - 1) - 1 ≤ gje_c₃ fp n :=
    gje_one_add_gamma_three_pow_sub_one_le_c3 fp n hn h3
  have hnn : 0 ≤ ch14ext_boundObj n N_hat (V start) start (n - 1) i j :=
    ch14ext_boundObj_nonneg n N_hat (V start) start (n - 1) i j
  exact le_trans hacc (mul_le_mul_of_nonneg_right hfold hnn)

/-- **Higham (14.28) RHS accumulation, printed `c₃` form.**
    `|x_final − (∏N̂) x_start| ≤ c₃ · (|N̂|···|N̂|) |x_start|`. -/
theorem ch14ext_rhsAccumulation_c3 (n : ℕ) (fp : FPModel)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (start : ℕ) (hn : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hrec : ∀ t : ℕ, (ht : t < n - 1) → ∀ i : Fin n,
      |x (start + (t + 1)) i -
          ∑ l : Fin n, N_hat ⟨start + t, hidx t ht⟩ i l * x (start + t) l| ≤
        gamma fp 3 *
          ∑ l : Fin n, |N_hat ⟨start + t, hidx t ht⟩ i l| * |x (start + t) l|) :
    ∀ i : Fin n,
      |x (start + (n - 1)) i -
          matMulVec n (gje_cumulative_product n N_hat start (start + (n - 1)))
            (x start) i| ≤
        gje_c₃ fp n *
          ch14ext_boundVec n N_hat (x start) start (n - 1) i := by
  intro i
  have hacc := ch14ext_rhsAccumulation n fp N_hat x start (n - 1) h3 hidx hrec i
  have hfold : (1 + gamma fp 3) ^ (n - 1) - 1 ≤ gje_c₃ fp n :=
    gje_one_add_gamma_three_pow_sub_one_le_c3 fp n hn h3
  have hnn : 0 ≤ ch14ext_boundVec n N_hat (x start) start (n - 1) i :=
    ch14ext_boundVec_nonneg n N_hat (x start) start (n - 1) i
  exact le_trans hacc (mul_le_mul_of_nonneg_right hfold hnn)

-- ══════════════════════════════════════════════════════════════════════
-- §6  Transport a componentwise bound through a left factor Q
-- ══════════════════════════════════════════════════════════════════════

/-- If `|E k j| ≤ c · B k j` entrywise, then `|(Q E)_{ij}| ≤ c · (|Q| B)_{ij}`.
    Left-multiplies a componentwise error bound by a (signed) matrix `Q`. -/
theorem ch14ext_matMul_abs_bound (n : ℕ) (Q E B : Fin n → Fin n → ℝ) (c : ℝ)
    (hE : ∀ k j : Fin n, |E k j| ≤ c * B k j) (i j : Fin n) :
    |matMul n Q E i j| ≤ c * matMul n (absMatrix n Q) B i j := by
  unfold matMul absMatrix
  calc |∑ k : Fin n, Q i k * E k j|
      ≤ ∑ k : Fin n, |Q i k * E k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |Q i k| * |E k j| :=
        Finset.sum_congr rfl (fun k _ => abs_mul _ _)
    _ ≤ ∑ k : Fin n, |Q i k| * (c * B k j) :=
        Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (hE k j) (abs_nonneg _))
    _ = c * ∑ k : Fin n, |Q i k| * B k j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)

/-- Vector analogue of `ch14ext_matMul_abs_bound`. -/
theorem ch14ext_matMulVec_abs_bound (n : ℕ) (Q : Fin n → Fin n → ℝ)
    (g bv : Fin n → ℝ) (c : ℝ)
    (hg : ∀ k : Fin n, |g k| ≤ c * bv k) (i : Fin n) :
    |matMulVec n Q g i| ≤ c * matMulVec n (absMatrix n Q) bv i := by
  unfold matMulVec absMatrix
  calc |∑ k : Fin n, Q i k * g k|
      ≤ ∑ k : Fin n, |Q i k * g k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |Q i k| * |g k| :=
        Finset.sum_congr rfl (fun k _ => abs_mul _ _)
    _ ≤ ∑ k : Fin n, |Q i k| * (c * bv k) :=
        Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (hg k) (abs_nonneg _))
    _ = c * ∑ k : Fin n, |Q i k| * bv k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The overall `|X_abs|` envelope of Theorem 14.5 built from the given left
    inverse `Q` of the cumulative product: `X_abs = |Q| · (|N̂|···|N̂|)`.  Since
    `Q = (∏N̂)⁻¹ = Û + O(u)` and `|N̂|···|N̂| = |X| ≥ |Û⁻¹|`, this is the exact
    (un-approximated) form of Higham's `|Û| |Û⁻¹|` middle factor in (14.31). -/
noncomputable def ch14ext_gjeXabs (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (Q : Fin n → Fin n → ℝ)
    (start steps : ℕ) : Fin n → Fin n → ℝ :=
  matMul n (absMatrix n Q) (ch14ext_absCumProd n N_hat start steps)

theorem ch14ext_gjeXabs_nonneg (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (Q : Fin n → Fin n → ℝ)
    (start steps : ℕ) (i j : Fin n) :
    0 ≤ ch14ext_gjeXabs n N_hat Q start steps i j := by
  unfold ch14ext_gjeXabs ch14ext_absCumProd matMul absMatrix
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (abs_nonneg _)
      (gje_cumulative_product_abs_nonneg n N_hat start (start + steps) k j)

-- ══════════════════════════════════════════════════════════════════════
-- §7  Theorem 14.5, eq. (14.31): overall GJE residual from the accumulation
-- ══════════════════════════════════════════════════════════════════════

/-- **Theorem 14.5 / eq. (14.31): overall GJE residual, fed from the accumulated
    ΔU_total/Δy_total — DERIVED from the concrete per-step waves.**

    Composes the (14.27)/(14.28) accumulation with Codex's `gje_overall_residual`
    socket to expose the Theorem-14.5 residual bound
        `|b − A x̂| ≤ γₙ|L̂||Û||x̂| + c₃|L̂||X_abs||Û||x̂| + c₃|L̂||X_abs||y|`,
    `c₃ = (n−1)γ₃(1+γ₃)^{n−2}`, `X_abs = |Q|·(|N̂|···|N̂|)` (the exact form of
    Higham's `|Û||Û⁻¹|` middle factor; `Q = (∏N̂)⁻¹ = Û + O(u)`).

    The accumulated second-stage perturbations are built ADDITIVELY, not via a
    single column-independent stage-matrix perturbation:
        ΔU_total := Q·(Û_final − (∏N̂)Û) ,   Δy_total := Q·(x̂_final − (∏N̂)y),
    whose bounds are `ch14ext_matrixAccumulation_c3` / `ch14ext_rhsAccumulation_c3`.
    (This is exactly the honest route flagged in wave 2: the concrete subtraction
    rounding is column-dependent, so the additive accumulation — not the
    `_of_cumulative_product_certificates` j-independent-perturbation route — is
    what the concrete loop yields.)

    Structural inputs, all honest and non-conclusion-shaped: `hVfinal` is Higham's
    own WLOG normalization D = I (p. 274, "negligible effect on the final
    bounds"); `hQP` supplies the left inverse of the cumulative product (the file
    already supplies A⁻¹ as data in `gje_overall_forward_error`); `hxfinal`
    identifies the computed solution with the final RHS iterate (D = I, no final
    scaling); the per-step `hrecM`/`hrecX` are exactly wave 2's γ₃ bounds. -/
theorem ch14ext_gje_overall_residual_of_accumulation
    (n : ℕ) (fp : FPModel)
    (A L_hat : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (N_hat : Fin n → Fin n → Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hQP : matMul n Q (gje_cumulative_product n N_hat start (start + (n - 1))) =
      idMatrix n)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * xseq start j = b i)
    (hrecM : ∀ t : ℕ, (ht : t < n - 1) → ∀ i j : Fin n,
      |V (start + (t + 1)) i j -
          ∑ l : Fin n, N_hat ⟨start + t, hidx t ht⟩ i l * V (start + t) l j| ≤
        gamma fp 3 *
          ∑ l : Fin n, |N_hat ⟨start + t, hidx t ht⟩ i l| * |V (start + t) l j|)
    (hrecX : ∀ t : ℕ, (ht : t < n - 1) → ∀ i : Fin n,
      |xseq (start + (t + 1)) i -
          ∑ l : Fin n, N_hat ⟨start + t, hidx t ht⟩ i l * xseq (start + t) l| ≤
        gamma fp 3 *
          ∑ l : Fin n, |N_hat ⟨start + t, hidx t ht⟩ i l| * |xseq (start + t) l|) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |V start k j|) * |x_hat j| +
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |ch14ext_gjeXabs n N_hat Q start (n - 1) k₁ k₂| * |V start k₂ j|)) *
          |x_hat j| +
      gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n,
          |ch14ext_gjeXabs n N_hat Q start (n - 1) k j| * |xseq start j|) := by
  -- accumulation error matrices/vectors
  let E : Fin n → Fin n → ℝ := fun i j =>
    V (start + (n - 1)) i j -
      matMul n (gje_cumulative_product n N_hat start (start + (n - 1))) (V start) i j
  let g : Fin n → ℝ := fun i =>
    xseq (start + (n - 1)) i -
      matMulVec n (gje_cumulative_product n N_hat start (start + (n - 1)))
        (xseq start) i
  -- (14.27)/(14.28) accumulation bounds in printed c₃ form
  have hEbnd : ∀ k j : Fin n,
      |E k j| ≤ gje_c₃ fp n * ch14ext_boundObj n N_hat (V start) start (n - 1) k j :=
    ch14ext_matrixAccumulation_c3 n fp N_hat V start hnpos h3 hidx hrecM
  have hgbnd : ∀ k : Fin n,
      |g k| ≤ gje_c₃ fp n * ch14ext_boundVec n N_hat (xseq start) start (n - 1) k :=
    ch14ext_rhsAccumulation_c3 n fp N_hat xseq start hnpos h3 hidx hrecX
  -- Q · (∏N̂) = I convenience rewrites
  have h1 : matMul n Q (V (start + (n - 1))) = Q := by rw [hVfinal, matMul_id_right]
  have h2 : matMul n Q
      (matMul n (gje_cumulative_product n N_hat start (start + (n - 1))) (V start)) =
      V start := by rw [← matMul_assoc, hQP, matMul_id_left]
  -- ΔU = Q E = Q − Û  (so Û + ΔU = Q, using D = I and QP = I)
  have key : matMul n Q E = fun i j => Q i j - V start i j := by
    funext i j
    have hexp : matMul n Q E i j =
        matMul n Q (V (start + (n - 1))) i j -
          matMul n Q
            (matMul n (gje_cumulative_product n N_hat start (start + (n - 1)))
              (V start)) i j := by
      show (∑ k : Fin n, Q i k * E k j) =
        (∑ k : Fin n, Q i k * V (start + (n - 1)) k j) -
          (∑ k : Fin n, Q i k *
            matMul n (gje_cumulative_product n N_hat start (start + (n - 1)))
              (V start) k j)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      show Q i k * (V (start + (n - 1)) k j -
        matMul n (gje_cumulative_product n N_hat start (start + (n - 1)))
          (V start) k j) = _
      ring
    rw [hexp, h1, h2]
  -- Δy = Q g = Q x̂_final − y  (so Q x̂_final = y + Δy)
  have hg1 : (fun i => matMulVec n Q
      (matMulVec n (gje_cumulative_product n N_hat start (start + (n - 1)))
        (xseq start)) i) = xseq start := by
    funext i
    rw [← matMulVec_matMul, hQP, matMulVec_id]
  have hg_eq : ∀ i : Fin n,
      matMulVec n Q g i =
        matMulVec n Q (xseq (start + (n - 1))) i - xseq start i := by
    intro i
    have hlin : matMulVec n Q g i =
        matMulVec n Q (xseq (start + (n - 1))) i -
          matMulVec n Q
            (matMulVec n (gje_cumulative_product n N_hat start (start + (n - 1)))
              (xseq start)) i := by
      show (∑ k : Fin n, Q i k * g k) =
        (∑ k : Fin n, Q i k * xseq (start + (n - 1)) k) -
          (∑ k : Fin n, Q i k *
            matMulVec n (gje_cumulative_product n N_hat start (start + (n - 1)))
              (xseq start) k)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      show Q i k * (xseq (start + (n - 1)) k -
        matMulVec n (gje_cumulative_product n N_hat start (start + (n - 1)))
          (xseq start) k) = _
      ring
    rw [hlin, congrFun hg1 i]
  -- socket hypothesis: backward equation (Û + ΔU) x̂ = y + Δy
  have hEq : ∀ i : Fin n,
      ∑ j : Fin n, (V start i j + matMul n Q E i j) * x_hat j =
        xseq start i + matMulVec n Q g i := by
    intro i
    have hUQ : ∀ j : Fin n, V start i j + matMul n Q E i j = Q i j := by
      intro j; rw [key]; ring
    calc ∑ j : Fin n, (V start i j + matMul n Q E i j) * x_hat j
        = ∑ j : Fin n, Q i j * x_hat j :=
          Finset.sum_congr rfl (fun j _ => by rw [hUQ j])
      _ = ∑ j : Fin n, Q i j * xseq (start + (n - 1)) j :=
          Finset.sum_congr rfl (fun j _ => by rw [hxfinal j])
      _ = matMulVec n Q (xseq (start + (n - 1))) i := rfl
      _ = xseq start i + matMulVec n Q g i := by rw [hg_eq i]; ring
  -- socket hypothesis: |ΔU| ≤ c₃ |X_abs| |Û|
  have hΔU : ∀ i j : Fin n,
      |matMul n Q E i j| ≤ gje_c₃ fp n *
        ∑ k : Fin n, |ch14ext_gjeXabs n N_hat Q start (n - 1) i k| * |V start k j| := by
    intro i j
    have hb := ch14ext_matMul_abs_bound n Q E
      (ch14ext_boundObj n N_hat (V start) start (n - 1)) (gje_c₃ fp n) hEbnd i j
    -- matMul |Q| boundObj = matMul X_abs |Û|
    have hrw : matMul n (absMatrix n Q)
          (ch14ext_boundObj n N_hat (V start) start (n - 1)) i j =
        ∑ k : Fin n, |ch14ext_gjeXabs n N_hat Q start (n - 1) i k| * |V start k j| := by
      have hassoc :
          matMul n (absMatrix n Q)
              (ch14ext_boundObj n N_hat (V start) start (n - 1)) =
            matMul n (ch14ext_gjeXabs n N_hat Q start (n - 1)) (absMatrix n (V start)) := by
        show matMul n (absMatrix n Q)
            (matMul n (ch14ext_absCumProd n N_hat start (n - 1)) (absMatrix n (V start))) = _
        rw [← matMul_assoc]; rfl
      rw [hassoc]
      show (∑ k : Fin n, ch14ext_gjeXabs n N_hat Q start (n - 1) i k * |V start k j|) =
        ∑ k : Fin n, |ch14ext_gjeXabs n N_hat Q start (n - 1) i k| * |V start k j|
      exact Finset.sum_congr rfl (fun k _ => by
        rw [abs_of_nonneg (ch14ext_gjeXabs_nonneg n N_hat Q start (n - 1) i k)])
    rw [hrw] at hb
    exact hb
  -- socket hypothesis: |Δy| ≤ c₃ |X_abs| |y|
  have hΔy : ∀ i : Fin n,
      |matMulVec n Q g i| ≤ gje_c₃ fp n *
        ∑ j : Fin n,
          |ch14ext_gjeXabs n N_hat Q start (n - 1) i j| * |xseq start j| := by
    intro i
    have hb := ch14ext_matMulVec_abs_bound n Q g
      (ch14ext_boundVec n N_hat (xseq start) start (n - 1)) (gje_c₃ fp n) hgbnd i
    have hrw : matMulVec n (absMatrix n Q)
          (ch14ext_boundVec n N_hat (xseq start) start (n - 1)) i =
        ∑ j : Fin n,
          |ch14ext_gjeXabs n N_hat Q start (n - 1) i j| * |xseq start j| := by
      have hassoc :
          matMulVec n (absMatrix n Q)
              (ch14ext_boundVec n N_hat (xseq start) start (n - 1)) =
            matMulVec n (ch14ext_gjeXabs n N_hat Q start (n - 1))
              (absVec n (xseq start)) := by
        funext i'
        show matMulVec n (absMatrix n Q)
            (matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
              (absVec n (xseq start))) i' = _
        rw [← matMulVec_matMul]; rfl
      rw [hassoc]
      show (∑ j : Fin n, ch14ext_gjeXabs n N_hat Q start (n - 1) i j * |xseq start j|) =
        ∑ j : Fin n, |ch14ext_gjeXabs n N_hat Q start (n - 1) i j| * |xseq start j|
      exact Finset.sum_congr rfl (fun j _ => by
        rw [abs_of_nonneg (ch14ext_gjeXabs_nonneg n N_hat Q start (n - 1) i j)])
    rw [hrw] at hb
    exact hb
  -- feed Codex's residual socket
  exact gje_overall_residual n fp A L_hat (V start) b (xseq start) x_hat
    (ch14ext_gjeXabs n N_hat Q start (n - 1)) hLU hn h3 hy
    (matMul n Q E) (matMulVec n Q g) hEq hΔU hΔy

-- ══════════════════════════════════════════════════════════════════════
-- §8  Theorem 14.5, eq. (14.32): overall GJE forward error
-- ══════════════════════════════════════════════════════════════════════

/-- **Theorem 14.5 / eq. (14.32): overall GJE forward error, from the
    accumulation.**

    Composes `ch14ext_gje_overall_residual_of_accumulation` (14.31) with Codex's
    `gje_overall_forward_error` (transfer through `|A⁻¹|`) to expose
        `|x − x̂| ≤ |A⁻¹|·(γₙ|L̂||Û||x̂| + c₃|L̂||X_abs||Û||x̂| + c₃|L̂||X_abs||y|)`,
    the componentwise (14.32) forward-error bound (`c₃ = (n−1)γ₃(1+γ₃)^{n−2}`,
    `X_abs = |Q|·(|N̂|···|N̂|)`).  The printed `2nu(|A⁻¹||L̂||Û| + 3|Û⁻¹||Û|)|x̂|`
    numeric constant is this `c₃`-plus-GE-first-stage budget under the standard
    `|X_abs| ≈ |Û||Û⁻¹|`, `|Q| ≈ |Û|` first-order identifications (documented
    scalar-audit residual for the final integer coefficient). -/
theorem ch14ext_gje_overall_forward_error_of_accumulation
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat : Fin n → Fin n → ℝ) (b x x_hat : Fin n → ℝ)
    (N_hat : Fin n → Fin n → Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hQP : matMul n Q (gje_cumulative_product n N_hat start (start + (n - 1))) =
      idMatrix n)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * xseq start j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hrecM : ∀ t : ℕ, (ht : t < n - 1) → ∀ i j : Fin n,
      |V (start + (t + 1)) i j -
          ∑ l : Fin n, N_hat ⟨start + t, hidx t ht⟩ i l * V (start + t) l j| ≤
        gamma fp 3 *
          ∑ l : Fin n, |N_hat ⟨start + t, hidx t ht⟩ i l| * |V (start + t) l j|)
    (hrecX : ∀ t : ℕ, (ht : t < n - 1) → ∀ i : Fin n,
      |xseq (start + (t + 1)) i -
          ∑ l : Fin n, N_hat ⟨start + t, hidx t ht⟩ i l * xseq (start + t) l| ≤
        gamma fp 3 *
          ∑ l : Fin n, |N_hat ⟨start + t, hidx t ht⟩ i l| * |xseq (start + t) l|) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |V start l k|) * |x_hat k| +
        gje_c₃ fp n * ∑ k : Fin n,
          (∑ k₁ : Fin n, |L_hat j k₁| *
            (∑ k₂ : Fin n,
              |ch14ext_gjeXabs n N_hat Q start (n - 1) k₁ k₂| * |V start k₂ k|)) *
            |x_hat k| +
        gje_c₃ fp n * ∑ l : Fin n, |L_hat j l| *
          (∑ k : Fin n,
            |ch14ext_gjeXabs n N_hat Q start (n - 1) l k| * |xseq start k|)) := by
  have hResidual :=
    ch14ext_gje_overall_residual_of_accumulation n fp A L_hat b x_hat N_hat V xseq
      Q start hLU hn hnpos h3 hidx hVfinal hxfinal hQP hy hrecM hrecX
  exact gje_overall_forward_error n fp A A_inv L_hat (V start) b (xseq start) x
    x_hat (ch14ext_gjeXabs n N_hat Q start (n - 1)) hLU hAinv hn h3 hExact hResidual

-- ══════════════════════════════════════════════════════════════════════
-- §9  Concrete instantiation: the abstract per-step hypotheses ARE wave 2's
-- ══════════════════════════════════════════════════════════════════════

/-- The concrete GJE stage matrices `N̂ₖ = I − n̂ₖ eₖᵀ` built from the running
    computed sequence `V`.  Stage `k` reads column `k` of the current iterate
    `V k.val`, matching Higham's definition `(N̂ₖ)_{ik} = −û_{ik}/û_{kk}`. -/
noncomputable def ch14ext_gjeSeqStages (n : ℕ) (V : ℕ → Fin n → Fin n → ℝ) :
    Fin n → Fin n → Fin n → ℝ :=
  fun k => ch14ext_gjeStageMatrix n (V k.val) k

/-- **The abstract matrix per-step hypothesis `hrecM` IS wave 2's γ₃ bound.**
    For a sequence obeying the concrete GJE matrix step
    `V_{k+1} = ch14ext_gjeStepMatrix (V_k) k` with nonzero pivots, the (14.25b)
    per-step bound `ch14ext_gjeStepMatrix_hComp` discharges the accumulation's
    `hrecM` hypothesis verbatim. -/
theorem ch14ext_gjeConcrete_hrecM (fp : FPModel) (n : ℕ)
    (V : ℕ → Fin n → Fin n → ℝ) (start : ℕ) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    ∀ t : ℕ, (ht : t < n - 1) → ∀ i j : Fin n,
      |V (start + (t + 1)) i j -
          ∑ l : Fin n,
            ch14ext_gjeSeqStages n V ⟨start + t, hidx t ht⟩ i l * V (start + t) l j| ≤
        gamma fp 3 *
          ∑ l : Fin n,
            |ch14ext_gjeSeqStages n V ⟨start + t, hidx t ht⟩ i l| * |V (start + t) l j| := by
  intro t ht i j
  rw [hVrec t ht]
  exact ch14ext_gjeStepMatrix_hComp fp n (V (start + t)) ⟨start + t, hidx t ht⟩
    (hpiv t ht) h3 i j

/-- **The abstract RHS per-step hypothesis `hrecX` IS wave 2's γ₃ bound.** -/
theorem ch14ext_gjeConcrete_hrecX (fp : FPModel) (n : ℕ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hxrec : ∀ t : ℕ, (ht : t < n - 1) →
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    ∀ t : ℕ, (ht : t < n - 1) → ∀ i : Fin n,
      |xseq (start + (t + 1)) i -
          ∑ l : Fin n,
            ch14ext_gjeSeqStages n V ⟨start + t, hidx t ht⟩ i l * xseq (start + t) l| ≤
        gamma fp 3 *
          ∑ l : Fin n,
            |ch14ext_gjeSeqStages n V ⟨start + t, hidx t ht⟩ i l| * |xseq (start + t) l| := by
  intro t ht i
  rw [hxrec t ht]
  exact ch14ext_gjeStepVec_hComp fp n (V (start + t)) ⟨start + t, hidx t ht⟩
    (xseq (start + t)) (hpiv t ht) h3 i

/-- **Higham (14.27) for the concrete GJE loop — DERIVED from wave 2.**
    Telescoping the actual `ch14ext_gjeStepMatrix` iteration:
    `|Û_final − (∏N̂)Û| ≤ c₃·(|N̂|···|N̂|)|Û|`. -/
theorem ch14ext_gjeConcrete_matrixAccumulation (fp : FPModel) (n : ℕ)
    (V : ℕ → Fin n → Fin n → ℝ) (start : ℕ) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    ∀ i j : Fin n,
      |V (start + (n - 1)) i j -
          matMul n (gje_cumulative_product n (ch14ext_gjeSeqStages n V) start
            (start + (n - 1))) (V start) i j| ≤
        gje_c₃ fp n *
          ch14ext_boundObj n (ch14ext_gjeSeqStages n V) (V start) start (n - 1) i j :=
  ch14ext_matrixAccumulation_c3 n fp (ch14ext_gjeSeqStages n V) V start hnpos h3 hidx
    (ch14ext_gjeConcrete_hrecM fp n V start h3 hidx hVrec hpiv)

/-- **Higham (14.28) for the concrete GJE loop — DERIVED from wave 2.** -/
theorem ch14ext_gjeConcrete_rhsAccumulation (fp : FPModel) (n : ℕ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hxrec : ∀ t : ℕ, (ht : t < n - 1) →
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    ∀ i : Fin n,
      |xseq (start + (n - 1)) i -
          matMulVec n (gje_cumulative_product n (ch14ext_gjeSeqStages n V) start
            (start + (n - 1))) (xseq start) i| ≤
        gje_c₃ fp n *
          ch14ext_boundVec n (ch14ext_gjeSeqStages n V) (xseq start) start (n - 1) i :=
  ch14ext_rhsAccumulation_c3 n fp (ch14ext_gjeSeqStages n V) xseq start hnpos h3 hidx
    (ch14ext_gjeConcrete_hrecX fp n V xseq start h3 hidx hxrec hpiv)

/-- The source-shaped right side of (14.29):
    `|X| (|Û| |x| + |y|)`, where `|X|` is the product of the absolute GJE
    stage matrices. -/
noncomputable def ch14ext_gjeForwardEnvelope (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (start steps : ℕ) (i : Fin n) : ℝ :=
  matMulVec n (ch14ext_absCumProd n N_hat start steps)
      (matMulVec n (absMatrix n U) (absVec n x)) i +
    matMulVec n (ch14ext_absCumProd n N_hat start steps) (absVec n y) i

/-- **Higham (14.29), concrete rounded second-stage loop.**

    If `x` is the exact solution of `Û x = y`, the actual matrix and RHS
    recurrences from `ch14ext_gjeStepMatrix`/`ch14ext_gjeStepVec` imply
    `|x - x̂| ≤ c₃ |X| (|Û||x| + |y|)`.  No forward-error certificate is an
    input: both accumulated terms are obtained from the per-operation FP
    model through `ch14ext_gjeConcrete_{matrix,rhs}Accumulation`. -/
theorem ch14ext_gjeConcrete_stage2_forward_error
    (fp : FPModel) (n : ℕ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ)
    (x : Fin n → ℝ) (start : ℕ)
    (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hUx : ∀ i : Fin n, matMulVec n (V start) x i = xseq start i)
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
      |x i - xseq (start + (n - 1)) i| ≤
        gje_c₃ fp n *
          ch14ext_gjeForwardEnvelope n (ch14ext_gjeSeqStages n V) (V start)
            x (xseq start) start (n - 1) i := by
  intro i
  let N_hat := ch14ext_gjeSeqStages n V
  let P := gje_cumulative_product n N_hat start (start + (n - 1))
  let B := ch14ext_boundObj n N_hat (V start) start (n - 1)
  let bv := ch14ext_boundVec n N_hat (xseq start) start (n - 1)
  let R₁ := ∑ j : Fin n, (idMatrix n i j - matMul n P (V start) i j) * x j
  let R₂ := matMulVec n P (xseq start) i - xseq (start + (n - 1)) i
  have hM := ch14ext_gjeConcrete_matrixAccumulation fp n V start hnpos h3 hidx
    hVrec hpiv
  have hR := ch14ext_gjeConcrete_rhsAccumulation fp n V xseq start hnpos h3 hidx
    hxrec hpiv
  have hM' : ∀ a b : Fin n,
      |idMatrix n a b - matMul n P (V start) a b| ≤ gje_c₃ fp n * B a b := by
    intro a b
    have h := hM a b
    rw [hVfinal] at h
    simpa [N_hat, P, B] using h
  have hR' : |R₂| ≤ gje_c₃ fp n * bv i := by
    have h := hR i
    have hsym :
        |matMulVec n P (xseq start) i - xseq (start + (n - 1)) i| =
          |xseq (start + (n - 1)) i - matMulVec n P (xseq start) i| :=
      abs_sub_comm _ _
    rw [hsym]
    simpa [N_hat, P, bv, R₂] using h
  have hUxFn : matMulVec n (V start) x = xseq start := by
    funext a
    exact hUx a
  have hPUx : matMulVec n (matMul n P (V start)) x i =
      matMulVec n P (xseq start) i := by
    rw [matMulVec_matMul, hUxFn]
  have hId : matMulVec n (idMatrix n) x i = x i := by
    rw [matMulVec_id]
  have hR₁eq : R₁ = x i - matMulVec n P (xseq start) i := by
    unfold R₁
    calc
      (∑ j : Fin n, (idMatrix n i j - matMul n P (V start) i j) * x j) =
          (∑ j : Fin n, idMatrix n i j * x j) -
            ∑ j : Fin n, matMul n P (V start) i j * x j := by
              rw [← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = matMulVec n (idMatrix n) x i -
            matMulVec n (matMul n P (V start)) x i := rfl
      _ = x i - matMulVec n P (xseq start) i := by rw [hId, hPUx]
  have hdecomp : x i - xseq (start + (n - 1)) i = R₁ + R₂ := by
    rw [hR₁eq]
    unfold R₂
    ring
  have hBaction :
      (∑ j : Fin n, B i j * |x j|) =
        matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
          (matMulVec n (absMatrix n (V start)) (absVec n x)) i := by
    change matMulVec n B (absVec n x) i = _
    unfold B ch14ext_boundObj
    rw [matMulVec_matMul]
  have hR₁ : |R₁| ≤ gje_c₃ fp n *
      matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
        (matMulVec n (absMatrix n (V start)) (absVec n x)) i := by
    unfold R₁
    calc
      |∑ j : Fin n, (idMatrix n i j - matMul n P (V start) i j) * x j| ≤
          ∑ j : Fin n,
            |(idMatrix n i j - matMul n P (V start) i j) * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n,
            |idMatrix n i j - matMul n P (V start) i j| * |x j| :=
        Finset.sum_congr rfl (fun j _ => abs_mul _ _)
      _ ≤ ∑ j : Fin n, (gje_c₃ fp n * B i j) * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hM' i j) (abs_nonneg _)
      _ = gje_c₃ fp n * ∑ j : Fin n, B i j * |x j| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = gje_c₃ fp n *
          matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
            (matMulVec n (absMatrix n (V start)) (absVec n x)) i := by
        rw [hBaction]
  have hR₂ : |R₂| ≤ gje_c₃ fp n *
      matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
        (absVec n (xseq start)) i := by
    simpa [bv, ch14ext_boundVec] using hR'
  rw [hdecomp]
  refine le_trans (abs_add_le R₁ R₂) ?_
  unfold ch14ext_gjeForwardEnvelope
  calc
    |R₁| + |R₂| ≤
        gje_c₃ fp n *
            matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
              (matMulVec n (absMatrix n (V start)) (absVec n x)) i +
          gje_c₃ fp n *
            matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
              (absVec n (xseq start)) i := add_le_add hR₁ hR₂
    _ = gje_c₃ fp n *
        (matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
            (matMulVec n (absMatrix n (V start)) (absVec n x)) i +
          matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
            (absVec n (xseq start)) i) := by ring

/-- **Higham (14.30a-c), accumulated second-stage backward equation.**

    The perturbations are exhibited as `ΔU = Q E` and `Δy = Q g`, where
    `E` and `g` are the accumulated errors of the concrete recurrences and
    `Q` is a supplied left inverse of their signed cumulative product.  The
    exact equation and both componentwise bounds are derived here; none is an
    input certificate. -/
theorem ch14ext_gje_stage2_backward_error_of_accumulation
    (n : ℕ) (fp : FPModel) (x_hat : Fin n → ℝ)
    (N_hat : Fin n → Fin n → Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ) (start : ℕ)
    (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hQP : matMul n Q (gje_cumulative_product n N_hat start (start + (n - 1))) =
      idMatrix n)
    (hrecM : ∀ t : ℕ, (ht : t < n - 1) → ∀ i j : Fin n,
      |V (start + (t + 1)) i j -
          ∑ l : Fin n, N_hat ⟨start + t, hidx t ht⟩ i l * V (start + t) l j| ≤
        gamma fp 3 *
          ∑ l : Fin n, |N_hat ⟨start + t, hidx t ht⟩ i l| * |V (start + t) l j|)
    (hrecX : ∀ t : ℕ, (ht : t < n - 1) → ∀ i : Fin n,
      |xseq (start + (t + 1)) i -
          ∑ l : Fin n, N_hat ⟨start + t, hidx t ht⟩ i l * xseq (start + t) l| ≤
        gamma fp 3 *
          ∑ l : Fin n, |N_hat ⟨start + t, hidx t ht⟩ i l| * |xseq (start + t) l|) :
    ∃ ΔU : Fin n → Fin n → ℝ, ∃ Δy : Fin n → ℝ,
      (∀ i : Fin n,
        ∑ j : Fin n, (V start i j + ΔU i j) * x_hat j =
          xseq start i + Δy i) ∧
      (∀ i j : Fin n, |ΔU i j| ≤ gje_c₃ fp n *
        ∑ k : Fin n, |ch14ext_gjeXabs n N_hat Q start (n - 1) i k| *
          |V start k j|) ∧
      (∀ i : Fin n, |Δy i| ≤ gje_c₃ fp n *
        ∑ j : Fin n, |ch14ext_gjeXabs n N_hat Q start (n - 1) i j| *
          |xseq start j|) := by
  let E : Fin n → Fin n → ℝ := fun i j =>
    V (start + (n - 1)) i j -
      matMul n (gje_cumulative_product n N_hat start (start + (n - 1)))
        (V start) i j
  let g : Fin n → ℝ := fun i =>
    xseq (start + (n - 1)) i -
      matMulVec n (gje_cumulative_product n N_hat start (start + (n - 1)))
        (xseq start) i
  let ΔU := matMul n Q E
  let Δy := matMulVec n Q g
  have hEbnd : ∀ k j : Fin n,
      |E k j| ≤ gje_c₃ fp n *
        ch14ext_boundObj n N_hat (V start) start (n - 1) k j :=
    ch14ext_matrixAccumulation_c3 n fp N_hat V start hnpos h3 hidx hrecM
  have hgbnd : ∀ k : Fin n,
      |g k| ≤ gje_c₃ fp n *
        ch14ext_boundVec n N_hat (xseq start) start (n - 1) k :=
    ch14ext_rhsAccumulation_c3 n fp N_hat xseq start hnpos h3 hidx hrecX
  have h1 : matMul n Q (V (start + (n - 1))) = Q := by
    rw [hVfinal, matMul_id_right]
  have h2 : matMul n Q
      (matMul n (gje_cumulative_product n N_hat start (start + (n - 1))) (V start)) =
      V start := by
    rw [← matMul_assoc, hQP, matMul_id_left]
  have hΔUeq : ΔU = fun i j => Q i j - V start i j := by
    funext i j
    have hexp : matMul n Q E i j =
        matMul n Q (V (start + (n - 1))) i j -
          matMul n Q
            (matMul n (gje_cumulative_product n N_hat start (start + (n - 1)))
              (V start)) i j := by
      show (∑ k : Fin n, Q i k * E k j) =
        (∑ k : Fin n, Q i k * V (start + (n - 1)) k j) -
          (∑ k : Fin n, Q i k *
            matMul n (gje_cumulative_product n N_hat start (start + (n - 1)))
              (V start) k j)
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by
        show Q i k * (V (start + (n - 1)) k j -
          matMul n (gje_cumulative_product n N_hat start (start + (n - 1)))
            (V start) k j) = _
        ring)
    change matMul n Q E i j = _
    rw [hexp, h1, h2]
  have hg1 : (fun i => matMulVec n Q
      (matMulVec n (gje_cumulative_product n N_hat start (start + (n - 1)))
        (xseq start)) i) = xseq start := by
    funext i
    rw [← matMulVec_matMul, hQP, matMulVec_id]
  have hΔyeq : ∀ i : Fin n,
      Δy i = matMulVec n Q (xseq (start + (n - 1))) i - xseq start i := by
    intro i
    have hlin : matMulVec n Q g i =
        matMulVec n Q (xseq (start + (n - 1))) i -
          matMulVec n Q
            (matMulVec n (gje_cumulative_product n N_hat start (start + (n - 1)))
              (xseq start)) i := by
      show (∑ k : Fin n, Q i k * g k) =
        (∑ k : Fin n, Q i k * xseq (start + (n - 1)) k) -
          (∑ k : Fin n, Q i k *
            matMulVec n (gje_cumulative_product n N_hat start (start + (n - 1)))
              (xseq start) k)
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by
        show Q i k * (xseq (start + (n - 1)) k -
          matMulVec n (gje_cumulative_product n N_hat start (start + (n - 1)))
            (xseq start) k) = _
        ring)
    change matMulVec n Q g i = _
    rw [hlin, congrFun hg1 i]
  have hEq : ∀ i : Fin n,
      ∑ j : Fin n, (V start i j + ΔU i j) * x_hat j =
        xseq start i + Δy i := by
    intro i
    have hUQ : ∀ j : Fin n, V start i j + ΔU i j = Q i j := by
      intro j
      rw [hΔUeq]
      ring
    calc
      ∑ j : Fin n, (V start i j + ΔU i j) * x_hat j =
          ∑ j : Fin n, Q i j * x_hat j :=
        Finset.sum_congr rfl (fun j _ => by rw [hUQ j])
      _ = ∑ j : Fin n, Q i j * xseq (start + (n - 1)) j :=
        Finset.sum_congr rfl (fun j _ => by rw [hxfinal j])
      _ = matMulVec n Q (xseq (start + (n - 1))) i := rfl
      _ = xseq start i + Δy i := by rw [hΔyeq i]; ring
  have hΔU : ∀ i j : Fin n, |ΔU i j| ≤ gje_c₃ fp n *
      ∑ k : Fin n, |ch14ext_gjeXabs n N_hat Q start (n - 1) i k| *
        |V start k j| := by
    intro i j
    have hb := ch14ext_matMul_abs_bound n Q E
      (ch14ext_boundObj n N_hat (V start) start (n - 1)) (gje_c₃ fp n) hEbnd i j
    have hrw : matMul n (absMatrix n Q)
          (ch14ext_boundObj n N_hat (V start) start (n - 1)) i j =
        ∑ k : Fin n, |ch14ext_gjeXabs n N_hat Q start (n - 1) i k| *
          |V start k j| := by
      have hassoc : matMul n (absMatrix n Q)
            (ch14ext_boundObj n N_hat (V start) start (n - 1)) =
          matMul n (ch14ext_gjeXabs n N_hat Q start (n - 1))
            (absMatrix n (V start)) := by
        show matMul n (absMatrix n Q)
            (matMul n (ch14ext_absCumProd n N_hat start (n - 1))
              (absMatrix n (V start))) = _
        rw [← matMul_assoc]
        rfl
      rw [hassoc]
      exact Finset.sum_congr rfl (fun k _ => by
        rw [abs_of_nonneg (ch14ext_gjeXabs_nonneg n N_hat Q start (n - 1) i k)]
        simp [absMatrix])
    change |matMul n Q E i j| ≤ _
    rw [hrw] at hb
    exact hb
  have hΔy : ∀ i : Fin n, |Δy i| ≤ gje_c₃ fp n *
      ∑ j : Fin n, |ch14ext_gjeXabs n N_hat Q start (n - 1) i j| *
        |xseq start j| := by
    intro i
    have hb := ch14ext_matMulVec_abs_bound n Q g
      (ch14ext_boundVec n N_hat (xseq start) start (n - 1)) (gje_c₃ fp n) hgbnd i
    have hrw : matMulVec n (absMatrix n Q)
          (ch14ext_boundVec n N_hat (xseq start) start (n - 1)) i =
        ∑ j : Fin n, |ch14ext_gjeXabs n N_hat Q start (n - 1) i j| *
          |xseq start j| := by
      have hassoc : matMulVec n (absMatrix n Q)
            (ch14ext_boundVec n N_hat (xseq start) start (n - 1)) =
          matMulVec n (ch14ext_gjeXabs n N_hat Q start (n - 1))
            (absVec n (xseq start)) := by
        funext i'
        show matMulVec n (absMatrix n Q)
            (matMulVec n (ch14ext_absCumProd n N_hat start (n - 1))
              (absVec n (xseq start))) i' = _
        rw [← matMulVec_matMul]
        rfl
      rw [hassoc]
      exact Finset.sum_congr rfl (fun j _ => by
        rw [abs_of_nonneg (ch14ext_gjeXabs_nonneg n N_hat Q start (n - 1) i j)]
        simp [absVec])
    change |matMulVec n Q g i| ≤ _
    rw [hrw] at hb
    exact hb
  exact ⟨ΔU, Δy, hEq, hΔU, hΔy⟩

/-- **Theorem 14.5 (14.31), concrete GJE loop.**  The overall residual for the
    actual `ch14ext_gjeStep{Matrix,Vec}` iteration, with the accumulation
    hypotheses discharged from wave 2's per-step γ₃ bounds. -/
theorem ch14ext_gjeConcrete_overall_residual
    (n : ℕ) (fp : FPModel)
    (A L_hat : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hQP : matMul n Q (gje_cumulative_product n (ch14ext_gjeSeqStages n V) start
      (start + (n - 1))) = idMatrix n)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * xseq start j = b i)
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
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |V start k j|) * |x_hat j| +
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V) Q start (n - 1) k₁ k₂| *
              |V start k₂ j|)) * |x_hat j| +
      gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n,
          |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V) Q start (n - 1) k j| *
            |xseq start j|) :=
  ch14ext_gje_overall_residual_of_accumulation n fp A L_hat b x_hat
    (ch14ext_gjeSeqStages n V) V xseq Q start hLU hn hnpos h3 hidx hVfinal hxfinal
    hQP hy (ch14ext_gjeConcrete_hrecM fp n V start h3 hidx hVrec hpiv)
    (ch14ext_gjeConcrete_hrecX fp n V xseq start h3 hidx hxrec hpiv)

end NumStability.Ch14Ext
