-- Algorithms/Ch14GaussJordanQConstruction.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 14 ("Matrix Inversion"), §14.4 ("Gauss-Jordan Elimination"),
-- equations (14.27)-(14.33) and Theorem 14.5, pp. 274-276.
--
-- PURPOSE.  `Ch14GaussJordanAccumulation.lean` exposed the Theorem-14.5 overall
-- residual (14.31) / forward error (14.32) from the concrete per-step GJE waves,
-- but under a SUPPLIED left inverse `Q` of the cumulative product
-- `P = N̂_{n-1}···N̂_2` (hypothesis `hQP : matMul Q P = I`).
--
-- THIS MODULE DISCHARGES that hypothesis by an explicit CONSTRUCTION.
--
--   (A)  Each GJE stage matrix `N̂ₖ = I − n̂ₖ eₖᵀ` is UNIPOTENT: since
--        `(n̂ₖ)ₖ = 0` (Higham: `eᵀᵢ nₖ = 0` for `i ≥ k`, p. 274), the rank-1
--        term is nilpotent, so `N̂ₖ⁻¹ = I + n̂ₖ eₖᵀ` — an EXACT two-sided
--        inverse (`ch14ext_gjeInvStageMatrix_mul_stage`).
--
--   (B)  `Q := (∏ₖ N̂ₖ)⁻¹` is the reverse-order product of the `N̂ₖ⁻¹`,
--        built by the right-append recursion `ch14ext_gjeInvCumProd`.  The
--        telescoping identity `matMul Q P = I`
--        (`ch14ext_gjeInvCumProd_mul_cumProd`) is proved by induction on the
--        number of stages using only the per-stage inverse identity (A).
--        For the CONCRETE GJE stage family the per-stage identity holds
--        UNCONDITIONALLY (no pivot hypothesis — `(n̂ₖ)ₖ = 0` is definitional),
--        so `hQP` is discharged outright.
--
-- The re-exposed accumulated residual/forward-error bounds
-- (`ch14ext_gjeConstructedQ_overall_residual` / `..._forward_error`) therefore
-- carry NO supplied-`Q` hypothesis: `Q` is the constructed cumulative-product
-- inverse.  These older wrappers still take the first forward solve as exact;
-- the concrete (14.33) theorem below instead derives its `DeltaL` contribution
-- from `forwardSub_backward_error`.
--
-- SCALAR AUDIT (Higham's printed leading constants).  §B derives, at the scalar
-- coefficient level, that `gje_c₃ = (n−1)γ₃(1+γ₃)^{n−2}` combined with the GE
-- first-stage `γₙ` budget yields the printed residual constant `8nu`
-- (14.31) and forward constant `2nu` (14.32) at leading order + O(u²).  The
-- entrywise fact `|X_abs| ≥ I` (from `matMul Q P = I`) lets the first-stage
-- object be absorbed into the second-stage object.  The scalar lemmas prove the
-- advertised coefficient budgets, but the old single-object `8nu` wrapper is
-- conditional on `hySharp`; that inequality is not a hypothesis of Higham's
-- theorem and is obtained there only modulo `O(u)`.  Likewise, the old forward
-- wrapper is not the printed two-term (14.32) surface.  Both limitations are
-- stated at their theorem declarations below.
--
-- Sections C and D provide the corrected endpoints.  Section C retains the
-- concrete `DeltaL` witness and exports (14.31) with no `hySharp`.  Section D
-- follows Higham's forward split and exports separate `2nu*T1` and `6nu*T2`
-- terms.  Its exact `T2` uses the absolute cumulative-stage product from
-- (14.29); the book's subsequent `X = U^{-1} + O(u)` replacement remains a
-- distinct first-order identification.
--
-- Import-only companion; does not modify any upstream file.

import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.GaussJordan
import NumStability.Algorithms.Ch14GaussJordanStep
import NumStability.Algorithms.Ch14GaussJordanAccumulation

namespace NumStability.Ch14Ext

open scoped BigOperators
open NumStability

-- ══════════════════════════════════════════════════════════════════════
-- §A1  The unipotent inverse of a GJE stage matrix:  N̂ₖ⁻¹ = I + n̂ₖ eₖᵀ
-- ══════════════════════════════════════════════════════════════════════

/-- The pivot-row entry of the GJE multiplier vector is zero: `(n̂ₖ)ₖ = 0`.
    This is Higham's `eᵀᵢ nₖ = 0` for `i ≥ k` at `i = k` (p. 274), and is what
    makes the rank-1 term `n̂ₖ eₖᵀ` nilpotent. -/
theorem ch14ext_gjeMultVec_self (n : ℕ) (U : Fin n → Fin n → ℝ) (k : Fin n) :
    ch14ext_gjeMultVec n U k k = 0 := by
  simp [ch14ext_gjeMultVec]

/-- The inverse of the GJE second-stage matrix `N̂ₖ = I − n̂ₖ eₖᵀ`, namely
    `N̂ₖ⁻¹ = I + n̂ₖ eₖᵀ`, built from the SAME multiplier vector
    `n̂ₖ = ch14ext_gjeMultVec n U k`. -/
noncomputable def ch14ext_gjeInvStageMatrix (n : ℕ) (U : Fin n → Fin n → ℝ)
    (k : Fin n) : Fin n → Fin n → ℝ :=
  fun i l => (if i = l then (1:ℝ) else 0) +
    (if l = k then ch14ext_gjeMultVec n U k i else 0)

/-- Apply the inverse stage matrix `N̂ₖ⁻¹` to a vector: `(N̂ₖ⁻¹ v)ᵢ = vᵢ + (n̂ₖ)ᵢ vₖ`.
    (Rank-1 analogue of `ch14ext_gjeStageMatrix_apply`, with `+`.) -/
theorem ch14ext_gjeInvStageMatrix_apply (n : ℕ) (U : Fin n → Fin n → ℝ)
    (k : Fin n) (v : Fin n → ℝ) (i : Fin n) :
    ∑ l : Fin n, ch14ext_gjeInvStageMatrix n U k i l * v l
      = v i + ch14ext_gjeMultVec n U k i * v k := by
  unfold ch14ext_gjeInvStageMatrix
  simp only [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **The elementary rank-1 inverse identity (Higham p. 274).**
    `N̂ₖ⁻¹ · N̂ₖ = I`.  The only structural input is `(n̂ₖ)ₖ = 0`
    (`ch14ext_gjeMultVec_self`), which makes `(n̂ₖ eₖᵀ)² = 0`. -/
theorem ch14ext_gjeInvStageMatrix_mul_stage (n : ℕ) (U : Fin n → Fin n → ℝ)
    (k : Fin n) :
    matMul n (ch14ext_gjeInvStageMatrix n U k) (ch14ext_gjeStageMatrix n U k) =
      idMatrix n := by
  funext i j
  show (∑ l : Fin n, ch14ext_gjeInvStageMatrix n U k i l *
      ch14ext_gjeStageMatrix n U k l j) = idMatrix n i j
  rw [ch14ext_gjeInvStageMatrix_apply n U k
    (fun l => ch14ext_gjeStageMatrix n U k l j) i]
  -- `(N̂ₖ⁻¹ · N̂ₖ)_{ij} = (N̂ₖ)_{ij} + (n̂ₖ)ᵢ (N̂ₖ)_{kj}`
  have hkj : ch14ext_gjeStageMatrix n U k k j = (if k = j then (1:ℝ) else 0) := by
    simp [ch14ext_gjeStageMatrix, ch14ext_gjeMultVec_self n U k]
  have hij : ch14ext_gjeStageMatrix n U k i j =
      (if i = j then (1:ℝ) else 0) -
        (if j = k then ch14ext_gjeMultVec n U k i else 0) := rfl
  rw [hkj, hij, idMatrix]
  by_cases h : j = k
  · rw [if_pos h, if_pos h.symm]; ring
  · rw [if_neg h, if_neg (fun hh : k = j => h hh.symm)]; ring

-- ══════════════════════════════════════════════════════════════════════
-- §A2  The reverse-order product Q = (∏ N̂)⁻¹ of the inverse stages
-- ══════════════════════════════════════════════════════════════════════

/-- **Reverse-order cumulative product of the inverse stage matrices.**
    Mirrors `gje_cumulative_product` but appends each new inverse stage on the
    RIGHT, so that `Q · P` telescopes:
      `ch14ext_gjeInvCumProd start finish = N̂_start⁻¹ ··· N̂_{finish-1}⁻¹`.
    (`P = gje_cumulative_product = N̂_{finish-1} ··· N̂_start`.) -/
noncomputable def ch14ext_gjeInvCumProd (n : ℕ)
    (Ninv : Fin n → Fin n → Fin n → ℝ) (start finish_ : ℕ) : Fin n → Fin n → ℝ :=
  if finish_ ≤ start then idMatrix n
  else if h : finish_ - 1 < n then
    matMul n (ch14ext_gjeInvCumProd n Ninv start (finish_ - 1)) (Ninv ⟨finish_ - 1, h⟩)
  else idMatrix n
termination_by finish_ - start

/-- Base case: an empty stage range gives the identity. -/
theorem ch14ext_gjeInvCumProd_base (n : ℕ)
    (Ninv : Fin n → Fin n → Fin n → ℝ) {start finish_ : ℕ}
    (hfinish : finish_ ≤ start) :
    ch14ext_gjeInvCumProd n Ninv start finish_ = idMatrix n := by
  conv_lhs => unfold ch14ext_gjeInvCumProd
  simp [hfinish]

/-- Step case: append stage `finish-1`'s inverse on the RIGHT. -/
theorem ch14ext_gjeInvCumProd_step (n : ℕ)
    (Ninv : Fin n → Fin n → Fin n → ℝ) {start finish_ : ℕ}
    (hstep : start < finish_) (hidx : finish_ - 1 < n) :
    ch14ext_gjeInvCumProd n Ninv start finish_ =
      matMul n (ch14ext_gjeInvCumProd n Ninv start (finish_ - 1))
        (Ninv ⟨finish_ - 1, hidx⟩) := by
  conv_lhs => unfold ch14ext_gjeInvCumProd
  simp [not_le_of_gt hstep, hidx]

-- ══════════════════════════════════════════════════════════════════════
-- §A3  Telescoping:  Q · P = I
-- ══════════════════════════════════════════════════════════════════════

/-- **The telescoping left-inverse identity — DERIVED.**
    If each inverse stage is a genuine left inverse of the corresponding stage
    (`matMul (Ninv m) (N̂ m) = I`), then the reverse-order product `Q` is a left
    inverse of the cumulative product `P`:
      `matMul (ch14ext_gjeInvCumProd) (gje_cumulative_product) = I`.
    Proof: induction on the number of stages; the newest inverse cancels the
    newest stage in the middle via associativity. -/
theorem ch14ext_gjeInvCumProd_mul_cumProd (n : ℕ)
    (N_hat Ninv : Fin n → Fin n → Fin n → ℝ) (start : ℕ)
    (hinv : ∀ (m : ℕ) (hm : m < n),
      matMul n (Ninv ⟨m, hm⟩) (N_hat ⟨m, hm⟩) = idMatrix n) :
    ∀ steps : ℕ, (∀ t : ℕ, t < steps → start + t < n) →
      matMul n (ch14ext_gjeInvCumProd n Ninv start (start + steps))
        (gje_cumulative_product n N_hat start (start + steps)) = idMatrix n := by
  intro steps
  induction steps with
  | zero =>
      intro _
      rw [Nat.add_zero,
        ch14ext_gjeInvCumProd_base n Ninv (le_refl start),
        gje_cumulative_product_base n N_hat (le_refl start),
        matMul_id_left]
  | succ steps ih =>
      intro hidx
      have hlt : steps < steps + 1 := Nat.lt_succ_self steps
      have htop : start + steps < n := hidx steps hlt
      have hstep : start < start + (steps + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos steps)
      have hfin_eq : start + (steps + 1) - 1 = start + steps := by omega
      have hidxfin : start + (steps + 1) - 1 < n := by rw [hfin_eq]; exact htop
      have hfin : (⟨start + (steps + 1) - 1, hidxfin⟩ : Fin n) =
          ⟨start + steps, htop⟩ := by apply Fin.ext; simp [hfin_eq]
      have hidx_prev : ∀ t : ℕ, t < steps → start + t < n :=
        fun t ht => hidx t (Nat.lt_trans ht hlt)
      have ih' := ih hidx_prev
      -- unfold the two products at the top stage
      have hP : gje_cumulative_product n N_hat start (start + (steps + 1)) =
          matMul n (N_hat ⟨start + steps, htop⟩)
            (gje_cumulative_product n N_hat start (start + steps)) := by
        rw [gje_cumulative_product_step n N_hat hstep hidxfin, hfin, hfin_eq]
      have hQ : ch14ext_gjeInvCumProd n Ninv start (start + (steps + 1)) =
          matMul n (ch14ext_gjeInvCumProd n Ninv start (start + steps))
            (Ninv ⟨start + steps, htop⟩) := by
        rw [ch14ext_gjeInvCumProd_step n Ninv hstep hidxfin, hfin, hfin_eq]
      rw [hP, hQ]
      rw [matMul_assoc n (ch14ext_gjeInvCumProd n Ninv start (start + steps))
            (Ninv ⟨start + steps, htop⟩)
            (matMul n (N_hat ⟨start + steps, htop⟩)
              (gje_cumulative_product n N_hat start (start + steps)))]
      rw [← matMul_assoc n (Ninv ⟨start + steps, htop⟩)
            (N_hat ⟨start + steps, htop⟩)
            (gje_cumulative_product n N_hat start (start + steps))]
      rw [hinv (start + steps) htop, matMul_id_left, ih']

-- ══════════════════════════════════════════════════════════════════════
-- §A4  The concrete inverse stage family and the constructed Q
-- ══════════════════════════════════════════════════════════════════════

/-- The concrete inverse GJE stage family `N̂ₖ⁻¹`, stage `k` reading column `k`
    of the running iterate `V k.val` (mirrors `ch14ext_gjeSeqStages`). -/
noncomputable def ch14ext_gjeSeqStagesInv (n : ℕ) (V : ℕ → Fin n → Fin n → ℝ) :
    Fin n → Fin n → Fin n → ℝ :=
  fun k => ch14ext_gjeInvStageMatrix n (V k.val) k

/-- **The constructed left inverse `Q = (∏ N̂)⁻¹`** for the concrete GJE loop,
    as the reverse-order product of the concrete inverse stages over the `n−1`
    second-stage steps. -/
noncomputable def ch14ext_gjeConstructedQ (n : ℕ) (V : ℕ → Fin n → Fin n → ℝ)
    (start : ℕ) : Fin n → Fin n → ℝ :=
  ch14ext_gjeInvCumProd n (ch14ext_gjeSeqStagesInv n V) start (start + (n - 1))

/-- **The per-stage inverse identity for the concrete GJE stages — UNCONDITIONAL.**
    `matMul (N̂ₖ⁻¹) (N̂ₖ) = I` holds for every concrete stage with no pivot
    hypothesis, since `(n̂ₖ)ₖ = 0` is definitional. -/
theorem ch14ext_gjeSeqStagesInv_mul_stages (n : ℕ) (V : ℕ → Fin n → Fin n → ℝ)
    (k : Fin n) :
    matMul n (ch14ext_gjeSeqStagesInv n V k) (ch14ext_gjeSeqStages n V k) =
      idMatrix n :=
  ch14ext_gjeInvStageMatrix_mul_stage n (V k.val) k

/-- **hQP DISCHARGED — the constructed `Q` is a genuine left inverse of the
    cumulative product `P` — UNCONDITIONAL.**
    `matMul (ch14ext_gjeConstructedQ) (gje_cumulative_product … ch14ext_gjeSeqStages …)
      = idMatrix`. -/
theorem ch14ext_gjeConstructedQ_isLeftInverse (n : ℕ) (V : ℕ → Fin n → Fin n → ℝ)
    (start : ℕ) (hidx : ∀ t : ℕ, t < n - 1 → start + t < n) :
    matMul n (ch14ext_gjeConstructedQ n V start)
      (gje_cumulative_product n (ch14ext_gjeSeqStages n V) start (start + (n - 1))) =
      idMatrix n :=
  ch14ext_gjeInvCumProd_mul_cumProd n (ch14ext_gjeSeqStages n V)
    (ch14ext_gjeSeqStagesInv n V) start
    (fun m hm => ch14ext_gjeSeqStagesInv_mul_stages n V ⟨m, hm⟩) (n - 1) hidx

-- ══════════════════════════════════════════════════════════════════════
-- §A5  Theorem 14.5 (14.31)/(14.32) re-exposed WITHOUT the supplied-Q hyp
-- ══════════════════════════════════════════════════════════════════════

/-- **Higham (14.30a-c), concrete rounded GJE loop with constructed `Q`.**

    This removes the final abstract input from
    `ch14ext_gje_stage2_backward_error_of_accumulation`: the left inverse is
    the explicit reverse product of the elementary stage inverses.  Thus the
    exact equation `(Û + ΔU)x̂ = y + Δy` and both printed `c₃` bounds follow
    from the rounded matrix/RHS recurrences and nonzero pivots alone. -/
theorem ch14ext_gjeConcrete_stage2_backward_error
    (n : ℕ) (fp : FPModel) (x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hxrec : ∀ t : ℕ, (ht : t < n - 1) →
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    ∃ ΔU : Fin n → Fin n → ℝ, ∃ Δy : Fin n → ℝ,
      (∀ i : Fin n,
        ∑ j : Fin n, (V start i j + ΔU i j) * x_hat j =
          xseq start i + Δy i) ∧
      (∀ i j : Fin n, |ΔU i j| ≤ gje_c₃ fp n *
        ∑ k : Fin n,
          |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1) i k| *
            |V start k j|) ∧
      (∀ i : Fin n, |Δy i| ≤ gje_c₃ fp n *
        ∑ j : Fin n,
          |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1) i j| *
            |xseq start j|) :=
  ch14ext_gje_stage2_backward_error_of_accumulation n fp x_hat
    (ch14ext_gjeSeqStages n V) V xseq (ch14ext_gjeConstructedQ n V start) start
    hnpos h3 hidx hVfinal hxfinal
    (ch14ext_gjeConstructedQ_isLeftInverse n V start hidx)
    (ch14ext_gjeConcrete_hrecM fp n V start h3 hidx hVrec hpiv)
    (ch14ext_gjeConcrete_hrecX fp n V xseq start h3 hidx hxrec hpiv)

/-- The exact residual expression in Higham (14.33), written with associated
    matrix-vector products:
    `(ΔA₁ + L̂ΔU + ΔLÛ + ΔLΔU)x̂ - (L̂ + ΔL)Δy`. -/
noncomputable def ch14ext_gjeResidual1433 (n : ℕ)
    (L_hat U_hat ΔA₁ ΔL ΔU : Fin n → Fin n → ℝ)
    (x_hat Δy : Fin n → ℝ) (i : Fin n) : ℝ :=
  matMulVec n ΔA₁ x_hat i +
    matMulVec n L_hat (matMulVec n ΔU x_hat) i +
    matMulVec n ΔL (matMulVec n U_hat x_hat) i +
    matMulVec n ΔL (matMulVec n ΔU x_hat) i -
    (matMulVec n L_hat Δy i + matMulVec n ΔL Δy i)

/-- **Higham (14.33), exact residual decomposition.**

    The identity is derived from the three preceding algorithm contracts:
    `A + ΔA₁ = L̂Û`, `(L̂ + ΔL)y = b`, and
    `(Û + ΔU)x̂ = y + Δy`.  The residual itself is not assumed. -/
theorem ch14ext_gje_residual_decomposition_14_33
    (n : ℕ) (A L_hat U_hat ΔA₁ ΔL ΔU : Fin n → Fin n → ℝ)
    (b y x_hat Δy : Fin n → ℝ)
    (hFactor : ∀ i j : Fin n,
      A i j + ΔA₁ i j = matMul n L_hat U_hat i j)
    (hForward : ∀ i : Fin n,
      matMulVec n L_hat y i + matMulVec n ΔL y i = b i)
    (hStage : ∀ i : Fin n,
      matMulVec n U_hat x_hat i + matMulVec n ΔU x_hat i = y i + Δy i) :
    ∀ i : Fin n,
      matMulVec n A x_hat i =
        b i - ch14ext_gjeResidual1433 n L_hat U_hat ΔA₁ ΔL ΔU x_hat Δy i := by
  intro i
  have hFactorAction :
      matMulVec n A x_hat i + matMulVec n ΔA₁ x_hat i =
        matMulVec n L_hat (matMulVec n U_hat x_hat) i := by
    calc
      matMulVec n A x_hat i + matMulVec n ΔA₁ x_hat i =
          ∑ j : Fin n, (A i j + ΔA₁ i j) * x_hat j := by
        unfold matMulVec
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = matMulVec n (matMul n L_hat U_hat) x_hat i := by
        unfold matMulVec
        exact Finset.sum_congr rfl (fun j _ => by rw [hFactor i j])
      _ = matMulVec n L_hat (matMulVec n U_hat x_hat) i := by
        rw [matMulVec_matMul]
  have hStageL :
      matMulVec n L_hat (matMulVec n U_hat x_hat) i +
          matMulVec n L_hat (matMulVec n ΔU x_hat) i =
        matMulVec n L_hat y i + matMulVec n L_hat Δy i := by
    unfold matMulVec
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by
      have hk := hStage k
      change (∑ j : Fin n, U_hat k j * x_hat j) +
        (∑ j : Fin n, ΔU k j * x_hat j) = y k + Δy k at hk
      calc
        L_hat i k * (∑ j : Fin n, U_hat k j * x_hat j) +
            L_hat i k * (∑ j : Fin n, ΔU k j * x_hat j) =
          L_hat i k *
            ((∑ j : Fin n, U_hat k j * x_hat j) +
              ∑ j : Fin n, ΔU k j * x_hat j) := by ring
        _ = L_hat i k * (y k + Δy k) := by rw [hk]
        _ = L_hat i k * y k + L_hat i k * Δy k := by ring)
  have hStageΔL :
      matMulVec n ΔL (matMulVec n U_hat x_hat) i +
          matMulVec n ΔL (matMulVec n ΔU x_hat) i =
        matMulVec n ΔL y i + matMulVec n ΔL Δy i := by
    unfold matMulVec
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by
      have hk := hStage k
      change (∑ j : Fin n, U_hat k j * x_hat j) +
        (∑ j : Fin n, ΔU k j * x_hat j) = y k + Δy k at hk
      calc
        ΔL i k * (∑ j : Fin n, U_hat k j * x_hat j) +
            ΔL i k * (∑ j : Fin n, ΔU k j * x_hat j) =
          ΔL i k *
            ((∑ j : Fin n, U_hat k j * x_hat j) +
              ∑ j : Fin n, ΔU k j * x_hat j) := by ring
        _ = ΔL i k * (y k + Δy k) := by rw [hk]
        _ = ΔL i k * y k + ΔL i k * Δy k := by ring)
  unfold ch14ext_gjeResidual1433
  linarith [hFactorAction, hStageL, hStageΔL, hForward i]

/-- **Higham (14.33) for the concrete rounded GJE computation.**

    `ΔA₁` is the actual LU residual, `ΔL` comes from the proved forward-
    substitution model, and `ΔU,Δy` come from the concrete (14.30) theorem.
    The result exports all four componentwise bounds together with the exact
    residual identity, so no target-equivalent residual hypothesis is present. -/
theorem ch14ext_gjeConcrete_residual_decomposition_14_33
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
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    ∃ ΔA₁ ΔL ΔU : Fin n → Fin n → ℝ, ∃ Δy : Fin n → ℝ,
      (∀ i j : Fin n, |ΔA₁ i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |V start k j|) ∧
      (∀ i j : Fin n, |ΔL i j| ≤ gamma fp n * |L_hat i j|) ∧
      (∀ i j : Fin n, |ΔU i j| ≤ gje_c₃ fp n *
        ∑ k : Fin n,
          |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1) i k| *
            |V start k j|) ∧
      (∀ i : Fin n, |Δy i| ≤ gje_c₃ fp n *
        ∑ j : Fin n,
          |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1) i j| *
            |xseq start j|) ∧
      (∀ i : Fin n, matMulVec n A x_hat i =
        b i - ch14ext_gjeResidual1433 n L_hat (V start) ΔA₁ ΔL ΔU x_hat Δy i) := by
  let ΔA₁ : Fin n → Fin n → ℝ := fun i j => matMul n L_hat (V start) i j - A i j
  have hΔA₁ : ∀ i j : Fin n, |ΔA₁ i j| ≤ gamma fp n *
      ∑ k : Fin n, |L_hat i k| * |V start k j| := by
    intro i j
    exact hLU.backward_bound i j
  have hFactor : ∀ i j : Fin n,
      A i j + ΔA₁ i j = matMul n L_hat (V start) i j := by
    intro i j
    unfold ΔA₁
    ring
  obtain ⟨ΔL, hΔL, hForwardRaw⟩ := forwardSub_backward_error fp n L_hat b
    (fun i => by rw [hLU.L_diag i]; norm_num) hLU.L_upper_zero hn
  have hForward : ∀ i : Fin n,
      matMulVec n L_hat (xseq start) i + matMulVec n ΔL (xseq start) i = b i := by
    intro i
    have h := hForwardRaw i
    rw [← hyStart] at h
    simpa [matMulVec, Finset.sum_add_distrib, add_mul] using h
  obtain ⟨ΔU, Δy, hStageRaw, hΔU, hΔy⟩ :=
    ch14ext_gjeConcrete_stage2_backward_error n fp x_hat V xseq start hnpos h3
      hidx hVfinal hxfinal hVrec hxrec hpiv
  have hStage : ∀ i : Fin n,
      matMulVec n (V start) x_hat i + matMulVec n ΔU x_hat i =
        xseq start i + Δy i := by
    intro i
    have h := hStageRaw i
    simpa [matMulVec, Finset.sum_add_distrib, add_mul] using h
  have hResidual := ch14ext_gje_residual_decomposition_14_33 n A L_hat (V start)
    ΔA₁ ΔL ΔU b (xseq start) x_hat Δy hFactor hForward hStage
  exact ⟨ΔA₁, ΔL, ΔU, Δy, hΔA₁, hΔL, hΔU, hΔy, hResidual⟩

/-- **Theorem 14.5 / eq. (14.31): overall GJE residual, constructed `Q`.**

    Identical to `ch14ext_gjeConcrete_overall_residual` of the accumulation
    module, but the left-inverse hypothesis `hQP` is GONE: `Q` is now the
    explicitly constructed cumulative-product inverse `ch14ext_gjeConstructedQ`,
    and `matMul Q P = I` is discharged by `ch14ext_gjeConstructedQ_isLeftInverse`
    (from the elementary rank-1 stage inverses).  The only remaining structural
    input is Higham's own WLOG normalization `D = I` (`hVfinal`, p. 274). -/
theorem ch14ext_gjeConstructedQ_overall_residual
    (n : ℕ) (fp : FPModel)
    (A L_hat : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
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
            |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
                (ch14ext_gjeConstructedQ n V start) start (n - 1) k₁ k₂| *
              |V start k₂ j|)) * |x_hat j| +
      gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n,
          |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1) k j| *
            |xseq start j|) :=
  ch14ext_gje_overall_residual_of_accumulation n fp A L_hat b x_hat
    (ch14ext_gjeSeqStages n V) V xseq (ch14ext_gjeConstructedQ n V start) start
    hLU hn hnpos h3 hidx hVfinal hxfinal
    (ch14ext_gjeConstructedQ_isLeftInverse n V start hidx) hy
    (ch14ext_gjeConcrete_hrecM fp n V start h3 hidx hVrec hpiv)
    (ch14ext_gjeConcrete_hrecX fp n V xseq start h3 hidx hxrec hpiv)

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

-- ══════════════════════════════════════════════════════════════════════
-- §B1  Scalar coefficient audit: the printed leading constants 8nu / 2nu
-- ══════════════════════════════════════════════════════════════════════

/-- The exact `O(u²)` remainder of the GE first-stage constant `γₙ`
    (from `gamma_eq_linear_plus_quadratic_remainder`): `γₙ = nu + this`. -/
noncomputable def ch14ext_gammaRem (fp : FPModel) (n : ℕ) : ℝ :=
  (((n : ℝ) * fp.u) ^ 2) / (1 - (n : ℝ) * fp.u)

/-- `γₙ = nu + ch14ext_gammaRem`, the first-order split of the GE constant. -/
theorem ch14ext_gamma_split (fp : FPModel) (n : ℕ) (hn : gammaValid fp n) :
    gamma fp n = (n : ℝ) * fp.u + ch14ext_gammaRem fp n :=
  gamma_eq_linear_plus_quadratic_remainder fp n hn

/-- The GE first-stage remainder is nonnegative (`nu < 1` ⇒ denominator `> 0`). -/
theorem ch14ext_gammaRem_nonneg (fp : FPModel) (n : ℕ) (hn : gammaValid fp n) :
    0 ≤ ch14ext_gammaRem fp n := by
  unfold ch14ext_gammaRem gammaValid at *
  apply div_nonneg (sq_nonneg _)
  linarith

/-- The `O(u²)` remainder carried by the residual leading constant `8nu`. -/
noncomputable def ch14ext_residualRem (fp : FPModel) (n : ℕ) : ℝ :=
  ch14ext_gammaRem fp n + 2 * gje_c3_quadratic_remainder fp n

/-- **SCALAR AUDIT (14.31): the residual leading constant is `8nu`.**

    The three accumulation coefficients — the GE first-stage `γₙ` (eq. 9.17 /
    `LUBackwardError`) and the two GJE second-stage `c₃ = (n−1)γ₃(1+γ₃)^{n−2}`
    (one for `ΔU`, one for `Δy`) — sum to at most `8nu` at leading order:
        `γₙ + c₃ + c₃  ≤  8·n·u + ch14ext_residualRem`,
    with the remainder `O(u²)` (`= n²u²/(1−nu) + 2·(9(n−1)u²/(1−3u)·(1+γ₃)^{n−2}
    + 3(n−1)u((1+γ₃)^{n−2}−1))`).

    Derivation of the integer `8`: `γₙ = nu + O(u²)` contributes `1`, and each
    `c₃ ≤ 3nu + O(u²)` contributes `3`, for `1 + 3 + 3 = 7 ≤ 8`.  The
    accumulation route's sharp constant is thus `7nu` — one `nu` below Higham's
    printed `8nu`, because the socket takes the forward substitution `L̂ŷ = b`
    exact (`hy`), whereas Higham's proof (14.33) carries a second first-stage
    `γₙ` from the Theorem-8.5 factor `ΔL` (the `L̂ŷ = b` rounding).  `7nu ≤ 8nu`,
    so the printed constant is a valid upper bound. -/
theorem ch14ext_gje_residual_coeff_budget (fp : FPModel) (n : ℕ)
    (hn : gammaValid fp n) (h3 : gammaValid fp 3) :
    gamma fp n + gje_c₃ fp n + gje_c₃ fp n ≤
      8 * (n : ℝ) * fp.u + ch14ext_residualRem fp n := by
  have hu : 0 ≤ (n : ℝ) * fp.u :=
    mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
  have hg := ch14ext_gamma_split fp n hn
  have hc := gje_c3_le_three_n_u_plus_quadratic_remainder fp n h3
  unfold ch14ext_residualRem
  -- γₙ + 2c₃ = nu + gammaRem + 2c₃ ≤ 7nu + (gammaRem + 2·Qrem) ≤ 8nu + (…)
  nlinarith [hc, hg, hu]

/-- **SCALAR AUDIT (14.32) first term: the forward constant `2nu`.**

    Higham's forward-error proof bounds the first two terms `(x − x₀) +
    (x₀ − Û⁻¹ŷ)` by `γₙ|A⁻¹||L̂||Û||x̂|`; the printed `2nu` prefactor is the
    standard readable cap `γₙ ≤ 2nu` valid whenever `nu ≤ 1/2`.  This is an
    EXACT bound (no `O(u²)` remainder). -/
theorem ch14ext_gje_forward_first_coeff (fp : FPModel) (n : ℕ)
    (hhalf : (n : ℝ) * fp.u ≤ 1 / 2) :
    gamma fp n ≤ 2 * ((n : ℝ) * fp.u) :=
  gamma_le_two_mul_n_u_of_nu_le_half fp n hhalf

/-- **SCALAR AUDIT (14.32) second term: the forward constant `6nu = 3·2nu`.**

    The forward-error term `(x₀ − x̂)`, bounded by (14.29), carries the two GJE
    `c₃` coefficients (from `ΔU`, `Δy`) on the `|Û⁻¹||Û|` object; their sum is at
    most `6nu` at leading order:
        `c₃ + c₃ ≤ 6·n·u + 2·gje_c3_quadratic_remainder`,
    i.e. Higham's `3·2nu` prefactor on `|Û⁻¹||Û|`. -/
theorem ch14ext_gje_forward_second_coeff (fp : FPModel) (n : ℕ)
    (h3 : gammaValid fp 3) :
    gje_c₃ fp n + gje_c₃ fp n ≤
      6 * (n : ℝ) * fp.u + 2 * gje_c3_quadratic_remainder fp n := by
  have hc := gje_c3_le_three_n_u_plus_quadratic_remainder fp n h3
  nlinarith [hc]

-- ══════════════════════════════════════════════════════════════════════
-- §B2  X_abs ≥ I on the diagonal, and the first-stage → second-stage fold
-- ══════════════════════════════════════════════════════════════════════

/-- **Entrywise abs-product domination.**
    `|∏ N̂| ≤ ∏ |N̂|` componentwise: the signed cumulative product is dominated
    by the cumulative product of the absolute-value stages (the `ch14ext_absCumProd`
    envelope).  Proof by induction peeling the top stage. -/
theorem ch14ext_cumProd_abs_dom (n : ℕ) (N_hat : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ) :
    ∀ steps : ℕ, (∀ t : ℕ, t < steps → start + t < n) → ∀ i j : Fin n,
      |gje_cumulative_product n N_hat start (start + steps) i j| ≤
        gje_cumulative_product n (fun k a b => |N_hat k a b|) start
          (start + steps) i j := by
  intro steps
  induction steps with
  | zero =>
      intro _ i j
      rw [Nat.add_zero, gje_cumulative_product_base n N_hat (le_refl start),
        gje_cumulative_product_base n (fun k a b => |N_hat k a b|) (le_refl start)]
      unfold idMatrix
      by_cases h : i = j <;> simp [h]
  | succ steps ih =>
      intro hidx i j
      have hlt : steps < steps + 1 := Nat.lt_succ_self steps
      have htop : start + steps < n := hidx steps hlt
      have hstep : start < start + (steps + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos steps)
      have hfin_eq : start + (steps + 1) - 1 = start + steps := by omega
      have hidxfin : start + (steps + 1) - 1 < n := by rw [hfin_eq]; exact htop
      have hfin : (⟨start + (steps + 1) - 1, hidxfin⟩ : Fin n) =
          ⟨start + steps, htop⟩ := by apply Fin.ext; simp [hfin_eq]
      have ih' := ih (fun t ht => hidx t (Nat.lt_trans ht hlt))
      have hPs : gje_cumulative_product n N_hat start (start + (steps + 1)) =
          matMul n (N_hat ⟨start + steps, htop⟩)
            (gje_cumulative_product n N_hat start (start + steps)) := by
        rw [gje_cumulative_product_step n N_hat hstep hidxfin, hfin, hfin_eq]
      have hPa : gje_cumulative_product n (fun k a b => |N_hat k a b|) start
            (start + (steps + 1)) =
          matMul n (fun a b => |N_hat ⟨start + steps, htop⟩ a b|)
            (gje_cumulative_product n (fun k a b => |N_hat k a b|) start
              (start + steps)) := by
        rw [gje_cumulative_product_step n (fun k a b => |N_hat k a b|) hstep hidxfin,
          hfin, hfin_eq]
      rw [hPs, hPa]
      show |∑ l : Fin n, N_hat ⟨start + steps, htop⟩ i l *
          gje_cumulative_product n N_hat start (start + steps) l j| ≤
        ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| *
          gje_cumulative_product n (fun k a b => |N_hat k a b|) start
            (start + steps) l j
      calc |∑ l : Fin n, N_hat ⟨start + steps, htop⟩ i l *
              gje_cumulative_product n N_hat start (start + steps) l j|
          ≤ ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l *
              gje_cumulative_product n N_hat start (start + steps) l j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| *
              |gje_cumulative_product n N_hat start (start + steps) l j| :=
            Finset.sum_congr rfl (fun l _ => abs_mul _ _)
        _ ≤ ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| *
              gje_cumulative_product n (fun k a b => |N_hat k a b|) start
                (start + steps) l j :=
            Finset.sum_le_sum
              (fun l _ => mul_le_mul_of_nonneg_left (ih' l j) (abs_nonneg _))

/-! ## The special upper-triangular product in (14.27)-(14.29) -/

/-- A rounded subtraction whose exact result is zero is exactly zero in the
    standard relative-error model. -/
theorem ch14ext_fl_sub_zero_zero (fp : FPModel) : fp.fl_sub 0 0 = 0 := by
  obtain ⟨δ, _hδ, hfl⟩ := fp.model_sub 0 0
  simpa using hfl

/-- Multiplication by an exact zero on the left remains zero. -/
theorem ch14ext_fl_mul_zero_left (fp : FPModel) (x : ℝ) : fp.fl_mul 0 x = 0 := by
  obtain ⟨δ, _hδ, hfl⟩ := fp.model_mul 0 x
  simpa using hfl

/-- Multiplication by an exact zero on the right remains zero. -/
theorem ch14ext_fl_mul_zero_right (fp : FPModel) (x : ℝ) : fp.fl_mul x 0 = 0 := by
  obtain ⟨δ, _hδ, hfl⟩ := fp.model_mul x 0
  simpa using hfl

/-- Division of zero by a nonzero pivot remains zero. -/
theorem ch14ext_fl_div_zero_left (fp : FPModel) (x : ℝ) (hx : x ≠ 0) :
    fp.fl_div 0 x = 0 := by
  obtain ⟨δ, _hδ, hfl⟩ := fp.model_div 0 x hx
  simpa using hfl

/-- One rounded GJE row-elimination step preserves upper-triangular shape. -/
theorem ch14ext_gjeStepMatrix_upper_triangular (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (k : Fin n)
    (hU : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hpiv : U k k ≠ 0) :
    ∀ i j : Fin n, j.val < i.val →
      ch14ext_gjeStepMatrix fp n U k i j = 0 := by
  intro i j hji
  by_cases hik : i = k
  · subst i
    simp [ch14ext_gjeStepMatrix, hU k j hji]
  · have hmul :
        fp.fl_mul (fp.fl_div (U i k) (U k k)) (U k j) = 0 := by
      by_cases hki : k.val < i.val
      · rw [hU i k hki, ch14ext_fl_div_zero_left fp (U k k) hpiv,
          ch14ext_fl_mul_zero_left]
      · have hikval : i.val < k.val := by
          have hne : i.val ≠ k.val := by
            intro h
            apply hik
            exact Fin.ext h
          omega
        have hkj : j.val < k.val := lt_trans hji hikval
        rw [hU k j hkj, ch14ext_fl_mul_zero_right]
    rw [ch14ext_gjeStepMatrix, if_neg hik, hU i j hji, hmul,
      ch14ext_fl_sub_zero_zero]

/-- Every concrete second-stage iterate remains upper triangular. -/
theorem ch14ext_gjeSeq_upper_triangular (fp : FPModel) (n : ℕ)
    (V : ℕ → Fin n → Fin n → ℝ) (start : ℕ)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hV0 : ∀ i j : Fin n, j.val < i.val → V start i j = 0)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    ∀ t : ℕ, t ≤ n - 1 →
      ∀ i j : Fin n, j.val < i.val → V (start + t) i j = 0 := by
  intro t
  induction t with
  | zero =>
      intro _ i j hji
      simpa using hV0 i j hji
  | succ t ih =>
      intro ht i j hji
      have htstep : t < n - 1 := by omega
      rw [hVrec t htstep]
      exact ch14ext_gjeStepMatrix_upper_triangular fp n (V (start + t))
        ⟨start + t, hidx t htstep⟩ (ih (by omega)) (hpiv t htstep) i j hji

/-- On an upper-triangular iterate, the stage multiplier has the source support
    `(n_k)_i = 0` for every `i ≥ k`. -/
theorem ch14ext_gjeMultVec_zero_of_upper (n : ℕ)
    (U : Fin n → Fin n → ℝ) (k i : Fin n)
    (hU : ∀ a b : Fin n, b.val < a.val → U a b = 0)
    (hki : k.val ≤ i.val) :
    ch14ext_gjeMultVec n U k i = 0 := by
  by_cases hik : i = k
  · simp [ch14ext_gjeMultVec, hik]
  · have hlt : k.val < i.val := by
      have hne : k.val ≠ i.val := by
        intro h
        apply hik
        exact Fin.ext h.symm
      omega
    simp [ch14ext_gjeMultVec, hik, hU i k hlt]

/-- Multiplying a nonnegative matrix by the absolute elementary GJE stage has
    the exact two-entry row formula used in the cumulative-product induction. -/
theorem ch14ext_abs_gjeStageMatrix_mul (n : ℕ)
    (U A : Fin n → Fin n → ℝ) (k i j : Fin n) :
    matMul n (fun a b => |ch14ext_gjeStageMatrix n U k a b|) A i j =
      A i j + |ch14ext_gjeMultVec n U k i| * A k j := by
  by_cases hik : i = k
  · subst i
    rw [ch14ext_gjeMultVec_self]
    simp only [abs_zero, zero_mul, add_zero]
    unfold matMul
    have hrow : ∀ x : Fin n,
        |ch14ext_gjeStageMatrix n U k k x| =
          if k = x then (1 : ℝ) else 0 := by
      intro x
      by_cases hkx : k = x <;>
        simp [ch14ext_gjeStageMatrix, ch14ext_gjeMultVec, hkx]
    simp_rw [hrow]
    simp
  · have hrow : ∀ l : Fin n,
        |ch14ext_gjeStageMatrix n U k i l| =
          (if i = l then 1 else 0) +
            (if l = k then |ch14ext_gjeMultVec n U k i| else 0) := by
      intro l
      by_cases hil : i = l
      · subst l
        simp [ch14ext_gjeStageMatrix, hik]
      · by_cases hlk : l = k
        · subst l
          simp [ch14ext_gjeStageMatrix, hil]
        · simp [ch14ext_gjeStageMatrix, hil, hlk]
    unfold matMul
    simp_rw [hrow]
    simp only [add_mul, Finset.sum_add_distrib]
    simp

/-- For increasing GJE stage indices with `(n_k)_i = 0` for `i ≥ k`, the
    product of the absolute stages is exactly the entrywise absolute value of
    the signed product.  The simultaneous second conclusion records that every
    not-yet-processed row and column of the signed product is still an identity
    row and column. -/
theorem ch14ext_gje_cumProd_abs_exact_and_future_identity (n : ℕ)
    (V : ℕ → Fin n → Fin n → ℝ) (start : ℕ) :
    ∀ steps : ℕ,
      (hidx : ∀ t : ℕ, t < steps → start + t < n) →
      (hsupport : ∀ t : ℕ, (ht : t < steps) → ∀ i : Fin n,
        start + t ≤ i.val →
          ch14ext_gjeMultVec n (V (start + t)) ⟨start + t, hidx t ht⟩ i = 0) →
      (∀ i j : Fin n,
        gje_cumulative_product n
            (fun k a b => |ch14ext_gjeSeqStages n V k a b|)
            start (start + steps) i j =
          |gje_cumulative_product n (ch14ext_gjeSeqStages n V)
            start (start + steps) i j|) ∧
      (∀ r : Fin n, start + steps ≤ r.val →
        (∀ j : Fin n,
          gje_cumulative_product n (ch14ext_gjeSeqStages n V)
              start (start + steps) r j = idMatrix n r j) ∧
        (∀ i : Fin n,
          gje_cumulative_product n (ch14ext_gjeSeqStages n V)
              start (start + steps) i r = idMatrix n i r)) := by
  intro steps
  induction steps with
  | zero =>
      intro _hidx _hsupport
      constructor
      · intro i j
        rw [Nat.add_zero,
          gje_cumulative_product_base n
            (fun k a b => |ch14ext_gjeSeqStages n V k a b|) (le_refl start),
          gje_cumulative_product_base n (ch14ext_gjeSeqStages n V) (le_refl start)]
        by_cases hij : i = j <;> simp [idMatrix, hij]
      · intro r _hr
        rw [Nat.add_zero,
          gje_cumulative_product_base n (ch14ext_gjeSeqStages n V) (le_refl start)]
        exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ steps ih =>
      intro hidx hsupport
      have hlt : steps < steps + 1 := Nat.lt_succ_self steps
      have htop : start + steps < n := hidx steps hlt
      let k : Fin n := ⟨start + steps, htop⟩
      let Ps := gje_cumulative_product n (ch14ext_gjeSeqStages n V)
        start (start + steps)
      let Pa := gje_cumulative_product n
        (fun q a b => |ch14ext_gjeSeqStages n V q a b|)
        start (start + steps)
      have hidxPrev : ∀ t : ℕ, t < steps → start + t < n :=
        fun t ht => hidx t (Nat.lt_trans ht hlt)
      have hsupportPrev : ∀ t : ℕ, (ht : t < steps) → ∀ i : Fin n,
          start + t ≤ i.val →
            ch14ext_gjeMultVec n (V (start + t))
              ⟨start + t, hidxPrev t ht⟩ i = 0 := by
        intro t ht i hti
        simpa using hsupport t (Nat.lt_trans ht hlt) i hti
      obtain ⟨habsPrev, hfuturePrev⟩ := ih hidxPrev hsupportPrev
      have hPaAbs : ∀ i j : Fin n, Pa i j = |Ps i j| := by
        simpa [Pa, Ps] using habsPrev
      have hkFuture := hfuturePrev k (by simp [k])
      have hkRow : ∀ j : Fin n, Ps k j = idMatrix n k j := by
        simpa [Ps] using hkFuture.1
      have hkCol : ∀ i : Fin n, Ps i k = idMatrix n i k := by
        simpa [Ps] using hkFuture.2
      have hstep : start < start + (steps + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos steps)
      have hfinEq : start + (steps + 1) - 1 = start + steps := by omega
      have hidxFin : start + (steps + 1) - 1 < n := by
        rw [hfinEq]
        exact htop
      have hfin : (⟨start + (steps + 1) - 1, hidxFin⟩ : Fin n) = k := by
        apply Fin.ext
        simp [k, hfinEq]
      have hSignedStep :
          gje_cumulative_product n (ch14ext_gjeSeqStages n V)
              start (start + (steps + 1)) =
            matMul n (ch14ext_gjeSeqStages n V k) Ps := by
        rw [gje_cumulative_product_step n (ch14ext_gjeSeqStages n V)
          hstep hidxFin, hfin, hfinEq]
      have hAbsStep :
          gje_cumulative_product n
              (fun q a b => |ch14ext_gjeSeqStages n V q a b|)
              start (start + (steps + 1)) =
            matMul n (fun a b => |ch14ext_gjeSeqStages n V k a b|) Pa := by
        rw [gje_cumulative_product_step n
          (fun q a b => |ch14ext_gjeSeqStages n V q a b|)
          hstep hidxFin, hfin, hfinEq]
      constructor
      · intro i j
        rw [hAbsStep, hSignedStep]
        have hSigned :
            matMul n (ch14ext_gjeSeqStages n V k) Ps i j =
              Ps i j - ch14ext_gjeMultVec n (V k.val) k i * idMatrix n k j := by
          change (∑ l : Fin n,
              ch14ext_gjeStageMatrix n (V k.val) k i l * Ps l j) = _
          rw [ch14ext_gjeStageMatrix_apply, hkRow j]
        have hAbs :
            matMul n (fun a b => |ch14ext_gjeSeqStages n V k a b|) Pa i j =
              Pa i j + |ch14ext_gjeMultVec n (V k.val) k i| * idMatrix n k j := by
          change matMul n
              (fun a b => |ch14ext_gjeStageMatrix n (V k.val) k a b|) Pa i j = _
          rw [ch14ext_abs_gjeStageMatrix_mul, hPaAbs k j, hkRow j]
          by_cases hkj : k = j <;> simp [idMatrix, hkj]
        rw [hAbs, hSigned, hPaAbs i j]
        by_cases hjk : j = k
        · subst j
          rw [hkCol i]
          by_cases hik : i = k
          · subst i
            simp [idMatrix, ch14ext_gjeMultVec]
          · simp [idMatrix, hik]
        · simp [idMatrix, Ne.symm hjk]
      · intro r hr
        have hrPrev : start + steps ≤ r.val := by omega
        obtain ⟨hrRow, hrCol⟩ := hfuturePrev r hrPrev
        have hkr : k ≠ r := by
          intro h
          have hval := congrArg Fin.val h
          simp [k] at hval
          omega
        constructor
        · intro j
          rw [hSignedStep]
          change (∑ l : Fin n,
              ch14ext_gjeStageMatrix n (V k.val) k r l * Ps l j) = _
          rw [ch14ext_gjeStageMatrix_apply]
          have hnr : ch14ext_gjeMultVec n (V k.val) k r = 0 := by
            have hle : start + steps ≤ r.val := by omega
            have hs := hsupport steps hlt r hle
            simpa [k] using hs
          rw [hnr]
          simpa [Ps] using hrRow j
        · intro i
          rw [hSignedStep]
          change (∑ l : Fin n,
              ch14ext_gjeStageMatrix n (V k.val) k i l * Ps l r) = _
          rw [ch14ext_gjeStageMatrix_apply]
          have hkrZero : Ps k r = 0 := by
            rw [show Ps k r = idMatrix n k r by simpa [Ps] using hrCol k]
            simp [idMatrix, hkr]
          rw [hkrZero]
          simpa [Ps] using hrCol i

/-- Concrete upper-triangular GJE stages therefore have no gap between the
    signed cumulative product and the absolute accumulation envelope. -/
theorem ch14ext_gje_absCumProd_eq_abs_signed (n : ℕ)
    (V : ℕ → Fin n → Fin n → ℝ) (start steps : ℕ)
    (hidx : ∀ t : ℕ, t < steps → start + t < n)
    (hUpper : ∀ t : ℕ, t ≤ steps →
      ∀ i j : Fin n, j.val < i.val → V (start + t) i j = 0) :
    ∀ i j : Fin n,
      ch14ext_absCumProd n (ch14ext_gjeSeqStages n V) start steps i j =
        |gje_cumulative_product n (ch14ext_gjeSeqStages n V)
          start (start + steps) i j| := by
  intro i j
  unfold ch14ext_absCumProd
  exact (ch14ext_gje_cumProd_abs_exact_and_future_identity n V start steps hidx
    (fun t ht a hta =>
      ch14ext_gjeMultVec_zero_of_upper n (V (start + t))
        ⟨start + t, hidx t ht⟩ a (hUpper t (Nat.le_of_lt ht)) hta)).1 i j

/-- If the signed product `S` satisfies `I - S U = E`, the exact identity
    `S = U⁻¹ - E U⁻¹` converts the accumulated residual into the source-facing
    comparison

    `|S| ≤ |U⁻¹| + c |S| |U| |U⁻¹|`.

    The equality `X = |S|` is supplied here as the structural conclusion above,
    not as an assumed asymptotic comparison. -/
theorem ch14ext_abs_signed_le_abs_rightInverse_add (n : ℕ)
    (S X U U_inv : Fin n → Fin n → ℝ) (c : ℝ)
    (hX : ∀ i j : Fin n, X i j = |S i j|)
    (hRight : IsRightInverse n U U_inv)
    (hResidual : ∀ i j : Fin n,
      |idMatrix n i j - matMul n S U i j| ≤
        c * matMul n X (absMatrix n U) i j) :
    ∀ i j : Fin n,
      X i j ≤ |U_inv i j| +
        c * matMul n (matMul n X (absMatrix n U))
          (absMatrix n U_inv) i j := by
  intro i j
  let E : Fin n → Fin n → ℝ := fun a b =>
    idMatrix n a b - matMul n S U a b
  have hUU : matMul n U U_inv = idMatrix n := by
    funext a b
    exact hRight a b
  have hAssoc : matMul n (matMul n S U) U_inv i j = S i j := by
    rw [matMul_assoc n S U U_inv, hUU, matMul_id_right]
  have hEprod : matMul n E U_inv i j = U_inv i j - S i j := by
    unfold E matMul
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib]
    have hId : (∑ a : Fin n, idMatrix n i a * U_inv a j) = U_inv i j := by
      change matMul n (idMatrix n) U_inv i j = U_inv i j
      rw [matMul_id_left]
    rw [hId]
    change U_inv i j - matMul n (matMul n S U) U_inv i j = U_inv i j - S i j
    rw [hAssoc]
  have hSrepr : S i j = U_inv i j - matMul n E U_inv i j := by
    linarith [hEprod]
  rw [hX i j, hSrepr]
  calc
    |U_inv i j - matMul n E U_inv i j| =
        |U_inv i j + -matMul n E U_inv i j| := by rw [sub_eq_add_neg]
    _ ≤ |U_inv i j| + |-matMul n E U_inv i j| := abs_add_le _ _
    _ = |U_inv i j| + |matMul n E U_inv i j| := by rw [abs_neg]
    _ ≤ |U_inv i j| + ∑ a : Fin n, |E i a * U_inv a j| := by
      have hsum : |matMul n E U_inv i j| ≤
          ∑ a : Fin n, |E i a * U_inv a j| :=
        Finset.abs_sum_le_sum_abs _ _
      linarith
    _ = |U_inv i j| + ∑ a : Fin n, |E i a| * |U_inv a j| := by
      congr 1
      exact Finset.sum_abs_mul (fun a => E i a) (fun a => U_inv a j)
    _ ≤ |U_inv i j| +
        ∑ a : Fin n,
          (c * matMul n X (absMatrix n U) i a) * |U_inv a j| := by
      have hsum : (∑ a : Fin n, |E i a| * |U_inv a j|) ≤
          ∑ a : Fin n,
            (c * matMul n X (absMatrix n U) i a) * |U_inv a j| := by
        apply Finset.sum_le_sum
        intro a _ha
        apply mul_le_mul_of_nonneg_right
        · simpa [E] using hResidual i a
        · exact abs_nonneg _
      linarith
    _ = |U_inv i j| +
        c * matMul n (matMul n X (absMatrix n U))
          (absMatrix n U_inv) i j := by
      unfold matMul absMatrix
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _ha
      ring

/-- **The constructed `Q` forces `X_abs ≥ I` on the diagonal.**
    Since `matMul Q P = I` and `|P| ≤ ch14ext_absCumProd`, the middle envelope
    `X_abs = |Q|·ch14ext_absCumProd` has every diagonal entry `≥ 1`:
        `1 = |(QP)ₖₖ| ≤ ∑ₗ |Qₖₗ||Pₗₖ| ≤ ∑ₗ |Qₖₗ| absCumProdₗₖ = (X_abs)ₖₖ`.
    This is the componentwise `|Û⁻¹||Û| ≥ I` of Higham's middle factor, made
    exact by the construction. -/
theorem ch14ext_gjeXabs_diag_ge_one (n : ℕ) (N_hat : Fin n → Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ) (start steps : ℕ)
    (hidx : ∀ t : ℕ, t < steps → start + t < n)
    (hQP : matMul n Q (gje_cumulative_product n N_hat start (start + steps)) =
      idMatrix n)
    (k : Fin n) :
    1 ≤ ch14ext_gjeXabs n N_hat Q start steps k k := by
  have hQPkk : matMul n Q (gje_cumulative_product n N_hat start (start + steps)) k k
      = 1 := by rw [hQP]; simp [idMatrix]
  calc (1 : ℝ)
      = |matMul n Q (gje_cumulative_product n N_hat start (start + steps)) k k| := by
        rw [hQPkk]; norm_num
    _ = |∑ l : Fin n, Q k l *
          gje_cumulative_product n N_hat start (start + steps) l k| := rfl
    _ ≤ ∑ l : Fin n, |Q k l *
          gje_cumulative_product n N_hat start (start + steps) l k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l : Fin n, |Q k l| *
          |gje_cumulative_product n N_hat start (start + steps) l k| :=
        Finset.sum_congr rfl (fun l _ => abs_mul _ _)
    _ ≤ ∑ l : Fin n, |Q k l| *
          ch14ext_absCumProd n N_hat start steps l k :=
        Finset.sum_le_sum (fun l _ =>
          mul_le_mul_of_nonneg_left
            (ch14ext_cumProd_abs_dom n N_hat start steps hidx l k) (abs_nonneg _))
    _ = ch14ext_gjeXabs n N_hat Q start steps k k := by
        unfold ch14ext_gjeXabs absMatrix matMul; rfl

/-- **First-stage object absorbed into the second-stage object.**
    Because `X_abs ≥ I` on the diagonal, the GE first-stage object
    `S1 = |L̂||Û||x̂|` is dominated entrywise by the GJE second-stage object
    `S2 = |L̂||X_abs||Û||x̂|` (insert the `≥1` diagonal `X_abs` factor).  This is
    the step that lets the `γₙ` coefficient share `S2`'s object with the `c₃`
    coefficient, collapsing the printed constant onto a single object. -/
theorem ch14ext_residual_S1_le_S2 (n : ℕ)
    (L_hat V0 Xabs : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n)
    (hdiag : ∀ k : Fin n, 1 ≤ Xabs k k) :
    (∑ j : Fin n, (∑ k : Fin n, |L_hat i k| * |V0 k j|) * |x_hat j|) ≤
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n, |Xabs k₁ k₂| * |V0 k₂ j|)) * |x_hat j| := by
  apply Finset.sum_le_sum; intro j _
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply Finset.sum_le_sum; intro k₁ _
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have h1 : (1 : ℝ) ≤ |Xabs k₁ k₁| := le_trans (hdiag k₁) (le_abs_self _)
  calc |V0 k₁ j|
      ≤ |Xabs k₁ k₁| * |V0 k₁ j| := by nlinarith [abs_nonneg (V0 k₁ j)]
    _ ≤ ∑ k₂ : Fin n, |Xabs k₁ k₂| * |V0 k₂ j| :=
        Finset.single_le_sum (f := fun k₂ => |Xabs k₁ k₂| * |V0 k₂ j|)
          (fun k₂ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ k₁)

/-- **Conditional residual fold toward Theorem 14.5 (14.31).**

    Collapsing the GE first-stage object into the GJE second-stage object via
    `ch14ext_residual_S1_le_S2` (justified by the constructed `Q`'s `X_abs ≥ I`
    property), the residual is bounded by ONLY the `S2 = |L̂||X_abs||Û||x̂|` and
    `S3 = |L̂||X_abs||y|` objects, with the first carrying the combined
    coefficient `γₙ + c₃`:
        `|b − A x̂| ≤ (γₙ + c₃)·S2 + c₃·S3`.
    Feeding `ch14ext_gje_residual_coeff_budget` (§B1) reads an `8nu` leading
    constant off `S2` only after a separate `S3 ≤ S2` hypothesis is supplied.
    This theorem also uses the older exact-forward-solve input `L_hat y = b`;
    it is therefore an intermediate bound, not the complete source theorem. -/
theorem ch14ext_gjeConstructedQ_residual_folded
    (n : ℕ) (fp : FPModel)
    (A L_hat : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
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
      (gamma fp n + gje_c₃ fp n) * (∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
                (ch14ext_gjeConstructedQ n V start) start (n - 1) k₁ k₂| *
              |V start k₂ j|)) * |x_hat j|) +
      gje_c₃ fp n * (∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n,
          |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1) k j| *
            |xseq start j|)) := by
  intro i
  have hres := ch14ext_gjeConstructedQ_overall_residual n fp A L_hat b x_hat V xseq
    start hLU hn hnpos h3 hidx hVfinal hxfinal hy hVrec hxrec hpiv i
  have hdiag : ∀ k : Fin n,
      1 ≤ ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
        (ch14ext_gjeConstructedQ n V start) start (n - 1) k k :=
    fun k => ch14ext_gjeXabs_diag_ge_one n (ch14ext_gjeSeqStages n V)
      (ch14ext_gjeConstructedQ n V start) start (n - 1) hidx
      (ch14ext_gjeConstructedQ_isLeftInverse n V start hidx) k
  have hS12 := ch14ext_residual_S1_le_S2 n L_hat (V start)
    (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
      (ch14ext_gjeConstructedQ n V start) start (n - 1)) x_hat i hdiag
  have hmul := mul_le_mul_of_nonneg_left hS12 (gamma_nonneg fp hn)
  nlinarith [hres, hmul]

-- ══════════════════════════════════════════════════════════════════════
-- §B3  Folding the RHS object into the second-stage object;  the 8nu endpoint
-- ══════════════════════════════════════════════════════════════════════

/-- Reordering identity `|L̂||X_abs||Û||x̂| = |L̂||X_abs|(|Û||x̂|)`: the
    second-stage object `S2` equals the `|L̂||X_abs|` map applied to the
    substitution bound `|Û||x̂|` (contracting `Û`'s columns against `x̂`). -/
theorem ch14ext_LXVx_reorder (n : ℕ) (L X V0 : Fin n → Fin n → ℝ) (xh : Fin n → ℝ)
    (i : Fin n) :
    (∑ j : Fin n, (∑ k₁ : Fin n, |L i k₁| *
        (∑ k₂ : Fin n, |X k₁ k₂| * |V0 k₂ j|)) * |xh j|)
      = ∑ k : Fin n, |L i k| *
          (∑ j : Fin n, |X k j| * (∑ l : Fin n, |V0 j l| * |xh l|)) := by
  have e1 : ∀ j : Fin n,
      (∑ k₁ : Fin n, |L i k₁| * (∑ k₂ : Fin n, |X k₁ k₂| * |V0 k₂ j|)) * |xh j|
        = ∑ k₁ : Fin n, |L i k₁| *
            (∑ k₂ : Fin n, |X k₁ k₂| * (|V0 k₂ j| * |xh j|)) := by
    intro j
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k₁ _
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl; intro k₂ _; ring
  simp_rw [e1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k₁ _
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k₂ _
  rw [Finset.mul_sum]

/-- **Conditional fold of the RHS object `S3` into `S2`.**

    The input `hySharp : |y| ≤ |Û||x̂|` is stronger than the concrete rounded
    stage equation, which gives this comparison only with additional `O(u)`
    terms.  Thus this lemma is valid algebra once that extra inequality is
    available, but it does not discharge a source hypothesis of Theorem 14.5.
    Under it, `S3 = |L̂||X_abs||y| ≤ |L̂||X_abs||Û||x̂| = S2`. -/
theorem ch14ext_residual_S3_le_S2 (n : ℕ)
    (L V0 X : Fin n → Fin n → ℝ) (xh y : Fin n → ℝ) (i : Fin n)
    (hySharp : ∀ m : Fin n, |y m| ≤ ∑ l : Fin n, |V0 m l| * |xh l|) :
    (∑ k : Fin n, |L i k| * (∑ j : Fin n, |X k j| * |y j|)) ≤
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L i k₁| *
          (∑ k₂ : Fin n, |X k₁ k₂| * |V0 k₂ j|)) * |xh j| := by
  rw [ch14ext_LXVx_reorder n L X V0 xh i]
  apply Finset.sum_le_sum; intro k _
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Finset.sum_le_sum; intro j _
  exact mul_le_mul_of_nonneg_left (hySharp j) (abs_nonneg _)

/-- The second-stage object `S2` is nonnegative (a sum of products of `|·|`). -/
theorem ch14ext_S2_nonneg (n : ℕ)
    (L V0 X : Fin n → Fin n → ℝ) (xh : Fin n → ℝ) (i : Fin n) :
    0 ≤ ∑ j : Fin n,
      (∑ k₁ : Fin n, |L i k₁| *
        (∑ k₂ : Fin n, |X k₁ k₂| * |V0 k₂ j|)) * |xh j| := by
  apply Finset.sum_nonneg; intro j _
  apply mul_nonneg _ (abs_nonneg _)
  apply Finset.sum_nonneg; intro k₁ _
  apply mul_nonneg (abs_nonneg _)
  apply Finset.sum_nonneg; intro k₂ _
  exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Scalar folding arithmetic: absorb `c·s₃` into `c·s₂` (via `s₃ ≤ s₂`), merge
    with the `(g+c)·s₂` term, and cap the combined coefficient `g + 2c` by the
    leading budget `eight + rem` on the nonnegative object `s₂`. -/
theorem ch14ext_fold_arith {R g c s2 s3 eight rem : ℝ}
    (hR : R ≤ (g + c) * s2 + c * s3) (hs : s3 ≤ s2)
    (hc : 0 ≤ c) (hs2 : 0 ≤ s2) (hb : g + c + c ≤ eight + rem) :
    R ≤ eight * s2 + rem * s2 := by
  nlinarith [hR, hs, hc, hs2, hb, mul_le_mul_of_nonneg_left hs hc,
    mul_le_mul_of_nonneg_right hb hs2]

/-- **Conditional `8nu` residual wrapper related to (14.31).**

    Combining the folded residual (`ch14ext_gjeConstructedQ_residual_folded`,
    which uses the constructed `Q`'s `X_abs ≥ I` to absorb the GE first-stage
    object) with the `S3 → S2` fold (`ch14ext_residual_S3_le_S2`, under Higham's
    sharpness `|y| ≤ |Û||x̂|`) and the scalar coefficient budget (§B1), the GJE
    residual is bounded by the SINGLE second-stage object `S2 = |L̂||X_abs||Û||x̂|`
    (`X_abs = |Q|·(∏|N̂|)`, the exact form of Higham's `|Û||Û⁻¹|` middle factor)
    with leading constant `8nu`:
        `|b − A x̂| ≤ 8·n·u · S2 + ch14ext_residualRem · S2`,
    the remainder being `O(u²)`.  This is not an unconditional source closure:
    `hySharp` is an extra, stronger-than-rounded-stage hypothesis, the older
    residual route assumes `L̂y = b` exactly, and `X_abs` is only the exact
    envelope later identified to first order with `|Û||Û⁻¹|`. -/
theorem ch14ext_gjeConstructedQ_residual_8nu
    (n : ℕ) (fp : FPModel)
    (A L_hat : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * xseq start j = b i)
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
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      8 * (n : ℝ) * fp.u * (∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
                (ch14ext_gjeConstructedQ n V start) start (n - 1) k₁ k₂| *
              |V start k₂ j|)) * |x_hat j|) +
      ch14ext_residualRem fp n * (∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
                (ch14ext_gjeConstructedQ n V start) start (n - 1) k₁ k₂| *
              |V start k₂ j|)) * |x_hat j|) := by
  intro i
  have hfold := ch14ext_gjeConstructedQ_residual_folded n fp A L_hat b x_hat V xseq
    start hLU hn hnpos h3 hidx hVfinal hxfinal hy hVrec hxrec hpiv i
  have hS3 := ch14ext_residual_S3_le_S2 n L_hat (V start)
    (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
      (ch14ext_gjeConstructedQ n V start) start (n - 1)) x_hat (xseq start) i hySharp
  have hS2nn := ch14ext_S2_nonneg n L_hat (V start)
    (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
      (ch14ext_gjeConstructedQ n V start) start (n - 1)) x_hat i
  exact ch14ext_fold_arith hfold hS3 (gje_c3_nonneg fp n hnpos h3) hS2nn
    (ch14ext_gje_residual_coeff_budget fp n hn h3)

-- ══════════════════════════════════════════════════════════════════════
-- §B4  Forward error (14.32): transfer through |A⁻¹|; the 3-factor endpoint
-- ══════════════════════════════════════════════════════════════════════

/-- **Exact inverse transfer `|x − x̂| ≤ |A⁻¹||b − A x̂|`.**
    From `A⁻¹A = I` and `Ax = b`, any per-row residual bound `bnd` transfers to a
    forward-error bound `|x − x̂|ᵢ ≤ ∑ⱼ |A⁻¹ᵢⱼ| bndⱼ`.  This is the transfer step
    of `gje_overall_forward_error`, isolated for reuse with a folded residual. -/
theorem ch14ext_forward_transfer (n : ℕ) (A A_inv : Fin n → Fin n → ℝ)
    (b x x_hat : Fin n → ℝ) (bnd : Fin n → ℝ)
    (hAinv : IsLeftInverse n A A_inv)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hres : ∀ j : Fin n, |b j - ∑ k : Fin n, A j k * x_hat k| ≤ bnd j) :
    ∀ i : Fin n, |x i - x_hat i| ≤ ∑ j : Fin n, |A_inv i j| * bnd j := by
  intro i
  have hDiff : x i - x_hat i =
      ∑ j : Fin n, A_inv i j * (b j - ∑ k : Fin n, A j k * x_hat k) := by
    have hRHS_expand : ∑ j : Fin n, A_inv i j * (b j - ∑ k : Fin n, A j k * x_hat k) =
        ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x k) -
        ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x_hat k) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _
      rw [hExact j]; ring
    rw [hRHS_expand]
    have hFirst : ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x k) = x i := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hAinv i]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hSecond : ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x_hat k) = x_hat i := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hAinv i]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    linarith
  rw [hDiff]
  calc |∑ j : Fin n, A_inv i j * (b j - ∑ k : Fin n, A j k * x_hat k)|
      ≤ ∑ j : Fin n, |A_inv i j| * |b j - ∑ k : Fin n, A j k * x_hat k| := by
        calc _ ≤ ∑ j : Fin n, |A_inv i j * (b j - ∑ k : Fin n, A j k * x_hat k)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = _ := by apply Finset.sum_congr rfl; intro j _; exact abs_mul _ _
    _ ≤ ∑ j : Fin n, |A_inv i j| * bnd j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hres j) (abs_nonneg _))

/-- The row-`i` second-stage object `S2ᵢ = (|L̂||X_abs||Û||x̂|)ᵢ`. -/
noncomputable def ch14ext_gjeS2row (n : ℕ) (L_hat : Fin n → Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (start : ℕ) (i : Fin n) : ℝ :=
  ∑ j : Fin n,
    (∑ k₁ : Fin n, |L_hat i k₁| *
      (∑ k₂ : Fin n,
        |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
            (ch14ext_gjeConstructedQ n V start) start (n - 1) k₁ k₂| *
          |V start k₂ j|)) * |x_hat j|

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

-- ══════════════════════════════════════════════════════════════════════
-- §C  Source-facing Theorem 14.5 residual with the DeltaL terms retained
-- ══════════════════════════════════════════════════════════════════════

/-- The first-stage source object `S1 = |L| |U| |xhat|`. -/
noncomputable def ch14ext_gjeResidualS1 (n : ℕ)
    (L U : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n) : ℝ :=
  matMulVec n (absMatrix n L)
    (matMulVec n (absMatrix n U) (absVec n x_hat)) i

/-- The principal second-stage source object `S2 = |L| |X| |U| |xhat|`. -/
noncomputable def ch14ext_gjeResidualS2 (n : ℕ)
    (L X U : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n) : ℝ :=
  matMulVec n (absMatrix n L)
    (matMulVec n (absMatrix n X)
      (matMulVec n (absMatrix n U) (absVec n x_hat))) i

/-- The quadratic correction object `S22 = |L| |X|^2 |U| |xhat|`. -/
noncomputable def ch14ext_gjeResidualS22 (n : ℕ)
    (L X U : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n) : ℝ :=
  matMulVec n (absMatrix n L)
    (matMulVec n (absMatrix n X)
      (matMulVec n (absMatrix n X)
        (matMulVec n (absMatrix n U) (absVec n x_hat)))) i

/-- The quadratic RHS correction object `S23 = |L| |X|^2 |y|`. -/
noncomputable def ch14ext_gjeResidualS23 (n : ℕ)
    (L X : Fin n → Fin n → ℝ) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  matMulVec n (absMatrix n L)
    (matMulVec n (absMatrix n X)
      (matMulVec n (absMatrix n X) (absVec n y))) i

/-- An entrywise matrix bound propagates through a matrix-vector product. -/
theorem ch14ext_abs_matMulVec_le_scaled (n : ℕ)
    (M B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (c : ℝ)
    (hM : ∀ i j : Fin n, |M i j| ≤ c * B i j) (i : Fin n) :
    |matMulVec n M x i| ≤ c * matMulVec n B (absVec n x) i := by
  calc
    |matMulVec n M x i| ≤ ∑ j : Fin n, |M i j| * |x j| :=
      abs_matMulVec_le n M x i
    _ ≤ ∑ j : Fin n, (c * B i j) * |x j| := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hM i j) (abs_nonneg _)
    _ = c * matMulVec n B (absVec n x) i := by
      unfold matMulVec absVec
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)

/-- A componentwise vector bound propagates through an absolute matrix. -/
theorem ch14ext_abs_matMulVec_le_of_vec_bound (n : ℕ)
    (M : Fin n → Fin n → ℝ) (x w : Fin n → ℝ)
    (hx : ∀ j : Fin n, |x j| ≤ w j) (i : Fin n) :
    |matMulVec n M x i| ≤ matMulVec n (absMatrix n M) w i := by
  calc
    |matMulVec n M x i| ≤ ∑ j : Fin n, |M i j| * |x j| :=
      abs_matMulVec_le n M x i
    _ ≤ ∑ j : Fin n, |M i j| * w j := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
    _ = matMulVec n (absMatrix n M) w i := by
      rfl

/-- Matrix-vector multiplication by a nonnegative matrix is monotone. -/
theorem ch14ext_matMulVec_mono_nonneg (n : ℕ)
    (M : Fin n → Fin n → ℝ) (x y : Fin n → ℝ)
    (hM : ∀ i j : Fin n, 0 ≤ M i j) (hxy : ∀ j : Fin n, x j ≤ y j)
    (i : Fin n) :
    matMulVec n M x i ≤ matMulVec n M y i := by
  unfold matMulVec
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hxy j) (hM i j)

/-- Pull a nonnegative or signed scalar through a matrix-vector product. -/
theorem ch14ext_matMulVec_scale (n : ℕ)
    (M : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    matMulVec n M (fun j => c * x j) i = c * matMulVec n M x i := by
  unfold matMulVec
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- Linearity in the three-term shape used by the corrected `|y|` bound. -/
theorem ch14ext_matMulVec_add_scale_scale (n : ℕ)
    (M : Fin n → Fin n → ℝ) (x y z : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    matMulVec n M (fun j => x j + c * y j + c * z j) i =
      matMulVec n M x i + c * matMulVec n M y i + c * matMulVec n M z i := by
  unfold matMulVec
  have hy : (∑ j : Fin n, M i j * (c * y j)) =
      c * ∑ j : Fin n, M i j * y j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hz : (∑ j : Fin n, M i j * (c * z j)) =
      c * ∑ j : Fin n, M i j * z j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hy, hz]

/-- Absolute-matrix action preserves componentwise nonnegativity. -/
theorem ch14ext_absMatrix_action_nonneg (n : ℕ)
    (M : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : ∀ j : Fin n, 0 ≤ x j) (i : Fin n) :
    0 ≤ matMulVec n (absMatrix n M) x i := by
  unfold matMulVec absMatrix
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hx j))

/-- The concrete stage equation implies Higham's corrected comparison
    `|y| <= |U||xhat| + c|X||U||xhat| + c|X||y|`.

    Unlike the legacy `hySharp` input, both correction terms are retained and
    therefore become quadratic only after multiplication by the outer `c`. -/
theorem ch14ext_gje_y_abs_bound_from_stage (n : ℕ)
    (U X ΔU : Fin n → Fin n → ℝ) (y x_hat Δy : Fin n → ℝ) (c : ℝ)
    (hΔU : ∀ i j : Fin n, |ΔU i j| ≤ c *
      ∑ k : Fin n, |X i k| * |U k j|)
    (hΔy : ∀ i : Fin n, |Δy i| ≤ c *
      ∑ j : Fin n, |X i j| * |y j|)
    (hStage : ∀ i : Fin n,
      matMulVec n U x_hat i + matMulVec n ΔU x_hat i = y i + Δy i) :
    ∀ i : Fin n,
      |y i| ≤
        matMulVec n (absMatrix n U) (absVec n x_hat) i +
        c * matMulVec n (absMatrix n X)
          (matMulVec n (absMatrix n U) (absVec n x_hat)) i +
        c * matMulVec n (absMatrix n X) (absVec n y) i := by
  intro i
  have hΔU' : ∀ a b : Fin n, |ΔU a b| ≤
      c * matMul n (absMatrix n X) (absMatrix n U) a b := by
    intro a b
    simpa [matMul, absMatrix] using hΔU a b
  have hΔUact := ch14ext_abs_matMulVec_le_scaled n ΔU
    (matMul n (absMatrix n X) (absMatrix n U)) x_hat c hΔU' i
  rw [matMulVec_matMul] at hΔUact
  have hUact := abs_matMulVec_le n U x_hat i
  have hUact' : |matMulVec n U x_hat i| ≤
      matMulVec n (absMatrix n U) (absVec n x_hat) i := by
    simpa [matMulVec, absMatrix, absVec] using hUact
  have hΔy' : |Δy i| ≤
      c * matMulVec n (absMatrix n X) (absVec n y) i := by
    simpa [matMulVec, absMatrix, absVec] using hΔy i
  have hyEq : y i =
      matMulVec n U x_hat i + matMulVec n ΔU x_hat i - Δy i := by
    linarith [hStage i]
  rw [hyEq]
  calc
    |matMulVec n U x_hat i + matMulVec n ΔU x_hat i - Δy i| ≤
        |matMulVec n U x_hat i + matMulVec n ΔU x_hat i| + |Δy i| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add_le (matMulVec n U x_hat i + matMulVec n ΔU x_hat i) (-Δy i)
    _ ≤ |matMulVec n U x_hat i| + |matMulVec n ΔU x_hat i| + |Δy i| := by
      linarith [abs_add_le (matMulVec n U x_hat i) (matMulVec n ΔU x_hat i)]
    _ ≤ _ := by linarith [hUact']

/-- Applying `|L||X|` to the corrected `|y|` comparison gives
    `S3 <= S2 + c*S22 + c*S23`. -/
theorem ch14ext_gjeResidualS3_le_corrected (n : ℕ)
    (L X U : Fin n → Fin n → ℝ) (y x_hat : Fin n → ℝ) (c : ℝ) (i : Fin n)
    (hy : ∀ i : Fin n,
      |y i| ≤
        matMulVec n (absMatrix n U) (absVec n x_hat) i +
        c * matMulVec n (absMatrix n X)
          (matMulVec n (absMatrix n U) (absVec n x_hat)) i +
        c * matMulVec n (absMatrix n X) (absVec n y) i) :
    matMulVec n (absMatrix n L)
        (matMulVec n (absMatrix n X) (absVec n y)) i ≤
      ch14ext_gjeResidualS2 n L X U x_hat i +
        c * ch14ext_gjeResidualS22 n L X U x_hat i +
        c * ch14ext_gjeResidualS23 n L X y i := by
  let ux := matMulVec n (absMatrix n U) (absVec n x_hat)
  let xx := matMulVec n (absMatrix n X) ux
  let xy := matMulVec n (absMatrix n X) (absVec n y)
  have hX : ∀ k : Fin n,
      matMulVec n (absMatrix n X) (absVec n y) k ≤
        matMulVec n (absMatrix n X) ux k +
          c * matMulVec n (absMatrix n X) xx k +
          c * matMulVec n (absMatrix n X) xy k := by
    intro k
    calc
      matMulVec n (absMatrix n X) (absVec n y) k ≤
          matMulVec n (absMatrix n X)
            (fun j => ux j + c * xx j + c * xy j) k :=
        ch14ext_matMulVec_mono_nonneg n (absMatrix n X) (absVec n y)
          (fun j => ux j + c * xx j + c * xy j)
          (fun a b => abs_nonneg (X a b))
          (fun j => by simpa [ux, xx, xy, absVec] using hy j) k
      _ = _ := ch14ext_matMulVec_add_scale_scale n (absMatrix n X)
        ux xx xy c k
  calc
    matMulVec n (absMatrix n L)
        (matMulVec n (absMatrix n X) (absVec n y)) i ≤
      matMulVec n (absMatrix n L)
        (fun k => matMulVec n (absMatrix n X) ux k +
          c * matMulVec n (absMatrix n X) xx k +
          c * matMulVec n (absMatrix n X) xy k) i :=
      ch14ext_matMulVec_mono_nonneg n (absMatrix n L)
        (matMulVec n (absMatrix n X) (absVec n y))
        (fun k => matMulVec n (absMatrix n X) ux k +
          c * matMulVec n (absMatrix n X) xx k +
          c * matMulVec n (absMatrix n X) xy k)
        (fun a b => abs_nonneg (L a b)) hX i
    _ = _ := by
      rw [ch14ext_matMulVec_add_scale_scale]
      rfl

/-- Exact componentwise bound for the six terms of Higham (14.33), retaining
    both `DeltaL` terms and replacing `hySharp` by the concrete stage equation.

    The first-order part is `2*g*S1 + 2*c*S2`.  Everything else is explicitly
    quadratic: `2*g*c*S2 + c^2*(1+g)*(S22+S23)`. -/
theorem ch14ext_gjeResidual1433_bound_corrected (n : ℕ)
    (L U X ΔA₁ ΔL ΔU : Fin n → Fin n → ℝ)
    (y x_hat Δy : Fin n → ℝ) (g c : ℝ)
    (hg : 0 ≤ g) (hc : 0 ≤ c)
    (hΔA₁ : ∀ i j : Fin n, |ΔA₁ i j| ≤ g *
      ∑ k : Fin n, |L i k| * |U k j|)
    (hΔL : ∀ i j : Fin n, |ΔL i j| ≤ g * |L i j|)
    (hΔU : ∀ i j : Fin n, |ΔU i j| ≤ c *
      ∑ k : Fin n, |X i k| * |U k j|)
    (hΔy : ∀ i : Fin n, |Δy i| ≤ c *
      ∑ j : Fin n, |X i j| * |y j|)
    (hStage : ∀ i : Fin n,
      matMulVec n U x_hat i + matMulVec n ΔU x_hat i = y i + Δy i)
    (i : Fin n) :
    |ch14ext_gjeResidual1433 n L U ΔA₁ ΔL ΔU x_hat Δy i| ≤
      2 * g * ch14ext_gjeResidualS1 n L U x_hat i +
      2 * c * ch14ext_gjeResidualS2 n L X U x_hat i +
      2 * g * c * ch14ext_gjeResidualS2 n L X U x_hat i +
      c * c * (1 + g) *
        (ch14ext_gjeResidualS22 n L X U x_hat i +
          ch14ext_gjeResidualS23 n L X y i) := by
  let AL := absMatrix n L
  let AU := absMatrix n U
  let AX := absMatrix n X
  let ux := matMulVec n AU (absVec n x_hat)
  let xu := matMulVec n AX ux
  let xy := matMulVec n AX (absVec n y)
  have hΔA₁' : ∀ a b : Fin n, |ΔA₁ a b| ≤
      g * matMul n AL AU a b := by
    intro a b
    simpa [AL, AU, matMul, absMatrix] using hΔA₁ a b
  have hA := ch14ext_abs_matMulVec_le_scaled n ΔA₁
    (matMul n AL AU) x_hat g hΔA₁' i
  rw [matMulVec_matMul] at hA
  have hA' : |matMulVec n ΔA₁ x_hat i| ≤
      g * ch14ext_gjeResidualS1 n L U x_hat i := by
    simpa [ch14ext_gjeResidualS1, AL, AU] using hA
  have hΔL' : ∀ a b : Fin n, |ΔL a b| ≤ g * AL a b := by
    intro a b
    simpa [AL, absMatrix] using hΔL a b
  have hΔU' : ∀ a b : Fin n, |ΔU a b| ≤
      c * matMul n AX AU a b := by
    intro a b
    simpa [AX, AU, matMul, absMatrix] using hΔU a b
  have hΔUact : ∀ a : Fin n,
      |matMulVec n ΔU x_hat a| ≤ c * xu a := by
    intro a
    have h := ch14ext_abs_matMulVec_le_scaled n ΔU
      (matMul n AX AU) x_hat c hΔU' a
    rw [matMulVec_matMul] at h
    simpa [xu, ux, AX, AU] using h
  have hUx : ∀ a : Fin n, |matMulVec n U x_hat a| ≤ ux a := by
    intro a
    simpa [ux, AU, matMulVec, absMatrix, absVec] using
      abs_matMulVec_le n U x_hat a
  have hΔyact : ∀ a : Fin n, |Δy a| ≤ c * xy a := by
    intro a
    simpa [xy, AX, matMulVec, absMatrix, absVec] using hΔy a
  have hLΔU0 := ch14ext_abs_matMulVec_le_of_vec_bound n L
    (matMulVec n ΔU x_hat) (fun a => c * xu a) hΔUact i
  have hLΔU : |matMulVec n L (matMulVec n ΔU x_hat) i| ≤
      c * ch14ext_gjeResidualS2 n L X U x_hat i := by
    calc
      |matMulVec n L (matMulVec n ΔU x_hat) i| ≤
          matMulVec n AL (fun a => c * xu a) i := by
        simpa [AL] using hLΔU0
      _ = c * ch14ext_gjeResidualS2 n L X U x_hat i := by
        rw [ch14ext_matMulVec_scale]
        rfl
  have hΔLU0 := ch14ext_abs_matMulVec_le_scaled n ΔL AL
    (matMulVec n U x_hat) g hΔL' i
  have hALU := ch14ext_matMulVec_mono_nonneg n AL
    (absVec n (matMulVec n U x_hat)) ux
    (fun a b => by simp [AL, absMatrix])
    (fun a => by simpa [absVec] using hUx a) i
  have hΔLU : |matMulVec n ΔL (matMulVec n U x_hat) i| ≤
      g * ch14ext_gjeResidualS1 n L U x_hat i := by
    calc
      |matMulVec n ΔL (matMulVec n U x_hat) i| ≤
          g * matMulVec n AL (absVec n (matMulVec n U x_hat)) i := hΔLU0
      _ ≤ g * matMulVec n AL ux i :=
        mul_le_mul_of_nonneg_left hALU hg
      _ = g * ch14ext_gjeResidualS1 n L U x_hat i := rfl
  have hΔLΔU0 := ch14ext_abs_matMulVec_le_scaled n ΔL AL
    (matMulVec n ΔU x_hat) g hΔL' i
  have hALΔU := ch14ext_matMulVec_mono_nonneg n AL
    (absVec n (matMulVec n ΔU x_hat)) (fun a => c * xu a)
    (fun a b => by simp [AL, absMatrix])
    (fun a => by simpa [absVec] using hΔUact a) i
  have hΔLΔU : |matMulVec n ΔL (matMulVec n ΔU x_hat) i| ≤
      g * c * ch14ext_gjeResidualS2 n L X U x_hat i := by
    calc
      |matMulVec n ΔL (matMulVec n ΔU x_hat) i| ≤
          g * matMulVec n AL (absVec n (matMulVec n ΔU x_hat)) i := hΔLΔU0
      _ ≤ g * matMulVec n AL (fun a => c * xu a) i :=
        mul_le_mul_of_nonneg_left hALΔU hg
      _ = g * c * ch14ext_gjeResidualS2 n L X U x_hat i := by
        rw [ch14ext_matMulVec_scale]
        change g * (c * ch14ext_gjeResidualS2 n L X U x_hat i) = _
        ring
  have hLΔy0 := ch14ext_abs_matMulVec_le_of_vec_bound n L Δy
    (fun a => c * xy a) hΔyact i
  have hLΔy : |matMulVec n L Δy i| ≤
      c * matMulVec n AL xy i := by
    calc
      |matMulVec n L Δy i| ≤ matMulVec n AL (fun a => c * xy a) i := by
        simpa [AL] using hLΔy0
      _ = c * matMulVec n AL xy i := ch14ext_matMulVec_scale n AL xy c i
  have hΔLΔy0 := ch14ext_abs_matMulVec_le_scaled n ΔL AL Δy g hΔL' i
  have hALΔy := ch14ext_matMulVec_mono_nonneg n AL (absVec n Δy)
    (fun a => c * xy a) (fun a b => by simp [AL, absMatrix])
    (fun a => by simpa [absVec] using hΔyact a) i
  have hΔLΔy : |matMulVec n ΔL Δy i| ≤
      g * c * matMulVec n AL xy i := by
    calc
      |matMulVec n ΔL Δy i| ≤ g * matMulVec n AL (absVec n Δy) i := hΔLΔy0
      _ ≤ g * matMulVec n AL (fun a => c * xy a) i :=
        mul_le_mul_of_nonneg_left hALΔy hg
      _ = g * c * matMulVec n AL xy i := by
        rw [ch14ext_matMulVec_scale]
        ring
  have hyBound := ch14ext_gje_y_abs_bound_from_stage n U X ΔU y x_hat Δy c
    hΔU hΔy hStage
  have hS3 := ch14ext_gjeResidualS3_le_corrected n L X U y x_hat c i hyBound
  let a := matMulVec n ΔA₁ x_hat i
  let b := matMulVec n L (matMulVec n ΔU x_hat) i
  let d := matMulVec n ΔL (matMulVec n U x_hat) i
  let e := matMulVec n ΔL (matMulVec n ΔU x_hat) i
  let f := matMulVec n L Δy i
  let q := matMulVec n ΔL Δy i
  have htri : |a + b + d + e - (f + q)| ≤
      |a| + |b| + |d| + |e| + |f| + |q| := by
    have h1 := abs_add_le a b
    have h2 := abs_add_le (a + b) d
    have h3 := abs_add_le (a + b + d) e
    have h4 := abs_add_le f q
    have h5 : |a + b + d + e - (f + q)| ≤ |a + b + d + e| + |f + q| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (a + b + d + e) (-(f + q))
    linarith
  unfold ch14ext_gjeResidual1433
  change |a + b + d + e - (f + q)| ≤ _
  have hraw : |a + b + d + e - (f + q)| ≤
      2 * g * ch14ext_gjeResidualS1 n L U x_hat i +
        c * (1 + g) * ch14ext_gjeResidualS2 n L X U x_hat i +
        c * (1 + g) * matMulVec n AL xy i := by
    dsimp [a, b, d, e, f, q] at htri
    nlinarith [htri, hA', hLΔU, hΔLU, hΔLΔU, hLΔy, hΔLΔy]
  have hcoef : 0 ≤ c * (1 + g) := mul_nonneg hc (by linarith)
  have hS3mul := mul_le_mul_of_nonneg_left hS3 hcoef
  calc
    |a + b + d + e - (f + q)| ≤
        2 * g * ch14ext_gjeResidualS1 n L U x_hat i +
          c * (1 + g) * ch14ext_gjeResidualS2 n L X U x_hat i +
          c * (1 + g) * matMulVec n AL xy i := hraw
    _ ≤ 2 * g * ch14ext_gjeResidualS1 n L U x_hat i +
          c * (1 + g) * ch14ext_gjeResidualS2 n L X U x_hat i +
          c * (1 + g) *
            (ch14ext_gjeResidualS2 n L X U x_hat i +
              c * ch14ext_gjeResidualS22 n L X U x_hat i +
              c * ch14ext_gjeResidualS23 n L X y i) := by
      linarith
    _ = _ := by ring

/-- The explicit higher-order part of the `c3` split is nonnegative. -/
theorem ch14ext_gjeC3Rem_nonneg (fp : FPModel) (n : ℕ)
    (hnpos : 1 ≤ n) (h3 : gammaValid fp 3) :
    0 ≤ gje_c3_quadratic_remainder fp n := by
  have hncast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  have hden : 0 < 1 - (3 : ℝ) * fp.u := by
    unfold gammaValid at h3
    norm_num at h3 ⊢
    linarith
  have hg3 : 0 ≤ gamma fp 3 := gamma_nonneg fp h3
  have hpow : 1 ≤ (1 + gamma fp 3) ^ (n - 2) :=
    one_le_pow₀ (by linarith)
  unfold gje_c3_quadratic_remainder
  apply mul_nonneg (by linarith)
  apply add_nonneg
  · exact mul_nonneg
      (div_nonneg (sq_nonneg _) (le_of_lt hden)) (pow_nonneg (by linarith) _)
  · exact mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg) (by linarith)

/-- With both `DeltaL` contributions retained, the first-order coefficient is
    `2*gamma_n + 2*c3`, bounded by the printed `8*n*u` plus explicit scalar
    remainders. -/
theorem ch14ext_gje_residual_coeff_budget_corrected (fp : FPModel) (n : ℕ)
    (hn : gammaValid fp n) (h3 : gammaValid fp 3) :
    2 * gamma fp n + 2 * gje_c₃ fp n ≤
      8 * (n : ℝ) * fp.u +
        2 * ch14ext_gammaRem fp n + 2 * gje_c3_quadratic_remainder fp n := by
  have hg := ch14ext_gamma_split fp n hn
  have hc := gje_c3_le_three_n_u_plus_quadratic_remainder fp n h3
  nlinarith

theorem ch14ext_gjeResidualS1_nonneg (n : ℕ)
    (L U : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n) :
    0 ≤ ch14ext_gjeResidualS1 n L U x_hat i := by
  unfold ch14ext_gjeResidualS1
  apply ch14ext_absMatrix_action_nonneg
  intro k
  apply ch14ext_absMatrix_action_nonneg
  intro j
  exact abs_nonneg _

theorem ch14ext_gjeResidualS2_nonneg (n : ℕ)
    (L X U : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n) :
    0 ≤ ch14ext_gjeResidualS2 n L X U x_hat i := by
  unfold ch14ext_gjeResidualS2
  apply ch14ext_absMatrix_action_nonneg
  intro k
  apply ch14ext_absMatrix_action_nonneg
  intro l
  apply ch14ext_absMatrix_action_nonneg
  intro j
  exact abs_nonneg _

theorem ch14ext_gjeResidualS22_nonneg (n : ℕ)
    (L X U : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n) :
    0 ≤ ch14ext_gjeResidualS22 n L X U x_hat i := by
  unfold ch14ext_gjeResidualS22
  apply ch14ext_absMatrix_action_nonneg
  intro k
  apply ch14ext_absMatrix_action_nonneg
  intro l
  apply ch14ext_absMatrix_action_nonneg
  intro m
  apply ch14ext_absMatrix_action_nonneg
  intro j
  exact abs_nonneg _

theorem ch14ext_gjeResidualS23_nonneg (n : ℕ)
    (L X : Fin n → Fin n → ℝ) (y : Fin n → ℝ) (i : Fin n) :
    0 ≤ ch14ext_gjeResidualS23 n L X y i := by
  unfold ch14ext_gjeResidualS23
  apply ch14ext_absMatrix_action_nonneg
  intro k
  apply ch14ext_absMatrix_action_nonneg
  intro l
  apply ch14ext_absMatrix_action_nonneg
  intro j
  exact abs_nonneg _

/-- The exact inverse-product construction gives `S1 <= S2`, with no
    condition-number or endpoint hypothesis. -/
theorem ch14ext_gjeResidualS1_le_S2 (n : ℕ)
    (L X U : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n)
    (hdiag : ∀ k : Fin n, 1 ≤ X k k) :
    ch14ext_gjeResidualS1 n L U x_hat i ≤
      ch14ext_gjeResidualS2 n L X U x_hat i := by
  let ux := matMulVec n (absMatrix n U) (absVec n x_hat)
  have hux : ∀ k : Fin n, 0 ≤ ux k := by
    intro k
    exact ch14ext_absMatrix_action_nonneg n U (absVec n x_hat)
      (fun j => abs_nonneg _) k
  have hinner : ∀ k : Fin n, ux k ≤
      matMulVec n (absMatrix n X) ux k := by
    intro k
    have hdiagAbs : 1 ≤ |X k k| := le_trans (hdiag k) (le_abs_self _)
    calc
      ux k ≤ |X k k| * ux k := by nlinarith [hux k]
      _ ≤ ∑ l : Fin n, |X k l| * ux l :=
        Finset.single_le_sum
          (fun l _ => mul_nonneg (abs_nonneg _) (hux l)) (Finset.mem_univ k)
      _ = matMulVec n (absMatrix n X) ux k := rfl
  exact ch14ext_matMulVec_mono_nonneg n (absMatrix n L) ux
    (matMulVec n (absMatrix n X) ux) (fun a b => abs_nonneg _) hinner i

/-- Explicit `O(u^2)` remainder in the source-facing residual theorem. -/
noncomputable def ch14ext_gjeResidualHigherOrder (n : ℕ) (fp : FPModel)
    (L X U : Fin n → Fin n → ℝ) (y x_hat : Fin n → ℝ) (i : Fin n) : ℝ :=
  (2 * ch14ext_gammaRem fp n + 2 * gje_c3_quadratic_remainder fp n +
      2 * gamma fp n * gje_c₃ fp n) *
      ch14ext_gjeResidualS2 n L X U x_hat i +
    gje_c₃ fp n * gje_c₃ fp n * (1 + gamma fp n) *
      (ch14ext_gjeResidualS22 n L X U x_hat i +
        ch14ext_gjeResidualS23 n L X y i)

theorem ch14ext_gjeResidualHigherOrder_nonneg (n : ℕ) (fp : FPModel)
    (L X U : Fin n → Fin n → ℝ) (y x_hat : Fin n → ℝ) (i : Fin n)
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3) :
    0 ≤ ch14ext_gjeResidualHigherOrder n fp L X U y x_hat i := by
  have hg : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hc : 0 ≤ gje_c₃ fp n := gje_c3_nonneg fp n hnpos h3
  have hgr : 0 ≤ ch14ext_gammaRem fp n := ch14ext_gammaRem_nonneg fp n hn
  have hcr : 0 ≤ gje_c3_quadratic_remainder fp n :=
    ch14ext_gjeC3Rem_nonneg fp n hnpos h3
  have hs2 := ch14ext_gjeResidualS2_nonneg n L X U x_hat i
  have hs22 := ch14ext_gjeResidualS22_nonneg n L X U x_hat i
  have hs23 := ch14ext_gjeResidualS23_nonneg n L X y i
  unfold ch14ext_gjeResidualHigherOrder
  positivity

/-- **Higham Theorem 14.5, equation (14.31), concrete source-facing form.**

    The LU residual, forward-substitution `DeltaL`, and rounded GJE
    `DeltaU,Deltay` witnesses are all constructed from their algorithms.  The
    exact (14.33) identity is bounded with the corrected stage consequence
    `|y| <= |U||xhat| + c3|X||U||xhat| + c3|X||y|`; hence no `hySharp` or
    final-residual hypothesis is present.  The displayed first-order term is
    exactly `8*n*u*S2`, and every correction is retained in the explicit
    nonnegative `ch14ext_gjeResidualHigherOrder`. -/
theorem ch14ext_gjeConcrete_overall_residual_14_31
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
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    ∀ i : Fin n,
      |b i - matMulVec n A x_hat i| ≤
        8 * (n : ℝ) * fp.u *
          ch14ext_gjeResidualS2 n L_hat
            (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1))
            (V start) x_hat i +
        ch14ext_gjeResidualHigherOrder n fp L_hat
          (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
            (ch14ext_gjeConstructedQ n V start) start (n - 1))
          (V start) (xseq start) x_hat i := by
  intro i
  let X := ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
    (ch14ext_gjeConstructedQ n V start) start (n - 1)
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
  obtain ⟨ΔU, Δy, hStageRaw, hΔUraw, hΔyraw⟩ :=
    ch14ext_gjeConcrete_stage2_backward_error n fp x_hat V xseq start hnpos h3
      hidx hVfinal hxfinal hVrec hxrec hpiv
  have hStage : ∀ a : Fin n,
      matMulVec n (V start) x_hat a + matMulVec n ΔU x_hat a =
        xseq start a + Δy a := by
    intro a
    have h := hStageRaw a
    simpa [matMulVec, Finset.sum_add_distrib, add_mul] using h
  have hΔU : ∀ a j : Fin n, |ΔU a j| ≤ gje_c₃ fp n *
      ∑ k : Fin n, |X a k| * |V start k j| := by
    intro a j
    simpa [X] using hΔUraw a j
  have hΔy : ∀ a : Fin n, |Δy a| ≤ gje_c₃ fp n *
      ∑ j : Fin n, |X a j| * |xseq start j| := by
    intro a
    simpa [X] using hΔyraw a
  have hResidual := ch14ext_gje_residual_decomposition_14_33 n A L_hat (V start)
    ΔA₁ ΔL ΔU b (xseq start) x_hat Δy hFactor hForward hStage
  have hR := ch14ext_gjeResidual1433_bound_corrected n L_hat (V start) X
    ΔA₁ ΔL ΔU (xseq start) x_hat Δy (gamma fp n) (gje_c₃ fp n)
    (gamma_nonneg fp hn) (gje_c3_nonneg fp n hnpos h3)
    hΔA₁ hΔL hΔU hΔy hStage i
  have hdiag : ∀ k : Fin n, 1 ≤ X k k := by
    intro k
    simpa [X] using ch14ext_gjeXabs_diag_ge_one n (ch14ext_gjeSeqStages n V)
      (ch14ext_gjeConstructedQ n V start) start (n - 1) hidx
      (ch14ext_gjeConstructedQ_isLeftInverse n V start hidx) k
  have hS12 := ch14ext_gjeResidualS1_le_S2 n L_hat X (V start) x_hat i hdiag
  have hS2nn := ch14ext_gjeResidualS2_nonneg n L_hat X (V start) x_hat i
  have hAbsorb :
      2 * gamma fp n * ch14ext_gjeResidualS1 n L_hat (V start) x_hat i ≤
        2 * gamma fp n * ch14ext_gjeResidualS2 n L_hat X (V start) x_hat i :=
    mul_le_mul_of_nonneg_left hS12
      (mul_nonneg (by norm_num) (gamma_nonneg fp hn))
  have hCoeff := ch14ext_gje_residual_coeff_budget_corrected fp n hn h3
  have hCoeffS2 := mul_le_mul_of_nonneg_right hCoeff hS2nn
  have hresEq : b i - matMulVec n A x_hat i =
      ch14ext_gjeResidual1433 n L_hat (V start) ΔA₁ ΔL ΔU x_hat Δy i := by
    linarith [hResidual i]
  rw [hresEq]
  have hFinal :
      |ch14ext_gjeResidual1433 n L_hat (V start) ΔA₁ ΔL ΔU x_hat Δy i| ≤
        8 * (n : ℝ) * fp.u * ch14ext_gjeResidualS2 n L_hat X (V start) x_hat i +
        ch14ext_gjeResidualHigherOrder n fp L_hat X (V start)
          (xseq start) x_hat i := by
    unfold ch14ext_gjeResidualHigherOrder
    nlinarith [hR, hAbsorb, hCoeffS2]
  simpa [X] using hFinal

-- ══════════════════════════════════════════════════════════════════════
-- §D  Theorem 14.5 forward split: exact two first-order objects
-- ══════════════════════════════════════════════════════════════════════

/-- First forward object `T1 = |A^{-1}| |L| |U| |xhat|`. -/
noncomputable def ch14ext_gjeForwardT1 (n : ℕ)
    (A_inv L U : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n) : ℝ :=
  matMulVec n (absMatrix n A_inv)
    (matMulVec n (absMatrix n L)
      (matMulVec n (absMatrix n U) (absVec n x_hat))) i

/-- Second forward object `T2 = |X| |U| |xhat|`; for the concrete recurrence,
    `X` is the product of the absolute GJE stage matrices. -/
noncomputable def ch14ext_gjeForwardT2 (n : ℕ)
    (X U : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n) : ℝ :=
  matMulVec n X (matMulVec n (absMatrix n U) (absVec n x_hat)) i

/-- The explicit first-order correction in
    `X ≤ |U⁻¹| + c₃ X |U| |U⁻¹|`, applied to the (14.32) vector
    `|U||xhat|`.  Its coefficient in the final theorem is `6*n*u*c₃`, hence
    genuinely second order in `u`. -/
noncomputable def ch14ext_gjeForwardUinvCorrection (n : ℕ)
    (X U U_inv : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n) : ℝ :=
  matMulVec n X
    (matMulVec n (absMatrix n U)
      (matMulVec n (absMatrix n U_inv)
        (matMulVec n (absMatrix n U) (absVec n x_hat)))) i

/-- Applying the exact inverse comparison to the second (14.32) object replaces
    the stage envelope by the printed `|U⁻¹|` plus the explicit correction. -/
theorem ch14ext_gjeForwardT2_le_printed_add_correction (n : ℕ)
    (X U U_inv : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (c : ℝ)
    (hCompare : ∀ a j : Fin n,
      X a j ≤ |U_inv a j| +
        c * matMul n (matMul n X (absMatrix n U))
          (absMatrix n U_inv) a j) (i : Fin n) :
    ch14ext_gjeForwardT2 n X U x_hat i ≤
      ch14ext_gjeForwardT2 n (absMatrix n U_inv) U x_hat i +
        c * ch14ext_gjeForwardUinvCorrection n X U U_inv x_hat i := by
  let w := matMulVec n (absMatrix n U) (absVec n x_hat)
  let D := matMul n (matMul n X (absMatrix n U)) (absMatrix n U_inv)
  have hw : ∀ j : Fin n, 0 ≤ w j := by
    intro j
    unfold w matMulVec absMatrix absVec
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsum : matMulVec n X w i ≤
      matMulVec n (fun a j => |U_inv a j| + c * D a j) w i := by
    unfold matMulVec
    apply Finset.sum_le_sum
    intro j _hj
    apply mul_le_mul_of_nonneg_right
    · simpa [D] using hCompare i j
    · exact hw j
  have hExpand :
      matMulVec n (fun a j => |U_inv a j| + c * D a j) w i =
        matMulVec n (absMatrix n U_inv) w i + c * matMulVec n D w i := by
    unfold matMulVec absMatrix
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hDaction : matMulVec n D w i =
      ch14ext_gjeForwardUinvCorrection n X U U_inv x_hat i := by
    unfold D w ch14ext_gjeForwardUinvCorrection
    rw [matMulVec_matMul, matMulVec_matMul]
  unfold ch14ext_gjeForwardT2
  change matMulVec n X w i ≤
    matMulVec n (absMatrix n U_inv) w i +
      c * ch14ext_gjeForwardUinvCorrection n X U U_inv x_hat i
  rw [hDaction] at hExpand
  linarith [hsum, hExpand]

/-- The inverse-comparison correction is entrywise nonnegative. -/
theorem ch14ext_gjeForwardUinvCorrection_nonneg (n : ℕ)
    (X U U_inv : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n)
    (hX : ∀ a j : Fin n, 0 ≤ X a j) :
    0 ≤ ch14ext_gjeForwardUinvCorrection n X U U_inv x_hat i := by
  have h0 : ∀ a : Fin n,
      0 ≤ matMulVec n (absMatrix n U) (absVec n x_hat) a := by
    intro a
    unfold matMulVec absMatrix absVec
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have h1 : ∀ a : Fin n,
      0 ≤ matMulVec n (absMatrix n U_inv)
        (matMulVec n (absMatrix n U) (absVec n x_hat)) a := by
    intro a
    unfold matMulVec absMatrix
    exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (h0 j)
  have h2 : ∀ a : Fin n,
      0 ≤ matMulVec n (absMatrix n U)
        (matMulVec n (absMatrix n U_inv)
          (matMulVec n (absMatrix n U) (absVec n x_hat))) a := by
    intro a
    unfold matMulVec absMatrix
    exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (h1 j)
  unfold ch14ext_gjeForwardUinvCorrection matMulVec
  exact Finset.sum_nonneg fun a _ => mul_nonneg (hX i a) (h2 a)

/-- The exact right side of (14.29), parameterized by its nonnegative stage
    product: `F = |X|(|U||z|+|y|)`. -/
noncomputable def ch14ext_gjeForwardRaw (n : ℕ)
    (X U : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) (i : Fin n) : ℝ :=
  matMulVec n X (matMulVec n (absMatrix n U) (absVec n z)) i +
    matMulVec n X (absVec n y) i

/-- First-stage quadratic correction map applied to the raw (14.29) envelope. -/
noncomputable def ch14ext_gjeForwardQ1 (n : ℕ)
    (A_inv L U X : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) (i : Fin n) : ℝ :=
  matMulVec n (absMatrix n A_inv)
    (matMulVec n (absMatrix n L)
      (matMulVec n (absMatrix n U)
        (fun j => ch14ext_gjeForwardRaw n X U z y j))) i

/-- Second-stage self-substitution correction
    `Q2 = |X||U| (|X|(|U||z|+|y|))`. -/
noncomputable def ch14ext_gjeForwardQ2 (n : ℕ)
    (X U : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) (i : Fin n) : ℝ :=
  matMulVec n X
    (matMulVec n (absMatrix n U)
      (fun j => ch14ext_gjeForwardRaw n X U z y j)) i

/-- Self-substitution form of (14.29).  If `Uz=y` and the concrete stage error
    is bounded by `c*F`, then
    `|z-xhat| <= 2c*T2 + 2c^2*Q2`.

    The first term is the exact source object used for the printed `6nu`
    contribution; the second is manifestly quadratic. -/
theorem ch14ext_gje_stage2_forward_split (n : ℕ)
    (U X : Fin n → Fin n → ℝ) (z y x_hat : Fin n → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hX : ∀ i j : Fin n, 0 ≤ X i j)
    (hUz : ∀ i : Fin n, matMulVec n U z i = y i)
    (hErr : ∀ i : Fin n, |z i - x_hat i| ≤
      c * ch14ext_gjeForwardRaw n X U z y i) :
    ∀ i : Fin n, |z i - x_hat i| ≤
      2 * c * ch14ext_gjeForwardT2 n X U x_hat i +
        2 * c * c * ch14ext_gjeForwardQ2 n X U z y i := by
  intro i
  let AU := absMatrix n U
  let e : Fin n → ℝ := fun j => |z j - x_hat j|
  let uz := matMulVec n AU (absVec n z)
  let ux := matMulVec n AU (absVec n x_hat)
  let ue := matMulVec n AU e
  let F : Fin n → ℝ := fun j => ch14ext_gjeForwardRaw n X U z y j
  have hy : ∀ j : Fin n, |y j| ≤ uz j := by
    intro j
    rw [← hUz j]
    simpa [uz, AU, matMulVec, absMatrix, absVec] using abs_matMulVec_le n U z j
  have hPy : matMulVec n X (absVec n y) i ≤ matMulVec n X uz i :=
    ch14ext_matMulVec_mono_nonneg n X (absVec n y) uz hX
      (fun j => by simpa [absVec] using hy j) i
  have hF : F i ≤ 2 * matMulVec n X uz i := by
    unfold F ch14ext_gjeForwardRaw
    nlinarith
  have hz : ∀ j : Fin n, |z j| ≤ |x_hat j| + e j := by
    intro j
    have h := abs_add_le (x_hat j) (z j - x_hat j)
    have heq : z j = x_hat j + (z j - x_hat j) := by ring
    rw [heq]
    simpa [e] using h
  have hUzX : ∀ j : Fin n, uz j ≤ ux j + ue j := by
    intro j
    have hU := ch14ext_matMulVec_mono_nonneg n AU (absVec n z)
      (fun j => |x_hat j| + e j) (fun a b => by simp [AU, absMatrix])
      (fun k => by simpa [absVec] using hz k) j
    have hadd : matMulVec n AU (fun k => |x_hat k| + e k) j = ux j + ue j := by
      simpa [ux, ue, absVec] using
        congrFun (matMulVec_add_right n AU (absVec n x_hat) e) j
    rw [hadd] at hU
    exact hU
  have hPUz : matMulVec n X uz i ≤
      ch14ext_gjeForwardT2 n X U x_hat i + matMulVec n X ue i := by
    have h := ch14ext_matMulVec_mono_nonneg n X uz (fun j => ux j + ue j)
      hX hUzX i
    have hadd : matMulVec n X (fun j => ux j + ue j) i =
        matMulVec n X ux i + matMulVec n X ue i := by
      simpa using congrFun (matMulVec_add_right n X ux ue) i
    rw [hadd] at h
    simpa [ch14ext_gjeForwardT2, ux, AU] using h
  have heF : ∀ j : Fin n, e j ≤ c * F j := by
    intro j
    simpa [e, F] using hErr j
  have hUe : ∀ j : Fin n, ue j ≤ c * matMulVec n AU F j := by
    intro j
    have h := ch14ext_matMulVec_mono_nonneg n AU e (fun j => c * F j)
      (fun a b => by simp [AU, absMatrix]) heF j
    rw [ch14ext_matMulVec_scale] at h
    simpa [ue] using h
  have hPUe0 := ch14ext_matMulVec_mono_nonneg n X ue
    (fun j => c * matMulVec n AU F j) hX hUe i
  have hPUe : matMulVec n X ue i ≤
      c * ch14ext_gjeForwardQ2 n X U z y i := by
    rw [ch14ext_matMulVec_scale] at hPUe0
    simpa [ch14ext_gjeForwardQ2, F, AU] using hPUe0
  have hFc : c * F i ≤ c * (2 * matMulVec n X uz i) :=
    mul_le_mul_of_nonneg_left hF hc
  have hPUzc : 2 * c * matMulVec n X uz i ≤
      2 * c * (ch14ext_gjeForwardT2 n X U x_hat i + matMulVec n X ue i) :=
    mul_le_mul_of_nonneg_left hPUz
      (mul_nonneg (by norm_num) hc)
  have hPUec : 2 * c * matMulVec n X ue i ≤
      2 * c * (c * ch14ext_gjeForwardQ2 n X U z y i) :=
    mul_le_mul_of_nonneg_left hPUe
      (mul_nonneg (by norm_num) hc)
  have hEi := hErr i
  change e i ≤ _
  change e i ≤ c * F i at hEi
  nlinarith

/-- Combined first two terms of Higham's forward split, derived without an
    `x0` certificate.  The exact identity is
    `A(x-z) = DeltaA1*z + DeltaL*y`, obtained from the factorization,
    forward-substitution, exact-system, and `Uz=y` equations.

    Replacing `|z|` by `|xhat|+|z-xhat|` and using the raw (14.29) bound only
    in the correction gives
    `|x-z| <= 2g*T1 + 2gc*Q1`. -/
theorem ch14ext_gje_first_stage_forward_split (n : ℕ)
    (A A_inv L U ΔA₁ ΔL : Fin n → Fin n → ℝ)
    (b x z y x_hat : Fin n → ℝ) (g c : ℝ)
    (hg : 0 ≤ g)
    (hAinv : IsLeftInverse n A A_inv)
    (hExact : ∀ i : Fin n, matMulVec n A x i = b i)
    (hFactor : ∀ i j : Fin n, A i j + ΔA₁ i j = matMul n L U i j)
    (hForward : ∀ i : Fin n,
      matMulVec n L y i + matMulVec n ΔL y i = b i)
    (hUz : ∀ i : Fin n, matMulVec n U z i = y i)
    (hΔA₁ : ∀ i j : Fin n, |ΔA₁ i j| ≤ g *
      ∑ k : Fin n, |L i k| * |U k j|)
    (hΔL : ∀ i j : Fin n, |ΔL i j| ≤ g * |L i j|)
    (X : Fin n → Fin n → ℝ)
    (hErr : ∀ i : Fin n, |z i - x_hat i| ≤
      c * ch14ext_gjeForwardRaw n X U z y i) :
    ∀ i : Fin n, |x i - z i| ≤
      2 * g * ch14ext_gjeForwardT1 n A_inv L U x_hat i +
        2 * g * c * ch14ext_gjeForwardQ1 n A_inv L U X z y i := by
  intro i
  let AA := absMatrix n A_inv
  let AL := absMatrix n L
  let AU := absMatrix n U
  let e : Fin n → ℝ := fun j => |z j - x_hat j|
  let F : Fin n → ℝ := fun j => ch14ext_gjeForwardRaw n X U z y j
  let uz := matMulVec n AU (absVec n z)
  let luz := matMulVec n AL uz
  let r : Fin n → ℝ := fun j =>
    matMulVec n ΔA₁ z j + matMulVec n ΔL y j
  have hFactorZ : ∀ a : Fin n,
      matMulVec n A z a + matMulVec n ΔA₁ z a =
        matMulVec n L (matMulVec n U z) a := by
    intro a
    calc
      matMulVec n A z a + matMulVec n ΔA₁ z a =
          ∑ j : Fin n, (A a j + ΔA₁ a j) * z j := by
        unfold matMulVec
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = matMulVec n (matMul n L U) z a := by
        unfold matMulVec
        exact Finset.sum_congr rfl (fun j _ => by rw [hFactor a j])
      _ = matMulVec n L (matMulVec n U z) a := by rw [matMulVec_matMul]
  have hAdiff : ∀ a : Fin n,
      matMulVec n A (fun j => x j - z j) a = r a := by
    intro a
    have hlin : matMulVec n A (fun j => x j - z j) a =
        matMulVec n A x a - matMulVec n A z a := by
      unfold matMulVec
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hUzFn : matMulVec n U z = y := by
      funext j
      exact hUz j
    have hLUzy : matMulVec n L (matMulVec n U z) a = matMulVec n L y a := by
      rw [hUzFn]
    unfold r
    rw [hlin]
    linarith [hExact a, hFactorZ a, hLUzy, hForward a]
  have hAinvMat : matMul n A_inv A = idMatrix n := by
    funext a j
    exact hAinv a j
  have hAdiffFn : matMulVec n A (fun j => x j - z j) = r := by
    funext a
    exact hAdiff a
  have hDiff : x i - z i = matMulVec n A_inv r i := by
    have hleft : matMulVec n A_inv
        (matMulVec n A (fun j => x j - z j)) i = x i - z i := by
      rw [← matMulVec_matMul, hAinvMat, matMulVec_id]
    calc
      x i - z i = matMulVec n A_inv
          (matMulVec n A (fun j => x j - z j)) i := hleft.symm
      _ = matMulVec n A_inv r i := by rw [hAdiffFn]
  have hΔA₁' : ∀ a j : Fin n, |ΔA₁ a j| ≤
      g * matMul n AL AU a j := by
    intro a j
    simpa [AL, AU, matMul, absMatrix] using hΔA₁ a j
  have hΔAz : ∀ a : Fin n, |matMulVec n ΔA₁ z a| ≤ g * luz a := by
    intro a
    have h := ch14ext_abs_matMulVec_le_scaled n ΔA₁ (matMul n AL AU)
      z g hΔA₁' a
    rw [matMulVec_matMul] at h
    simpa [luz, uz, AL, AU] using h
  have hy : ∀ a : Fin n, |y a| ≤ uz a := by
    intro a
    rw [← hUz a]
    simpa [uz, AU, matMulVec, absMatrix, absVec] using abs_matMulVec_le n U z a
  have hΔL' : ∀ a j : Fin n, |ΔL a j| ≤ g * AL a j := by
    intro a j
    simpa [AL, absMatrix] using hΔL a j
  have hΔLy0 : ∀ a : Fin n,
      |matMulVec n ΔL y a| ≤ g * matMulVec n AL (absVec n y) a := by
    intro a
    exact ch14ext_abs_matMulVec_le_scaled n ΔL AL y g hΔL' a
  have hLy : ∀ a : Fin n, matMulVec n AL (absVec n y) a ≤ luz a := by
    intro a
    exact ch14ext_matMulVec_mono_nonneg n AL (absVec n y) uz
      (fun p q => by simp [AL, absMatrix])
      (fun j => by simpa [absVec] using hy j) a
  have hΔLy : ∀ a : Fin n, |matMulVec n ΔL y a| ≤ g * luz a := by
    intro a
    exact le_trans (hΔLy0 a) (mul_le_mul_of_nonneg_left (hLy a) hg)
  have hr : ∀ a : Fin n, |r a| ≤ 2 * g * luz a := by
    intro a
    unfold r
    have ht := abs_add_le (matMulVec n ΔA₁ z a) (matMulVec n ΔL y a)
    nlinarith [hΔAz a, hΔLy a]
  have hOuter := ch14ext_abs_matMulVec_le_of_vec_bound n A_inv r
    (fun a => 2 * g * luz a) hr i
  have hBase : |x i - z i| ≤
      2 * g * matMulVec n AA luz i := by
    rw [hDiff]
    calc
      |matMulVec n A_inv r i| ≤ matMulVec n AA (fun a => 2 * g * luz a) i := by
        simpa [AA] using hOuter
      _ = 2 * g * matMulVec n AA luz i := by
        rw [ch14ext_matMulVec_scale]
  have hz : ∀ j : Fin n, |z j| ≤ |x_hat j| + e j := by
    intro j
    have h := abs_add_le (x_hat j) (z j - x_hat j)
    have heq : z j = x_hat j + (z j - x_hat j) := by ring
    rw [heq]
    simpa [e] using h
  let ux := matMulVec n AU (absVec n x_hat)
  let ue := matMulVec n AU e
  have hU : ∀ a : Fin n, uz a ≤ ux a + ue a := by
    intro a
    have h := ch14ext_matMulVec_mono_nonneg n AU (absVec n z)
      (fun j => |x_hat j| + e j) (fun p q => by simp [AU, absMatrix])
      (fun j => by simpa [absVec] using hz j) a
    have hadd : matMulVec n AU (fun j => |x_hat j| + e j) a = ux a + ue a := by
      simpa [ux, ue, absVec] using
        congrFun (matMulVec_add_right n AU (absVec n x_hat) e) a
    rw [hadd] at h
    exact h
  let lux := matMulVec n AL ux
  let lue := matMulVec n AL ue
  have hL : ∀ a : Fin n, luz a ≤ lux a + lue a := by
    intro a
    have h := ch14ext_matMulVec_mono_nonneg n AL uz (fun j => ux j + ue j)
      (fun p q => by simp [AL, absMatrix]) hU a
    have hadd : matMulVec n AL (fun j => ux j + ue j) a = lux a + lue a := by
      simpa [lux, lue] using congrFun (matMulVec_add_right n AL ux ue) a
    rw [hadd] at h
    exact h
  have hA : matMulVec n AA luz i ≤
      matMulVec n AA lux i + matMulVec n AA lue i := by
    have h := ch14ext_matMulVec_mono_nonneg n AA luz (fun j => lux j + lue j)
      (fun p q => by simp [AA, absMatrix]) hL i
    have hadd : matMulVec n AA (fun j => lux j + lue j) i =
        matMulVec n AA lux i + matMulVec n AA lue i := by
      simpa using congrFun (matMulVec_add_right n AA lux lue) i
    rw [hadd] at h
    exact h
  have heF : ∀ j : Fin n, e j ≤ c * F j := by
    intro j
    simpa [e, F] using hErr j
  have hUe : ∀ a : Fin n, ue a ≤ c * matMulVec n AU F a := by
    intro a
    have h := ch14ext_matMulVec_mono_nonneg n AU e (fun j => c * F j)
      (fun p q => by simp [AU, absMatrix]) heF a
    rw [ch14ext_matMulVec_scale] at h
    simpa [ue] using h
  have hLue : ∀ a : Fin n, lue a ≤
      c * matMulVec n AL (matMulVec n AU F) a := by
    intro a
    have h := ch14ext_matMulVec_mono_nonneg n AL ue
      (fun j => c * matMulVec n AU F j) (fun p q => by simp [AL, absMatrix])
      hUe a
    rw [ch14ext_matMulVec_scale] at h
    simpa [lue] using h
  have hQ1 : matMulVec n AA lue i ≤
      c * ch14ext_gjeForwardQ1 n A_inv L U X z y i := by
    have h := ch14ext_matMulVec_mono_nonneg n AA lue
      (fun j => c * matMulVec n AL (matMulVec n AU F) j)
      (fun p q => by simp [AA, absMatrix]) hLue i
    rw [ch14ext_matMulVec_scale] at h
    simpa [ch14ext_gjeForwardQ1, F, AA, AL, AU] using h
  have hAmul : 2 * g * matMulVec n AA luz i ≤
      2 * g * (matMulVec n AA lux i + matMulVec n AA lue i) :=
    mul_le_mul_of_nonneg_left hA (mul_nonneg (by norm_num) hg)
  have hQmul : 2 * g * matMulVec n AA lue i ≤
      2 * g * (c * ch14ext_gjeForwardQ1 n A_inv L U X z y i) :=
    mul_le_mul_of_nonneg_left hQ1 (mul_nonneg (by norm_num) hg)
  have hT1 : matMulVec n AA lux i =
      ch14ext_gjeForwardT1 n A_inv L U x_hat i := rfl
  rw [hT1] at hAmul
  nlinarith

/-- A nonnegative matrix maps a nonnegative vector to a nonnegative vector. -/
theorem ch14ext_matMulVec_action_nonneg (n : ℕ)
    (M : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hM : ∀ i j : Fin n, 0 ≤ M i j) (hx : ∀ j : Fin n, 0 ≤ x j)
    (i : Fin n) :
    0 ≤ matMulVec n M x i := by
  unfold matMulVec
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hM i j) (hx j))

theorem ch14ext_gjeForwardT1_nonneg (n : ℕ)
    (A_inv L U : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n) :
    0 ≤ ch14ext_gjeForwardT1 n A_inv L U x_hat i := by
  unfold ch14ext_gjeForwardT1
  apply ch14ext_absMatrix_action_nonneg
  intro a
  apply ch14ext_absMatrix_action_nonneg
  intro j
  apply ch14ext_absMatrix_action_nonneg
  intro k
  exact abs_nonneg _

theorem ch14ext_gjeForwardT2_nonneg (n : ℕ)
    (X U : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n)
    (hX : ∀ a j : Fin n, 0 ≤ X a j) :
    0 ≤ ch14ext_gjeForwardT2 n X U x_hat i := by
  unfold ch14ext_gjeForwardT2
  apply ch14ext_matMulVec_action_nonneg n X _ hX
  intro a
  apply ch14ext_absMatrix_action_nonneg
  intro j
  exact abs_nonneg _

theorem ch14ext_gjeForwardRaw_nonneg (n : ℕ)
    (X U : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) (i : Fin n)
    (hX : ∀ a j : Fin n, 0 ≤ X a j) :
    0 ≤ ch14ext_gjeForwardRaw n X U z y i := by
  unfold ch14ext_gjeForwardRaw
  apply add_nonneg
  · apply ch14ext_matMulVec_action_nonneg n X _ hX
    intro a
    apply ch14ext_absMatrix_action_nonneg
    intro j
    exact abs_nonneg _
  · apply ch14ext_matMulVec_action_nonneg n X _ hX
    intro j
    exact abs_nonneg _

theorem ch14ext_gjeForwardQ1_nonneg (n : ℕ)
    (A_inv L U X : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) (i : Fin n)
    (hX : ∀ a j : Fin n, 0 ≤ X a j) :
    0 ≤ ch14ext_gjeForwardQ1 n A_inv L U X z y i := by
  unfold ch14ext_gjeForwardQ1
  apply ch14ext_absMatrix_action_nonneg
  intro a
  apply ch14ext_absMatrix_action_nonneg
  intro j
  apply ch14ext_absMatrix_action_nonneg
  intro k
  exact ch14ext_gjeForwardRaw_nonneg n X U z y k hX

theorem ch14ext_gjeForwardQ2_nonneg (n : ℕ)
    (X U : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) (i : Fin n)
    (hX : ∀ a j : Fin n, 0 ≤ X a j) :
    0 ≤ ch14ext_gjeForwardQ2 n X U z y i := by
  unfold ch14ext_gjeForwardQ2
  apply ch14ext_matMulVec_action_nonneg n X _ hX
  intro a
  apply ch14ext_absMatrix_action_nonneg
  intro j
  exact ch14ext_gjeForwardRaw_nonneg n X U z y j hX

/-- Explicit higher-order term in the source split for (14.32). -/
noncomputable def ch14ext_gjeForwardHigherOrder (n : ℕ) (fp : FPModel)
    (A_inv L U X : Fin n → Fin n → ℝ)
    (z y x_hat : Fin n → ℝ) (i : Fin n) : ℝ :=
  2 * ch14ext_gammaRem fp n * ch14ext_gjeForwardT1 n A_inv L U x_hat i +
    2 * gje_c3_quadratic_remainder fp n *
      ch14ext_gjeForwardT2 n X U x_hat i +
    2 * gamma fp n * gje_c₃ fp n *
      ch14ext_gjeForwardQ1 n A_inv L U X z y i +
    2 * gje_c₃ fp n * gje_c₃ fp n *
      ch14ext_gjeForwardQ2 n X U z y i

theorem ch14ext_gjeForwardHigherOrder_nonneg (n : ℕ) (fp : FPModel)
    (A_inv L U X : Fin n → Fin n → ℝ)
    (z y x_hat : Fin n → ℝ) (i : Fin n)
    (hX : ∀ a j : Fin n, 0 ≤ X a j)
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3) :
    0 ≤ ch14ext_gjeForwardHigherOrder n fp A_inv L U X z y x_hat i := by
  have hg : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hc : 0 ≤ gje_c₃ fp n := gje_c3_nonneg fp n hnpos h3
  have hgr : 0 ≤ ch14ext_gammaRem fp n := ch14ext_gammaRem_nonneg fp n hn
  have hcr : 0 ≤ gje_c3_quadratic_remainder fp n :=
    ch14ext_gjeC3Rem_nonneg fp n hnpos h3
  have ht1 := ch14ext_gjeForwardT1_nonneg n A_inv L U x_hat i
  have ht2 := ch14ext_gjeForwardT2_nonneg n X U x_hat i hX
  have hq1 := ch14ext_gjeForwardQ1_nonneg n A_inv L U X z y i hX
  have hq2 := ch14ext_gjeForwardQ2_nonneg n X U z y i hX
  unfold ch14ext_gjeForwardHigherOrder
  positivity

/-- The literal (14.32) higher-order remainder.  The final summand is the
    correction needed to replace the exact stage envelope by `|Uhat⁻¹|`; its
    coefficient `6*n*u*c₃` is explicitly `O(u²)`. -/
noncomputable def ch14ext_gjeForwardLiteralHigherOrder (n : ℕ) (fp : FPModel)
    (A_inv L U X U_inv : Fin n → Fin n → ℝ)
    (z y x_hat : Fin n → ℝ) (i : Fin n) : ℝ :=
  ch14ext_gjeForwardHigherOrder n fp A_inv L U X z y x_hat i +
    6 * (n : ℝ) * fp.u * gje_c₃ fp n *
      ch14ext_gjeForwardUinvCorrection n X U U_inv x_hat i

theorem ch14ext_gjeForwardLiteralHigherOrder_nonneg (n : ℕ) (fp : FPModel)
    (A_inv L U X U_inv : Fin n → Fin n → ℝ)
    (z y x_hat : Fin n → ℝ) (i : Fin n)
    (hX : ∀ a j : Fin n, 0 ≤ X a j)
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3) :
    0 ≤ ch14ext_gjeForwardLiteralHigherOrder n fp A_inv L U X U_inv
      z y x_hat i := by
  have hOld := ch14ext_gjeForwardHigherOrder_nonneg n fp A_inv L U X
    z y x_hat i hX hn hnpos h3
  have hCorr := ch14ext_gjeForwardUinvCorrection_nonneg n X U U_inv x_hat i hX
  have hc : 0 ≤ gje_c₃ fp n := gje_c3_nonneg fp n hnpos h3
  have hCoeff : 0 ≤ 6 * (n : ℝ) * fp.u * gje_c₃ fp n :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg) hc
  unfold ch14ext_gjeForwardLiteralHigherOrder
  exact add_nonneg hOld (mul_nonneg hCoeff hCorr)

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

end NumStability.Ch14Ext
