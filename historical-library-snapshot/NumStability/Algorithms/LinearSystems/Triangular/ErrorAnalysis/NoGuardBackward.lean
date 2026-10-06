import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.FloatingPointArithmetic.ErrorModels.NoGuardBasic
import NumStability.Analysis.FloatingPointArithmetic.ErrorModels.NoGuardModel
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.FloatingPoint.Model

-- Algorithms/TriangularNoGuard.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 8, Problem 8.1.  No-guard-digit triangular-substitution support.





namespace NumStability

open scoped BigOperators

namespace NoGuardFPModel

/-- A standard-model proxy with the same unit roundoff, used only to reuse the
`γ_k` product calculus for no-guard proofs.  It does not model no-guard
addition/subtraction as standard rounded operations. -/
noncomputable def gammaProxy (fp : NoGuardFPModel) : FPModel :=
  FPModel.exactWithUnitRoundoff fp.u (le_of_lt fp.u_pos)

end NoGuardFPModel

/-- Higham `γ_k` built from a no-guard model's unit roundoff. -/
noncomputable abbrev noGuardGamma (fp : NoGuardFPModel) (k : ℕ) : ℝ :=
  gamma fp.gammaProxy k

/-- Validity predicate for no-guard `γ_k` bounds. -/
abbrev noGuardGammaValid (fp : NoGuardFPModel) (k : ℕ) : Prop :=
  gammaValid fp.gammaProxy k

/-! ## Problem 8.1 support: no-guard subtraction folds -/

/-- **No-guard subtraction fold with individual error tracking.**

For a fold `s₀ = c`, `s_{t+1} = fl_sub(s_t, a_t)` in the no-guard model,
each subtraction has two perturbations:

`fl_sub(x,y) = x*(1+α) - y*(1+β)`.

The unrolled fold therefore has accumulator factors `α` on the initial term and
on later propagation, while each subtracted term gets its own local `β` factor
and only the later accumulator factors:

`s_m = c*Π(1+α_k) - Σ_t a_t*(1+β_t)*Π_{k>t}(1+α_k)`. -/
lemma noGuard_sub_fold_unroll (fp : NoGuardFPModel) (m : ℕ)
    (a : Fin m → ℝ) (c : ℝ) :
    ∃ (α β : Fin m → ℝ),
      (∀ k, |α k| ≤ fp.u) ∧
      (∀ k, |β k| ≤ fp.u) ∧
      Fin.foldl m (fun acc t => fp.fl_sub acc (a t)) c =
        c * ∏ k : Fin m, (1 + α k) -
          ∑ t : Fin m, a t * (1 + β t) *
            ∏ k : Fin m, if t.val < k.val then (1 + α k) else 1 := by
  induction m generalizing c with
  | zero =>
      refine ⟨fun i => i.elim0, fun i => i.elim0, ?_, ?_, ?_⟩
      · intro i; exact i.elim0
      · intro i; exact i.elim0
      · simp
  | succ m ih =>
      obtain ⟨α', β', hα', hβ', hfold_m⟩ := ih (fun i => a i.castSucc) c
      have hfold_last :
          Fin.foldl (m + 1) (fun acc t => fp.fl_sub acc (a t)) c =
            fp.fl_sub
              (Fin.foldl m (fun acc t => fp.fl_sub acc (a t.castSucc)) c)
              (a (Fin.last m)) :=
        Fin.foldl_succ_last _ _
      obtain ⟨αnew, βnew, hsub⟩ :=
        fp.model_sub
          (Fin.foldl m (fun acc t => fp.fl_sub acc (a t.castSucc)) c)
          (a (Fin.last m))
      let α : Fin (m + 1) → ℝ := Fin.lastCases αnew α'
      let β : Fin (m + 1) → ℝ := Fin.lastCases βnew β'
      refine ⟨α, β, ?_, ?_, ?_⟩
      · intro k
        refine Fin.lastCases ?_ ?_ k
        · simp only [α, Fin.lastCases_last]; exact hsub.1
        · intro j; simp only [α, Fin.lastCases_castSucc]; exact hα' j
      · intro k
        refine Fin.lastCases ?_ ?_ k
        · simp only [β, Fin.lastCases_last]; exact hsub.2.1
        · intro j; simp only [β, Fin.lastCases_castSucc]; exact hβ' j
      · rw [hfold_last, noGuardSubWitness_value hsub, hfold_m]
        have hP :
            ∏ k : Fin (m + 1), (1 + α k) =
              (∏ k : Fin m, (1 + α' k)) * (1 + αnew) := by
          rw [Fin.prod_univ_castSucc]
          congr 1
          · apply Finset.prod_congr rfl
            intro k _
            simp only [α, Fin.lastCases_castSucc]
          · simp only [α, Fin.lastCases_last]
        have hTP_cast : ∀ t : Fin m,
            ∏ k : Fin (m + 1),
                (if (t.castSucc : Fin (m + 1)).val < k.val then (1 + α k) else 1) =
              (∏ k : Fin m,
                (if t.val < k.val then (1 + α' k) else 1)) * (1 + αnew) := by
          intro t
          rw [Fin.prod_univ_castSucc]
          congr 1
          · apply Finset.prod_congr rfl
            intro k _
            simp only [Fin.val_castSucc, α, Fin.lastCases_castSucc]
          · simp only [Fin.val_last, α, Fin.lastCases_last]
            have : t.val < m := t.isLt
            simp [this]
        have hTP_last :
            ∏ k : Fin (m + 1),
                (if (Fin.last m).val < k.val then (1 + α k) else 1) = 1 := by
          apply Finset.prod_eq_one
          intro k _
          have hk : ¬ (Fin.last m).val < k.val := by
            exact Nat.not_lt.mpr (Nat.le_of_lt_succ k.isLt)
          have hk' : ¬ m < k.val := by
            simpa using hk
          simp [Fin.val_last, hk']
        rw [hP]
        rw [Fin.sum_univ_castSucc]
        simp only [β, Fin.lastCases_castSucc, Fin.lastCases_last]
        rw [hTP_last]
        have hsum_cast :
            (∑ x : Fin m,
                a x.castSucc * (1 + β' x) *
                  ∏ k : Fin (m + 1),
                    (if (x.castSucc : Fin (m + 1)).val < k.val then (1 + α k) else 1)) =
              ∑ x : Fin m,
                a x.castSucc * (1 + β' x) *
                  ((∏ k : Fin m, (if x.val < k.val then (1 + α' k) else 1)) *
                    (1 + αnew)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hTP_cast x]
        have hsum :
            (∑ x : Fin m,
                a x.castSucc * (1 + β' x) *
                  ∏ k : Fin m, (if x.val < k.val then (1 + α' k) else 1)) *
                (1 + αnew) =
              ∑ x : Fin m,
                a x.castSucc * (1 + β' x) *
                  ((∏ k : Fin m, (if x.val < k.val then (1 + α' k) else 1)) *
                    (1 + αnew)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _
          ring
        rw [hsum_cast]
        rw [← hsum]
        ring

/-- **Problem 8.1 scalar row form.**

Under the no-guard-digit model (Higham (2.6)), the ordered scalar computation

`s = c; s := fl_sub(s, fl_mul(a_t, x_t)); y = fl_div(s, bk)`

still admits a backward-error identity with the right-hand side `c` left
unperturbed.  The diagonal/division factor uses the product of the `m`
accumulator perturbations and the final division perturbation, giving
`γ_(m+1)`.  The `t`th subtracted product uses its multiplication perturbation,
the no-guard operand perturbation, and the reciprocal of the first `t+1`
accumulator perturbations, giving `γ_(t+3)` (zero-based indexing). -/
theorem noGuard_mulSub_div_row_tight (fp : NoGuardFPModel) (m : ℕ)
    (a x : Fin m → ℝ) (c bk : ℝ) (hbk : bk ≠ 0)
    (hγ : noGuardGammaValid fp (m + 2)) :
    let fold :=
      Fin.foldl m (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) c
    ∃ (θdiag : ℝ) (η : Fin m → ℝ),
      |θdiag| ≤ noGuardGamma fp (m + 1) ∧
      (∀ t, |η t| ≤ noGuardGamma fp (t.val + 3)) ∧
      bk * fp.fl_div fold bk * (1 + θdiag) =
        c - ∑ t : Fin m, a t * x t * (1 + η t) := by
  classical
  intro fold
  let gfp := fp.gammaProxy
  have hgfp_u : gfp.u = fp.u := rfl
  have hγ_m1 : gammaValid gfp (m + 1) := gammaValid_mono gfp (by omega) hγ
  have hu_gfp : gfp.u < 1 := by
    have h1 : gammaValid gfp 1 := gammaValid_mono gfp (by omega) hγ
    unfold gammaValid at h1
    simpa using h1
  have hu : fp.u < 1 := by simpa [gfp, NoGuardFPModel.gammaProxy] using hu_gfp
  let a_vals : Fin m → ℝ := fun t => fp.fl_mul (a t) (x t)
  obtain ⟨α, β, hα_lt, hβ_lt, hfold_eq⟩ := noGuard_sub_fold_unroll fp m a_vals c
  have hα_bd : ∀ k, |α k| ≤ gfp.u := fun k => by
    rw [hgfp_u]
    exact hα_lt k
  have hβ_bd : ∀ k, |β k| ≤ gfp.u := fun k => by
    rw [hgfp_u]
    exact hβ_lt k
  -- Rounded products in the no-guard model still satisfy the ordinary
  -- relative-error law.
  have hmul : ∀ t : Fin m, ∃ ε, |ε| ≤ gfp.u ∧
      a_vals t = a t * x t * (1 + ε) := by
    intro t
    obtain ⟨ε, hε_lt, hε_eq⟩ :=
      fp.model_mul_signedRelErrorWitness (a t) (x t)
    refine ⟨ε, ?_, ?_⟩
    · rw [hgfp_u]
      exact hε_lt
    · exact hε_eq
  let ε : Fin m → ℝ := fun t => Classical.choose (hmul t)
  have hε_bd : ∀ t, |ε t| ≤ gfp.u := fun t =>
    (Classical.choose_spec (hmul t)).1
  have hε_eq : ∀ t, a_vals t = a t * x t * (1 + ε t) := fun t =>
    (Classical.choose_spec (hmul t)).2
  -- Final division contributes the last diagonal perturbation.
  obtain ⟨δd, hδd_lt, hδd_eq⟩ :=
    fp.model_div_signedRelErrorWitness fold bk hbk
  have hδd_bd : |δd| ≤ gfp.u := by
    rw [hgfp_u]
    exact hδd_lt
  have hbk_y : bk * fp.fl_div fold bk = fold * (1 + δd) := by
    rw [hδd_eq]
    field_simp [hbk]
  set P : ℝ := ∏ k : Fin m, (1 + α k) with hP_def
  set Q : ℝ := P * (1 + δd) with hQ_def
  have hP_pos : (0 : ℝ) < P := by
    rw [hP_def]
    exact prod_pos_of_u_bound gfp m α hα_bd hu_gfp
  have hδd_pos : (0 : ℝ) < 1 + δd := by
    linarith [neg_abs_le δd, hδd_bd, hu_gfp]
  have hQ_pos : (0 : ℝ) < Q := by
    rw [hQ_def]
    exact mul_pos hP_pos hδd_pos
  let ρ : Fin (m + 1) → ℝ := Fin.snoc α δd
  have hρ_bd : ∀ k, |ρ k| ≤ gfp.u := by
    intro k
    rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
    · simp only [ρ, Fin.snoc_castSucc]
      exact hα_bd j
    · simp only [ρ, Fin.snoc_last]
      exact hδd_bd
  have hQ_prod : Q = ∏ k : Fin (m + 1), (1 + ρ k) := by
    rw [hQ_def, hP_def, Fin.prod_univ_castSucc]
    show (∏ k : Fin m, (1 + α k)) * (1 + δd) =
      (∏ k : Fin m, (1 + ρ k.castSucc)) * (1 + ρ (Fin.last m))
    congr 1
    · apply Finset.prod_congr rfl
      intro k _
      simp only [ρ, Fin.snoc_castSucc]
    · simp only [ρ, Fin.snoc_last]
  obtain ⟨θdiag, hθdiag, hθdiag_eq⟩ :=
    inv_prod_error_bound gfp (m + 1) ρ hρ_bd hu_gfp hγ_m1
  have hθdiagQ : (1 + θdiag) * Q = 1 := by
    rw [hQ_prod, ← hθdiag_eq, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro k _
    have hk_pos : (0 : ℝ) < 1 + ρ k := by
      rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
      · simp only [ρ, Fin.snoc_castSucc]
        linarith [neg_abs_le (α j), hα_bd j, hu_gfp]
      · simp only [ρ, Fin.snoc_last]
        exact hδd_pos
    field_simp [hk_pos.ne']
  have hP_split : ∀ t : Fin m,
      P =
        (∏ k : Fin m, if k.val ≤ t.val then (1 + α k) else 1) *
        (∏ k : Fin m, if t.val < k.val then (1 + α k) else 1) := by
    intro t
    rw [hP_def, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    by_cases hle : k.val ≤ t.val
    · have hnot : ¬ t.val < k.val := by omega
      simp [hle, hnot]
    · have hlt : t.val < k.val := by omega
      simp [hle, hlt]
  have hHead_eq : ∀ t : Fin m,
      (∏ k : Fin m, if k.val ≤ t.val then (1 + α k) else 1) =
        ∏ j : Fin (t.val + 1), (1 + α ⟨j.val, by omega⟩) := by
    intro t
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun k : Fin m => k.val ≤ t.val)]
    have hrest : ∏ k ∈ Finset.filter (fun k : Fin m => ¬ k.val ≤ t.val) Finset.univ,
        (if k.val ≤ t.val then (1 + α k) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp [hk]
    rw [hrest, mul_one]
    have hS_eq : ∏ k ∈ Finset.filter (fun k : Fin m => k.val ≤ t.val) Finset.univ,
        (if k.val ≤ t.val then (1 + α k) else 1) =
      ∏ k ∈ Finset.filter (fun k : Fin m => k.val ≤ t.val) Finset.univ,
        (1 + α k) := by
      apply Finset.prod_congr rfl
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp [hk]
    rw [hS_eq]
    symm
    apply Finset.prod_nbij (fun j : Fin (t.val + 1) => (⟨j.val, by omega⟩ : Fin m))
    · intro j _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro j₁ _ j₂ _ h
      exact Fin.ext (Fin.mk.inj h)
    · intro k hk
      have hk_le : k.val ≤ t.val := by
        simpa [Finset.mem_filter] using hk
      exact ⟨⟨k.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · intro j _
      rfl
  have hoff : ∀ t : Fin m, ∃ η : ℝ,
      |η| ≤ gamma gfp (t.val + 3) ∧
      a_vals t * (1 + β t) *
          (∏ k : Fin m, if t.val < k.val then (1 + α k) else 1) *
          (1 + δd) * (1 + θdiag) =
        a t * x t * (1 + η) := by
    intro t
    let α_head : Fin (t.val + 1) → ℝ := fun j => α ⟨j.val, by omega⟩
    have hα_head_bd : ∀ j, |α_head j| ≤ gfp.u := fun j => hα_bd ⟨j.val, by omega⟩
    have hγ_head : gammaValid gfp (t.val + 1) := gammaValid_mono gfp (by omega) hγ
    obtain ⟨αinv, hαinv, hαinv_eq⟩ :=
      inv_prod_error_bound gfp (t.val + 1) α_head hα_head_bd hu_gfp hγ_head
    have hHead_cancel :
        (1 + αinv) *
          (∏ k : Fin m, if k.val ≤ t.val then (1 + α k) else 1) = 1 := by
      rw [hHead_eq t, ← hαinv_eq, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro j _
      have hj_pos : (0 : ℝ) < 1 + α_head j := by
        linarith [neg_abs_le (α_head j), hα_head_bd j, hu_gfp]
      field_simp [hj_pos.ne']
      simp [α_head]
    have htail_cancel :
        (∏ k : Fin m, if t.val < k.val then (1 + α k) else 1) *
            (1 + δd) * (1 + θdiag) =
          1 + αinv := by
      apply mul_right_cancel₀
        (show (∏ k : Fin m, if k.val ≤ t.val then (1 + α k) else 1) ≠ 0 by
          apply ne_of_gt
          apply Finset.prod_pos
          intro k _
          by_cases hle : k.val ≤ t.val
          · simp [hle]
            linarith [neg_abs_le (α k), hα_bd k, hu_gfp]
          · simp [hle])
      calc
        ((∏ k : Fin m, if t.val < k.val then (1 + α k) else 1) *
            (1 + δd) * (1 + θdiag)) *
            (∏ k : Fin m, if k.val ≤ t.val then (1 + α k) else 1)
            = (1 + θdiag) * Q := by
                rw [hQ_def, hP_split t]
                ring
        _ = 1 := hθdiagQ
        _ = (1 + αinv) *
            (∏ k : Fin m, if k.val ≤ t.val then (1 + α k) else 1) := hHead_cancel.symm
    have hε_γ1 : |ε t| ≤ gamma gfp 1 :=
      le_trans (hε_bd t) (u_le_gamma gfp one_pos (gammaValid_mono gfp (by omega) hγ))
    have hβ_γ1 : |β t| ≤ gamma gfp 1 :=
      le_trans (hβ_bd t) (u_le_gamma gfp one_pos (gammaValid_mono gfp (by omega) hγ))
    have hγ2 : gammaValid gfp 2 := gammaValid_mono gfp (by omega) hγ
    obtain ⟨ξ, hξ, hξ_eq⟩ := gamma_mul gfp 1 1 (ε t) (β t) hε_γ1 hβ_γ1 hγ2
    have hγ_t3 : gammaValid gfp (t.val + 3) := gammaValid_mono gfp (by omega) hγ
    have hγ_t3' : gammaValid gfp (2 + (t.val + 1)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hγ_t3
    obtain ⟨η, hη, hη_eq⟩ :=
      gamma_mul gfp 2 (t.val + 1) ξ αinv hξ hαinv hγ_t3'
    refine ⟨η, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hη, ?_⟩
    calc
      a_vals t * (1 + β t) *
          (∏ k : Fin m, if t.val < k.val then (1 + α k) else 1) *
          (1 + δd) * (1 + θdiag)
          = a t * x t * ((1 + ε t) * (1 + β t)) *
              ((∏ k : Fin m, if t.val < k.val then (1 + α k) else 1) *
                (1 + δd) * (1 + θdiag)) := by
              rw [hε_eq t]
              ring
      _ = a t * x t * ((1 + ε t) * (1 + β t)) * (1 + αinv) := by
              rw [htail_cancel]
      _ = a t * x t * (1 + ξ) * (1 + αinv) := by
              rw [hξ_eq]
      _ = a t * x t * (1 + η) := by
              rw [← hη_eq]
              ring
  let η : Fin m → ℝ := fun t => Classical.choose (hoff t)
  have hη_bd : ∀ t, |η t| ≤ gamma gfp (t.val + 3) := fun t =>
    (Classical.choose_spec (hoff t)).1
  have hη_eq : ∀ t,
      a_vals t * (1 + β t) *
          (∏ k : Fin m, if t.val < k.val then (1 + α k) else 1) *
          (1 + δd) * (1 + θdiag) =
        a t * x t * (1 + η t) := fun t =>
    (Classical.choose_spec (hoff t)).2
  refine ⟨θdiag, η, hθdiag, hη_bd, ?_⟩
  rw [hbk_y]
  change (Fin.foldl m (fun acc t => fp.fl_sub acc (a_vals t)) c) *
      (1 + δd) * (1 + θdiag) =
    c - ∑ t : Fin m, a t * x t * (1 + η t)
  rw [hfold_eq]
  have hsum_rw :
      (∑ t : Fin m,
        a_vals t * (1 + β t) *
          (∏ k : Fin m, if t.val < k.val then (1 + α k) else 1) *
          (1 + δd) * (1 + θdiag)) =
      ∑ t : Fin m, a t * x t * (1 + η t) := by
    apply Finset.sum_congr rfl
    intro t _
    exact hη_eq t
  have hdiag_cancel : c * P * (1 + δd) * (1 + θdiag) = c := by
    have hcomm : P * (1 + δd) * (1 + θdiag) = (1 + θdiag) * Q := by
      rw [hQ_def]
      ring
    rw [show c * P * (1 + δd) * (1 + θdiag) =
        c * (P * (1 + δd) * (1 + θdiag)) by ring, hcomm, hθdiagQ, mul_one]
  rw [show (c * P -
        ∑ x : Fin m,
          a_vals x * (1 + β x) *
            ∏ k : Fin m, (if x.val < k.val then (1 + α k) else 1)) *
        (1 + δd) * (1 + θdiag) =
      c * P * (1 + δd) * (1 + θdiag) -
        (∑ x : Fin m,
          a_vals x * (1 + β x) *
            ∏ k : Fin m, (if x.val < k.val then (1 + α k) else 1)) *
            (1 + δd) * (1 + θdiag) by ring]
  rw [Finset.sum_mul, Finset.sum_mul]
  rw [hdiag_cancel, hsum_rw]

/-! ## Problem 8.1: no-guard triangular substitution -/

/-- Ordered no-guard back-substitution row fold:
`bᵢ - fl(Uᵢ,i+1*xᵢ₊₁) - ... - fl(Uᵢ,n*xₙ)`. -/
noncomputable def noGuardBackSubRowFold (fp : NoGuardFPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ) (i : Fin n) : ℝ :=
  Fin.foldl (n - i.val - 1) (fun acc q =>
    fp.fl_sub acc
      (fp.fl_mul (U i ⟨i.val + 1 + q.val, by omega⟩)
        (xhat ⟨i.val + 1 + q.val, by omega⟩))) (b i)

/-- A vector satisfies the ordered no-guard back-substitution row equations. -/
def NoGuardBackSubSpec (fp : NoGuardFPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ) : Prop :=
  ∀ i, xhat i = fp.fl_div (noGuardBackSubRowFold fp n U b xhat i) (U i i)

/-- Per-row no-guard backward-error identity for upper-triangular substitution. -/
theorem noGuard_backSub_row_error (fp : NoGuardFPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hn : noGuardGammaValid fp (n + 1))
    (hrow : NoGuardBackSubSpec fp n U b xhat)
    (i : Fin n) :
    ∃ (θdiag : ℝ) (η : Fin (n - i.val - 1) → ℝ),
      |θdiag| ≤ noGuardGamma fp (n + 1) ∧
      (∀ q, |η q| ≤ noGuardGamma fp (n + 1)) ∧
      U i i * xhat i * (1 + θdiag) =
        b i - ∑ q : Fin (n - i.val - 1),
          U i ⟨i.val + 1 + q.val, by omega⟩ *
            xhat ⟨i.val + 1 + q.val, by omega⟩ * (1 + η q) := by
  set m := n - i.val - 1 with hm
  have hm2_le : m + 2 ≤ n + 1 := by
    have hi := i.isLt
    omega
  have hm1_le : m + 1 ≤ n + 1 := by omega
  have hm2_valid : noGuardGammaValid fp (m + 2) :=
    gammaValid_mono fp.gammaProxy hm2_le hn
  let a : Fin m → ℝ := fun q => U i ⟨i.val + 1 + q.val, by omega⟩
  let x : Fin m → ℝ := fun q => xhat ⟨i.val + 1 + q.val, by omega⟩
  obtain ⟨θdiag, η, hθdiag, hη, heq⟩ :=
    noGuard_mulSub_div_row_tight fp m a x (b i) (U i i) (hU i) hm2_valid
  refine ⟨θdiag, η, ?_, ?_, ?_⟩
  · exact le_trans hθdiag (gamma_mono fp.gammaProxy hm1_le hn)
  · intro q
    have hq_le : q.val + 3 ≤ n + 1 := by
      have hq := q.isLt
      omega
    exact le_trans (hη q) (gamma_mono fp.gammaProxy hq_le hn)
  · rw [hrow i]
    simpa [noGuardBackSubRowFold, a, x, hm] using heq

set_option maxHeartbeats 800000
















































































































































































































































































































end NumStability
