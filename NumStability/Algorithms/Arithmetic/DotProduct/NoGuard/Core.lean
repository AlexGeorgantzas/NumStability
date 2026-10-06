import NumStability.Algorithms.DotProduct

/-!
# No-guard dot-product arithmetic

Reusable left-to-right no-guard dot-product execution, its exact local-factor
expansion, and the associated gamma bounds.  This module is source-independent.
-/

namespace NumStability

open scoped BigOperators

/-- The actual left-to-right dot-product executor using the Chapter 2
no-guard-digit operations. -/
noncomputable def fl_noGuardDotProduct (fp : NoGuardFPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | m + 1 =>
      Fin.foldl m
        (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

/-- Unrolling a no-guard addition fold exposes the accumulator perturbation
`alpha` and the incoming-operand perturbation `beta` separately. -/
lemma noGuard_add_fold_unroll (fp : NoGuardFPModel) (m : ℕ)
    (a : Fin m → ℝ) (c : ℝ) :
    ∃ (alpha beta : Fin m → ℝ),
      (∀ k, |alpha k| ≤ fp.u) ∧
      (∀ k, |beta k| ≤ fp.u) ∧
      Fin.foldl m (fun acc t => fp.fl_add acc (a t)) c =
        c * ∏ k : Fin m, (1 + alpha k) +
          ∑ t : Fin m, a t * (1 + beta t) *
            ∏ k : Fin m, if t.val < k.val then (1 + alpha k) else 1 := by
  induction m generalizing c with
  | zero =>
      refine ⟨fun i => i.elim0, fun i => i.elim0, ?_, ?_, ?_⟩
      · intro i; exact i.elim0
      · intro i; exact i.elim0
      · simp
  | succ m ih =>
      obtain ⟨alpha', beta', halpha', hbeta', hfold_m⟩ :=
        ih (fun i => a i.castSucc) c
      have hfold_last :
          Fin.foldl (m + 1) (fun acc t => fp.fl_add acc (a t)) c =
            fp.fl_add
              (Fin.foldl m (fun acc t => fp.fl_add acc (a t.castSucc)) c)
              (a (Fin.last m)) :=
        Fin.foldl_succ_last _ _
      obtain ⟨alphaNew, betaNew, hadd⟩ :=
        fp.model_add
          (Fin.foldl m (fun acc t => fp.fl_add acc (a t.castSucc)) c)
          (a (Fin.last m))
      let alpha : Fin (m + 1) → ℝ := Fin.lastCases alphaNew alpha'
      let beta : Fin (m + 1) → ℝ := Fin.lastCases betaNew beta'
      refine ⟨alpha, beta, ?_, ?_, ?_⟩
      · intro k
        refine Fin.lastCases ?_ ?_ k
        · simpa [alpha] using hadd.1
        · intro j; simpa [alpha] using halpha' j
      · intro k
        refine Fin.lastCases ?_ ?_ k
        · simpa [beta] using hadd.2.1
        · intro j; simpa [beta] using hbeta' j
      · rw [hfold_last, noGuardAddWitness_value hadd, hfold_m]
        have hP :
            ∏ k : Fin (m + 1), (1 + alpha k) =
              (∏ k : Fin m, (1 + alpha' k)) * (1 + alphaNew) := by
          rw [Fin.prod_univ_castSucc]
          congr 1
          · apply Finset.prod_congr rfl
            intro k _
            simp [alpha]
          · simp [alpha]
        have hTP_cast : ∀ t : Fin m,
            ∏ k : Fin (m + 1),
                (if t.castSucc.val < k.val then (1 + alpha k) else 1) =
              (∏ k : Fin m,
                (if t.val < k.val then (1 + alpha' k) else 1)) *
                (1 + alphaNew) := by
          intro t
          rw [Fin.prod_univ_castSucc]
          congr 1
          · apply Finset.prod_congr rfl
            intro k _
            simp [alpha]
          · simp [alpha, t.isLt]
        have hTP_last :
            ∏ k : Fin (m + 1),
                (if (Fin.last m).val < k.val then (1 + alpha k) else 1) = 1 := by
          apply Finset.prod_eq_one
          intro k _
          have hk : ¬ (Fin.last m).val < k.val :=
            Nat.not_lt.mpr (Nat.le_of_lt_succ k.isLt)
          exact if_neg hk
        rw [hP, Fin.sum_univ_castSucc]
        simp only [beta, Fin.lastCases_castSucc, Fin.lastCases_last]
        rw [hTP_last]
        have hsum_cast :
            (∑ t : Fin m,
                a t.castSucc * (1 + beta' t) *
                  ∏ k : Fin (m + 1),
                    (if t.castSucc.val < k.val then (1 + alpha k) else 1)) =
              ∑ t : Fin m,
                a t.castSucc * (1 + beta' t) *
                  ((∏ k : Fin m,
                    (if t.val < k.val then (1 + alpha' k) else 1)) *
                    (1 + alphaNew)) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [hTP_cast t]
        rw [hsum_cast]
        have hsum_factor :
            (∑ t : Fin m,
                a t.castSucc * (1 + beta' t) *
                  ((∏ k : Fin m,
                    (if t.val < k.val then (1 + alpha' k) else 1)) *
                    (1 + alphaNew))) =
              (∑ t : Fin m,
                a t.castSucc * (1 + beta' t) *
                  ∏ k : Fin m,
                    (if t.val < k.val then (1 + alpha' k) else 1)) *
                (1 + alphaNew) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _
          ring
        rw [hsum_factor]
        ring

/-- The concrete no-guard executor expanded into one local factor per input
term.  The first term carries every accumulator perturbation; every later term
carries its own incoming-operand perturbation and only the later accumulator
perturbations. -/
theorem noGuardDot_factor_expansion_succ (fp : NoGuardFPModel) (m : ℕ)
    (x y : Fin (m + 1) → ℝ) :
    ∃ (mulDelta : Fin (m + 1) → ℝ) (alpha beta : Fin m → ℝ),
      (∀ i, |mulDelta i| ≤ fp.u) ∧
      (∀ i, |alpha i| ≤ fp.u) ∧
      (∀ i, |beta i| ≤ fp.u) ∧
      fl_noGuardDotProduct fp (m + 1) x y =
        x 0 * y 0 * (1 + mulDelta 0) *
            (∏ k : Fin m, (1 + alpha k)) +
          ∑ t : Fin m,
            x t.succ * y t.succ * (1 + mulDelta t.succ) *
              (1 + beta t) *
              ∏ k : Fin m,
                if t.val < k.val then (1 + alpha k) else 1 := by
  let z : Fin (m + 1) → ℝ := fun i => fp.fl_mul (x i) (y i)
  have hmul : ∀ i, ∃ d, |d| ≤ fp.u ∧ z i = x i * y i * (1 + d) := by
    intro i
    obtain ⟨d, hd, heq⟩ := fp.model_mul_signedRelErrorWitness (x i) (y i)
    exact ⟨d, hd, heq⟩
  let mulDelta : Fin (m + 1) → ℝ := fun i => Classical.choose (hmul i)
  have hmulBound : ∀ i, |mulDelta i| ≤ fp.u := fun i =>
    (Classical.choose_spec (hmul i)).1
  have hmulEq : ∀ i, z i = x i * y i * (1 + mulDelta i) := fun i =>
    (Classical.choose_spec (hmul i)).2
  obtain ⟨alpha, beta, halpha, hbeta, hfold⟩ :=
    noGuard_add_fold_unroll fp m (fun i => z i.succ) (z 0)
  refine ⟨mulDelta, alpha, beta, hmulBound, halpha, hbeta, ?_⟩
  change Fin.foldl m (fun acc i => fp.fl_add acc (z i.succ)) (z 0) = _
  rw [hfold, hmulEq 0]
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro t _
    rw [hmulEq t.succ]

/-- A standard-model proxy used only for the Chapter 3 `gamma` product
calculus.  Its unit roundoff is definitionally the no-guard model's unit
roundoff; none of its arithmetic operations are used by the executor. -/
noncomputable def noGuardDotGammaProxy (fp : NoGuardFPModel) : FPModel :=
  FPModel.exactWithUnitRoundoff fp.u (le_of_lt fp.u_pos)

/-- `gamma_k` for a no-guard dot product. -/
noncomputable abbrev noGuardDotGamma (fp : NoGuardFPModel) (k : ℕ) : ℝ :=
  gamma (noGuardDotGammaProxy fp) k

/-- The standard `k*u < 1` validity condition for the no-guard dot bound. -/
abbrev noGuardDotGammaValid (fp : NoGuardFPModel) (k : ℕ) : Prop :=
  gammaValid (noGuardDotGammaProxy fp) k

/-- The multiplicative factor attached to each exact input product in the
no-guard expansion. -/
noncomputable def noGuardDotLocalFactor (m : ℕ)
    (mulDelta : Fin (m + 1) → ℝ) (alpha beta : Fin m → ℝ) :
    Fin (m + 1) → ℝ :=
  Fin.cases
    ((1 + mulDelta 0) * ∏ k : Fin m, (1 + alpha k))
    (fun t =>
      (1 + mulDelta t.succ) * (1 + beta t) *
        ∏ k : Fin m, if t.val < k.val then (1 + alpha k) else 1)

/-- Single-sum form of the actual no-guard local-factor expansion. -/
theorem noGuardDot_factor_expansion_sum_succ (fp : NoGuardFPModel) (m : ℕ)
    (x y : Fin (m + 1) → ℝ) :
    ∃ (mulDelta : Fin (m + 1) → ℝ) (alpha beta : Fin m → ℝ),
      (∀ i, |mulDelta i| ≤ fp.u) ∧
      (∀ i, |alpha i| ≤ fp.u) ∧
      (∀ i, |beta i| ≤ fp.u) ∧
      fl_noGuardDotProduct fp (m + 1) x y =
        ∑ i : Fin (m + 1),
          x i * y i * noGuardDotLocalFactor m mulDelta alpha beta i := by
  obtain ⟨mulDelta, alpha, beta, hmul, halpha, hbeta, hfl⟩ :=
    noGuardDot_factor_expansion_succ fp m x y
  refine ⟨mulDelta, alpha, beta, hmul, halpha, hbeta, ?_⟩
  rw [hfl, Fin.sum_univ_succ]
  simp [noGuardDotLocalFactor]
  ring_nf

/-- Every local factor in an `m+1` term no-guard dot product differs from one
by at most `gamma_(m+1)`.  The incoming `beta` factor replaces, rather than
adds to, the current accumulator factor, exactly as described after (3.5). -/
theorem noGuardDotLocalFactor_abs_sub_one_le (fp : NoGuardFPModel) (m : ℕ)
    (mulDelta : Fin (m + 1) → ℝ) (alpha beta : Fin m → ℝ)
    (hmul : ∀ i, |mulDelta i| ≤ fp.u)
    (halpha : ∀ i, |alpha i| ≤ fp.u)
    (hbeta : ∀ i, |beta i| ≤ fp.u)
    (hvalid : noGuardDotGammaValid fp (m + 1)) :
    ∀ i, |noGuardDotLocalFactor m mulDelta alpha beta i - 1| ≤
      noGuardDotGamma fp (m + 1) := by
  let gfp := noGuardDotGammaProxy fp
  have hgu : gfp.u = fp.u := rfl
  intro i
  refine Fin.cases ?_ ?_ i
  · let delta : Fin (m + 1) → ℝ := Fin.cases (mulDelta 0) alpha
    have hdelta : ∀ j, |delta j| ≤ gfp.u := by
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa [delta, hgu] using hmul 0
      · intro k
        simpa [delta, hgu] using halpha k
    obtain ⟨eta, heta, hprod⟩ := prod_error_bound gfp (m + 1) delta hdelta hvalid
    have hfactor :
        noGuardDotLocalFactor m mulDelta alpha beta 0 = 1 + eta := by
      rw [← hprod, Fin.prod_univ_succ]
      simp [noGuardDotLocalFactor, delta]
    rw [hfactor]
    simpa using heta
  · intro t
    let tail : Fin m → ℝ := fun k =>
      if k.val = 0 then beta t
      else if t.val < k.val then alpha k else 0
    let delta : Fin (m + 1) → ℝ := Fin.cases (mulDelta t.succ) tail
    have htail : ∀ k, |tail k| ≤ fp.u := by
      intro k
      by_cases hk0 : k.val = 0
      · simp only [tail, hk0, if_pos]
        exact hbeta t
      · by_cases htk : t.val < k.val
        · simp only [tail, hk0, if_false, htk, if_pos]
          exact halpha k
        · have hu : 0 ≤ fp.u := le_of_lt fp.u_pos
          simp only [tail, hk0, if_false, htk, abs_zero]
          exact hu
    have hdelta : ∀ j, |delta j| ≤ gfp.u := by
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa [delta, hgu] using hmul t.succ
      · intro k
        simpa [delta, hgu] using htail k
    obtain ⟨eta, heta, hprod⟩ := prod_error_bound gfp (m + 1) delta hdelta hvalid
    have hmpos : 0 < m := Nat.pos_of_ne_zero fun hm0 => by
      subst m
      exact Fin.elim0 t
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
    have htailProd :
        (∏ k : Fin (q + 1), (1 + tail k)) =
          (1 + beta t) *
            ∏ k : Fin (q + 1),
              if t.val < k.val then (1 + alpha k) else 1 := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [tail, Fin.val_zero, if_pos, Nat.not_lt_zero, if_false, one_mul]
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      by_cases hle : t.val ≤ k.val <;> simp [hle]
    have hfactor :
        noGuardDotLocalFactor (q + 1) mulDelta alpha beta t.succ = 1 + eta := by
      rw [← hprod, Fin.prod_univ_succ]
      simp only [delta, Fin.cases_zero, Fin.cases_succ]
      rw [htailProd]
      simp [noGuardDotLocalFactor]
      ring
    rw [hfactor]
    simpa using heta

end NumStability
