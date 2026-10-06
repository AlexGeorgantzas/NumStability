import NumStability.Algorithms.Cholesky.Higham1014SourceSuccess
import NumStability.Algorithms.HighamChapter9DoolittleClosure

namespace NumStability

open scoped BigOperators

/-!
# Higham Theorem 10.14: literal displays (10.23) and (10.24)

After the first `r` stages of Algorithm 10.2, the book denotes by
`Ahat^(r+1)` the trailing matrix left by the rounded inner-product updates.
Here that matrix is an actual executor: every trailing entry is evaluated by
the sequential rounded multiply/subtract fold used by `fl_cholesky`.

The resulting definitions make (10.23) an exact identity and prove (10.24)
with the printed `gamma_(r+1)` constant.  No residual or error matrix is
supplied as a certificate by the caller.
-/

/-- The literal trailing matrix after `r` completed Cholesky stages.

Only the trailing principal block is retained.  Its entries are computed by
the same sequential rounded multiply/subtract fold as Algorithm 10.2. -/
noncomputable def higham10_14_sourceTrailing (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hr : r ≤ n) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if r ≤ i.val ∧ r ≤ j.val then
      fl_cholSubFold fp r
        (fun k => fl_cholesky fp n A (Fin.castLE hr k) i)
        (fun k => fl_cholesky fp n A (Fin.castLE hr k) j)
        (A i j)
    else 0

/-- The actual perturbation in display (10.23), determined by the rounded
factor and literal trailing executor rather than postulated by a caller. -/
noncomputable def higham10_14_sourceError (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hr : r ≤ n) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    (∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
      fl_choleskyTrunc fp n A r k j) +
      higham10_14_sourceTrailing fp A r hr i j - A i j

/-- The source's rectangular `r × n` computed factor, without the zero-row
square padding used by `fl_choleskyTrunc`. -/
noncomputable def higham10_14_sourceFactorRows (fp : FPModel) {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ) : Fin r → Fin (r + s) → ℝ :=
  fun k j => fl_cholesky fp (r + s) A (Fin.castAdd s k) j

/-- The nonzero `s × (r+s)` row block of `Ahat^(r+1)`.  Its first `r`
columns are zero, so its operator norm is exactly the norm of the trailing
`s × s` Schur block printed in Theorem 10.14. -/
noncomputable def higham10_14_sourceTrailingRows (fp : FPModel) {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ) : Fin s → Fin (r + s) → ℝ :=
  fun i j => higham10_14_sourceTrailing fp A r (Nat.le_add_right r s)
    (Fin.natAdd r i) j

/-- A matrix obtained by padding a rectangular block with `r` zero rows has
the same rectangular operator bound as that block. -/
private theorem higham10_14_zeroRowPad_opNorm2Le {r s : ℕ}
    (M : Fin (r + s) → Fin (r + s) → ℝ)
    (C : Fin s → Fin (r + s) → ℝ) (c : ℝ)
    (htop : ∀ i : Fin r, ∀ j : Fin (r + s), M (Fin.castAdd s i) j = 0)
    (htail : ∀ i : Fin s, ∀ j : Fin (r + s),
      M (Fin.natAdd r i) j = C i j)
    (hC : rectOpNorm2Le C c) : opNorm2Le M c := by
  intro x
  have htopAction : ∀ i : Fin r,
      matMulVec (r + s) M x (Fin.castAdd s i) = 0 := by
    intro i
    unfold matMulVec
    simp [htop i]
  have htailAction : ∀ i : Fin s,
      matMulVec (r + s) M x (Fin.natAdd r i) = rectMatMulVec C x i := by
    intro i
    unfold matMulVec rectMatMulVec
    apply Finset.sum_congr rfl
    intro j _
    rw [htail i j]
  have hnorm : vecNorm2 (matMulVec (r + s) M x) =
      vecNorm2 (rectMatMulVec C x) := by
    unfold vecNorm2 vecNorm2Sq
    congr 1
    rw [Fin.sum_univ_add]
    simp_rw [htopAction, htailAction]
    simp
  rw [hnorm]
  exact hC x

/-- For a natural dimension, `sqrt s ≤ s`; this is the last elementary
dimension estimate in Higham's derivation of (10.25). -/
private lemma higham10_14_sqrt_nat_le_nat (s : ℕ) :
    Real.sqrt (s : ℝ) ≤ (s : ℝ) := by
  by_cases hs : s = 0
  · simp [hs]
  · have hs1 : (1 : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hs)
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    have hsq : Real.sqrt (s : ℝ) ^ 2 = (s : ℝ) :=
      Real.sq_sqrt hs0
    nlinarith [Real.sqrt_nonneg (s : ℝ)]

private lemma higham10_14_opNorm2Le_neg {n : ℕ}
    {M : Fin n → Fin n → ℝ} {c : ℝ} (hM : opNorm2Le M c) :
    opNorm2Le (fun i j => -M i j) c := by
  intro x
  have haction : matMulVec n (fun i j => -M i j) x =
      fun i => -matMulVec n M x i := by
    ext i
    unfold matMulVec
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [haction, vecNorm2_neg]
  exact hM x

/-- Rank-sensitive norm bridge behind display (10.25).

The hypotheses are only the exact structural identities of (10.23), the
componentwise inequality (10.24), and the fact that `Ahat` is the zero-row
padding of its trailing row block `C`.  All norm bounds are then generated
internally from exact operator norms and Lemma 6.6; no numerical error budget
is accepted from the caller. -/
theorem higham10_25_rank_sensitive_bridge {r s : ℕ} (hr0 : 0 < r)
    (A E Ahat : Fin (r + s) → Fin (r + s) → ℝ)
    (B : Fin r → Fin (r + s) → ℝ)
    (C : Fin s → Fin (r + s) → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hrγ : (r : ℝ) * γ < 1)
    (htop : ∀ i : Fin r, ∀ j : Fin (r + s),
      Ahat (Fin.castAdd s i) j = 0)
    (htail : ∀ i : Fin s, ∀ j : Fin (r + s),
      Ahat (Fin.natAdd r i) j = C i j)
    (h23 : ∀ i j : Fin (r + s),
      A i j + E i j = rectMatMul (finiteTranspose B) B i j + Ahat i j)
    (h24 : ∀ i j : Fin (r + s),
      |E i j| ≤ γ *
        (rectMatMul (absMatrixRect (finiteTranspose B))
          (absMatrixRect B) i j + |Ahat i j|)) :
    opNorm2Le E
      (γ / (1 - (r : ℝ) * γ) *
        ((r : ℝ) * complexMatrixOp2 (realRectToCMatrix A) +
          ((r + s : ℕ) : ℝ) * complexMatrixOp2 (realRectToCMatrix C))) := by
  let cA : ℝ := complexMatrixOp2 (realRectToCMatrix A)
  let cE : ℝ := complexMatrixOp2 (realRectToCMatrix E)
  let cB : ℝ := complexMatrixOp2 (realRectToCMatrix B)
  let cC : ℝ := complexMatrixOp2 (realRectToCMatrix C)
  have hn : 0 < r + s := Nat.add_pos_left hr0 s
  have hcA0 : 0 ≤ cA := complexMatrixOp2_nonneg _
  have hcE0 : 0 ≤ cE := complexMatrixOp2_nonneg _
  have hcB0 : 0 ≤ cB := complexMatrixOp2_nonneg _
  have hcC0 : 0 ≤ cC := complexMatrixOp2_nonneg _

  have hBbase : rectOpNorm2Le B cB :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le B le_rfl
  have hrankB : realRectMatrixRank B ≤ r := by
    simpa [realRectMatrixRank, complexMatrixRank] using
      (Matrix.rank_le_height
        (realRectToCMatrix B : Matrix (Fin r) (Fin (r + s)) ℂ))
  have hsqrtB : Real.sqrt (realRectMatrixRank B : ℝ) ≤ Real.sqrt (r : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hrankB)
  have hBabs0 :=
    rectOpNorm2Le_absMatrixRect_sqrt_rank_mul_of_rectOpNorm2Le
      hn B hcB0 hBbase
  have hBabs : rectOpNorm2Le (absMatrixRect B) (Real.sqrt (r : ℝ) * cB) :=
    rectOpNorm2Le_mono
      (mul_le_mul_of_nonneg_right hsqrtB hcB0) hBabs0
  have hBTabs : rectOpNorm2Le (absMatrixRect (finiteTranspose B))
      (Real.sqrt (r : ℝ) * cB) := by
    have hcommute : absMatrixRect (finiteTranspose B) =
        finiteTranspose (absMatrixRect B) := by
      ext i j
      rfl
    rw [hcommute]
    exact rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (absMatrixRect B) (mul_nonneg (Real.sqrt_nonneg _) hcB0) hBabs
  have hGabs0 := rectOpNorm2Le_rectMatMul
    (absMatrixRect (finiteTranspose B)) (absMatrixRect B)
    (mul_nonneg (Real.sqrt_nonneg _) hcB0) hBTabs hBabs
  have hsqR : (Real.sqrt (r : ℝ) * cB) * (Real.sqrt (r : ℝ) * cB) =
      (r : ℝ) * cB ^ 2 := by
    calc
      (Real.sqrt (r : ℝ) * cB) * (Real.sqrt (r : ℝ) * cB) =
          (Real.sqrt (r : ℝ) * Real.sqrt (r : ℝ)) * cB ^ 2 := by ring
      _ = (r : ℝ) * cB ^ 2 := by
        rw [Real.mul_self_sqrt (Nat.cast_nonneg r)]
  have hGabs : opNorm2Le
      (rectMatMul (absMatrixRect (finiteTranspose B)) (absMatrixRect B))
      ((r : ℝ) * cB ^ 2) := by
    rw [hsqR] at hGabs0
    intro x
    simpa [opNorm2Le, rectOpNorm2Le, matMulVec, rectMatMulVec] using hGabs0 x

  have hCbase : rectOpNorm2Le C cC :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le C le_rfl
  have hrankC : realRectMatrixRank C ≤ s := by
    simpa [realRectMatrixRank, complexMatrixRank] using
      (Matrix.rank_le_height
        (realRectToCMatrix C : Matrix (Fin s) (Fin (r + s)) ℂ))
  have hsqrtC : Real.sqrt (realRectMatrixRank C : ℝ) ≤ Real.sqrt (s : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hrankC)
  have hCabs0 :=
    rectOpNorm2Le_absMatrixRect_sqrt_rank_mul_of_rectOpNorm2Le
      hn C hcC0 hCbase
  have hCabs : rectOpNorm2Le (absMatrixRect C) (Real.sqrt (s : ℝ) * cC) :=
    rectOpNorm2Le_mono
      (mul_le_mul_of_nonneg_right hsqrtC hcC0) hCabs0
  have hAhat : opNorm2Le Ahat cC :=
    higham10_14_zeroRowPad_opNorm2Le Ahat C cC htop htail hCbase
  have hAbsAhat : opNorm2Le (fun i j => |Ahat i j|)
      (Real.sqrt (s : ℝ) * cC) := by
    apply higham10_14_zeroRowPad_opNorm2Le
      (fun i j => |Ahat i j|) (absMatrixRect C)
        (Real.sqrt (s : ℝ) * cC)
    · intro i j
      rw [htop i j, abs_zero]
    · intro i j
      rw [htail i j]
      rfl
    · exact hCabs

  have hmajor := opNorm2Le_add
    (rectMatMul (absMatrixRect (finiteTranspose B)) (absMatrixRect B))
    (fun i j => |Ahat i j|) ((r : ℝ) * cB ^ 2)
    (Real.sqrt (s : ℝ) * cC) hGabs hAbsAhat
  have hscaled := opNorm2Le_smul (r + s)
    (fun i j =>
      rectMatMul (absMatrixRect (finiteTranspose B)) (absMatrixRect B) i j +
        |Ahat i j|)
    ((r : ℝ) * cB ^ 2 + Real.sqrt (s : ℝ) * cC) γ hγ0 hmajor
  have hEpre : opNorm2Le E
      (γ * ((r : ℝ) * cB ^ 2 + Real.sqrt (s : ℝ) * cC)) :=
    opNorm2Le_of_abs_le (r + s) E _ h24 _ hscaled
  have hcEpre : cE ≤
      γ * ((r : ℝ) * cB ^ 2 + Real.sqrt (s : ℝ) * cC) := by
    exact complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le E
      (mul_nonneg hγ0 (add_nonneg
        (mul_nonneg (Nat.cast_nonneg r) (sq_nonneg cB))
        (mul_nonneg (Real.sqrt_nonneg _) hcC0))) hEpre

  have hAop : opNorm2Le A cA :=
    opNorm2Le_complexMatrixOp2_realRectToCMatrix A
  have hEop : opNorm2Le E cE :=
    opNorm2Le_complexMatrixOp2_realRectToCMatrix E
  have hAE := opNorm2Le_add A E cA cE hAop hEop
  have hAEminus := opNorm2Le_add (fun i j => A i j + E i j)
    (fun i j => -Ahat i j) (cA + cE) cC hAE
      (higham10_14_opNorm2Le_neg hAhat)
  have hGramMatrix : rectMatMul (finiteTranspose B) B =
      fun i j => A i j + E i j + -Ahat i j := by
    ext i j
    have h := h23 i j
    linarith
  have hGram : opNorm2Le (rectMatMul (finiteTranspose B) B)
      (cA + cE + cC) := by
    rw [hGramMatrix]
    exact hAEminus
  have hGramNorm := complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le
    (rectMatMul (finiteTranspose B) B)
    (add_nonneg (add_nonneg hcA0 hcE0) hcC0) hGram
  have hcBsq : cB ^ 2 ≤ cA + cE + cC := by
    rw [complexMatrixOp2_realRectToCMatrix_finiteTranspose_mul_self_eq_sq B]
      at hGramNorm
    exact hGramNorm
  have hsqrts : Real.sqrt (s : ℝ) ≤ (s : ℝ) :=
    higham10_14_sqrt_nat_le_nat s
  have hchain : cE ≤ γ *
      ((r : ℝ) * cA + (r : ℝ) * cE + ((r + s : ℕ) : ℝ) * cC) := by
    calc
      cE ≤ γ * ((r : ℝ) * cB ^ 2 + Real.sqrt (s : ℝ) * cC) := hcEpre
      _ ≤ γ * ((r : ℝ) * (cA + cE + cC) +
          Real.sqrt (s : ℝ) * cC) := by
        apply mul_le_mul_of_nonneg_left _ hγ0
        exact add_le_add
          (mul_le_mul_of_nonneg_left hcBsq (Nat.cast_nonneg r)) le_rfl
      _ = γ * ((r : ℝ) * cA + (r : ℝ) * cE +
          ((r : ℝ) + Real.sqrt (s : ℝ)) * cC) := by ring
      _ ≤ γ * ((r : ℝ) * cA + (r : ℝ) * cE +
          ((r : ℝ) + (s : ℝ)) * cC) := by
        apply mul_le_mul_of_nonneg_left _ hγ0
        have hcoef0 : (r : ℝ) + Real.sqrt (s : ℝ) ≤
            (r : ℝ) + (s : ℝ) := by linarith
        have hcoef := mul_le_mul_of_nonneg_right hcoef0 hcC0
        linarith
      _ = γ * ((r : ℝ) * cA + (r : ℝ) * cE +
          ((r + s : ℕ) : ℝ) * cC) := by
        norm_num
  have hcEfinal := higham10_25_absorption γ (r : ℝ) ((r + s : ℕ) : ℝ)
    cA cC cE hrγ hchain
  intro x
  exact le_trans (hEop x)
    (mul_le_mul_of_nonneg_right hcEfinal (vecNorm2_nonneg x))

/-- Display (10.23): `A + E = Rhatᵀ Rhat + Ahat^(r+1)`. -/
theorem higham10_14_equation_10_23 (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hr : r ≤ n) (i j : Fin n) :
    A i j + higham10_14_sourceError fp A r hr i j =
      (∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j) +
        higham10_14_sourceTrailing fp A r hr i j := by
  simp only [higham10_14_sourceError]
  ring

/-- On a computed column, truncation does not change the entrywise absolute
Gram mass. -/
private lemma higham10_14_trunc_abs_gram_computed (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℕ) (i j : Fin n) (hi : i.val < r) :
    (∑ k : Fin n, |fl_choleskyTrunc fp n A r k i| *
      |fl_choleskyTrunc fp n A r k j|) =
    ∑ k : Fin n, |fl_cholesky fp n A k i| * |fl_cholesky fp n A k j| := by
  unfold fl_choleskyTrunc
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.val < r
  · simp [hk]
  · have hki : i.val < k.val := lt_of_lt_of_le hi (Nat.le_of_not_gt hk)
    rw [if_neg hk, abs_zero, zero_mul,
      fl_cholesky_strict_lower fp n A k i hki, abs_zero, zero_mul]

/-- The absolute Gram mass of the truncated factor is exactly the `Fin r`
mass used by the trailing rounded fold. -/
private lemma higham10_14_trunc_abs_gram (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hr : r ≤ n) (i j : Fin n) :
    (∑ k : Fin n, |fl_choleskyTrunc fp n A r k i| *
      |fl_choleskyTrunc fp n A r k j|) =
    ∑ k : Fin r, |fl_cholesky fp n A (Fin.castLE hr k) i *
      fl_cholesky fp n A (Fin.castLE hr k) j| := by
  unfold fl_choleskyTrunc
  have hfilter :
      (∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
        |fl_cholesky fp n A k i * fl_cholesky fp n A k j|) =
      ∑ k : Fin r, |fl_cholesky fp n A (Fin.castLE hr k) i *
        fl_cholesky fp n A (Fin.castLE hr k) j| := by
    simpa [Fin.castLE] using
      (sum_fin_eq_sum_filter_lt' hr
        (fun k : Fin n => |fl_cholesky fp n A k i *
          fl_cholesky fp n A k j|)).symm
  calc
    (∑ k : Fin n, |if k.val < r then fl_cholesky fp n A k i else 0| *
        |if k.val < r then fl_cholesky fp n A k j else 0|) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
          |fl_cholesky fp n A k i * fl_cholesky fp n A k j| := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k.val < r
      · simp [hk, abs_mul]
      · simp [hk]
    _ = _ := hfilter

/-- Truncate a full sum at row `i` when the summand vanishes below the
diagonal of column `i`.  This local copy supports the source-sharp
`gamma_(r+1)` entry certificate below. -/
private lemma higham10_14_sum_truncate_at (n : ℕ) (i : Fin n) (f : Fin n → ℝ)
    (hf : ∀ k : Fin n, i.val < k.val → f k = 0) :
    ∑ k : Fin n, f k =
      (∑ k : Fin i.val, f ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩) + f i := by
  rw [sum_fin_eq_sum_filter_lt' (Nat.le_of_lt i.isLt) f]
  have h1 : ∑ k : Fin n, f k =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val ≤ i.val), f k := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.not_le] at hk
    exact hf k hk
  rw [h1]
  have h2 : Finset.univ.filter (fun k : Fin n => k.val ≤ i.val) =
      insert i (Finset.univ.filter (fun k : Fin n => k.val < i.val)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hk
      rcases Nat.lt_or_eq_of_le hk with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | hk)
      · exact le_rfl
      · exact Nat.le_of_lt hk
  rw [h2, Finset.sum_insert (by simp)]
  ring

/-- A solved rounded Cholesky recurrence with local factors within `γ` of
one gives the componentwise residual bound for a single entry. -/
private lemma higham10_14_cert_core (m : ℕ) (a d z : ℝ)
    (x y : Fin m → ℝ) (φ₀ : ℝ) (φ : Fin m → ℝ) (γ : ℝ)
    (hφ₀ : |φ₀ - 1| ≤ γ) (hφ : ∀ k, |φ k - 1| ≤ γ)
    (heqn : d * z * φ₀ = a - ∑ k : Fin m, x k * y k * φ k) :
    |(∑ k : Fin m, x k * y k) + d * z - a| ≤
      γ * ((∑ k : Fin m, |x k| * |y k|) + |d| * |z|) := by
  have hs : ∑ k : Fin m, x k * y k * (φ k - 1) =
      (∑ k : Fin m, x k * y k * φ k) - ∑ k : Fin m, x k * y k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hres : (∑ k : Fin m, x k * y k) + d * z - a =
      -(d * z * (φ₀ - 1) + ∑ k : Fin m, x k * y k * (φ k - 1)) := by
    rw [hs]
    linear_combination heqn
  rw [hres, abs_neg]
  calc
    |d * z * (φ₀ - 1) + ∑ k : Fin m, x k * y k * (φ k - 1)| ≤
        |d * z * (φ₀ - 1)| + |∑ k : Fin m, x k * y k * (φ k - 1)| :=
      abs_add_le _ _
    _ ≤ |d| * |z| * γ + ∑ k : Fin m, |x k| * |y k| * γ := by
      apply add_le_add
      · rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left hφ₀
          (mul_nonneg (abs_nonneg d) (abs_nonneg z))
      · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hφ k)
          (mul_nonneg (abs_nonneg (x k)) (abs_nonneg (y k)))
    _ = γ * ((∑ k : Fin m, |x k| * |y k|) + |d| * |z|) := by
      rw [← Finset.sum_mul]
      ring

/-- Source-sharp stage certificate.  If column `i` is among the first `r`
computed columns, its Gram residual uses `gamma_(r+1)`, independently of the
ambient matrix dimension. -/
private theorem higham10_14_entry_bound (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hr1 : gammaValid fp (r + 1))
    (i j : Fin n) (hir : i.val < r) (hij : i.val ≤ j.val)
    (hdz : ∀ q : Fin n, q.val < r → fl_cholesky fp n A q q ≠ 0)
    (hpiv : ∀ q : Fin n, q.val < r → 0 ≤ fl_cholPivot fp n A q) :
    |∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k j - A i j| ≤
      gamma fp (r + 1) *
        ∑ k : Fin n, |fl_cholesky fp n A k i| * |fl_cholesky fp n A k j| := by
  have htrunc : ∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k j =
      (∑ k : Fin i.val,
        fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ i *
        fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ j) +
      fl_cholesky fp n A i i * fl_cholesky fp n A i j := by
    apply higham10_14_sum_truncate_at n i
    intro k hk
    rw [fl_cholesky_strict_lower fp n A k i hk, zero_mul]
  have htruncAbs : ∑ k : Fin n,
      |fl_cholesky fp n A k i| * |fl_cholesky fp n A k j| =
      (∑ k : Fin i.val,
        |fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ i| *
        |fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ j|) +
      |fl_cholesky fp n A i i| * |fl_cholesky fp n A i j| := by
    apply higham10_14_sum_truncate_at n i
    intro k hk
    rw [fl_cholesky_strict_lower fp n A k i hk, abs_zero, zero_mul]
  rw [htrunc, htruncAbs]
  rcases Nat.lt_or_eq_of_le hij with hlt | heq
  · have hm1 : gammaValid fp (i.val + 1) :=
      gammaValid_mono fp (by omega) hr1
    obtain ⟨φ₀, φ, hφ₀, hφ, heqn⟩ := fl_chol_offdiag_solve_form fp i.val
      (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ i)
      (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ j)
      (A i j) (fl_cholesky fp n A i i) (hdz i hir) hm1
    rw [← fl_cholesky_offdiag_eq fp n A i j hlt] at heqn
    have hmono : gamma fp (i.val + 1) ≤ gamma fp (r + 1) :=
      gamma_mono fp (by omega) hr1
    exact higham10_14_cert_core i.val (A i j)
      (fl_cholesky fp n A i i) (fl_cholesky fp n A i j) _ _ φ₀ φ
      (gamma fp (r + 1)) (le_trans hφ₀ hmono)
      (fun k => le_trans (hφ k) hmono) heqn
  · have hieqj : i = j := Fin.ext heq
    subst hieqj
    have hm2 : gammaValid fp (i.val + 2) :=
      gammaValid_mono fp (by omega) hr1
    obtain ⟨φ₀, φ, hφ₀, hφ, heqn⟩ := fl_chol_diag_solve_form fp i.val
      (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ i)
      (A i i) (hpiv i hir) hm2
    rw [← fl_cholesky_diag_eq fp n A i, pow_two] at heqn
    have hmono1 : gamma fp (i.val + 1) ≤ gamma fp (r + 1) :=
      gamma_mono fp (by omega) hr1
    have hmono2 : gamma fp (i.val + 2) ≤ gamma fp (r + 1) :=
      gamma_mono fp (by omega) hr1
    exact higham10_14_cert_core i.val (A i i)
      (fl_cholesky fp n A i i) (fl_cholesky fp n A i i) _ _ φ₀ φ
      (gamma fp (r + 1)) (le_trans hφ₀ hmono2)
      (fun k => le_trans (hφ k) hmono1) heqn

/-- Display (10.24) for the actual factor and literal trailing executor:
`|E| ≤ gamma_(r+1) (|Rhatᵀ||Rhat| + |Ahat^(r+1)|)` entrywise. -/
theorem higham10_14_equation_10_24 (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hr : r ≤ n)
    (hr1 : gammaValid fp (r + 1))
    (hsymm : ∀ i j : Fin n, A i j = A j i)
    (hsuccess : ∀ q : Fin n, q.val < r → 0 < fl_cholPivot fp n A q) :
    ∀ i j : Fin n,
      |higham10_14_sourceError fp A r hr i j| ≤
        gamma fp (r + 1) *
          ((∑ k : Fin n, |fl_choleskyTrunc fp n A r k i| *
            |fl_choleskyTrunc fp n A r k j|) +
            |higham10_14_sourceTrailing fp A r hr i j|) := by
  have hu : fp.u < 1 := by
    unfold gammaValid at hr1
    push_cast at hr1
    nlinarith [mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ (r : ℝ)) fp.u_nonneg]
  have hpiv : ∀ q : Fin n, q.val < r → 0 ≤ fl_cholPivot fp n A q :=
    fun q hq => (hsuccess q hq).le
  have hdz : ∀ q : Fin n, q.val < r → fl_cholesky fp n A q q ≠ 0 := by
    intro q hq
    rw [fl_cholesky_diag_eq]
    exact (fl_sqrt_pos fp hu _ (hsuccess q hq)).ne'
  intro i j
  by_cases hi : i.val < r
  · have htrail : higham10_14_sourceTrailing fp A r hr i j = 0 := by
      simp [higham10_14_sourceTrailing, Nat.not_le_of_gt hi]
    rw [htrail, abs_zero, add_zero]
    rw [higham10_14_sourceError, htrail, add_zero]
    rw [fl_choleskyTrunc_gram_computed fp n A r i j hi]
    rw [higham10_14_trunc_abs_gram_computed fp A r i j hi]
    by_cases hij : i.val ≤ j.val
    · simpa using higham10_14_entry_bound fp A r hr1 i j hi hij hdz hpiv
    · have hji : j.val ≤ i.val := Nat.le_of_lt (Nat.lt_of_not_ge hij)
      have hjr : j.val < r := lt_of_le_of_lt hji hi
      have h := higham10_14_entry_bound fp A r hr1 j i hjr hji hdz hpiv
      rw [hsymm i j]
      simpa [mul_comm] using h
  · have hir : r ≤ i.val := Nat.le_of_not_gt hi
    by_cases hj : j.val < r
    · have htrail : higham10_14_sourceTrailing fp A r hr i j = 0 := by
        simp [higham10_14_sourceTrailing, Nat.not_le_of_gt hj]
      rw [htrail, abs_zero, add_zero]
      rw [higham10_14_sourceError, htrail, add_zero]
      have h := higham10_14_entry_bound fp A r hr1 j i hj (Nat.le_of_lt (by omega))
        hdz hpiv
      have hgram :
          (∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
            fl_choleskyTrunc fp n A r k j) =
          ∑ k : Fin n, fl_cholesky fp n A k j * fl_cholesky fp n A k i := by
        calc
          _ = ∑ k : Fin n, fl_choleskyTrunc fp n A r k j *
                fl_choleskyTrunc fp n A r k i :=
            Finset.sum_congr rfl fun k _ => mul_comm _ _
          _ = ∑ k : Fin n, fl_cholesky fp n A k j *
                fl_cholesky fp n A k i :=
            fl_choleskyTrunc_gram_computed fp n A r j i hj
      have habs :
          (∑ k : Fin n, |fl_choleskyTrunc fp n A r k i| *
            |fl_choleskyTrunc fp n A r k j|) =
          ∑ k : Fin n, |fl_cholesky fp n A k j| * |fl_cholesky fp n A k i| := by
        calc
          _ = ∑ k : Fin n, |fl_choleskyTrunc fp n A r k j| *
                |fl_choleskyTrunc fp n A r k i| :=
            Finset.sum_congr rfl fun k _ => mul_comm _ _
          _ = ∑ k : Fin n, |fl_cholesky fp n A k j| *
                |fl_cholesky fp n A k i| :=
            higham10_14_trunc_abs_gram_computed fp A r j i hj
      rw [hgram, habs, hsymm i j]
      exact h
    · have hjr : r ≤ j.val := Nat.le_of_not_gt hj
      have hfold := higham9_2_flMulSubFold_source_residual_abs_le fp r (A i j)
        (fun k => fl_cholesky fp n A (Fin.castLE hr k) i)
        (fun k => fl_cholesky fp n A (Fin.castLE hr k) j) hr1
      have hγmono : gamma fp r ≤ gamma fp (r + 1) :=
        gamma_mono fp (Nat.le_succ r) hr1
      have hmass0 : 0 ≤
          (∑ k : Fin r,
            |fl_cholesky fp n A (Fin.castLE hr k) i *
              fl_cholesky fp n A (Fin.castLE hr k) j|) +
            |fl_cholSubFold fp r
              (fun k => fl_cholesky fp n A (Fin.castLE hr k) i)
              (fun k => fl_cholesky fp n A (Fin.castLE hr k) j)
              (A i j)| := by positivity
      have hfold' := hfold.trans
        (mul_le_mul_of_nonneg_right hγmono hmass0)
      rw [higham10_14_sourceError, higham10_14_sourceTrailing, if_pos ⟨hir, hjr⟩]
      rw [fl_choleskyTrunc_gram]
      have hsum :
          (∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
              fl_cholesky fp n A k i * fl_cholesky fp n A k j) =
          ∑ k : Fin r, fl_cholesky fp n A (Fin.castLE hr k) i *
            fl_cholesky fp n A (Fin.castLE hr k) j :=
        (sum_fin_eq_sum_filter_lt' hr _).symm
      have hsumAbs :
          (∑ k : Fin n, |fl_choleskyTrunc fp n A r k i| *
              |fl_choleskyTrunc fp n A r k j|) =
          ∑ k : Fin r, |fl_cholesky fp n A (Fin.castLE hr k) i *
            fl_cholesky fp n A (Fin.castLE hr k) j| := by
        exact higham10_14_trunc_abs_gram fp A r hr i j
      rw [hsum, hsumAbs]
      have hsign :
          |(∑ k : Fin r, fl_cholesky fp n A (Fin.castLE hr k) i *
                fl_cholesky fp n A (Fin.castLE hr k) j) +
              fl_cholSubFold fp r
                (fun k => fl_cholesky fp n A (Fin.castLE hr k) i)
                (fun k => fl_cholesky fp n A (Fin.castLE hr k) j)
                (A i j) - A i j| =
          |(A i j - ∑ k : Fin r,
                fl_cholesky fp n A (Fin.castLE hr k) i *
                  fl_cholesky fp n A (Fin.castLE hr k) j) -
              fl_cholSubFold fp r
                (fun k => fl_cholesky fp n A (Fin.castLE hr k) i)
                (fun k => fl_cholesky fp n A (Fin.castLE hr k) j)
                (A i j)| := by
        rw [← abs_neg]
        congr 1
        ring
      rw [hsign]
      simpa [fl_cholSubFold] using hfold'

/-- Display (10.25) for the literal factor, trailing executor, and error
matrix.  The denominator condition is exactly the positivity required by the
printed fraction; the combined source theorem below derives it from (10.21). -/
theorem higham10_14_equation_10_25 (fp : FPModel) {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ) (hr0 : 0 < r)
    (hr1 : gammaValid fp (r + 1))
    (hrγ : (r : ℝ) * gamma fp (r + 1) < 1)
    (hsymm : ∀ i j : Fin (r + s), A i j = A j i)
    (hsuccess : ∀ q : Fin (r + s), q.val < r →
      0 < fl_cholPivot fp (r + s) A q) :
    opNorm2Le (higham10_14_sourceError fp A r (Nat.le_add_right r s))
      (gamma fp (r + 1) / (1 - (r : ℝ) * gamma fp (r + 1)) *
        ((r : ℝ) * complexMatrixOp2 (realRectToCMatrix A) +
          ((r + s : ℕ) : ℝ) * complexMatrixOp2
            (realRectToCMatrix (higham10_14_sourceTrailingRows fp A)))) := by
  let hr : r ≤ r + s := Nat.le_add_right r s
  let E := higham10_14_sourceError fp A r hr
  let Ahat := higham10_14_sourceTrailing fp A r hr
  let B := higham10_14_sourceFactorRows fp A
  let C := higham10_14_sourceTrailingRows fp A
  have htop : ∀ i : Fin r, ∀ j : Fin (r + s),
      Ahat (Fin.castAdd s i) j = 0 := by
    intro i j
    simp [Ahat, higham10_14_sourceTrailing, Fin.castAdd, i.isLt]
  have htail : ∀ i : Fin s, ∀ j : Fin (r + s),
      Ahat (Fin.natAdd r i) j = C i j := by
    intro i j
    rfl
  have hGram : ∀ i j : Fin (r + s),
      (∑ k : Fin (r + s), fl_choleskyTrunc fp (r + s) A r k i *
        fl_choleskyTrunc fp (r + s) A r k j) =
      rectMatMul (finiteTranspose B) B i j := by
    intro i j
    rw [fl_choleskyTrunc_gram]
    change (∑ k ∈ Finset.univ.filter (fun k : Fin (r + s) => k.val < r),
      fl_cholesky fp (r + s) A k i * fl_cholesky fp (r + s) A k j) =
      ∑ k : Fin r,
        fl_cholesky fp (r + s) A (Fin.castAdd s k) i *
          fl_cholesky fp (r + s) A (Fin.castAdd s k) j
    simpa [Fin.castAdd, Fin.castLE] using
      (sum_fin_eq_sum_filter_lt' hr
        (fun k : Fin (r + s) => fl_cholesky fp (r + s) A k i *
          fl_cholesky fp (r + s) A k j)).symm
  have hAbsGram : ∀ i j : Fin (r + s),
      (∑ k : Fin (r + s),
        |fl_choleskyTrunc fp (r + s) A r k i| *
          |fl_choleskyTrunc fp (r + s) A r k j|) =
      rectMatMul (absMatrixRect (finiteTranspose B))
        (absMatrixRect B) i j := by
    intro i j
    rw [higham10_14_trunc_abs_gram fp A r hr i j]
    change (∑ k : Fin r,
      |fl_cholesky fp (r + s) A (Fin.castLE hr k) i *
        fl_cholesky fp (r + s) A (Fin.castLE hr k) j|) =
      ∑ k : Fin r,
        |fl_cholesky fp (r + s) A (Fin.castAdd s k) i| *
          |fl_cholesky fp (r + s) A (Fin.castAdd s k) j|
    apply Finset.sum_congr rfl
    intro k _
    have hcast : Fin.castLE hr k = Fin.castAdd s k := Fin.ext rfl
    rw [hcast, abs_mul]
  have h23 : ∀ i j : Fin (r + s),
      A i j + E i j = rectMatMul (finiteTranspose B) B i j + Ahat i j := by
    intro i j
    rw [← hGram i j]
    exact higham10_14_equation_10_23 fp A r hr i j
  have h24actual := higham10_14_equation_10_24 fp A r hr hr1 hsymm hsuccess
  have h24 : ∀ i j : Fin (r + s),
      |E i j| ≤ gamma fp (r + 1) *
        (rectMatMul (absMatrixRect (finiteTranspose B))
          (absMatrixRect B) i j + |Ahat i j|) := by
    intro i j
    simpa [E, Ahat, hAbsGram i j] using h24actual i j
  simpa [E, Ahat, B, C, hr] using
    (higham10_25_rank_sensitive_bridge hr0 A E Ahat B C
      (gamma fp (r + 1)) (gamma_nonneg fp hr1) hrγ htop htail h23 h24)

/-- The exact source endpoint combines display (10.21)'s success criterion
with the actual (10.23)--(10.24) matrices.  The full PSD/rank hypotheses from
the book are not needed for these determinate conclusions. -/
theorem higham10_14_source_success_and_error (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hr0 : 0 < r) (hr : r ≤ n)
    (hA11 : IsSymPosDef r
      (fun i j : Fin r => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩))
    (hr1 : gammaValid fp (r + 1)) (hγ1 : gamma fp (r + 1) < 1)
    (hH11sym : IsSymmetricFiniteMatrix (fun i j : Fin r =>
      A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ /
        (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
         Real.sqrt (A ⟨j.val, by omega⟩ ⟨j.val, by omega⟩))))
    (h1021 : (r : ℝ) *
        (gamma fp (r + 1) / (1 - gamma fp (r + 1))) <
      finiteMinEigenvalue hr0 (fun i j : Fin r =>
        A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ /
          (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
           Real.sqrt (A ⟨j.val, by omega⟩ ⟨j.val, by omega⟩))) hH11sym)
    (hsymm : ∀ i j : Fin n, A i j = A j i) :
    (∀ q : Fin n, q.val < r → 0 < fl_cholPivot fp n A q) ∧
    (∀ i j : Fin n,
      A i j + higham10_14_sourceError fp A r hr i j =
        (∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
          fl_choleskyTrunc fp n A r k j) +
          higham10_14_sourceTrailing fp A r hr i j) ∧
    (∀ i j : Fin n,
      |higham10_14_sourceError fp A r hr i j| ≤
        gamma fp (r + 1) *
          ((∑ k : Fin n, |fl_choleskyTrunc fp n A r k i| *
            |fl_choleskyTrunc fp n A r k j|) +
            |higham10_14_sourceTrailing fp A r hr i j|)) := by
  have hs := higham10_14_fl_cholesky_success_source fp A r hr0 hr hA11 hr1
    hγ1 hH11sym h1021
  exact ⟨hs, higham10_14_equation_10_23 fp A r hr,
    higham10_14_equation_10_24 fp A r hr hr1 hsymm hs⟩

/-- Full determinate source endpoint for Theorem 10.14: (10.21) produces
literal execution success, which in turn produces the actual matrices in
(10.23), the componentwise bound (10.24), and the rank-sensitive operator
bound (10.25).  The separate (10.22) conclusion is intentionally absent
because its `O(u^2)` term is not quantified in the source. -/
theorem higham10_14_source_determinate_endpoint (fp : FPModel) {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ) (hr0 : 0 < r)
    (hA11 : IsSymPosDef r
      (fun i j : Fin r => A (Fin.castAdd s i) (Fin.castAdd s j)))
    (hr1 : gammaValid fp (r + 1)) (hγ1 : gamma fp (r + 1) < 1)
    (hH11sym : IsSymmetricFiniteMatrix (fun i j : Fin r =>
      A (Fin.castAdd s i) (Fin.castAdd s j) /
        (Real.sqrt (A (Fin.castAdd s i) (Fin.castAdd s i)) *
         Real.sqrt (A (Fin.castAdd s j) (Fin.castAdd s j)))))
    (h1021 : (r : ℝ) *
        (gamma fp (r + 1) / (1 - gamma fp (r + 1))) <
      finiteMinEigenvalue hr0 (fun i j : Fin r =>
        A (Fin.castAdd s i) (Fin.castAdd s j) /
          (Real.sqrt (A (Fin.castAdd s i) (Fin.castAdd s i)) *
           Real.sqrt (A (Fin.castAdd s j) (Fin.castAdd s j)))) hH11sym)
    (hsymm : ∀ i j : Fin (r + s), A i j = A j i) :
    (∀ q : Fin (r + s), q.val < r →
      0 < fl_cholPivot fp (r + s) A q) ∧
    (∀ i j : Fin (r + s),
      A i j + higham10_14_sourceError fp A r (Nat.le_add_right r s) i j =
        (∑ k : Fin (r + s), fl_choleskyTrunc fp (r + s) A r k i *
          fl_choleskyTrunc fp (r + s) A r k j) +
          higham10_14_sourceTrailing fp A r (Nat.le_add_right r s) i j) ∧
    (∀ i j : Fin (r + s),
      |higham10_14_sourceError fp A r (Nat.le_add_right r s) i j| ≤
        gamma fp (r + 1) *
          ((∑ k : Fin (r + s),
            |fl_choleskyTrunc fp (r + s) A r k i| *
              |fl_choleskyTrunc fp (r + s) A r k j|) +
            |higham10_14_sourceTrailing fp A r
              (Nat.le_add_right r s) i j|)) ∧
    opNorm2Le (higham10_14_sourceError fp A r (Nat.le_add_right r s))
      (gamma fp (r + 1) / (1 - (r : ℝ) * gamma fp (r + 1)) *
        ((r : ℝ) * complexMatrixOp2 (realRectToCMatrix A) +
          ((r + s : ℕ) : ℝ) * complexMatrixOp2
            (realRectToCMatrix (higham10_14_sourceTrailingRows fp A)))) := by
  let hr : r ≤ r + s := Nat.le_add_right r s
  let H : Fin r → Fin r → ℝ := fun i j =>
    A (Fin.castAdd s i) (Fin.castAdd s j) /
      (Real.sqrt (A (Fin.castAdd s i) (Fin.castAdd s i)) *
       Real.sqrt (A (Fin.castAdd s j) (Fin.castAdd s j)))
  have hHsym : IsSymmetricFiniteMatrix H := hH11sym
  let i0 : Fin r := ⟨0, hr0⟩
  let A11 : Fin r → Fin r → ℝ :=
    fun i j => A (Fin.castAdd s i) (Fin.castAdd s j)
  have hdiag0 : 0 < A11 i0 i0 :=
    higham10_spd_diag_pos A11 hA11 i0
  have hHdiag : H i0 i0 = 1 := by
    dsimp [H, A11] at hdiag0 ⊢
    rw [Real.mul_self_sqrt hdiag0.le]
    exact div_self hdiag0.ne'
  let e0 : Fin r → ℝ := fun i => if i = i0 then 1 else 0
  have he0norm : ∑ i : Fin r, e0 i ^ 2 = 1 := by
    simp [e0]
  have he0quad : (∑ i : Fin r, ∑ j : Fin r, e0 i * H i j * e0 j) =
      H i0 i0 := by
    simp [e0]
  have hminle1 : finiteMinEigenvalue hr0 H hHsym ≤ 1 := by
    have hray := finiteMinEigenvalue_rayleigh hr0 H hHsym e0
    rw [he0norm, he0quad, hHdiag, mul_one] at hray
    exact hray
  have hfrac : (r : ℝ) *
      (gamma fp (r + 1) / (1 - gamma fp (r + 1))) < 1 := by
    exact lt_of_lt_of_le h1021 hminle1
  have hden : (0 : ℝ) < 1 - gamma fp (r + 1) := by linarith
  have hfrac' : (r : ℝ) * gamma fp (r + 1) /
      (1 - gamma fp (r + 1)) < 1 := by
    calc
      (r : ℝ) * gamma fp (r + 1) / (1 - gamma fp (r + 1)) =
          (r : ℝ) *
            (gamma fp (r + 1) / (1 - gamma fp (r + 1))) := by ring
      _ < 1 := hfrac
  have hmul := (div_lt_iff₀ hden).mp hfrac'
  have hγ0 := gamma_nonneg fp hr1
  have hrγ : (r : ℝ) * gamma fp (r + 1) < 1 := by linarith
  have hs := higham10_14_fl_cholesky_success_source fp A r hr0 hr hA11 hr1
    hγ1 hH11sym h1021
  exact ⟨hs, higham10_14_equation_10_23 fp A r hr,
    higham10_14_equation_10_24 fp A r hr hr1 hsymm hs,
    higham10_14_equation_10_25 fp A hr0 hr1 hrγ hsymm hs⟩

end NumStability
