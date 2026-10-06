/-
Chapter 11 closure: printed-strength backward-error bound for the all-1×1-pivot
(no-interchange, σ = id) floating-point block-LDLᵀ factorization.

This file constructs NAMED computed factors `L̂, D̂` for the recursive rounded
all-1×1-pivot path (mirroring the explicit construction inside
`fl_blockLDLT_all_oneByOne_bound`), proves the entrywise backward-error envelope
for those named factors, and then shows that the recursive envelope is dominated
by the printed Theorem 11.3 first-order bound
`p(n) · u · (|A| + |L̂||D̂||L̂ᵀ|)`.

All results are derived from the floating-point model; nothing assumes the
conclusion.  See the closing comments for the exact smallness hypotheses used.
-/
import NumStability.Algorithms.HighamChapter11

open scoped BigOperators

namespace NumStability.Ch11Closure

open NumStability

/-! ## Step 1 — named computed factors for the all-1×1-pivot path -/

/-- Named lower-triangular computed factor `L̂` for the rounded all-1×1-pivot
    block-LDLᵀ path.  This mirrors the explicit witness constructed inside the
    proof of `fl_blockLDLT_all_oneByOne_bound`. -/
noncomputable def flAllOneByOneL (fp : FPModel) :
    (n : ℕ) → (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | 0, _ => fun I _ => Fin.elim0 I
  | _ + 1, A => fun I J =>
      Fin.cases (Fin.cases 1 (fun _ => 0) J)
        (fun i => Fin.cases (fp.fl_div (A i.succ 0) (A 0 0))
          (fun j => flAllOneByOneL fp _ (flSchurCompl _ fp A) i j) J) I

/-- Named block-diagonal computed factor `D̂` for the rounded all-1×1-pivot
    block-LDLᵀ path.  Mirrors the `fl_blockLDLT_all_oneByOne_bound` witness. -/
noncomputable def flAllOneByOneD (fp : FPModel) :
    (n : ℕ) → (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | 0, _ => fun I _ => Fin.elim0 I
  | _ + 1, A => fun I J =>
      Fin.cases (Fin.cases (A 0 0) (fun _ => 0) J)
        (fun i => Fin.cases 0 (fun j => flAllOneByOneD fp _ (flSchurCompl _ fp A) i j) J) I

@[simp] theorem flAllOneByOneL_zero_zero (fp : FPModel) (n : ℕ)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    flAllOneByOneL fp (n + 1) A 0 0 = 1 := by
  simp [flAllOneByOneL]

@[simp] theorem flAllOneByOneL_zero_succ (fp : FPModel) (n : ℕ)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (j : Fin n) :
    flAllOneByOneL fp (n + 1) A 0 j.succ = 0 := by
  simp [flAllOneByOneL]

@[simp] theorem flAllOneByOneL_succ_zero (fp : FPModel) (n : ℕ)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (i : Fin n) :
    flAllOneByOneL fp (n + 1) A i.succ 0 = fp.fl_div (A i.succ 0) (A 0 0) := by
  simp [flAllOneByOneL]

@[simp] theorem flAllOneByOneL_succ_succ (fp : FPModel) (n : ℕ)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (i j : Fin n) :
    flAllOneByOneL fp (n + 1) A i.succ j.succ
      = flAllOneByOneL fp n (flSchurCompl n fp A) i j := by
  simp [flAllOneByOneL]

@[simp] theorem flAllOneByOneD_zero_zero (fp : FPModel) (n : ℕ)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    flAllOneByOneD fp (n + 1) A 0 0 = A 0 0 := by
  simp [flAllOneByOneD]

@[simp] theorem flAllOneByOneD_zero_succ (fp : FPModel) (n : ℕ)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (j : Fin n) :
    flAllOneByOneD fp (n + 1) A 0 j.succ = 0 := by
  simp [flAllOneByOneD]

@[simp] theorem flAllOneByOneD_succ_zero (fp : FPModel) (n : ℕ)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (i : Fin n) :
    flAllOneByOneD fp (n + 1) A i.succ 0 = 0 := by
  simp [flAllOneByOneD]

@[simp] theorem flAllOneByOneD_succ_succ (fp : FPModel) (n : ℕ)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (i j : Fin n) :
    flAllOneByOneD fp (n + 1) A i.succ j.succ
      = flAllOneByOneD fp n (flSchurCompl n fp A) i j := by
  simp [flAllOneByOneD]

/-! ## Step 2 — factorization + envelope bound for the named factors -/

/-- The named computed factors satisfy the recursive entrywise backward-error
    envelope `flBlockLDLTAllOneByOneBound`.  This is the same statement as
    `fl_blockLDLT_all_oneByOne_bound`, but pinned to the explicit named factors
    so that the printed product `|L̂||D̂||L̂ᵀ|` is available for Step 3. -/
theorem flAllOneByOne_factorization_bound (fp : FPModel) (hval : gammaValid fp 3) :
    ∀ (n : ℕ) (A : Fin n → Fin n → ℝ),
      FlAllOneSymmetricPivots fp n A →
      ∀ I J : Fin n,
        |(∑ k₁, ∑ k₂, flAllOneByOneL fp n A I k₁ * flAllOneByOneD fp n A k₁ k₂
            * flAllOneByOneL fp n A J k₂) - A I J|
          ≤ flBlockLDLTAllOneByOneBound fp n A I J := by
  intro n
  induction n with
  | zero => intro A _ I; exact Fin.elim0 I
  | succ n ih =>
      intro A hp
      obtain ⟨ha, hsym1, hpS⟩ := hp
      have hIHs := ih (flSchurCompl n fp A) hpS
      apply fl_blockLDLT_oneByOne_stage_bound n fp A ha hsym1 hval
        (flAllOneByOneL fp n (flSchurCompl n fp A))
        (flAllOneByOneD fp n (flSchurCompl n fp A))
        (flBlockLDLTAllOneByOneBound fp n (flSchurCompl n fp A))
      · intro i j
        simpa [flSchurCompl] using hIHs i j
      · simp
      · intro i; simp
      · intro j; simp
      · intro i j; simp
      · simp
      · intro j; simp
      · intro i; simp
      · intro i j; simp

/-! ## Step 3 — structural and geometric lemmas -/

/-- **Structural sum-split (Lemma A).**  The `(i+1, j+1)` entry of the named
    product `|L̂||D̂||L̂ᵀ|` at size `n+1` equals the pivot-path term
    `|L̂(i+1,0)|·|D̂(0,0)|·|L̂(j+1,0)|` plus the corresponding entry of the
    Schur-complement product.  This is the key fact that lets the recursive
    product embed into the full product without double counting. -/
theorem productEntry_succ_split (fp : FPModel) (n : ℕ)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (i j : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 1)
        (flAllOneByOneL fp (n + 1) A) (flAllOneByOneD fp (n + 1) A) i.succ j.succ
      = |fp.fl_div (A i.succ 0) (A 0 0)| * |A 0 0|
          * |fp.fl_div (A j.succ 0) (A 0 0)|
        + higham11_4_bunchKaufmanProductEntry n
            (flAllOneByOneL fp n (flSchurCompl n fp A))
            (flAllOneByOneD fp n (flSchurCompl n fp A)) i j := by
  unfold higham11_4_bunchKaufmanProductEntry
  rw [Fin.sum_univ_succ]
  congr 1
  · -- pivot-path term: k₁ = 0
    rw [Fin.sum_univ_succ]
    have hz : (∑ k₂ : Fin n,
        |flAllOneByOneL fp (n + 1) A i.succ 0|
          * |flAllOneByOneD fp (n + 1) A 0 k₂.succ|
          * |flAllOneByOneL fp (n + 1) A j.succ k₂.succ|) = 0 := by
      apply Finset.sum_eq_zero; intro x _; simp
    rw [hz, add_zero]
    simp
  · -- trailing block: k₁ = k₁'.succ  ⇒  Schur-complement product
    apply Finset.sum_congr rfl
    intro k₁ _
    rw [Fin.sum_univ_succ]
    have hz : |flAllOneByOneL fp (n + 1) A i.succ k₁.succ|
          * |flAllOneByOneD fp (n + 1) A k₁.succ 0|
          * |flAllOneByOneL fp (n + 1) A j.succ 0| = 0 := by simp
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro k₂ _
    simp

/-- Elementary two-sided bound on `|1 + δ|` for a relative-error perturbation. -/
theorem abs_one_add_le (fp : FPModel) {x : ℝ} (hx : |x| ≤ fp.u) :
    |1 + x| ≤ 1 + fp.u := by
  calc |1 + x| ≤ |(1 : ℝ)| + |x| := abs_add_le _ _
    _ = 1 + |x| := by rw [abs_one]
    _ ≤ 1 + fp.u := by linarith

theorem le_abs_one_add (fp : FPModel) (hu1 : fp.u ≤ 1) {x : ℝ} (hx : |x| ≤ fp.u) :
    1 - fp.u ≤ |1 + x| := by
  have hxlb : -fp.u ≤ x := (abs_le.mp hx).1
  have hnn : (0 : ℝ) ≤ 1 + x := by linarith
  rw [abs_of_nonneg hnn]; linarith

/-- **Lemma D.**  Under the standard smallness `3u ≤ 1/2`, the third
    order gamma constant is linear in `u`: `γ₃ ≤ 6u`. -/
theorem gamma_three_le (fp : FPModel) (h : (3 : ℝ) * fp.u ≤ 1 / 2) :
    gamma fp 3 ≤ 6 * fp.u := by
  have := gamma_le_two_mul_n_u_of_nu_le_half fp 3 (by push_cast; linarith)
  push_cast at this
  linarith

/-- **Lemma B.**  The exact pivot-path product term dominates the printed
    Schur product term `|A(i+1,0)·A(0,j+1)/A(0,0)|` up to the factor `(1-u)²`.
    This is the source of the tight cancellation that keeps `p(n)` linear. -/
theorem schur_pivot_product_lower (fp : FPModel) (hu1 : fp.u ≤ 1)
    (n : ℕ) (A : Fin (n + 1) → Fin (n + 1) → ℝ) (i j : Fin n)
    (ha : A 0 0 ≠ 0) (hsym : A 0 j.succ = A j.succ 0) :
    |A i.succ 0 * A 0 j.succ / A 0 0| * (1 - fp.u) ^ 2
      ≤ |fp.fl_div (A i.succ 0) (A 0 0)| * |A 0 0|
          * |fp.fl_div (A j.succ 0) (A 0 0)| := by
  obtain ⟨δ₁, hδ₁, hd₁⟩ := fp.model_div (A i.succ 0) (A 0 0) ha
  obtain ⟨δ₂, hδ₂, hd₂⟩ := fp.model_div (A j.succ 0) (A 0 0) ha
  have hc : |A 0 0| ≠ 0 := abs_ne_zero.mpr ha
  -- rewrite the right-hand product as Q · |1+δ₁| · |1+δ₂|
  have key : |fp.fl_div (A i.succ 0) (A 0 0)| * |A 0 0|
              * |fp.fl_div (A j.succ 0) (A 0 0)|
            = |A i.succ 0 * A 0 j.succ / A 0 0| * (|1 + δ₁| * |1 + δ₂|) := by
    rw [hd₁, hd₂, hsym]
    simp only [abs_mul, abs_div]
    field_simp
  rw [key]
  have hQ : 0 ≤ |A i.succ 0 * A 0 j.succ / A 0 0| := abs_nonneg _
  have h1 : 1 - fp.u ≤ |1 + δ₁| := le_abs_one_add fp hu1 hδ₁
  have h2 : 1 - fp.u ≤ |1 + δ₂| := le_abs_one_add fp hu1 hδ₂
  have hnn : (0 : ℝ) ≤ 1 - fp.u := by linarith
  have hprod : (1 - fp.u) ^ 2 ≤ |1 + δ₁| * |1 + δ₂| := by
    calc (1 - fp.u) ^ 2 = (1 - fp.u) * (1 - fp.u) := by ring
      _ ≤ |1 + δ₁| * |1 + δ₂| := by
          apply mul_le_mul h1 h2 hnn
          exact le_trans hnn h1
  exact mul_le_mul_of_nonneg_left hprod hQ

/-- **Lemma C.**  The rounded Schur-complement entry is bounded by the original
    trailing entry plus the pivot-path product, each inflated by rounding
    factors `(1+u)`, `(1+u)³`. -/
theorem schur_entry_upper (fp : FPModel) (hu0 : 0 ≤ fp.u)
    (n : ℕ) (A : Fin (n + 1) → Fin (n + 1) → ℝ) (i j : Fin n)
    (ha : A 0 0 ≠ 0) :
    |flSchurCompl n fp A i j|
      ≤ (1 + fp.u) * |A i.succ j.succ|
        + (1 + fp.u) ^ 3 * |A i.succ 0 * A 0 j.succ / A 0 0| := by
  unfold flSchurCompl
  obtain ⟨δ, hδ, hd⟩ := fp.model_div (A i.succ 0) (A 0 0) ha
  obtain ⟨μ, hμ, hm⟩ :=
    fp.model_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ)
  obtain ⟨σ, hσ, hs⟩ :=
    fp.model_sub (A i.succ j.succ)
      (fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ))
  set P := |A i.succ j.succ| with hP
  set Q := |A i.succ 0 * A 0 j.succ / A 0 0| with hQdef
  have hPnn : 0 ≤ P := abs_nonneg _
  have hQnn : 0 ≤ Q := abs_nonneg _
  -- bound on the rounded product term M
  have hMabs : |fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ)|
              = Q * (|1 + δ| * |1 + μ|) := by
    rw [hm, hd, hQdef]
    simp only [abs_mul, abs_div]
    field_simp
  have hMle : |fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ)|
              ≤ Q * (1 + fp.u) ^ 2 := by
    rw [hMabs]
    have hδ' : |1 + δ| ≤ 1 + fp.u := abs_one_add_le fp hδ
    have hμ' : |1 + μ| ≤ 1 + fp.u := abs_one_add_le fp hμ
    have h1u : (0 : ℝ) ≤ 1 + fp.u := by linarith
    calc Q * (|1 + δ| * |1 + μ|)
        ≤ Q * ((1 + fp.u) * (1 + fp.u)) := by
          apply mul_le_mul_of_nonneg_left _ hQnn
          apply mul_le_mul hδ' hμ' (abs_nonneg _) h1u
      _ = Q * (1 + fp.u) ^ 2 := by ring
  -- combine
  rw [hs, abs_mul]
  have hσ' : |1 + σ| ≤ 1 + fp.u := abs_one_add_le fp hσ
  have h1u : (0 : ℝ) ≤ 1 + fp.u := by linarith
  have hsum_nn : 0 ≤ P + |fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ)| :=
    add_nonneg hPnn (abs_nonneg _)
  calc |A i.succ j.succ
          - fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ)| * |1 + σ|
      ≤ (P + |fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ)|) * |1 + σ| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        rw [hP]; exact abs_sub _ _
    _ ≤ (P + |fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ)|) * (1 + fp.u) := by
        exact mul_le_mul_of_nonneg_left hσ' hsum_nn
    _ ≤ (P + Q * (1 + fp.u) ^ 2) * (1 + fp.u) := by
        apply mul_le_mul_of_nonneg_right _ h1u
        linarith [hMle]
    _ = (1 + fp.u) * P + (1 + fp.u) ^ 3 * Q := by ring

/-- The linear backward-error polynomial `p(n) = 20 n`. -/
def pPoly (n : ℕ) : ℝ := 20 * (n : ℝ)

/-- **Arithmetic core of the trailing case.**  This isolates the real-number
    inequality that closes the recursion at printed (linear-in-`n`) strength.
    The variables abstract: `p = |A(i+1,j+1)|`, `q` the pivot-path product,
    `t` the pivot-path product entry of `|L̂||D̂||L̂ᵀ|`, `fs` the Schur-complement
    product entry, `as = |Ŝ(i,j)|`, `g3 = γ₃`, `Bs` the recursive envelope,
    `K = n`.  The smallness `n·u ≤ 1/100` keeps the constant `20` uniform. -/
theorem trailing_arith (u K p q t fs as g3 Bs : ℝ)
    (hu0 : 0 ≤ u) (huε : u ≤ 1 / 100) (hK0 : 0 ≤ K) (hKu : K * u ≤ 1 / 100)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (_ht : 0 ≤ t) (hfs : 0 ≤ fs) (_has0 : 0 ≤ as)
    (_hg3 : 0 ≤ g3) (hg3u : g3 ≤ 6 * u)
    (has : as ≤ (1 + u) * p + (1 + u) ^ 3 * q)
    (htq : q * (1 - u) ^ 2 ≤ t)
    (hBs : Bs ≤ 20 * K * u * (as + fs)) :
    2 * g3 * (p + q) + Bs ≤ 20 * (K + 1) * u * (p + t + fs) := by
  have hpq : 0 ≤ p + q := by linarith
  have h20Ku : 0 ≤ 20 * K * u :=
    mul_nonneg (mul_nonneg (by norm_num) hK0) hu0
  -- Step 1: linearize the fresh pivot error
  have step1 : 2 * g3 * (p + q) ≤ 12 * u * (p + q) :=
    mul_le_mul_of_nonneg_right (by linarith) hpq
  -- Step 2: expand the recursive envelope via the Schur-entry bound
  have step2 : Bs ≤ 20 * K * u * ((1 + u) * p + (1 + u) ^ 3 * q + fs) :=
    hBs.trans (mul_le_mul_of_nonneg_left (by linarith) h20Ku)
  -- key structural inequality after cancelling one factor of `u`
  have hW : 0 ≤ 20 * (K + 1) * (1 - u) ^ 2 - 20 * K * (1 + u) ^ 3 - 12 := by
    have hKuu : K * u * u ≤ (1 / 100) * u :=
      mul_le_mul_of_nonneg_right hKu hu0
    nlinarith [hKu, huε, hu0, hK0, mul_nonneg hK0 hu0, hKuu,
      mul_nonneg (mul_nonneg hK0 hu0) hu0, sq_nonneg u]
  have hstar :
      12 * (p + q) + 20 * K * ((1 + u) * p + (1 + u) ^ 3 * q + fs)
        ≤ 20 * (K + 1) * (p + t + fs) := by
    have htbound : 20 * (K + 1) * (q * (1 - u) ^ 2) ≤ 20 * (K + 1) * t :=
      mul_le_mul_of_nonneg_left htq (by nlinarith [hK0])
    have hpc : 0 ≤ p * (8 - 20 * K * u) := mul_nonneg hp (by nlinarith [hKu])
    have hqW : 0 ≤ q * (20 * (K + 1) * (1 - u) ^ 2 - 20 * K * (1 + u) ^ 3 - 12) :=
      mul_nonneg hq hW
    nlinarith [hpc, hqW, htbound, hfs]
  -- reinstate the factor of `u`
  have h44 :
      12 * u * (p + q) + 20 * K * u * ((1 + u) * p + (1 + u) ^ 3 * q + fs)
        ≤ 20 * (K + 1) * u * (p + t + fs) := by
    nlinarith [mul_le_mul_of_nonneg_left hstar hu0]
  linarith [step1, step2, h44]

/-- Pivot-row / pivot-column case bound: a bare `u|A|` term is dominated by the
    printed envelope whenever the polynomial coefficient is at least one. -/
theorem easy_case_bound (u c a F : ℝ) (hu : 0 ≤ u) (hc : 1 ≤ c)
    (ha : 0 ≤ a) (hF : 0 ≤ F) :
    u * a ≤ c * u * (a + F) := by
  have hc0 : (0 : ℝ) ≤ c := le_trans zero_le_one hc
  have h1 : u * a ≤ c * u * a :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hu hc) ha
  have h2 : c * u * a ≤ c * u * (a + F) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc0 hu)
  linarith

/-- **Step 3 (the crux).**  The recursive backward-error envelope is dominated by
    the printed Theorem 11.3 first-order bound `p(n)·u·(|A| + |L̂||D̂||L̂ᵀ|)` with
    the linear polynomial `p(n) = 20 n`, under the smallness `n·u ≤ 1/100`. -/
theorem flAllOneByOne_envelope_le_printed (fp : FPModel) (hval : gammaValid fp 3) :
    ∀ (n : ℕ) (A : Fin n → Fin n → ℝ),
      (n : ℝ) * fp.u ≤ 1 / 100 →
      FlAllOneSymmetricPivots fp n A →
      ∀ i j : Fin n,
        flBlockLDLTAllOneByOneBound fp n A i j
          ≤ higham11_3_printedFirstOrderBound n A
              (flAllOneByOneL fp n A) (flAllOneByOneD fp n A) id (pPoly n) fp.u i j := by
  intro n
  induction n with
  | zero => intro A _ _ i; exact Fin.elim0 i
  | succ n ih =>
      intro A hsmall hp i j
      obtain ⟨ha, hsym1, hpS⟩ := hp
      have hu0 := fp.u_nonneg
      have hsmall' : (n : ℝ) * fp.u ≤ 1 / 100 := by
        have hmono : (n : ℝ) * fp.u ≤ ((n + 1 : ℕ) : ℝ) * fp.u :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hu0
        push_cast at hmono hsmall ⊢; linarith
      have hu100 : fp.u ≤ 1 / 100 := by
        have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        have : fp.u ≤ ((n + 1 : ℕ) : ℝ) * fp.u := le_mul_of_one_le_left hu0 h1
        push_cast at this hsmall; linarith
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · -- pivot (0,0)
          have hL : flBlockLDLTAllOneByOneBound fp (n + 1) A 0 0 = 0 := by
            simp [flBlockLDLTAllOneByOneBound, flBlockLDLTOneByOneStageBound]
          rw [hL]
          exact higham11_3_printedFirstOrderBound_nonneg (n + 1) A
            (flAllOneByOneL fp (n + 1) A) (flAllOneByOneD fp (n + 1) A) id
            (pPoly (n + 1)) fp.u (mul_nonneg (by unfold pPoly; positivity) hu0) 0 0
        · -- pivot row (0, j'+1)
          have hL : flBlockLDLTAllOneByOneBound fp (n + 1) A 0 j'.succ
              = fp.u * |A 0 j'.succ| := by
            simp [flBlockLDLTAllOneByOneBound, flBlockLDLTOneByOneStageBound]
          rw [hL]
          simp only [higham11_3_printedFirstOrderBound, pPoly, id_eq]
          push_cast
          refine easy_case_bound fp.u _ _ _ hu0 ?_ (abs_nonneg _)
            (higham11_4_bunchKaufmanProductEntry_nonneg _ _ _ _ _)
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · -- pivot column (i'+1, 0)
          have hL : flBlockLDLTAllOneByOneBound fp (n + 1) A i'.succ 0
              = fp.u * |A i'.succ 0| := by
            simp [flBlockLDLTAllOneByOneBound, flBlockLDLTOneByOneStageBound]
          rw [hL]
          simp only [higham11_3_printedFirstOrderBound, pPoly, id_eq]
          push_cast
          refine easy_case_bound fp.u _ _ _ hu0 ?_ (abs_nonneg _)
            (higham11_4_bunchKaufmanProductEntry_nonneg _ _ _ _ _)
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
        · -- trailing block (i'+1, j'+1): the main case
          have hLHS : flBlockLDLTAllOneByOneBound fp (n + 1) A i'.succ j'.succ
              = 2 * gamma fp 3
                  * (|A i'.succ j'.succ| + |A i'.succ 0 * A 0 j'.succ / A 0 0|)
                + flBlockLDLTAllOneByOneBound fp n (flSchurCompl n fp A) i' j' := by
            simp [flBlockLDLTAllOneByOneBound, flBlockLDLTOneByOneStageBound]
          have hRHS : higham11_3_printedFirstOrderBound (n + 1) A
              (flAllOneByOneL fp (n + 1) A) (flAllOneByOneD fp (n + 1) A) id
              (pPoly (n + 1)) fp.u i'.succ j'.succ
              = 20 * ((n : ℝ) + 1) * fp.u
                  * (|A i'.succ j'.succ|
                      + |fp.fl_div (A i'.succ 0) (A 0 0)| * |A 0 0|
                          * |fp.fl_div (A j'.succ 0) (A 0 0)|
                      + higham11_4_bunchKaufmanProductEntry n
                          (flAllOneByOneL fp n (flSchurCompl n fp A))
                          (flAllOneByOneD fp n (flSchurCompl n fp A)) i' j') := by
            simp only [higham11_3_printedFirstOrderBound, pPoly, id_eq]
            rw [productEntry_succ_split]
            push_cast; ring
          have hBs : flBlockLDLTAllOneByOneBound fp n (flSchurCompl n fp A) i' j'
              ≤ 20 * (n : ℝ) * fp.u
                  * (|flSchurCompl n fp A i' j'|
                      + higham11_4_bunchKaufmanProductEntry n
                          (flAllOneByOneL fp n (flSchurCompl n fp A))
                          (flAllOneByOneD fp n (flSchurCompl n fp A)) i' j') := by
            have hih := ih (flSchurCompl n fp A) hsmall' hpS i' j'
            simpa [higham11_3_printedFirstOrderBound, pPoly, id_eq] using hih
          rw [hLHS, hRHS]
          exact trailing_arith fp.u (n : ℝ)
            (|A i'.succ j'.succ|)
            (|A i'.succ 0 * A 0 j'.succ / A 0 0|)
            (|fp.fl_div (A i'.succ 0) (A 0 0)| * |A 0 0|
              * |fp.fl_div (A j'.succ 0) (A 0 0)|)
            (higham11_4_bunchKaufmanProductEntry n
              (flAllOneByOneL fp n (flSchurCompl n fp A))
              (flAllOneByOneD fp n (flSchurCompl n fp A)) i' j')
            (|flSchurCompl n fp A i' j'|)
            (gamma fp 3)
            (flBlockLDLTAllOneByOneBound fp n (flSchurCompl n fp A) i' j')
            hu0 hu100 (Nat.cast_nonneg n) hsmall'
            (abs_nonneg _) (abs_nonneg _)
            (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
            (higham11_4_bunchKaufmanProductEntry_nonneg _ _ _ _ _)
            (abs_nonneg _)
            (gamma_nonneg fp hval)
            (gamma_three_le fp (by linarith))
            (schur_entry_upper fp hu0 n A i' j' ha)
            (schur_pivot_product_lower fp (by linarith) n A i' j' ha (hsym1 j'))
            hBs

/-! ## Step 4 — the honest printed-strength all-1×1 backward-error theorem -/

/-- **Theorem 11.3, all-1×1-pivot (σ = id) case, printed first-order strength.**
    For a symmetric input whose rounded all-1×1-pivot block-LDLᵀ path has nonzero
    successive pivots (and, at each stage, matching active first row/column),
    under the smallness `n·u ≤ 1/100` there are computed factors `L̂, D̂` and
    backward-error matrices `ΔA₁, ΔA₂` with

      `L̂D̂L̂ᵀ = A + ΔA₁`,   `|ΔAₖ| ≤ p(n)·u·(|A| + |L̂||D̂||L̂ᵀ|)`,

    the printed Higham (11.5) envelope with linear polynomial `p(n) = 20 n`.
    Everything is derived from the floating-point model. -/
theorem higham11_3_block_ldlt_all_oneByOne_printed (fp : FPModel)
    (hval : gammaValid fp 3) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hp : FlAllOneSymmetricPivots fp n A) :
    ∃ L D ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA1 i j|
          ≤ higham11_3_printedFirstOrderBound n A L D id (pPoly n) fp.u i j) ∧
      (∀ i j, |ΔA2 i j|
          ≤ higham11_3_printedFirstOrderBound n A L D id (pPoly n) fp.u i j) ∧
      (∀ i j, (∑ k₁, ∑ k₂, L i k₁ * D k₁ k₂ * L j k₂) = A i j + ΔA1 i j) := by
  refine ⟨flAllOneByOneL fp n A, flAllOneByOneD fp n A,
    fun i j => (∑ k₁, ∑ k₂, flAllOneByOneL fp n A i k₁ * flAllOneByOneD fp n A k₁ k₂
        * flAllOneByOneL fp n A j k₂) - A i j,
    0, ?_, ?_, ?_⟩
  · intro i j
    exact le_trans (flAllOneByOne_factorization_bound fp hval n A hp i j)
      (flAllOneByOne_envelope_le_printed fp hval n A hsmall hp i j)
  · intro i j
    simp only [Pi.zero_apply, abs_zero]
    exact higham11_3_printedFirstOrderBound_nonneg n A
      (flAllOneByOneL fp n A) (flAllOneByOneD fp n A) id (pPoly n) fp.u
      (mul_nonneg (by unfold pPoly; positivity) fp.u_nonneg) i j
  · intro i j; ring

end NumStability.Ch11Closure
