import NumStability.Algorithms.Summation.Tree.ArbitraryOrderError.PivotNormalized
import NumStability.Algorithms.Summation.Tree.Core
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# ArbitraryOrder

Retained R03 owner (source): every declaration stays at this exact path
under the frozen B0005 route; wave R03 adds this module docstring only.
-/


-- Algorithms/TriangularArbitraryOrder.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed., Chapter 8.
--
-- Split 2 primary labels Lemma 8.4 and Theorem 8.5: substitution backward error
-- that holds for *any* evaluation order of the inner sum.  The sharp constant
-- `gamma_k` (k = number of summands) is obtained from the Split 1 summation-tree
-- foundation (`SumTree`, Higham Algorithm 4.1) together with the Split 1
-- signed-product calculus (`relErrorCounter`, Higham Lemma 3.1).
--
-- The key new device is a *pivot-normalised* summation-tree backward error:
-- relative to one distinguished leaf `p`, the computed tree sum factors as
-- `G * ∑ v i (1 + θ i)` where `G` is the product of the rounding factors on
-- `p`'s root path (a `relErrorCounter`) and every `θ i` is bounded by
-- `gamma (n-1)`.  The shared root-prefix factors cancel in the leaf/pivot ratio,
-- which is exactly Higham's "divide through by the shared `(1 + δ)` factors"
-- step and is what keeps the constant at `gamma (n-1)` rather than `gamma (2n)`.



namespace NumStability

open scoped BigOperators

-- ============================================================
-- relErrorCounter helpers (Stewart `<k>` counters)
-- ============================================================






























-- ============================================================
-- Pivot-normalised summation-tree backward error
-- ============================================================

namespace SumTree





















































































































































































































































































































































































end SumTree

-- ============================================================
-- Lemma 8.4: order-independent backward error of `(c - Σ aᵢbᵢ)/bₖ`
-- ============================================================

/-- **Higham, 2nd ed., Lemma 8.4.**

Let `ŷ = fl((s)/bₖ)` where `s = ∑ wᵢ` is the computed value of the `n`-term sum
`∑ wᵢ` formed in floating-point arithmetic in *any* order (encoded by an
arbitrary summation tree `t`), and let `p` index the distinguished summand kept
unperturbed (Higham's `c`, the right-hand side).  Then there are relative
perturbations, all bounded by `γ_n`, with the pivot summand unperturbed, such
that
  `bₖ · ŷ · (1 + θ₀) = ∑ᵢ wᵢ (1 + θᵢ)`,   `θ p = 0`.

This is the order-independent backward-error identity (8.1 generalised): regardless
of the evaluation order, the computed quotient solves a relatively perturbed
version of the exact expression with the unperturbed summand `w p` on the right.
The sharp constant `γ_n` (= `γ_k` for `k` summands) follows from the
pivot-normalised tree backward error, whose shared root-prefix factors cancel. -/
theorem higham8_4_anyOrder (fp : FPModel) {n : ℕ} (t : SumTree n)
    (ht : gammaValid fp n) (w : Fin n → ℝ) (p : Fin n)
    (bk : ℝ) (hbk : bk ≠ 0) :
    ∃ (θ₀ : ℝ) (θ : Fin n → ℝ),
      |θ₀| ≤ gamma fp n ∧
      θ p = 0 ∧
      (∀ i, |θ i| ≤ gamma fp n) ∧
      bk * fp.fl_div (t.eval fp w) bk * (1 + θ₀) = ∑ i : Fin n, w i * (1 + θ i) := by
  have hn1 : 1 ≤ n := t.n_pos
  have ht_n1 : gammaValid fp (n - 1) := gammaValid_mono fp (by omega) ht
  have hu : fp.u < 1 := by
    have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) ht
    unfold gammaValid at h1; simpa using h1
  -- pivot-normalised backward error of the computed sum
  obtain ⟨G, θ, hG, hθp, hθb, hGeq⟩ := SumTree.backward_error_pivot fp t ht_n1 p w
  -- rounding error of the final division
  obtain ⟨δ, hδ, hfldiv⟩ := fp.model_div (t.eval fp w) bk hbk
  -- the divisor-side counter H = G * (1 + δ)
  set H : ℝ := G * (1 + δ) with hH
  have hHcounter : relErrorCounter fp n H := by
    have h1 : relErrorCounter fp ((n - 1) + 1) (G * (1 + δ)) :=
      relErrorCounter_mul fp (n - 1) 1 G (1 + δ) hG
        (higham8_relErrorCounter_single fp hδ)
    rwa [show (n - 1) + 1 = n by omega] at h1
  have hHpos : 0 < H := higham8_relErrorCounter_pos fp hHcounter hu
  -- inverse counter and its bound
  have hHinv : relErrorCounter fp n (1 / H) := relErrorCounter_inv fp n H hHcounter hu
  have hHinv_bd : |(1 / H) - 1| ≤ gamma fp n :=
    relErrorCounter_abs_sub_one_le_gamma fp n (1 / H) hHinv ht
  refine ⟨(1 / H) - 1, θ, hHinv_bd, hθp,
    fun i => le_trans (hθb i) (gamma_mono fp (by omega) ht), ?_⟩
  -- bk * ŷ = H * (G⁻¹-cleared) ... compute directly
  have hbky : bk * fp.fl_div (t.eval fp w) bk = H * ∑ i : Fin n, w i * (1 + θ i) := by
    rw [hfldiv, hGeq]
    field_simp
    ring
  rw [hbky]
  have : (1 + ((1 / H) - 1)) = 1 / H := by ring
  rw [this]
  field_simp

/-- Sharp no-division form of Higham Lemma 8.4, with the operation counters
retained for subsequent composition.

For an arbitrary evaluation order of
`c - ∑ q, a q * x q`, the correction on the computed sum and every product
coefficient use at most `m` rounding factors.  This is the special `bₖ = 1`
clause used in Higham Problem 10.3. -/
theorem higham8_4_anyOrder_mulSub_noDiv_counter (fp : FPModel) {m : ℕ}
    (t : SumTree (m + 1)) (ht : gammaValid fp m) (hu : fp.u < 1)
    (c : ℝ) (a x : Fin m → ℝ) :
    let w : Fin (m + 1) → ℝ :=
      Fin.cases c (fun q => - fp.fl_mul (a q) (x q))
    ∃ (θ₀ : ℝ) (η : Fin m → ℝ),
      relErrorCounter fp m (1 + θ₀) ∧
      |θ₀| ≤ gamma fp m ∧
      (∀ q, relErrorCounter fp m (1 + η q)) ∧
      (∀ q, |η q| ≤ gamma fp m) ∧
      t.eval fp w * (1 + θ₀) =
        c - ∑ q : Fin m, a q * x q * (1 + η q) := by
  intro w
  obtain ⟨G, θ, hG, hθ0, hθc, hGeq⟩ :=
    SumTree.backward_error_pivot_counter fp t (by simpa using ht)
      (0 : Fin (m + 1)) w
  have hGpos : 0 < G := higham8_relErrorCounter_pos fp hG hu
  have hGinv : relErrorCounter fp m (1 / G) :=
    relErrorCounter_inv fp m G (by simpa using hG) hu
  have hθ0counter : relErrorCounter fp m (1 + (1 / G - 1)) := by
    convert hGinv using 1 <;> ring
  have hθ0bd : |1 / G - 1| ≤ gamma fp m :=
    relErrorCounter_abs_sub_one_le_gamma fp m (1 / G) hGinv ht
  have hmul : ∀ q : Fin m, ∃ ε, |ε| ≤ fp.u ∧
      fp.fl_mul (a q) (x q) = a q * x q * (1 + ε) :=
    fun q => fp.model_mul (a q) (x q)
  let ε : Fin m → ℝ := fun q => Classical.choose (hmul q)
  have hεbd : ∀ q, |ε q| ≤ fp.u := fun q =>
    (Classical.choose_spec (hmul q)).1
  have hεeq : ∀ q, fp.fl_mul (a q) (x q) = a q * x q * (1 + ε q) :=
    fun q => (Classical.choose_spec (hmul q)).2
  let η : Fin m → ℝ := fun q => (1 + ε q) * (1 + θ q.succ) - 1
  have hηcounter : ∀ q, relErrorCounter fp m (1 + η q) := by
    intro q
    have hm1 : 1 ≤ m := by
      have hq := q.isLt
      omega
    have hprod := relErrorCounter_mul fp 1 (m - 1)
      (1 + ε q) (1 + θ q.succ)
      (higham8_relErrorCounter_single fp (hεbd q)) (hθc q.succ)
    have hcount : 1 + (m - 1) = m := by omega
    rw [hcount] at hprod
    convert hprod using 1 <;> simp [η] <;> ring
  have hηbd : ∀ q, |η q| ≤ gamma fp m := fun q => by
    simpa using
      (relErrorCounter_abs_sub_one_le_gamma fp m (1 + η q) (hηcounter q) ht)
  refine ⟨1 / G - 1, η, hθ0counter, hθ0bd, hηcounter, hηbd, ?_⟩
  have hsum :
      (∑ i : Fin (m + 1), w i * (1 + θ i)) =
        c - ∑ q : Fin m, fp.fl_mul (a q) (x q) * (1 + θ q.succ) := by
    rw [Fin.sum_univ_succ]
    simp [w, hθ0, sub_eq_add_neg]
  have hsumProducts :
      c - ∑ q : Fin m, fp.fl_mul (a q) (x q) * (1 + θ q.succ) =
        c - ∑ q : Fin m, a q * x q * (1 + η q) := by
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    rw [hεeq q]
    simp only [η]
    ring
  rw [hGeq]
  have hInv : 1 + (1 / G - 1) = 1 / G := by ring
  rw [hInv]
  field_simp [ne_of_gt hGpos]
  exact hsum.trans hsumProducts

/-- **Product-aware arbitrary-order row identity.**

This is the form of Lemma 8.4 used by Theorem 8.5.  The summation tree has one
distinguished pivot summand `c` and `m` off-diagonal summands
`-fl(aᵢ*xᵢ)`.  After the final division by `bk`, the result satisfies

`bk * y * (1 + θ₀) = c - Σ aᵢ*xᵢ*(1 + ηᵢ)`

with every perturbation bounded by `γ_(m+1)`.  The off-diagonal constant is
sharp: the pivot-normalised tree contributes at most `γ_m`, and the local
product rounding contributes one additional factor. -/
theorem higham8_4_anyOrder_mulSub_div (fp : FPModel) {m : ℕ}
    (t : SumTree (m + 1)) (ht : gammaValid fp (m + 1))
    (c bk : ℝ) (hbk : bk ≠ 0) (a x : Fin m → ℝ) :
    let w : Fin (m + 1) → ℝ :=
      Fin.cases c (fun q => - fp.fl_mul (a q) (x q))
    ∃ (θ₀ : ℝ) (η : Fin m → ℝ),
      |θ₀| ≤ gamma fp (m + 1) ∧
      (∀ q, |η q| ≤ gamma fp (m + 1)) ∧
      bk * fp.fl_div (t.eval fp w) bk * (1 + θ₀) =
        c - ∑ q : Fin m, a q * x q * (1 + η q) := by
  intro w
  have ht_m : gammaValid fp ((m + 1) - 1) := gammaValid_mono fp (by omega) ht
  have ht_m' : gammaValid fp m := by
    simpa using ht_m
  have hu : fp.u < 1 := by
    have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) ht
    unfold gammaValid at h1
    simpa using h1
  -- Pivot-normalised backward error for the arbitrary summation order.
  obtain ⟨G, θ, hG, hθ0, hθb, hGeq⟩ :=
    SumTree.backward_error_pivot fp t ht_m (0 : Fin (m + 1)) w
  -- Final division error.
  obtain ⟨δd, hδd, hdiv⟩ := fp.model_div (t.eval fp w) bk hbk
  -- The divisor-side counter is the tree pivot counter times the final division
  -- rounding factor.
  set H : ℝ := G * (1 + δd) with hH
  have hHcounter : relErrorCounter fp (m + 1) H := by
    have h1 : relErrorCounter fp (m + 1) (G * (1 + δd)) :=
      relErrorCounter_mul fp m 1 G (1 + δd) hG
        (higham8_relErrorCounter_single fp hδd)
    rwa [hH]
  have hHpos : 0 < H := higham8_relErrorCounter_pos fp hHcounter hu
  have hHinv : relErrorCounter fp (m + 1) (1 / H) :=
    relErrorCounter_inv fp (m + 1) H hHcounter hu
  have hHinv_bd : |(1 / H) - 1| ≤ gamma fp (m + 1) :=
    relErrorCounter_abs_sub_one_le_gamma fp (m + 1) (1 / H) hHinv ht
  -- Product errors for the off-diagonal products.
  have hmul : ∀ q : Fin m, ∃ ε, |ε| ≤ fp.u ∧
      fp.fl_mul (a q) (x q) = a q * x q * (1 + ε) :=
    fun q => fp.model_mul (a q) (x q)
  let ε : Fin m → ℝ := fun q => Classical.choose (hmul q)
  have hε_bd : ∀ q, |ε q| ≤ fp.u := fun q => (Classical.choose_spec (hmul q)).1
  have hε_eq : ∀ q, fp.fl_mul (a q) (x q) = a q * x q * (1 + ε q) :=
    fun q => (Classical.choose_spec (hmul q)).2
  -- Combine each local product factor with the tree leaf/pivot factor.
  have hη_exists : ∀ q : Fin m, ∃ η, |η| ≤ gamma fp (m + 1) ∧
      (1 + ε q) * (1 + θ q.succ) = 1 + η := by
    intro q
    have hεγ : |ε q| ≤ gamma fp 1 :=
      le_trans (hε_bd q) (u_le_gamma fp one_pos (gammaValid_mono fp (by omega) ht))
    have hθγ : |θ q.succ| ≤ gamma fp m := by
      simpa using hθb q.succ
    obtain ⟨η, hη, hη_eq⟩ :=
      gamma_mul fp 1 m (ε q) (θ q.succ) hεγ hθγ
        (by simpa [Nat.add_comm] using ht)
    refine ⟨η, ?_, hη_eq⟩
    simpa [Nat.add_comm] using hη
  let η : Fin m → ℝ := fun q => Classical.choose (hη_exists q)
  have hη_bd : ∀ q, |η q| ≤ gamma fp (m + 1) := fun q =>
    (Classical.choose_spec (hη_exists q)).1
  have hη_eq : ∀ q, (1 + ε q) * (1 + θ q.succ) = 1 + η q := fun q =>
    (Classical.choose_spec (hη_exists q)).2
  refine ⟨(1 / H) - 1, η, hHinv_bd, hη_bd, ?_⟩
  have hsum :
      (∑ i : Fin (m + 1), w i * (1 + θ i)) =
        c - ∑ q : Fin m, fp.fl_mul (a q) (x q) * (1 + θ q.succ) := by
    rw [Fin.sum_univ_succ]
    have hzero : θ (0 : Fin (m + 1)) = 0 := hθ0
    simp [w, hzero, sub_eq_add_neg]
  have hsum_products :
      c - ∑ q : Fin m, fp.fl_mul (a q) (x q) * (1 + θ q.succ) =
        c - ∑ q : Fin m, a q * x q * (1 + η q) := by
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    rw [hε_eq q, ← hη_eq q]
    ring
  have hbky : bk * fp.fl_div (t.eval fp w) bk =
      H * ∑ i : Fin (m + 1), w i * (1 + θ i) := by
    rw [hdiv, hGeq]
    field_simp [hbk]
    ring
  rw [hbky]
  have hHfactor : 1 + (1 / H - 1) = 1 / H := by ring
  rw [hHfactor]
  have hcancel :
      (H * ∑ i : Fin (m + 1), w i * (1 + θ i)) * (1 / H) =
        ∑ i : Fin (m + 1), w i * (1 + θ i) := by
    field_simp [ne_of_gt hHpos]
  rw [hcancel, hsum, hsum_products]

-- ============================================================
-- Theorem 8.5: arbitrary-order back-substitution model
-- ============================================================

/-- Row terms for an arbitrary-order back-substitution row:

`bᵢ, -fl(Uᵢ,i+1*x̂ᵢ₊₁), ..., -fl(Uᵢ,n*x̂ₙ)`.

The summation order itself is supplied separately as a `SumTree`. -/
noncomputable def backSubAnyOrderRowTerms (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ) (i : Fin n) :
    Fin ((n - i.val - 1) + 1) → ℝ :=
  Fin.cases (b i) (fun q =>
    - fp.fl_mul (U i ⟨i.val + 1 + q.val, by omega⟩)
        (xhat ⟨i.val + 1 + q.val, by omega⟩))

/-- A concrete arbitrary-order back-substitution computation.  For each row `i`,
the caller supplies a summation tree over the row terms; the computed component
is the rounded division of that tree sum by the diagonal. -/
def BackSubAnyOrderSpec (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (rowTree : (i : Fin n) → SumTree ((n - i.val - 1) + 1)) : Prop :=
  ∀ i, xhat i =
    fp.fl_div ((rowTree i).eval fp (backSubAnyOrderRowTerms fp n U b xhat i)) (U i i)

/-- Per-row arbitrary-order backward-error identity for upper-triangular
substitution.  It is the row form of Higham Theorem 8.5: each row tree may use
any evaluation order, and the row still admits a `γ_n` componentwise
perturbation envelope. -/
theorem backSub_anyOrder_row_error (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (rowTree : (i : Fin n) → SumTree ((n - i.val - 1) + 1))
    (hU : ∀ i, U i i ≠ 0)
    (hn : gammaValid fp n)
    (hrow : BackSubAnyOrderSpec fp n U b xhat rowTree)
    (i : Fin n) :
    ∃ (θdiag : ℝ) (η : Fin (n - i.val - 1) → ℝ),
      |θdiag| ≤ gamma fp n ∧
      (∀ q, |η q| ≤ gamma fp n) ∧
      U i i * xhat i * (1 + θdiag) =
        b i - ∑ q : Fin (n - i.val - 1),
          U i ⟨i.val + 1 + q.val, by omega⟩ *
            xhat ⟨i.val + 1 + q.val, by omega⟩ * (1 + η q) := by
  set m := n - i.val - 1 with hm
  have hm1_le : m + 1 ≤ n := by
    have hi := i.isLt
    omega
  have hm1_valid : gammaValid fp (m + 1) := gammaValid_mono fp hm1_le hn
  let a : Fin m → ℝ := fun q => U i ⟨i.val + 1 + q.val, by omega⟩
  let x : Fin m → ℝ := fun q => xhat ⟨i.val + 1 + q.val, by omega⟩
  obtain ⟨θdiag, η, hθdiag, hη, heq⟩ :=
    higham8_4_anyOrder_mulSub_div fp (m := m) (rowTree i) hm1_valid
      (b i) (U i i) (hU i) a x
  refine ⟨θdiag, η, ?_, ?_, ?_⟩
  · exact le_trans hθdiag (gamma_mono fp hm1_le hn)
  · intro q
    exact le_trans (hη q) (gamma_mono fp hm1_le hn)
  · rw [hrow i]
    simpa [backSubAnyOrderRowTerms, a, x, hm] using heq

/-- **Higham Theorem 8.5, upper-triangular arbitrary-order form.**

If every row of back substitution is evaluated by an arbitrary summation tree
over the standard row terms and then divided by the diagonal, the resulting
vector is the exact solution of a componentwise perturbed upper-triangular
system `(U + ΔU)x̂ = b`, with `|ΔUᵢⱼ| ≤ γ_n |Uᵢⱼ|`. -/
theorem backSub_backward_error_anyOrder (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (rowTree : (i : Fin n) → SumTree ((n - i.val - 1) + 1))
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp n)
    (hrow : BackSubAnyOrderSpec fp n U b xhat rowTree) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i j, |ΔU i j| ≤ gamma fp n * |U i j|) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * xhat j = b i := by
  classical
  have h_rows : ∀ i : Fin n,
      ∃ (θdiag : ℝ) (η : Fin (n - i.val - 1) → ℝ),
        |θdiag| ≤ gamma fp n ∧
        (∀ q, |η q| ≤ gamma fp n) ∧
        U i i * xhat i * (1 + θdiag) =
          b i - ∑ q : Fin (n - i.val - 1),
            U i ⟨i.val + 1 + q.val, by omega⟩ *
              xhat ⟨i.val + 1 + q.val, by omega⟩ * (1 + η q) :=
    fun i => backSub_anyOrder_row_error fp n U b xhat rowTree hU hn hrow i
  let θdiag : Fin n → ℝ := fun i => Classical.choose (h_rows i)
  let η_data : (i : Fin n) → Fin (n - i.val - 1) → ℝ := fun i =>
    Classical.choose (Classical.choose_spec (h_rows i))
  have hθdiag_bound : ∀ i, |θdiag i| ≤ gamma fp n := fun i =>
    (Classical.choose_spec (Classical.choose_spec (h_rows i))).1
  have hη_bound : ∀ i q, |η_data i q| ≤ gamma fp n := fun i q =>
    (Classical.choose_spec (Classical.choose_spec (h_rows i))).2.1 q
  have hrow_eq : ∀ i,
      U i i * xhat i * (1 + θdiag i) =
        b i - ∑ q : Fin (n - i.val - 1),
          U i ⟨i.val + 1 + q.val, by omega⟩ *
            xhat ⟨i.val + 1 + q.val, by omega⟩ * (1 + η_data i q) := fun i =>
    (Classical.choose_spec (Classical.choose_spec (h_rows i))).2.2
  let ΔU : Fin n → Fin n → ℝ := fun i j =>
    if hdiag : j.val = i.val then U i j * θdiag i
    else if hupper : i.val < j.val then
      U i j * η_data i ⟨j.val - (i.val + 1), by omega⟩
    else 0
  refine ⟨ΔU, ?_, ?_⟩
  · intro i j
    show |ΔU i j| ≤ gamma fp n * |U i j|
    simp only [ΔU]
    by_cases hdiag : j.val = i.val
    · simp only [hdiag, dite_true, abs_mul]
      rw [mul_comm (gamma fp n)]
      exact mul_le_mul_of_nonneg_left (hθdiag_bound i) (abs_nonneg _)
    · simp only [hdiag, dite_false]
      by_cases hupper : i.val < j.val
      · simp only [hupper, dite_true, abs_mul]
        rw [mul_comm (gamma fp n)]
        exact mul_le_mul_of_nonneg_left
          (hη_bound i ⟨j.val - (i.val + 1), by omega⟩) (abs_nonneg _)
      · simp only [hupper, dite_false, abs_zero]
        exact mul_nonneg (gamma_nonneg fp hn) (abs_nonneg _)
  · intro i
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => i.val ≤ j.val)]
    have hbelow_zero : Finset.sum
        (Finset.filter (fun j : Fin n => ¬(i.val ≤ j.val)) Finset.univ)
        (fun j => (U i j + ΔU i j) * xhat j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
      have hU_zero : U i j = 0 := hUT i j hj
      have hΔ_zero : ΔU i j = 0 := by
        simp only [ΔU]
        have hdiag : ¬ j.val = i.val := by omega
        have hupper : ¬ i.val < j.val := by omega
        simp [hdiag, hupper]
      rw [hU_zero, hΔ_zero, add_zero, zero_mul]
    rw [hbelow_zero, add_zero]
    have hrow_sum : U i i * xhat i * (1 + θdiag i) +
        (∑ q : Fin (n - i.val - 1),
          U i ⟨i.val + 1 + q.val, by omega⟩ *
            xhat ⟨i.val + 1 + q.val, by omega⟩ * (1 + η_data i q)) = b i := by
      linarith [hrow_eq i]
    rw [← hrow_sum]
    rw [← Finset.add_sum_erase _ _
      (by simp : i ∈ Finset.filter (fun j : Fin n => i.val ≤ j.val) Finset.univ)]
    have hdiag_term :
        (U i i + ΔU i i) * xhat i =
          U i i * xhat i * (1 + θdiag i) := by
      simp only [ΔU, dite_true]
      ring
    rw [hdiag_term]
    congr 1
    have hbound : ∀ q : Fin (n - i.val - 1), i.val + 1 + q.val < n := fun q => by
      have hi := i.isLt
      omega
    symm
    apply Finset.sum_nbij
      (fun (q : Fin (n - i.val - 1)) =>
        (⟨i.val + 1 + q.val, hbound q⟩ : Fin n))
    · intro q _
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by intro h; exact absurd (Fin.mk.inj h) (by omega), by omega⟩
    · intro q₁ _ q₂ _ h
      exact Fin.ext (by simp only [Fin.mk.injEq] at h; omega)
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_filter,
        Finset.mem_univ, true_and] at hj
      have hij : i.val < j.val := by
        by_cases heq : j.val = i.val
        · exfalso
          exact hj.1 (Fin.ext heq)
        · omega
      exact ⟨⟨j.val - (i.val + 1), by omega⟩, Finset.mem_univ _,
        Fin.ext (by simp; omega)⟩
    · intro q _
      show
        U i ⟨i.val + 1 + q.val, hbound q⟩ *
            xhat ⟨i.val + 1 + q.val, hbound q⟩ * (1 + η_data i q) =
          (U i ⟨i.val + 1 + q.val, hbound q⟩ +
              ΔU i ⟨i.val + 1 + q.val, hbound q⟩) *
            xhat ⟨i.val + 1 + q.val, hbound q⟩
      have hΔ :
          ΔU i ⟨i.val + 1 + q.val, hbound q⟩ =
            U i ⟨i.val + 1 + q.val, hbound q⟩ * η_data i q := by
        simp only [ΔU]
        rw [dif_neg (by omega : ¬(i.val + 1 + q.val = i.val)),
          dif_pos (by omega : i.val < i.val + 1 + q.val)]
        have hidx :
            (⟨(⟨i.val + 1 + q.val, hbound q⟩ : Fin n).val - (i.val + 1), by
                change i.val + 1 + q.val - (i.val + 1) < n - i.val - 1
                omega⟩ :
              Fin (n - i.val - 1)) = q := by
          apply Fin.ext
          change i.val + 1 + q.val - (i.val + 1) = q.val
          omega
        rw [hidx]
      rw [hΔ]
      ring

-- ============================================================
-- Theorem 8.5: arbitrary-order forward-substitution model
-- ============================================================

/-- Row terms for an arbitrary-order forward-substitution row:

`bᵢ, -fl(Lᵢ,0*x̂₀), ..., -fl(Lᵢ,i-1*x̂ᵢ₋₁)`.

The summation order itself is supplied separately as a `SumTree`. -/
noncomputable def forwardSubAnyOrderRowTerms (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ) (i : Fin n) :
    Fin (i.val + 1) → ℝ :=
  Fin.cases (b i) (fun q =>
    - fp.fl_mul (L i ⟨q.val, by omega⟩) (xhat ⟨q.val, by omega⟩))

/-- A concrete arbitrary-order forward-substitution computation.  For each row
`i`, the caller supplies a summation tree over the row terms; the computed
component is the rounded division of that tree sum by the diagonal. -/
def ForwardSubAnyOrderSpec (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (rowTree : (i : Fin n) → SumTree (i.val + 1)) : Prop :=
  ∀ i, xhat i =
    fp.fl_div ((rowTree i).eval fp (forwardSubAnyOrderRowTerms fp n L b xhat i)) (L i i)

/-- Per-row arbitrary-order backward-error identity for lower-triangular
substitution. -/
theorem forwardSub_anyOrder_row_error (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (rowTree : (i : Fin n) → SumTree (i.val + 1))
    (hL : ∀ i, L i i ≠ 0)
    (hn : gammaValid fp n)
    (hrow : ForwardSubAnyOrderSpec fp n L b xhat rowTree)
    (i : Fin n) :
    ∃ (θdiag : ℝ) (η : Fin i.val → ℝ),
      |θdiag| ≤ gamma fp n ∧
      (∀ q, |η q| ≤ gamma fp n) ∧
      L i i * xhat i * (1 + θdiag) =
        b i - ∑ q : Fin i.val,
          L i ⟨q.val, by omega⟩ * xhat ⟨q.val, by omega⟩ * (1 + η q) := by
  set m := i.val with hm
  have hm1_le : m + 1 ≤ n := by
    have hi := i.isLt
    omega
  have hm1_valid : gammaValid fp (m + 1) := gammaValid_mono fp hm1_le hn
  let a : Fin m → ℝ := fun q => L i ⟨q.val, by omega⟩
  let x : Fin m → ℝ := fun q => xhat ⟨q.val, by omega⟩
  obtain ⟨θdiag, η, hθdiag, hη, heq⟩ :=
    higham8_4_anyOrder_mulSub_div fp (m := m) (rowTree i) hm1_valid
      (b i) (L i i) (hL i) a x
  refine ⟨θdiag, η, ?_, ?_, ?_⟩
  · exact le_trans hθdiag (gamma_mono fp hm1_le hn)
  · intro q
    exact le_trans (hη q) (gamma_mono fp hm1_le hn)
  · rw [hrow i]
    simpa [forwardSubAnyOrderRowTerms, a, x, hm] using heq

/-- **Higham Theorem 8.5, lower-triangular arbitrary-order form.**

If every row of forward substitution is evaluated by an arbitrary summation tree
over the standard row terms and then divided by the diagonal, the resulting
vector is the exact solution of a componentwise perturbed lower-triangular
system `(L + ΔL)x̂ = b`, with `|ΔLᵢⱼ| ≤ γ_n |Lᵢⱼ|`. -/
theorem forwardSub_backward_error_anyOrder (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (rowTree : (i : Fin n) → SumTree (i.val + 1))
    (hL : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : gammaValid fp n)
    (hrow : ForwardSubAnyOrderSpec fp n L b xhat rowTree) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i j, |ΔL i j| ≤ gamma fp n * |L i j|) ∧
      ∀ i, ∑ j : Fin n, (L i j + ΔL i j) * xhat j = b i := by
  classical
  have h_rows : ∀ i : Fin n,
      ∃ (θdiag : ℝ) (η : Fin i.val → ℝ),
        |θdiag| ≤ gamma fp n ∧
        (∀ q, |η q| ≤ gamma fp n) ∧
        L i i * xhat i * (1 + θdiag) =
          b i - ∑ q : Fin i.val,
            L i ⟨q.val, by omega⟩ * xhat ⟨q.val, by omega⟩ * (1 + η q) :=
    fun i => forwardSub_anyOrder_row_error fp n L b xhat rowTree hL hn hrow i
  let θdiag : Fin n → ℝ := fun i => Classical.choose (h_rows i)
  let η_data : (i : Fin n) → Fin i.val → ℝ := fun i =>
    Classical.choose (Classical.choose_spec (h_rows i))
  have hθdiag_bound : ∀ i, |θdiag i| ≤ gamma fp n := fun i =>
    (Classical.choose_spec (Classical.choose_spec (h_rows i))).1
  have hη_bound : ∀ i q, |η_data i q| ≤ gamma fp n := fun i q =>
    (Classical.choose_spec (Classical.choose_spec (h_rows i))).2.1 q
  have hrow_eq : ∀ i,
      L i i * xhat i * (1 + θdiag i) =
        b i - ∑ q : Fin i.val,
          L i ⟨q.val, by omega⟩ * xhat ⟨q.val, by omega⟩ * (1 + η_data i q) := fun i =>
    (Classical.choose_spec (Classical.choose_spec (h_rows i))).2.2
  let ΔL : Fin n → Fin n → ℝ := fun i j =>
    if hdiag : j.val = i.val then L i j * θdiag i
    else if hlower : j.val < i.val then
      L i j * η_data i ⟨j.val, by omega⟩
    else 0
  refine ⟨ΔL, ?_, ?_⟩
  · intro i j
    show |ΔL i j| ≤ gamma fp n * |L i j|
    simp only [ΔL]
    by_cases hdiag : j.val = i.val
    · simp only [hdiag, dite_true, abs_mul]
      rw [mul_comm (gamma fp n)]
      exact mul_le_mul_of_nonneg_left (hθdiag_bound i) (abs_nonneg _)
    · simp only [hdiag, dite_false]
      by_cases hlower : j.val < i.val
      · simp only [hlower, dite_true, abs_mul]
        rw [mul_comm (gamma fp n)]
        exact mul_le_mul_of_nonneg_left (hη_bound i ⟨j.val, by omega⟩) (abs_nonneg _)
      · simp only [hlower, dite_false, abs_zero]
        exact mul_nonneg (gamma_nonneg fp hn) (abs_nonneg _)
  · intro i
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => j.val ≤ i.val)]
    have habove_zero : Finset.sum
        (Finset.filter (fun j : Fin n => ¬(j.val ≤ i.val)) Finset.univ)
        (fun j => (L i j + ΔL i j) * xhat j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
      have hL_zero : L i j = 0 := hLT i j hj
      have hΔ_zero : ΔL i j = 0 := by
        simp only [ΔL]
        have hdiag : ¬ j.val = i.val := by omega
        have hlower : ¬ j.val < i.val := by omega
        simp [hdiag, hlower]
      rw [hL_zero, hΔ_zero, add_zero, zero_mul]
    rw [habove_zero, add_zero]
    have hrow_sum : L i i * xhat i * (1 + θdiag i) +
        (∑ q : Fin i.val,
          L i ⟨q.val, by omega⟩ * xhat ⟨q.val, by omega⟩ * (1 + η_data i q)) = b i := by
      linarith [hrow_eq i]
    rw [← hrow_sum]
    rw [← Finset.add_sum_erase _ _
      (by simp : i ∈ Finset.filter (fun j : Fin n => j.val ≤ i.val) Finset.univ)]
    have hdiag_term :
        (L i i + ΔL i i) * xhat i =
          L i i * xhat i * (1 + θdiag i) := by
      simp only [ΔL, dite_true]
      ring
    rw [hdiag_term]
    congr 1
    have hbound : ∀ q : Fin i.val, q.val < n := fun q => by
      have hi := i.isLt
      omega
    symm
    apply Finset.sum_nbij
      (fun (q : Fin i.val) => (⟨q.val, hbound q⟩ : Fin n))
    · intro q _
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by intro h; exact absurd (Fin.mk.inj h) (by omega), by omega⟩
    · intro q₁ _ q₂ _ h
      exact Fin.ext (by simp only [Fin.mk.injEq] at h; omega)
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_filter,
        Finset.mem_univ, true_and] at hj
      have hji : j.val < i.val := by
        by_cases heq : j.val = i.val
        · exfalso
          exact hj.1 (Fin.ext heq)
        · omega
      exact ⟨⟨j.val, hji⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
    · intro q _
      show
        L i ⟨q.val, hbound q⟩ * xhat ⟨q.val, hbound q⟩ * (1 + η_data i q) =
          (L i ⟨q.val, hbound q⟩ + ΔL i ⟨q.val, hbound q⟩) *
            xhat ⟨q.val, hbound q⟩
      have hΔ :
          ΔL i ⟨q.val, hbound q⟩ =
            L i ⟨q.val, hbound q⟩ * η_data i q := by
        simp only [ΔL]
        rw [dif_neg (by omega : ¬(q.val = i.val)),
          dif_pos (by omega : q.val < i.val)]
      rw [hΔ]
      ring

end NumStability
