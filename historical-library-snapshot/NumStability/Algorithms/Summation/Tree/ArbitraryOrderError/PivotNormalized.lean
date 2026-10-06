import NumStability.Algorithms.Summation.Tree.Core
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# PivotNormalized

Retained R03 owner (reusable): every declaration stays at this exact path
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

/-- The empty / unit Stewart counter: `1 = <m>` for any `m`. -/
lemma higham8_relErrorCounter_one (fp : FPModel) (m : ℕ) :
    relErrorCounter fp m 1 := by
  refine ⟨fun _ => 0, fun _ => false, fun _ => by simpa using fp.u_nonneg, ?_⟩
  simp

/-- A single local rounding factor is a `<1>` counter. -/
lemma higham8_relErrorCounter_single (fp : FPModel) {δ : ℝ} (hδ : |δ| ≤ fp.u) :
    relErrorCounter fp 1 (1 + δ) := by
  refine ⟨fun _ => δ, fun _ => false, fun _ => hδ, ?_⟩
  simp

/-- Counters can be padded with trivial unit factors: `<k>` is also a `<k'>`
counter whenever `k ≤ k'`. -/
lemma higham8_relErrorCounter_pad (fp : FPModel) {k k' : ℕ} (hk : k ≤ k') {c : ℝ}
    (hc : relErrorCounter fp k c) :
    relErrorCounter fp k' c := by
  have h := relErrorCounter_mul fp k (k' - k) c 1 hc
    (higham8_relErrorCounter_one fp (k' - k))
  rwa [mul_one, Nat.add_sub_cancel' hk] at h

/-- A `relErrorCounter` is a product of strictly positive factors, hence
positive. -/
lemma higham8_relErrorCounter_pos (fp : FPModel) {k : ℕ} {c : ℝ}
    (hc : relErrorCounter fp k c) (hu : fp.u < 1) : 0 < c := by
  rcases hc with ⟨δ, neg, hδ, hc_eq⟩
  rw [hc_eq]
  exact Finset.prod_pos (fun i _ => relErrorCounter_factor_pos fp (hδ i) hu)

-- ============================================================
-- Pivot-normalised summation-tree backward error
-- ============================================================

namespace SumTree

/-- **Pivot-normalised summation-tree backward error.**

For any `SumTree n` and any distinguished pivot leaf `p`, the computed tree sum
factors as
  `t.eval fp v = G * ∑ i, v i * (1 + θ i)`
where `G` is the `relErrorCounter` collecting the rounding factors on `p`'s root
path, the pivot itself is unperturbed (`θ p = 0`), and every other leaf carries a
perturbation bounded by `gamma (n-1)`.

This is the order-independent sharpening of `SumTree.backward_error`: after
dividing through by the pivot's factor `G`, the shared root-prefix factors cancel
and each leaf/pivot ratio collects at most `n-1` local factors. -/
theorem backward_error_pivot (fp : FPModel) {n : ℕ} (t : SumTree n) :
    ∀ (_ : gammaValid fp (n - 1)) (p : Fin n) (v : Fin n → ℝ),
      ∃ (G : ℝ) (θ : Fin n → ℝ),
        relErrorCounter fp (n - 1) G ∧
        θ p = 0 ∧
        (∀ i, |θ i| ≤ gamma fp (n - 1)) ∧
        t.eval fp v = G * ∑ i : Fin n, v i * (1 + θ i) := by
  induction t with
  | leaf =>
    intro ht p v
    refine ⟨1, fun _ => 0, higham8_relErrorCounter_one fp 0, rfl, ?_, ?_⟩
    · intro i; simpa using gamma_nonneg fp ht
    · simp [eval]
  | node l r ihl ihr =>
    rename_i m k
    intro ht p v
    -- `u < 1` from validity of `gamma (m+k-1)` (needs m+k ≥ 1, true since both ≥ 1)
    have hm1 : 1 ≤ m := l.n_pos
    have hk1 : 1 ≤ k := r.n_pos
    have hu : fp.u < 1 := by
      have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) ht
      unfold gammaValid at h1; simpa using h1
    -- depth/size facts
    have hml : l.depth ≤ m - 1 := l.depth_le
    have hmr : r.depth ≤ k - 1 := r.depth_le
    -- sub-validities
    have ht_lm : gammaValid fp (m - 1) := gammaValid_mono fp (by omega) ht
    have ht_km : gammaValid fp (k - 1) := gammaValid_mono fp (by omega) ht
    have ht_ld : gammaValid fp l.depth :=
      gammaValid_mono fp (le_trans hml (by omega)) ht
    have ht_rd : gammaValid fp r.depth :=
      gammaValid_mono fp (le_trans hmr (by omega)) ht
    have ht_1 : gammaValid fp 1 := gammaValid_mono fp (by omega) ht
    set vL : Fin m → ℝ := fun i => v (Fin.castAdd k i) with hvL
    set vR : Fin k → ℝ := fun i => v (Fin.natAdd m i) with hvR
    -- top-level rounding error of the final addition
    obtain ⟨δ, hδ, hflδ⟩ := fp.model_add (l.eval fp vL) (r.eval fp vR)
    -- We split on which subtree the pivot lives in.
    refine Fin.addCases ?_ ?_ p
    · -- pivot in the LEFT subtree
      intro pL
      obtain ⟨GL, θL, hGL, hθLp, hθLb, hLeq⟩ := ihl ht_lm pL vL
      obtain ⟨ηR, hηR, hReq⟩ := backward_error fp r ht_rd vR
      have hGLpos : 0 < GL := higham8_relErrorCounter_pos fp hGL hu
      -- new pivot factor: (1 + δ) * GL, a <m> counter, padded to <m+k-1>
      have hGnew : relErrorCounter fp (m + k - 1) ((1 + δ) * GL) := by
        have h1 : relErrorCounter fp (1 + (m - 1)) ((1 + δ) * GL) :=
          relErrorCounter_mul fp 1 (m - 1) (1 + δ) GL
            (higham8_relErrorCounter_single fp hδ) hGL
        exact higham8_relErrorCounter_pad fp (show m ≤ m + k - 1 by omega)
          (by rwa [show 1 + (m - 1) = m by omega] at h1)
      -- inverse of GL is an <m-1> counter
      have hGLinv : relErrorCounter fp (m - 1) (1 / GL) :=
        relErrorCounter_inv fp (m - 1) GL hGL hu
      have hGLinv_bd : |(1 / GL) - 1| ≤ gamma fp (m - 1) :=
        relErrorCounter_abs_sub_one_le_gamma fp (m - 1) (1 / GL) hGLinv ht_lm
      refine ⟨(1 + δ) * GL,
        Fin.addCases θL (fun j => (1 + ηR j) / GL - 1), hGnew, ?_, ?_, ?_⟩
      · -- pivot unperturbed
        simp [Fin.addCases_left, hθLp]
      · -- bounds
        intro i
        refine Fin.addCases ?_ ?_ i
        · intro j
          simp only [Fin.addCases_left]
          exact le_trans (hθLb j) (gamma_mono fp (show m - 1 ≤ m + k - 1 by omega) ht)
        · intro j
          simp only [Fin.addCases_right]
          -- (1 + ηR j)/GL - 1 = θ from gamma_mul with factors (1+ηR j) and (1/GL)
          have hηRj : |ηR j| ≤ gamma fp (k - 1) :=
            le_trans (hηR j) (gamma_mono fp hmr ht_km)
          obtain ⟨θ, hθ, heq⟩ :=
            gamma_mul fp (k - 1) (m - 1) (ηR j) ((1 / GL) - 1) hηRj hGLinv_bd
              (by
                have : (k - 1) + (m - 1) ≤ m + k - 1 := by omega
                exact gammaValid_mono fp this ht)
          have hval : (1 + ηR j) / GL - 1 = θ := by
            have : (1 + ηR j) * (1 + ((1 / GL) - 1)) = (1 + ηR j) / GL := by
              ring
            rw [← this, heq]; ring
          rw [hval]
          exact le_trans hθ (gamma_mono fp (show (k - 1) + (m - 1) ≤ m + k - 1 by omega) ht)
      · -- sum identity
        show fp.fl_add (l.eval fp vL) (r.eval fp vR) =
          (1 + δ) * GL * ∑ i : Fin (m + k), v i *
            (1 + Fin.addCases θL (fun j => (1 + ηR j) / GL - 1) i)
        rw [hflδ, hLeq, hReq, Fin.sum_univ_add]
        have hsplit :
            ∑ i : Fin m, v (Fin.castAdd k i) *
                (1 + Fin.addCases θL (fun j => (1 + ηR j) / GL - 1) (Fin.castAdd k i)) +
            ∑ j : Fin k, v (Fin.natAdd m j) *
                (1 + Fin.addCases θL (fun j => (1 + ηR j) / GL - 1) (Fin.natAdd m j)) =
            (∑ i : Fin m, vL i * (1 + θL i)) +
              (1 / GL) * ∑ j : Fin k, vR j * (1 + ηR j) := by
          rw [Finset.mul_sum]
          congr 1
          · apply Finset.sum_congr rfl; intro i _
            simp [Fin.addCases_left, hvL]
          · apply Finset.sum_congr rfl; intro j _
            rw [Fin.addCases_right]
            have : (1 + ((1 + ηR j) / GL - 1)) = (1 + ηR j) / GL := by ring
            rw [this, hvR]
            field_simp
        rw [hsplit]
        field_simp
    · -- pivot in the RIGHT subtree
      intro pR
      obtain ⟨GR, θR, hGR, hθRp, hθRb, hReq⟩ := ihr ht_km pR vR
      obtain ⟨ηL, hηL, hLeq⟩ := backward_error fp l ht_ld vL
      have hGRpos : 0 < GR := higham8_relErrorCounter_pos fp hGR hu
      have hGnew : relErrorCounter fp (m + k - 1) ((1 + δ) * GR) := by
        have h1 : relErrorCounter fp (1 + (k - 1)) ((1 + δ) * GR) :=
          relErrorCounter_mul fp 1 (k - 1) (1 + δ) GR
            (higham8_relErrorCounter_single fp hδ) hGR
        exact higham8_relErrorCounter_pad fp (show k ≤ m + k - 1 by omega)
          (by rwa [show 1 + (k - 1) = k by omega] at h1)
      have hGRinv : relErrorCounter fp (k - 1) (1 / GR) :=
        relErrorCounter_inv fp (k - 1) GR hGR hu
      have hGRinv_bd : |(1 / GR) - 1| ≤ gamma fp (k - 1) :=
        relErrorCounter_abs_sub_one_le_gamma fp (k - 1) (1 / GR) hGRinv ht_km
      refine ⟨(1 + δ) * GR,
        Fin.addCases (fun i => (1 + ηL i) / GR - 1) θR, hGnew, ?_, ?_, ?_⟩
      · simp [Fin.addCases_right, hθRp]
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro j
          simp only [Fin.addCases_left]
          have hηLj : |ηL j| ≤ gamma fp (m - 1) :=
            le_trans (hηL j) (gamma_mono fp hml ht_lm)
          obtain ⟨θ, hθ, heq⟩ :=
            gamma_mul fp (m - 1) (k - 1) (ηL j) ((1 / GR) - 1) hηLj hGRinv_bd
              (by
                have : (m - 1) + (k - 1) ≤ m + k - 1 := by omega
                exact gammaValid_mono fp this ht)
          have hval : (1 + ηL j) / GR - 1 = θ := by
            have : (1 + ηL j) * (1 + ((1 / GR) - 1)) = (1 + ηL j) / GR := by
              ring
            rw [← this, heq]; ring
          rw [hval]
          exact le_trans hθ (gamma_mono fp (show (m - 1) + (k - 1) ≤ m + k - 1 by omega) ht)
        · intro j
          simp only [Fin.addCases_right]
          exact le_trans (hθRb j) (gamma_mono fp (show k - 1 ≤ m + k - 1 by omega) ht)
      · show fp.fl_add (l.eval fp vL) (r.eval fp vR) =
          (1 + δ) * GR * ∑ i : Fin (m + k), v i *
            (1 + Fin.addCases (fun i => (1 + ηL i) / GR - 1) θR i)
        rw [hflδ, hLeq, hReq, Fin.sum_univ_add]
        have hsplit :
            ∑ i : Fin m, v (Fin.castAdd k i) *
                (1 + Fin.addCases (fun i => (1 + ηL i) / GR - 1) θR (Fin.castAdd k i)) +
            ∑ j : Fin k, v (Fin.natAdd m j) *
                (1 + Fin.addCases (fun i => (1 + ηL i) / GR - 1) θR (Fin.natAdd m j)) =
            (1 / GR) * (∑ i : Fin m, vL i * (1 + ηL i)) +
              ∑ j : Fin k, vR j * (1 + θR j) := by
          rw [Finset.mul_sum]
          congr 1
          · apply Finset.sum_congr rfl; intro i _
            rw [Fin.addCases_left]
            have : (1 + ((1 + ηL i) / GR - 1)) = (1 + ηL i) / GR := by ring
            rw [this, hvL]
            field_simp
          · apply Finset.sum_congr rfl; intro j _
            simp [Fin.addCases_right, hvR]
        rw [hsplit]
        field_simp

/-- Operation-count form of the summation-tree backward error.  In addition
to the usual equality, every leaf coefficient is exhibited as an actual
Stewart counter with at most `t.depth` factors.  This is the bookkeeping
needed for the no-division clause of Lemma 8.4: a rounded product at a leaf can
then be combined with the *relative* leaf/pivot counter without losing one
operation in the gamma index. -/
theorem backward_error_counter (fp : FPModel) {n : ℕ} (t : SumTree n)
    (v : Fin n → ℝ) :
    ∃ η : Fin n → ℝ,
      (∀ i, relErrorCounter fp t.depth (1 + η i)) ∧
      t.eval fp v = ∑ i : Fin n, v i * (1 + η i) := by
  induction t with
  | leaf =>
      refine ⟨fun _ => 0, ?_, by simp [eval]⟩
      intro i
      simpa using higham8_relErrorCounter_one fp 0
  | node l r ihl ihr =>
      rename_i m k
      let vL : Fin m → ℝ := fun i => v (Fin.castAdd k i)
      let vR : Fin k → ℝ := fun i => v (Fin.natAdd m i)
      obtain ⟨ηL, hηL, hLeq⟩ := ihl vL
      obtain ⟨ηR, hηR, hReq⟩ := ihr vR
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add (l.eval fp vL) (r.eval fp vR)
      let η : Fin (m + k) → ℝ :=
        Fin.addCases
          (fun i => ηL i + δ + ηL i * δ)
          (fun i => ηR i + δ + ηR i * δ)
      refine ⟨η, ?_, ?_⟩
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro j
          have hprod := relErrorCounter_mul fp l.depth 1
            (1 + ηL j) (1 + δ) (hηL j)
            (higham8_relErrorCounter_single fp hδ)
          have hpad : l.depth + 1 ≤ max l.depth r.depth + 1 := by omega
          have hcounter := higham8_relErrorCounter_pad fp hpad hprod
          simp only [η, Fin.addCases_left]
          convert hcounter using 1 <;> ring
        · intro j
          have hprod := relErrorCounter_mul fp r.depth 1
            (1 + ηR j) (1 + δ) (hηR j)
            (higham8_relErrorCounter_single fp hδ)
          have hpad : r.depth + 1 ≤ max l.depth r.depth + 1 := by omega
          have hcounter := higham8_relErrorCounter_pad fp hpad hprod
          simp only [η, Fin.addCases_right]
          convert hcounter using 1 <;> ring
      · show fp.fl_add (l.eval fp vL) (r.eval fp vR) =
          ∑ i : Fin (m + k), v i * (1 + η i)
        rw [hfl, hLeq, hReq, Fin.sum_univ_add]
        rw [add_mul, Finset.sum_mul, Finset.sum_mul]
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro i _
          simp [η, vL, Fin.addCases_left]
          ring
        · apply Finset.sum_congr rfl
          intro i _
          simp [η, vR, Fin.addCases_right]
          ring

/-- Sharp counter form of the pivot-normalised summation-tree theorem.

The pivot factor itself uses at most `n-1` rounding factors.  Relative to that
pivot, every leaf coefficient uses at most `n-2` factors (the common root
rounding cancels).  The latter count is the missing operation-count fact behind
Higham Lemma 8.4's special clause for `b_k = 1`. -/
theorem backward_error_pivot_counter (fp : FPModel) {n : ℕ} (t : SumTree n) :
    ∀ (_ : gammaValid fp (n - 1)) (p : Fin n) (v : Fin n → ℝ),
      ∃ (G : ℝ) (θ : Fin n → ℝ),
        relErrorCounter fp (n - 1) G ∧
        θ p = 0 ∧
        (∀ i, relErrorCounter fp (n - 2) (1 + θ i)) ∧
        t.eval fp v = G * ∑ i : Fin n, v i * (1 + θ i) := by
  induction t with
  | leaf =>
      intro ht p v
      refine ⟨1, fun _ => 0, higham8_relErrorCounter_one fp 0, rfl, ?_, ?_⟩
      · intro i
        simpa using higham8_relErrorCounter_one fp 0
      · simp [eval]
  | node l r ihl ihr =>
      rename_i m k
      intro ht p v
      have hm1 : 1 ≤ m := l.n_pos
      have hk1 : 1 ≤ k := r.n_pos
      have hu : fp.u < 1 := by
        have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) ht
        unfold gammaValid at h1
        simpa using h1
      have ht_l : gammaValid fp (m - 1) := gammaValid_mono fp (by omega) ht
      have ht_r : gammaValid fp (k - 1) := gammaValid_mono fp (by omega) ht
      let vL : Fin m → ℝ := fun i => v (Fin.castAdd k i)
      let vR : Fin k → ℝ := fun i => v (Fin.natAdd m i)
      obtain ⟨ηL, hηL, hLeq0⟩ := backward_error_counter fp l vL
      obtain ⟨ηR, hηR, hReq0⟩ := backward_error_counter fp r vR
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add (l.eval fp vL) (r.eval fp vR)
      refine Fin.addCases ?_ ?_ p
      · intro pL
        obtain ⟨GL, θL, hGL, hθLp, hθLc, hLeq⟩ := ihl ht_l pL vL
        have hGLpos : 0 < GL := higham8_relErrorCounter_pos fp hGL hu
        have hGnew0 : relErrorCounter fp m ((1 + δ) * GL) := by
          have hprod := relErrorCounter_mul fp 1 (m - 1)
            (1 + δ) GL (higham8_relErrorCounter_single fp hδ) hGL
          simpa [show 1 + (m - 1) = m by omega] using hprod
        have hGnew : relErrorCounter fp (m + k - 1) ((1 + δ) * GL) :=
          higham8_relErrorCounter_pad fp (by omega) hGnew0
        have hGLinv : relErrorCounter fp (m - 1) (1 / GL) :=
          relErrorCounter_inv fp (m - 1) GL hGL hu
        let θ : Fin (m + k) → ℝ :=
          Fin.addCases θL (fun j => (1 + ηR j) / GL - 1)
        refine ⟨(1 + δ) * GL, θ, hGnew, ?_, ?_, ?_⟩
        · simp [θ, Fin.addCases_left, hθLp]
        · intro i
          refine Fin.addCases ?_ ?_ i
          · intro j
            have hpad : m - 2 ≤ m + k - 2 := by omega
            simpa [θ, Fin.addCases_left] using
              (higham8_relErrorCounter_pad fp hpad (hθLc j))
          · intro j
            have hRpad : relErrorCounter fp (k - 1) (1 + ηR j) :=
              higham8_relErrorCounter_pad fp (r.depth_le) (hηR j)
            have hprod := relErrorCounter_mul fp (k - 1) (m - 1)
              (1 + ηR j) (1 / GL) hRpad hGLinv
            have hcount : (k - 1) + (m - 1) = m + k - 2 := by omega
            rw [hcount] at hprod
            simpa [θ, Fin.addCases_right, div_eq_mul_inv] using hprod
        · show fp.fl_add (l.eval fp vL) (r.eval fp vR) =
            (1 + δ) * GL * ∑ i : Fin (m + k), v i * (1 + θ i)
          rw [hfl, hLeq, hReq0, Fin.sum_univ_add]
          have hsplit :
              (∑ i : Fin m, v (Fin.castAdd k i) * (1 + θ (Fin.castAdd k i))) +
                (∑ j : Fin k, v (Fin.natAdd m j) * (1 + θ (Fin.natAdd m j))) =
              (∑ i : Fin m, vL i * (1 + θL i)) +
                (1 / GL) * ∑ j : Fin k, vR j * (1 + ηR j) := by
            rw [Finset.mul_sum]
            congr 1
            · apply Finset.sum_congr rfl
              intro i _
              simp [θ, vL, Fin.addCases_left]
            · apply Finset.sum_congr rfl
              intro j _
              simp [θ, vR, Fin.addCases_right]
              field_simp [ne_of_gt hGLpos]
          rw [hsplit]
          field_simp [ne_of_gt hGLpos]
      · intro pR
        obtain ⟨GR, θR, hGR, hθRp, hθRc, hReq⟩ := ihr ht_r pR vR
        have hGRpos : 0 < GR := higham8_relErrorCounter_pos fp hGR hu
        have hGnew0 : relErrorCounter fp k ((1 + δ) * GR) := by
          have hprod := relErrorCounter_mul fp 1 (k - 1)
            (1 + δ) GR (higham8_relErrorCounter_single fp hδ) hGR
          simpa [show 1 + (k - 1) = k by omega] using hprod
        have hGnew : relErrorCounter fp (m + k - 1) ((1 + δ) * GR) :=
          higham8_relErrorCounter_pad fp (by omega) hGnew0
        have hGRinv : relErrorCounter fp (k - 1) (1 / GR) :=
          relErrorCounter_inv fp (k - 1) GR hGR hu
        let θ : Fin (m + k) → ℝ :=
          Fin.addCases (fun i => (1 + ηL i) / GR - 1) θR
        refine ⟨(1 + δ) * GR, θ, hGnew, ?_, ?_, ?_⟩
        · simp [θ, Fin.addCases_right, hθRp]
        · intro i
          refine Fin.addCases ?_ ?_ i
          · intro j
            have hLpad : relErrorCounter fp (m - 1) (1 + ηL j) :=
              higham8_relErrorCounter_pad fp (l.depth_le) (hηL j)
            have hprod := relErrorCounter_mul fp (m - 1) (k - 1)
              (1 + ηL j) (1 / GR) hLpad hGRinv
            have hcount : (m - 1) + (k - 1) = m + k - 2 := by omega
            rw [hcount] at hprod
            simpa [θ, Fin.addCases_left, div_eq_mul_inv] using hprod
          · intro j
            have hpad : k - 2 ≤ m + k - 2 := by omega
            simpa [θ, Fin.addCases_right] using
              (higham8_relErrorCounter_pad fp hpad (hθRc j))
        · show fp.fl_add (l.eval fp vL) (r.eval fp vR) =
            (1 + δ) * GR * ∑ i : Fin (m + k), v i * (1 + θ i)
          rw [hfl, hLeq0, hReq, Fin.sum_univ_add]
          have hsplit :
              (∑ i : Fin m, v (Fin.castAdd k i) * (1 + θ (Fin.castAdd k i))) +
                (∑ j : Fin k, v (Fin.natAdd m j) * (1 + θ (Fin.natAdd m j))) =
              (1 / GR) * (∑ i : Fin m, vL i * (1 + ηL i)) +
                ∑ j : Fin k, vR j * (1 + θR j) := by
            rw [Finset.mul_sum]
            congr 1
            · apply Finset.sum_congr rfl
              intro i _
              simp [θ, vL, Fin.addCases_left]
              field_simp [ne_of_gt hGRpos]
            · apply Finset.sum_congr rfl
              intro j _
              simp [θ, vR, Fin.addCases_right]
          rw [hsplit]
          field_simp [ne_of_gt hGRpos]

end SumTree

-- ============================================================
-- Lemma 8.4: order-independent backward error of `(c - Σ aᵢbᵢ)/bₖ`
-- ============================================================









































































































































































































































-- ============================================================
-- Theorem 8.5: arbitrary-order back-substitution model
-- ============================================================



































































































































































































-- ============================================================
-- Theorem 8.5: arbitrary-order forward-substitution model
-- ============================================================














































































































































































end NumStability
