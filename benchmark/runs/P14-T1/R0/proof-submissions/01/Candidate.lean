import Mathlib

namespace HighamBenchCandidate

/- The exact positive sum and the exponential values returned by the algorithm. -/
noncomputable def exactSum (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, Real.exp (x i)

noncomputable def computedExp (n : ℕ) (x δ : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (x i) * (1 + δ i)

/- The exact sum of the already computed exponential values. -/
noncomputable def exactComputedExpSum (n : ℕ) (x δ : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, computedExp n x δ i

/- Algorithm 3.1 accumulates the computed exponentials in increasing index
   order. Adding the first value to zero is exact; each subsequent addition
   has one relative rounding error. -/
noncomputable def computedSum (n : ℕ) (x δ ε : Fin n → ℝ) : ℝ :=
  (List.finRange n).foldl
    (fun acc i =>
      if i.val = 0 then computedExp n x δ i
      else (acc + computedExp n x δ i) * (1 + ε i)) 0

noncomputable def sumError (n : ℕ) (x δ ε : Fin n → ℝ) : ℝ :=
  (computedSum n x δ ε - exactComputedExpSum n x δ) +
    (exactComputedExpSum n x δ - exactSum n x)

private lemma roundedFold_bounds {α : Type*} (p w e : α → ℝ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hp : ∀ i, 0 ≤ p i)
    (hw : ∀ i, (1 - u) * p i ≤ w i ∧ w i ≤ (1 + u) * p i)
    (he : ∀ i, 1 - u ≤ 1 + e i ∧ 1 + e i ≤ 1 + u)
    (l : List α) (k : ℕ) (hk : 1 ≤ k) (A a : ℝ) (hA : 0 ≤ A)
    (ha : (1 - u) ^ k * A ≤ a ∧ a ≤ (1 + u) ^ k * A) :
    (1 - u) ^ (k + l.length) * (A + (l.map p).sum) ≤
      l.foldl (fun z i => (z + w i) * (1 + e i)) a ∧
    l.foldl (fun z i => (z + w i) * (1 + e i)) a ≤
      (1 + u) ^ (k + l.length) * (A + (l.map p).sum) := by
  induction l generalizing k A a with
  | nil => simpa using ha
  | cons i t ih =>
    have hq : 0 ≤ p i := hp i
    have hlowpow : (1 - u) ^ (k + 1) ≤ (1 - u) ^ 2 :=
      calc
        (1 - u) ^ (k + 1) = (1 - u) ^ 2 * (1 - u) ^ (k - 1) := by
          rw [← pow_add]; congr 1; omega
        _ ≤ (1 - u) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (by linarith) (by linarith))
            (sq_nonneg _)
        _ = (1 - u) ^ 2 := by ring
    have huppow : (1 + u) ^ 2 ≤ (1 + u) ^ (k + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hpowlo_nonneg : 0 ≤ (1 - u) ^ k := pow_nonneg (by linarith) _
    have hpowhi_nonneg : 0 ≤ (1 + u) ^ k := pow_nonneg (by linarith) _
    have hwl_nonneg : 0 ≤ w i := le_trans (mul_nonneg (by linarith) hq) (hw i).1
    have ha_nonneg : 0 ≤ a := le_trans (mul_nonneg hpowlo_nonneg hA) ha.1
    have hnewlo : (1 - u) ^ (k + 1) * (A + p i) ≤
        (a + w i) * (1 + e i) := by
      have hsum : (1 - u) ^ k * A + (1 - u) * p i ≤ a + w i :=
        add_le_add ha.1 (hw i).1
      have hmul := mul_le_mul_of_nonneg_right hsum (by linarith : 0 ≤ 1 - u)
      have hmul2 := mul_le_mul_of_nonneg_left (he i).1 (by positivity : 0 ≤ a + w i)
      have hpowmul := mul_le_mul_of_nonneg_right hlowpow hq
      rw [pow_succ]
      rw [pow_two] at hpowmul
      rw [pow_succ] at hpowmul
      nlinarith only [hmul, hmul2, hpowmul]
    have hnewhi : (a + w i) * (1 + e i) ≤
        (1 + u) ^ (k + 1) * (A + p i) := by
      have hsum : a + w i ≤ (1 + u) ^ k * A + (1 + u) * p i :=
        add_le_add ha.2 (hw i).2
      have hmul := mul_le_mul_of_nonneg_right hsum (by linarith : 0 ≤ 1 + u)
      have hmul2 := mul_le_mul_of_nonneg_left (he i).2 (by positivity : 0 ≤ a + w i)
      have hpowmul := mul_le_mul_of_nonneg_right huppow hq
      rw [pow_succ]
      rw [pow_two] at hpowmul
      rw [pow_succ] at hpowmul
      nlinarith only [hmul, hmul2, hpowmul]
    have hrec := ih (k + 1) (by omega) (A + p i) ((a + w i) * (1 + e i))
      (by positivity) ⟨hnewlo, hnewhi⟩
    simpa only [List.map_cons, List.sum_cons, List.length_cons, List.foldl_cons,
      add_assoc, add_comm, add_left_comm] using hrec

private lemma power_two_ge (m : ℕ) : (m : ℝ) + 1 ≤ (2 : ℝ) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ]
    push_cast
    nlinarith [show (0 : ℝ) ≤ m by positivity]

private lemma power_quadratic (m : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 + u) ^ m ≤ 1 + (m : ℝ) * u + ((2 : ℝ) ^ m - (m : ℝ) - 1) * u ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hC : 0 ≤ (2 : ℝ) ^ m - (m : ℝ) - 1 := by
      linarith [power_two_ge m]
    have hprod := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1 + u)
    have hrem : 0 ≤ ((2 : ℝ) ^ m - (m : ℝ) - 1) * u ^ 2 * (1 - u) :=
      mul_nonneg (mul_nonneg hC (sq_nonneg u)) (by linarith)
    rw [pow_succ, pow_succ]
    push_cast
    nlinarith [hprod, hrem]

private lemma computedSum_bounds (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (δ ε : Fin n → ℝ)
    (hδ : ∀ i, |δ i| ≤ u) (hε : ∀ i, |ε i| ≤ u) :
    (1 - u) ^ n * exactSum n x ≤ computedSum n x δ ε ∧
    computedSum n x δ ε ≤ (1 + u) ^ n * exactSum n x := by
  cases n with
  | zero => omega
  | succ m =>
    let p : Fin (m + 1) → ℝ := fun i => Real.exp (x i)
    let w : Fin (m + 1) → ℝ := computedExp (m + 1) x δ
    let t : List (Fin (m + 1)) := (List.finRange m).map Fin.succ
    have hp : ∀ i, 0 ≤ p i := fun i => Real.exp_nonneg _
    have hw : ∀ i, (1 - u) * p i ≤ w i ∧ w i ≤ (1 + u) * p i := by
      intro i
      dsimp [p, w, computedExp]
      rcases abs_le.mp (hδ i) with ⟨hlo, hhi⟩
      constructor
      · have h := mul_le_mul_of_nonneg_left
          (show 1 - u ≤ 1 + δ i by linarith) (Real.exp_nonneg (x i))
        nlinarith
      · have h := mul_le_mul_of_nonneg_left
          (show 1 + δ i ≤ 1 + u by linarith) (Real.exp_nonneg (x i))
        nlinarith
    have he : ∀ i : Fin (m + 1),
        1 - u ≤ 1 + ε i ∧ 1 + ε i ≤ 1 + u := by
      intro i
      rcases abs_le.mp (hε i) with ⟨hlo, hhi⟩
      constructor <;> linarith
    have hlist : ((List.finRange (m + 1)).map p).sum = exactSum (m + 1) x := by
      simp [exactSum, p, ← List.sum_toFinset _ (List.nodup_finRange (m + 1))]
    have hsum : p 0 + (t.map p).sum = exactSum (m + 1) x := by
      simpa [t, List.finRange_succ] using hlist
    have htail : ∀ (l : List (Fin m)) (a : ℝ),
        ((l.map Fin.succ).foldl
          (fun z i => if i.val = 0 then w i else (z + w i) * (1 + ε i)) a) =
        ((l.map Fin.succ).foldl (fun z i => (z + w i) * (1 + ε i)) a) := by
      intro l
      induction l with
      | nil => intro a; rfl
      | cons i tl ih =>
        intro a
        have hne : (Fin.succ i).val ≠ 0 := by simp
        simp only [List.map_cons, List.foldl_cons]
        rw [if_neg hne]
        exact ih _
    have hcomp : computedSum (m + 1) x δ ε =
        t.foldl (fun z i => (z + w i) * (1 + ε i)) (w 0) := by
      simp only [computedSum, List.finRange_succ, List.foldl_cons]
      simp only [Fin.val_zero, ↓reduceIte]
      exact htail (List.finRange m)  (w 0)
    have hfirst : (1 - u) ^ 1 * p 0 ≤ w 0 ∧ w 0 ≤ (1 + u) ^ 1 * p 0 := by
      simpa [pow_one] using hw 0
    have hbound := roundedFold_bounds p w ε u hu0 hu1 hp hw he t 1
      (by omega) (p 0) (w 0) (hp 0) hfirst
    have hlen : 1 + t.length = m + 1 := by simp [t]; omega
    simpa only [hcomp, hlen, hsum] using hbound

theorem target
    (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (δ ε : Fin n → ℝ)
    (hδ : ∀ i, |δ i| ≤ u)
    (hε : ∀ i, |ε i| ≤ u) :
    computedSum n x δ ε = exactSum n x + sumError n x δ ε ∧
      |sumError n x δ ε| ≤
        (((n + 1 : ℕ) : ℝ) * u + (2 : ℝ) ^ (n + 1) * u ^ 2) * exactSum n x := by
  let s := exactSum n x
  let sh := computedSum n x δ ε
  have hs : 0 ≤ s := by
    dsimp [s, exactSum]
    exact Finset.sum_nonneg (fun i _ => Real.exp_nonneg (x i))
  have hb := computedSum_bounds n hn x u hu0 hu1 δ ε hδ hε
  have hpowlo : (1 - u) ^ (n + 1) ≤ (1 - u) ^ n := by
    calc
      (1 - u) ^ (n + 1) = (1 - u) ^ n * (1 - u) := pow_succ _ _
      _ ≤ (1 - u) ^ n * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by linarith) _)
      _ = (1 - u) ^ n := by ring
  have hpowhi : (1 + u) ^ n ≤ (1 + u) ^ (n + 1) :=
    pow_le_pow_right₀ (by linarith) (Nat.le_succ n)
  have hbern : 1 - ((n + 1 : ℕ) : ℝ) * u ≤ (1 - u) ^ (n + 1) := by
    simpa [sub_eq_add_neg, mul_neg] using
      (one_add_mul_le_pow (a := -u) (by linarith : -2 ≤ -u) (n + 1))
  have hquad : (1 + u) ^ (n + 1) ≤
      1 + ((n + 1 : ℕ) : ℝ) * u + (2 : ℝ) ^ (n + 1) * u ^ 2 := by
    have h := power_quadratic (n + 1) u hu0 hu1
    have hnonneg : 0 ≤ (((n + 1 : ℕ) : ℝ) + 1) * u ^ 2 := by positivity
    nlinarith
  have hlow : (1 - ((n + 1 : ℕ) : ℝ) * u) * s ≤ sh := by
    calc
      _ ≤ (1 - u) ^ (n + 1) * s := mul_le_mul_of_nonneg_right hbern hs
      _ ≤ (1 - u) ^ n * s := mul_le_mul_of_nonneg_right hpowlo hs
      _ ≤ sh := hb.1
  have hhigh : sh ≤
      (1 + ((n + 1 : ℕ) : ℝ) * u + (2 : ℝ) ^ (n + 1) * u ^ 2) * s := by
    calc
      sh ≤ (1 + u) ^ n * s := hb.2
      _ ≤ (1 + u) ^ (n + 1) * s := mul_le_mul_of_nonneg_right hpowhi hs
      _ ≤ _ := mul_le_mul_of_nonneg_right hquad hs
  have hqnonneg : 0 ≤ ((2 : ℝ) ^ (n + 1) * u ^ 2) * s := by positivity
  have herr : sumError n x δ ε = sh - s := by
    dsimp [sumError, sh, s]
    ring
  constructor
  · rw [herr]
    dsimp [sh, s]
    ring
  · rw [herr]
    apply abs_le.mpr
    constructor <;> nlinarith [hlow, hhigh, hqnonneg]

end HighamBenchCandidate
