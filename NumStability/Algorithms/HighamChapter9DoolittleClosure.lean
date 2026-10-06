-- Algorithms/HighamChapter9DoolittleClosure.lean
-- Source-shaped executable closure for Higham Theorem 9.3.

import NumStability.Algorithms.HighamChapter9

namespace NumStability

open scoped BigOperators

private theorem higham9_mulSubFold_source_identity
    (fp : FPModel) (m : ℕ) (c : ℝ) (a x : Fin m → ℝ)
    (hm1 : gammaValid fp (m + 1)) :
    let rounded : Fin m → ℝ := fun t => fp.fl_mul (a t) (x t)
    let fold : ℝ :=
      Fin.foldl m (fun acc t => fp.fl_sub acc (rounded t)) c
    ∃ (β : ℝ) (η : Fin m → ℝ),
      |β| ≤ gamma fp m ∧
      (∀ t, |η t| ≤ gamma fp m) ∧
      c = fold * (1 + β) + ∑ t : Fin m, a t * x t * (1 + η t) := by
  dsimp only
  let exact : Fin m → ℝ := fun t => a t * x t
  let rounded : Fin m → ℝ := fun t => fp.fl_mul (a t) (x t)
  let fold : ℝ :=
    Fin.foldl m (fun acc t => fp.fl_sub acc (rounded t)) c
  have hm : gammaValid fp m :=
    gammaValid_mono fp (Nat.le_succ m) hm1
  have h1 : gammaValid fp 1 :=
    gammaValid_mono fp (by omega) hm1
  have hu : fp.u < 1 := by
    unfold gammaValid at h1
    simpa using h1
  obtain ⟨σ, hσ, hfold⟩ := fl_sub_fold_unroll fp m rounded c
  let P : ℝ := ∏ k : Fin m, (1 + σ k)
  have hP_pos : 0 < P := by
    exact prod_pos_of_u_bound fp m σ hσ hu
  have hP_ne : P ≠ 0 := hP_pos.ne'
  obtain ⟨β, hβ, hβ_eq⟩ := inv_prod_error_bound fp m σ hσ hu hm
  have hβP : (1 + β) * P = 1 := by
    change (1 + β) * (∏ k : Fin m, (1 + σ k)) = 1
    rw [← hβ_eq, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro k _
    have hk_pos : 0 < 1 + σ k := by
      linarith [neg_abs_le (σ k), hσ k]
    field_simp [hk_pos.ne']
  have hmul : ∀ t : Fin m, ∃ ε : ℝ,
      |ε| ≤ fp.u ∧ rounded t = exact t * (1 + ε) := by
    intro t
    simpa [rounded, exact] using fp.model_mul (a t) (x t)
  let ε : Fin m → ℝ := fun t => Classical.choose (hmul t)
  have hε_bd : ∀ t, |ε t| ≤ fp.u :=
    fun t => (Classical.choose_spec (hmul t)).1
  have hε_eq : ∀ t, rounded t = exact t * (1 + ε t) :=
    fun t => (Classical.choose_spec (hmul t)).2
  have hP_split : ∀ t : Fin m,
      P = (∏ k : Fin m, if k.val < t.val then (1 + σ k) else 1) *
          (∏ k : Fin m, if t.val ≤ k.val then (1 + σ k) else 1) := by
    intro t
    show (∏ k : Fin m, (1 + σ k)) = _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    by_cases h : k.val < t.val
    · simp [h, show ¬ t.val ≤ k.val from by omega]
    · simp [h, show t.val ≤ k.val from by omega]
  have hoff : ∀ t : Fin m, ∃ η : ℝ,
      |η| ≤ gamma fp m ∧
      rounded t *
          (∏ k : Fin m, if t.val ≤ k.val then (1 + σ k) else 1) =
        exact t * (1 + η) * P := by
    intro t
    let σhead : Fin t.val → ℝ := fun j => σ ⟨j.val, by omega⟩
    have hσhead : ∀ j, |σhead j| ≤ fp.u :=
      fun j => hσ ⟨j.val, by omega⟩
    have ht : gammaValid fp t.val :=
      gammaValid_mono fp (by omega) hm
    obtain ⟨α, hα, hα_eq⟩ :=
      inv_prod_error_bound fp t.val σhead hσhead hu ht
    have hhead_eq :
        (∏ k : Fin m, if k.val < t.val then (1 + σ k) else 1) =
          ∏ j : Fin t.val, (1 + σhead j) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun k : Fin m => k.val < t.val)]
      have hrest :
          ∏ k ∈ Finset.filter (fun k : Fin m => ¬ (k.val < t.val)) Finset.univ,
              (if k.val < t.val then (1 + σ k) else 1) = 1 := by
        apply Finset.prod_eq_one
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp [hk]
      rw [hrest, mul_one]
      have hfiltered :
          ∏ k ∈ Finset.filter (fun k : Fin m => k.val < t.val) Finset.univ,
              (if k.val < t.val then (1 + σ k) else 1) =
            ∏ k ∈ Finset.filter (fun k : Fin m => k.val < t.val) Finset.univ,
              (1 + σ k) := by
        apply Finset.prod_congr rfl
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp [hk]
      rw [hfiltered]
      symm
      apply Finset.prod_nbij (fun j => ⟨j.val, by omega⟩)
      · intro j _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · intro j₁ _ j₂ _ h
        exact Fin.ext (Fin.mk.inj h)
      · intro k hk
        simp at hk
        exact ⟨⟨k.val, hk⟩, Finset.mem_univ _, Fin.ext rfl⟩
      · intro j _
        simp only [σhead]
    have hα_cancel :
        (1 + α) *
            (∏ k : Fin m, if k.val < t.val then (1 + σ k) else 1) = 1 := by
      rw [hhead_eq, ← hα_eq, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro j _
      have hj_pos : 0 < 1 + σhead j := by
        linarith [neg_abs_le (σhead j), hσhead j]
      field_simp [hj_pos.ne']
    have hεγ : |ε t| ≤ gamma fp 1 :=
      le_trans (hε_bd t) (u_le_gamma fp one_pos h1)
    obtain ⟨η, hη, hη_eq⟩ :=
      gamma_mul fp 1 t.val (ε t) α hεγ hα
        (gammaValid_mono fp (by omega) hm)
    have hη_m : |η| ≤ gamma fp m :=
      le_trans hη (gamma_mono fp (by omega) hm)
    refine ⟨η, hη_m, ?_⟩
    have htail_eq :
        (1 + α) * P =
          ∏ k : Fin m, if t.val ≤ k.val then (1 + σ k) else 1 := by
      calc
        (1 + α) * P =
            (1 + α) *
              ((∏ k : Fin m, if k.val < t.val then (1 + σ k) else 1) *
                (∏ k : Fin m, if t.val ≤ k.val then (1 + σ k) else 1)) := by
                  rw [hP_split t]
        _ = ((1 + α) *
              (∏ k : Fin m, if k.val < t.val then (1 + σ k) else 1)) *
                (∏ k : Fin m, if t.val ≤ k.val then (1 + σ k) else 1) := by
                  ring
        _ = ∏ k : Fin m, if t.val ≤ k.val then (1 + σ k) else 1 := by
              rw [hα_cancel, one_mul]
    rw [hε_eq t, ← htail_eq, ← hη_eq]
    ring
  let η : Fin m → ℝ := fun t => Classical.choose (hoff t)
  have hη_bd : ∀ t, |η t| ≤ gamma fp m :=
    fun t => (Classical.choose_spec (hoff t)).1
  have hη_eq : ∀ t,
      rounded t *
          (∏ k : Fin m, if t.val ≤ k.val then (1 + σ k) else 1) =
        exact t * (1 + η t) * P :=
    fun t => (Classical.choose_spec (hoff t)).2
  have hfold' :
      fold = c * P -
        ∑ t : Fin m,
          rounded t *
            ∏ k : Fin m, if t.val ≤ k.val then (1 + σ k) else 1 := by
    simpa [fold, P] using hfold
  have hkey :
      c * P = fold +
        ∑ t : Fin m,
          rounded t *
            ∏ k : Fin m, if t.val ≤ k.val then (1 + σ k) else 1 := by
    rw [hfold']
    ring
  have hsource :
      c = fold * (1 + β) + ∑ t : Fin m, exact t * (1 + η t) := by
    calc
      c = c * ((1 + β) * P) := by rw [hβP, mul_one]
      _ = (c * P) * (1 + β) := by ring
      _ = (fold +
          ∑ t : Fin m,
            rounded t *
              ∏ k : Fin m, if t.val ≤ k.val then (1 + σ k) else 1) *
            (1 + β) := by rw [hkey]
      _ = fold * (1 + β) +
          ∑ t : Fin m,
            (rounded t *
              (∏ k : Fin m, if t.val ≤ k.val then (1 + σ k) else 1)) *
                (1 + β) := by rw [add_mul, Finset.sum_mul]
      _ = fold * (1 + β) + ∑ t : Fin m, exact t * (1 + η t) := by
        congr 1
        apply Finset.sum_congr rfl
        intro t _
        rw [hη_eq t]
        calc
          exact t * (1 + η t) * P * (1 + β) =
              exact t * (1 + η t) * ((1 + β) * P) := by ring
          _ = exact t * (1 + η t) := by rw [hβP, mul_one]
  refine ⟨β, η, hβ, hη_bd, ?_⟩
  simpa [fold, rounded, exact] using hsource

theorem higham9_2_flMulSubFold_source_residual_abs_le
    (fp : FPModel) (m : ℕ) (c : ℝ) (a x : Fin m → ℝ)
    (hm1 : gammaValid fp (m + 1)) :
    |(c - ∑ t : Fin m, a t * x t) -
        Fin.foldl m
          (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) c| ≤
      gamma fp m *
        ((∑ t : Fin m, |a t * x t|) +
          |Fin.foldl m
            (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) c|) := by
  let fold : ℝ :=
    Fin.foldl m (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) c
  obtain ⟨β, η, hβ, hη, hid⟩ :=
    higham9_mulSubFold_source_identity fp m c a x hm1
  have hsum :
      (∑ t : Fin m, a t * x t * (1 + η t)) =
        (∑ t : Fin m, a t * x t) + ∑ t : Fin m, (a t * x t) * η t := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hres :
      (c - ∑ t : Fin m, a t * x t) - fold =
        fold * β + ∑ t : Fin m, (a t * x t) * η t := by
    rw [hid, hsum]
    ring
  calc
    |(c - ∑ t : Fin m, a t * x t) -
        Fin.foldl m
          (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) c| =
        |fold * β + ∑ t : Fin m, (a t * x t) * η t| := by
          rw [hres]
    _ ≤ |fold * β| + |∑ t : Fin m, (a t * x t) * η t| := abs_add_le _ _
    _ ≤ |fold| * gamma fp m +
          ∑ t : Fin m, |a t * x t| * gamma fp m := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hβ (abs_nonneg _)
      · calc
          |∑ t : Fin m, (a t * x t) * η t| ≤
              ∑ t : Fin m, |(a t * x t) * η t| :=
                Finset.abs_sum_le_sum_abs _ _
          _ = ∑ t : Fin m, |a t * x t| * |η t| := by
                apply Finset.sum_congr rfl
                intro t _
                rw [abs_mul]
          _ ≤ ∑ t : Fin m, |a t * x t| * gamma fp m := by
                apply Finset.sum_le_sum
                intro t _
                exact mul_le_mul_of_nonneg_left (hη t) (abs_nonneg _)
    _ = gamma fp m *
        ((∑ t : Fin m, |a t * x t|) +
          |Fin.foldl m
            (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) c|) := by
      rw [← Finset.sum_mul]
      simp only [fold]
      ring

theorem higham9_2_flMulSubFold_div_source_residual_abs_le
    (fp : FPModel) (m : ℕ) (c bk : ℝ) (hbk : bk ≠ 0)
    (a x : Fin m → ℝ) (hm1 : gammaValid fp (m + 1)) :
    let fold : ℝ :=
      Fin.foldl m
        (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) c
    let y : ℝ := fp.fl_div fold bk
    |(c - ∑ t : Fin m, a t * x t) - y * bk| ≤
      gamma fp (m + 1) *
        ((∑ t : Fin m, |a t * x t|) + |y * bk|) := by
  dsimp only
  let fold : ℝ :=
    Fin.foldl m
      (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) c
  let y : ℝ := fp.fl_div fold bk
  obtain ⟨β, η, hβ, hη, hid⟩ :=
    higham9_mulSubFold_source_identity fp m c a x hm1
  have hid' :
      c = fold * (1 + β) + ∑ t : Fin m, a t * x t * (1 + η t) := by
    simpa [fold] using hid
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div fold bk hbk
  have hy : y = (fold / bk) * (1 + δ) := by
    simpa [y] using hdiv
  have hyb : y * bk = fold * (1 + δ) := by
    rw [hy]
    field_simp [hbk]
  have h1 : gammaValid fp 1 :=
    gammaValid_mono fp (by omega) hm1
  have hm : gammaValid fp m :=
    gammaValid_mono fp (Nat.le_succ m) hm1
  have hu : fp.u < 1 := by
    unfold gammaValid at h1
    simpa using h1
  let δone : Fin 1 → ℝ := fun _ => δ
  have hδone : ∀ q, |δone q| ≤ fp.u := by
    intro q
    simpa [δone] using hδ
  obtain ⟨α, hα, hα_eq⟩ :=
    inv_prod_error_bound fp 1 δone hδone hu h1
  have hα_rel : 1 / (1 + δ) = 1 + α := by
    simpa [δone] using hα_eq
  obtain ⟨φ, hφ, hφ_eq⟩ :=
    gamma_mul fp m 1 β α hβ hα hm1
  have hδ_pos : 0 < 1 + δ := by
    linarith [neg_abs_le δ, hδ]
  have houtput : y * bk * (1 + φ) = fold * (1 + β) := by
    rw [hyb, ← hφ_eq, ← hα_rel]
    field_simp [hδ_pos.ne']
  have hsource :
      c = y * bk * (1 + φ) + ∑ t : Fin m, a t * x t * (1 + η t) := by
    rw [houtput]
    exact hid'
  have hη' : ∀ t, |η t| ≤ gamma fp (m + 1) := by
    intro t
    exact le_trans (hη t) (gamma_mono fp (Nat.le_succ m) hm1)
  have hsum :
      (∑ t : Fin m, a t * x t * (1 + η t)) =
        (∑ t : Fin m, a t * x t) + ∑ t : Fin m, (a t * x t) * η t := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hres :
      (c - ∑ t : Fin m, a t * x t) - y * bk =
        (y * bk) * φ + ∑ t : Fin m, (a t * x t) * η t := by
    rw [hsource, hsum]
    ring
  calc
    |(c - ∑ t : Fin m, a t * x t) -
        fp.fl_div
          (Fin.foldl m
            (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) c) bk * bk| =
        |(y * bk) * φ + ∑ t : Fin m, (a t * x t) * η t| := by
          simpa [fold, y] using congrArg abs hres
    _ ≤ |(y * bk) * φ| + |∑ t : Fin m, (a t * x t) * η t| :=
      abs_add_le _ _
    _ ≤ |y * bk| * gamma fp (m + 1) +
          ∑ t : Fin m, |a t * x t| * gamma fp (m + 1) := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hφ (abs_nonneg _)
      · calc
          |∑ t : Fin m, (a t * x t) * η t| ≤
              ∑ t : Fin m, |(a t * x t) * η t| :=
                Finset.abs_sum_le_sum_abs _ _
          _ = ∑ t : Fin m, |a t * x t| * |η t| := by
                apply Finset.sum_congr rfl
                intro t _
                rw [abs_mul]
          _ ≤ ∑ t : Fin m, |a t * x t| * gamma fp (m + 1) := by
                apply Finset.sum_le_sum
                intro t _
                exact mul_le_mul_of_nonneg_left (hη' t) (abs_nonneg _)
    _ = gamma fp (m + 1) *
        ((∑ t : Fin m, |a t * x t|) +
          |fp.fl_div
            (Fin.foldl m
              (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) c) bk * bk|) := by
      rw [← Finset.sum_mul]
      simp only [fold, y]
      ring

theorem higham9_2_rectFlDoolittleUEntry_source_residual_abs_le
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) (hn : gammaValid fp n)
    (hentry : U k j = higham9_2_rectFlDoolittleUEntry fp hmn A L U k j) :
    |(A (higham9_2_rectRow hmn k) j -
        higham9_2_rectPrefixDot L U (higham9_2_rectRow hmn k) j k) - U k j| ≤
      gamma fp n *
        ((∑ s : Fin k.val,
            |L (higham9_2_rectRow hmn k) ⟨s.val, by omega⟩ *
              U ⟨s.val, by omega⟩ j|) + |U k j|) := by
  have hk1 : gammaValid fp (k.val + 1) :=
    gammaValid_mono fp (by omega) hn
  have hraw := higham9_2_flMulSubFold_source_residual_abs_le fp k.val
    (A (higham9_2_rectRow hmn k) j)
    (fun s : Fin k.val => L (higham9_2_rectRow hmn k) ⟨s.val, by omega⟩)
    (fun s : Fin k.val => U ⟨s.val, by omega⟩ j) hk1
  have hpref := finMaskedPrefixSum_eq_finSum k
    (fun s : Fin n => L (higham9_2_rectRow hmn k) s * U s j)
  have hγ : gamma fp k.val ≤ gamma fp n :=
    gamma_mono fp (Nat.le_of_lt k.isLt) hn
  calc
    |(A (higham9_2_rectRow hmn k) j -
        higham9_2_rectPrefixDot L U (higham9_2_rectRow hmn k) j k) - U k j| ≤
      gamma fp k.val *
        ((∑ s : Fin k.val,
            |L (higham9_2_rectRow hmn k) ⟨s.val, by omega⟩ *
              U ⟨s.val, by omega⟩ j|) + |U k j|) := by
        rw [hentry]
        unfold higham9_2_rectPrefixDot
        rw [hpref]
        simpa [higham9_2_rectFlDoolittleUEntry, flDoolittleUEntry] using hraw
    _ ≤ gamma fp n *
        ((∑ s : Fin k.val,
            |L (higham9_2_rectRow hmn k) ⟨s.val, by omega⟩ *
              U ⟨s.val, by omega⟩ j|) + |U k j|) := by
      exact mul_le_mul_of_nonneg_right hγ (by positivity)

theorem higham9_2_rectFlDoolittleLEntry_source_residual_abs_le
    {m n : ℕ} (fp : FPModel)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) (hn : gammaValid fp n)
    (hUkk : U k k ≠ 0)
    (hentry : L i k = higham9_2_rectFlDoolittleLEntry fp A L U i k) :
    |(A i k - higham9_2_rectPrefixDot L U i k k) - L i k * U k k| ≤
      gamma fp n *
        ((∑ s : Fin k.val,
            |L i ⟨s.val, by omega⟩ * U ⟨s.val, by omega⟩ k|) +
          |L i k * U k k|) := by
  have hk1 : gammaValid fp (k.val + 1) :=
    gammaValid_mono fp (by omega) hn
  have hraw := higham9_2_flMulSubFold_div_source_residual_abs_le fp k.val
    (A i k) (U k k) hUkk
    (fun s : Fin k.val => L i ⟨s.val, by omega⟩)
    (fun s : Fin k.val => U ⟨s.val, by omega⟩ k) hk1
  have hpref := finMaskedPrefixSum_eq_finSum k
    (fun s : Fin n => L i s * U s k)
  have hγ : gamma fp (k.val + 1) ≤ gamma fp n :=
    gamma_mono fp (by omega) hn
  calc
    |(A i k - higham9_2_rectPrefixDot L U i k k) - L i k * U k k| ≤
      gamma fp (k.val + 1) *
        ((∑ s : Fin k.val,
            |L i ⟨s.val, by omega⟩ * U ⟨s.val, by omega⟩ k|) +
          |L i k * U k k|) := by
        rw [hentry]
        unfold higham9_2_rectPrefixDot
        rw [hpref]
        simpa [higham9_2_rectFlDoolittleLEntry,
          higham9_2_rectFlDoolittleLNumerator, flDoolittleLNumerator] using hraw
    _ ≤ gamma fp n *
        ((∑ s : Fin k.val,
            |L i ⟨s.val, by omega⟩ * U ⟨s.val, by omega⟩ k|) +
          |L i k * U k k|) := by
      exact mul_le_mul_of_nonneg_right hγ (by positivity)

theorem higham9_2_rectAbsProductSum_eq_prefix_add_upper
    {m n : ℕ} {hmn : n ≤ m}
    {L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n,
      i.val < j.val → L i j = 0)
    (k j : Fin n) (hkj : k.val ≤ j.val) :
    (∑ s : Fin n,
        |L (higham9_2_rectRow hmn k) s| * |U s j|) =
      (∑ s : Fin k.val,
        |L (higham9_2_rectRow hmn k) ⟨s.val, by omega⟩ *
          U ⟨s.val, by omega⟩ j|) + |U k j| := by
  let Labs : Fin m → Fin n → ℝ := fun i s => |L i s|
  let Uabs : Fin n → Fin n → ℝ := fun s j => |U s j|
  have hdiag : ∀ q : Fin n, Labs (higham9_2_rectRow hmn q) q = 1 := by
    intro q
    simp [Labs, hL_diag q]
  have hzero : ∀ i : Fin m, ∀ q : Fin n,
      i.val < q.val → Labs i q = 0 := by
    intro i q hiq
    simp [Labs, hL_upper_zero i q hiq]
  have hsplit := higham9_2_rectMatMul_eq_prefix_add_upper
    (L := Labs) (U := Uabs) hdiag hzero k j hkj
  have hpref := finMaskedPrefixSum_eq_finSum k
    (fun s : Fin n => Labs (higham9_2_rectRow hmn k) s * Uabs s j)
  unfold rectMatMul at hsplit
  unfold higham9_2_rectPrefixDot at hsplit
  rw [hpref] at hsplit
  simpa [Labs, Uabs] using hsplit

theorem higham9_2_rectAbsProductSum_eq_prefix_add_lower
    {m n : ℕ} {L : Fin m → Fin n → ℝ}
    {U : Fin n → Fin n → ℝ}
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (i : Fin m) (k : Fin n) :
    (∑ s : Fin n, |L i s| * |U s k|) =
      (∑ s : Fin k.val,
        |L i ⟨s.val, by omega⟩ * U ⟨s.val, by omega⟩ k|) +
        |L i k * U k k| := by
  let Labs : Fin m → Fin n → ℝ := fun i s => |L i s|
  let Uabs : Fin n → Fin n → ℝ := fun s j => |U s j|
  have hzero : ∀ p q : Fin n, q.val < p.val → Uabs p q = 0 := by
    intro p q hpq
    simp [Uabs, hU_lower_zero p q hpq]
  have hsplit := higham9_2_rectMatMul_eq_prefix_add_lower
    (L := Labs) (U := Uabs) hzero i k
  have hpref := finMaskedPrefixSum_eq_finSum k
    (fun s : Fin n => Labs i s * Uabs s k)
  unfold rectMatMul at hsplit
  unfold higham9_2_rectPrefixDot at hsplit
  rw [hpref] at hsplit
  simpa [Labs, Uabs, abs_mul] using hsplit

structure higham9_2_RectDoolittleSourceCertificate {m n : ℕ}
    (hmn : n ≤ m) (A L : Fin m → Fin n → ℝ)
    (U : Fin n → Fin n → ℝ) (fp : FPModel) : Prop where
  L_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1
  L_upper_zero : ∀ i : Fin m, ∀ j : Fin n,
    i.val < j.val → L i j = 0
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0
  U_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
    U k j = higham9_2_rectFlDoolittleUEntry fp hmn A L U k j
  L_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
    L i k = higham9_2_rectFlDoolittleLEntry fp A L U i k
  U_source_residual : ∀ k j : Fin n, k.val ≤ j.val →
    |(A (higham9_2_rectRow hmn k) j -
        higham9_2_rectPrefixDot L U (higham9_2_rectRow hmn k) j k) - U k j| ≤
      gamma fp n *
        ((∑ s : Fin k.val,
            |L (higham9_2_rectRow hmn k) ⟨s.val, by omega⟩ *
              U ⟨s.val, by omega⟩ j|) + |U k j|)
  L_source_residual : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
    |(A i k - higham9_2_rectPrefixDot L U i k k) - L i k * U k k| ≤
      gamma fp n *
        ((∑ s : Fin k.val,
            |L i ⟨s.val, by omega⟩ * U ⟨s.val, by omega⟩ k|) +
          |L i k * U k k|)

theorem higham9_2_rectRoundedLoopSourceCertificate {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (hU_diag : ∀ k : Fin n, higham9_2_rectRoundedLoopU fp hmn A k k ≠ 0)
    (hn : gammaValid fp n) :
    higham9_2_RectDoolittleSourceCertificate hmn A
      (higham9_2_rectRoundedLoopL fp hmn A)
      (higham9_2_rectRoundedLoopU fp hmn A) fp where
  L_diag := higham9_2_rectRoundedLoopL_diag fp hmn A
  L_upper_zero := higham9_2_rectRoundedLoopL_upper_zero fp hmn A
  U_lower_zero := higham9_2_rectRoundedLoopU_lower_zero fp hmn A
  U_entry_eq := higham9_2_rectRoundedLoopU_stage_eq A
  L_entry_eq := higham9_2_rectRoundedLoopL_stage_eq A
  U_source_residual := by
    intro k j hkj
    exact higham9_2_rectFlDoolittleUEntry_source_residual_abs_le
      fp hmn A
      (higham9_2_rectRoundedLoopL fp hmn A)
      (higham9_2_rectRoundedLoopU fp hmn A) k j hn
      (higham9_2_rectRoundedLoopU_stage_eq A k j hkj)
  L_source_residual := by
    intro i k hki
    exact higham9_2_rectFlDoolittleLEntry_source_residual_abs_le
      fp A
      (higham9_2_rectRoundedLoopL fp hmn A)
      (higham9_2_rectRoundedLoopU fp hmn A) i k hn (hU_diag k)
      (higham9_2_rectRoundedLoopL_stage_eq A i k hki)

theorem higham9_3_rectSourceCertificate_backward_error
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (hC : higham9_2_RectDoolittleSourceCertificate hmn A L U fp) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L i k| * |U k j|) ∧
      (∀ i j, rectMatMul L U i j = A i j + ΔA i j) := by
  refine ⟨fun i j => rectMatMul L U i j - A i j, ?_, ?_⟩
  · intro i j
    by_cases hij : i.val ≤ j.val
    · let k : Fin n := ⟨i.val, lt_of_le_of_lt hij j.isLt⟩
      have hi_row : higham9_2_rectRow hmn k = i := by
        ext
        rfl
      have hkj : k.val ≤ j.val := by
        simpa [k] using hij
      have hprod := higham9_2_rectMatMul_eq_prefix_add_upper
        (hmn := hmn) (U := U) hC.L_diag hC.L_upper_zero k j hkj
      have habs := higham9_2_rectAbsProductSum_eq_prefix_add_upper
        (U := U) hC.L_diag hC.L_upper_zero k j hkj
      have hres := hC.U_source_residual k j hkj
      calc
        |(fun i j => rectMatMul L U i j - A i j) i j| =
            |rectMatMul L U (higham9_2_rectRow hmn k) j -
              A (higham9_2_rectRow hmn k) j| := by rw [hi_row]
        _ = |(higham9_2_rectPrefixDot L U
              (higham9_2_rectRow hmn k) j k + U k j) -
              A (higham9_2_rectRow hmn k) j| := by rw [hprod]
        _ = |(A (higham9_2_rectRow hmn k) j -
              higham9_2_rectPrefixDot L U
                (higham9_2_rectRow hmn k) j k) - U k j| := by
            have hneg :
                (higham9_2_rectPrefixDot L U
                    (higham9_2_rectRow hmn k) j k + U k j) -
                    A (higham9_2_rectRow hmn k) j =
                  -((A (higham9_2_rectRow hmn k) j -
                    higham9_2_rectPrefixDot L U
                      (higham9_2_rectRow hmn k) j k) - U k j) := by ring
            rw [hneg, abs_neg]
        _ ≤ gamma fp n *
              ((∑ s : Fin k.val,
                |L (higham9_2_rectRow hmn k) ⟨s.val, by omega⟩ *
                  U ⟨s.val, by omega⟩ j|) + |U k j|) := hres
        _ = gamma fp n *
              ∑ s : Fin n,
                |L (higham9_2_rectRow hmn k) s| * |U s j| := by rw [habs]
        _ = gamma fp n * ∑ s : Fin n, |L i s| * |U s j| := by rw [hi_row]
    · have hji : j.val < i.val := lt_of_not_ge hij
      have hprod := higham9_2_rectMatMul_eq_prefix_add_lower
        (L := L) hC.U_lower_zero i j
      have habs := higham9_2_rectAbsProductSum_eq_prefix_add_lower
        (L := L) hC.U_lower_zero i j
      have hres := hC.L_source_residual i j hji
      calc
        |(fun i j => rectMatMul L U i j - A i j) i j| =
            |rectMatMul L U i j - A i j| := rfl
        _ = |(higham9_2_rectPrefixDot L U i j j + L i j * U j j) - A i j| := by
              rw [hprod]
        _ = |(A i j - higham9_2_rectPrefixDot L U i j j) - L i j * U j j| := by
            have hneg :
                (higham9_2_rectPrefixDot L U i j j + L i j * U j j) - A i j =
                  -((A i j - higham9_2_rectPrefixDot L U i j j) -
                    L i j * U j j) := by ring
            rw [hneg, abs_neg]
        _ ≤ gamma fp n *
              ((∑ s : Fin j.val,
                |L i ⟨s.val, by omega⟩ * U ⟨s.val, by omega⟩ j|) +
                |L i j * U j j|) := hres
        _ = gamma fp n * ∑ s : Fin n, |L i s| * |U s j| := by rw [habs]
  · intro i j
    ring

theorem higham9_3_rectRoundedLoop_source_backward_error {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (hU_diag : ∀ k : Fin n, higham9_2_rectRoundedLoopU fp hmn A k k ≠ 0)
    (hn : gammaValid fp n) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp hmn A i k| *
            |higham9_2_rectRoundedLoopU fp hmn A k j|) ∧
      (∀ i j,
        rectMatMul (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) i j = A i j + ΔA i j) :=
  higham9_3_rectSourceCertificate_backward_error A
    (higham9_2_rectRoundedLoopL fp hmn A)
    (higham9_2_rectRoundedLoopU fp hmn A)
    (higham9_2_rectRoundedLoopSourceCertificate fp hmn A hU_diag hn)

/-- **Algorithm 9.2 / Theorem 9.3**, square executable Doolittle loop in the
repository's standard `LUBackwardError` interface.  Unlike the older
absolute-budget adapter, this theorem needs no output-only compression
premises: the source-shaped residual estimate already has the full
`|L̂||Û|` weight required by Theorem 9.3. -/
theorem higham9_3_rectRoundedLoop_square_to_LUBackwardError_source {n : ℕ}
    (fp : FPModel) (A : Fin n → Fin n → ℝ)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hn : gammaValid fp n) :
    LUBackwardError n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
      (gamma fp n) := by
  let L := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
  let U := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
  obtain ⟨ΔA, hΔA, hprod⟩ :=
    higham9_3_rectRoundedLoop_source_backward_error fp (Nat.le_refl n) A
      hU_diag hn
  refine {
    L_diag := ?_
    L_upper_zero := ?_
    U_lower_zero := ?_
    backward_bound := ?_ }
  · intro i
    simpa [L, higham9_2_rectRow] using
      (higham9_2_rectRoundedLoopL_diag fp (Nat.le_refl n) A i)
  · simpa [L] using
      (higham9_2_rectRoundedLoopL_upper_zero fp (Nat.le_refl n) A)
  · simpa [U] using
      (higham9_2_rectRoundedLoopU_lower_zero fp (Nat.le_refl n) A)
  · intro i j
    have hΔeq :
        ΔA i j = (∑ k : Fin n, L i k * U k j) - A i j := by
      have hij := hprod i j
      change (∑ k : Fin n, L i k * U k j) = A i j + ΔA i j at hij
      linarith
    simpa [L, U, hΔeq] using hΔA i j

/-- **Algorithm 9.2 / Theorem 9.3**, row-permuted executable loop form.
Running the literal loop on `PA` and supplying only a genuine permutation,
nonzero pivots, and `gammaValid` produces the pivoted backward-error
certificate consumed by the source-facing GEPP analysis. -/
theorem higham9_3_rectRoundedLoop_permuted_to_PermutedLUBackwardError_source
    {n : ℕ} (fp : FPModel) (A : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (hsigma : IsPermutation n sigma)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma) k k ≠ 0)
    (hn : gammaValid fp n) :
    higham9_2_PermutedLUBackwardError n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma))
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma))
      sigma (gamma fp n) := by
  let PA := higham9_2_rowPermutedMatrix A sigma
  let L := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) PA
  let U := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) PA
  have hBE : LUBackwardError n PA L U (gamma fp n) := by
    simpa [PA, L, U] using
      (higham9_3_rectRoundedLoop_square_to_LUBackwardError_source fp PA
        (by simpa [PA] using hU_diag) hn)
  exact {
    perm := hsigma
    L_diag := hBE.L_diag
    L_upper_zero := hBE.L_upper_zero
    U_lower_zero := hBE.U_lower_zero
    backward_bound := by
      intro i j
      simpa [PA, higham9_2_rowPermutedMatrix] using hBE.backward_bound i j }

/-- **Algorithm 9.2 / Theorem 9.4**, literal square Doolittle loop followed
by the actual floating-point triangular solves.  The source-shaped Theorem
9.3 producer removes the obsolete cancellation-sensitive budget hypotheses
from the executable endpoint. -/
theorem higham9_4_rectRoundedLoop_square_lu_solve_backward_error_source
    {n : ℕ} (fp : FPModel) (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n)) :
    let y_hat := fl_forwardSub fp n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A) b
    let x_hat := fl_backSub fp n
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (3 * n) *
        ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  let L := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
  let U := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
  have hL_diag_ne : ∀ i : Fin n, L i i ≠ 0 := by
    intro i
    have hdiag : L i i = 1 := by
      simpa [L, higham9_2_rectRow] using
        (higham9_2_rectRoundedLoopL_diag fp (Nat.le_refl n) A i)
    rw [hdiag]
    norm_num
  have hU_diag' : ∀ i : Fin n, U i i ≠ 0 := by
    intro i
    simpa [U] using hU_diag i
  have hBE : LUBackwardError n A L U (gamma fp n) := by
    simpa [L, U] using
      (higham9_3_rectRoundedLoop_square_to_LUBackwardError_source fp A
        hU_diag hn)
  simpa [L, U] using
    (higham9_4_lu_solve_backward_error fp n A L U b
      hL_diag_ne hU_diag' hBE hn hn3)

/-- **Theorem 9.5 / equation (9.10)**, executable row-permuted Doolittle
loop feeding the GEPP Wilkinson bound.  The multiplier bound and agreement
with the GEPP `U` trace remain the mathematical partial-pivoting hypotheses;
the invalid output-only residual-compression premises do not. -/
theorem higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_rectRoundedLoop_source
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma)))
    (hU_diag : ∀ i : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma) i i ≠ 0)
    (hsigma : IsPermutation n sigma)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n,
      |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma) i j| ≤ 1) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
      (higham9_2_rowPermutedMatrix A sigma)
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
      (higham9_2_rowPermutedMatrix A sigma)
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  let PA := higham9_2_rowPermutedMatrix A sigma
  let L := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) PA
  let U := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) PA
  have hPBE : higham9_2_PermutedLUBackwardError n A L U sigma
      (gamma fp n) := by
    simpa [PA, L, U] using
      (higham9_3_rectRoundedLoop_permuted_to_PermutedLUBackwardError_source
        fp A sigma hsigma (by simpa [PA] using hU_diag) hn)
  simpa [PA, L, U] using
    (higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace
      fp n hn_pos A L U sigma b hAmax
      (by simpa [PA, U] using htrace)
      (by simpa [PA, U] using hU_diag)
      hPBE hn hn3 (by simpa [PA, L] using hL_bound))

/-- **Theorem 9.14**, executable rounded Doolittle loop feeding the source
`f(u)` bound.  Only the source theorem's genuine factor-growth comparison is
left to the caller. -/
theorem higham9_14_source_f_bound_of_rectRoundedLoop_square_sourceResidual_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (c u : ℝ) (hu : 0 ≤ u)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        c * |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ c * higham9_14_f u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  let L := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
  let U := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
  have hBE : LUBackwardError n A L U (gamma fp n) := by
    simpa [L, U] using
      (higham9_3_rectRoundedLoop_square_to_LUBackwardError_source fp A
        hU_diag hn)
  exact
    higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
      fp n A L U b c (gamma fp n) u hu hn hBE hγ_le_u hγ_le_u
      (by simpa [U] using hU_diag)
      (by simpa [L, U] using hAbsLU_le)

/-- Gamma-specialized corollary of the source-residual executable Theorem
9.14 `f(u)` bridge. -/
theorem higham9_14_source_f_bound_of_rectRoundedLoop_square_sourceResidual_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (c : ℝ) (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        c * |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        c * higham9_14_f (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_f_bound_of_rectRoundedLoop_square_sourceResidual_gamma_le
    fp n A b c (gamma fp n) (gamma_nonneg fp hn) hn hU_diag le_rfl hAbsLU_le

/-- **Theorem 9.14**, executable rounded Doolittle loop feeding the final
source `h(u)` bound under the exact-growth comparison
`|L̂||Û| ≤ |A|`. -/
theorem higham9_14_source_h_bound_of_rectRoundedLoop_square_sourceResidual_gamma_le
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hn : gammaValid fp n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hγ_le_u : gamma fp n ≤ u)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) := by
  let L := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
  let U := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
  have hBE : LUBackwardError n A L U (gamma fp n) := by
    simpa [L, U] using
      (higham9_3_rectRoundedLoop_square_to_LUBackwardError_source fp A
        hU_diag hn)
  exact
    higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le
      fp n A L U b (gamma fp n) u hu hu_lt_one hn hBE
      hγ_le_u hγ_le_u (by simpa [U] using hU_diag)
      (by simpa [L, U] using hAbsLU_le)

/-- Gamma-specialized corollary of the source-residual executable Theorem
9.14 `h(u)` bridge. -/
theorem higham9_14_source_h_bound_of_rectRoundedLoop_square_sourceResidual_gamma
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hγ_lt_one : gamma fp n < 1)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| ≤
        |A i j|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        higham9_14_h (gamma fp n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x_hat j = b i) :=
  higham9_14_source_h_bound_of_rectRoundedLoop_square_sourceResidual_gamma_le
    fp n A b (gamma fp n) (gamma_nonneg fp hn) hγ_lt_one hn hU_diag
      le_rfl hAbsLU_le

/-- Cancellation makes the old output-only compression shape false even for
one exact subtraction: a nonzero work sum can produce a zero stored result.
This counterexample is deliberately scoped to that obsolete adapter premise;
the source-shaped prefix-plus-stored-output residual bound above remains
valid. -/
theorem higham9_3_outputOnlyCompression_fails_under_cancellation :
    ∀ γ : ℝ, 0 < γ →
      ¬ γ * (|((1 : ℝ))| + |((1 : ℝ))|) ≤ γ * |((1 : ℝ) - 1)| := by
  intro γ hγ hbad
  norm_num at hbad
  have hpos : 0 < γ * 2 := mul_pos hγ (by norm_num)
  have hnonpos : γ * 2 ≤ 0 := hbad.trans_eq (mul_zero γ)
  exact (not_lt_of_ge hnonpos) hpos

end NumStability
