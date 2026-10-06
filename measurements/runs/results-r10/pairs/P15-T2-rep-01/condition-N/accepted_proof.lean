import HighamBench.P15Definitions

namespace HighamBench

private lemma gamma_nonneg_of_valid {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (h : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at h
  rw [gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by nlinarith)

private lemma gamma_mono_nat {u : ℝ} {k n : ℕ}
    (hu : 0 ≤ u) (hn : GammaValid u n) (hkn : k ≤ n) :
    gamma u k ≤ gamma u n := by
  unfold GammaValid at hn
  rw [gamma, gamma]
  have hk : (k : ℝ) * u < 1 := by
    have hcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hmul := mul_le_mul_of_nonneg_right hcast hu
    nlinarith
  have hmul : (k : ℝ) * u ≤ (n : ℝ) * u := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkn) hu
  apply (div_le_div_iff₀ (by nlinarith : 0 < 1 - (k : ℝ) * u)
    (by nlinarith : 0 < 1 - (n : ℝ) * u)).2
  nlinarith

private lemma gamma_mul_step {u : ℝ} {k : ℕ}
    (hu : 0 ≤ u) (h : GammaValid u (k + 1)) :
    gamma u k + u + gamma u k * u ≤ gamma u (k + 1) := by
  unfold GammaValid at h
  norm_num [Nat.cast_add, Nat.cast_one] at h
  rw [gamma, gamma]
  have hk : (k : ℝ) * u < 1 := by
    push_cast at h
    nlinarith
  have heq :
      (k : ℝ) * u / (1 - (k : ℝ) * u) + u +
          (k : ℝ) * u / (1 - (k : ℝ) * u) * u =
        ((k : ℝ) + 1) * u / (1 - (k : ℝ) * u) := by
    field_simp [ne_of_gt (by nlinarith : 0 < 1 - (k : ℝ) * u)]
    ring
  rw [heq]
  norm_num [Nat.cast_add, Nat.cast_one]
  apply div_le_div_of_nonneg_left (by positivity)
    (by nlinarith : 0 < 1 - ((k : ℝ) + 1) * u)
  nlinarith

private lemma gamma_div_step {u : ℝ} {k : ℕ}
    (hu : 0 ≤ u) (h : GammaValid u (k + 1)) :
    (gamma u k + u) / (1 - u) ≤ gamma u (k + 1) := by
  unfold GammaValid at h
  norm_num [Nat.cast_add, Nat.cast_one] at h
  have hu1 : u < 1 := by
    push_cast at h
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith
  rw [gamma, gamma]
  have hk : (k : ℝ) * u < 1 := by
    push_cast at h
    nlinarith
  have heq :
      (k : ℝ) * u / (1 - (k : ℝ) * u) + u =
        (((k : ℝ) + 1) * u - (k : ℝ) * u ^ 2) /
          (1 - (k : ℝ) * u) := by
    field_simp [ne_of_gt (by nlinarith : 0 < 1 - (k : ℝ) * u)]
    ring
  rw [heq, div_div]
  norm_num [Nat.cast_add, Nat.cast_one]
  apply (div_le_div_iff₀
    (mul_pos (by nlinarith : 0 < 1 - (k : ℝ) * u) (sub_pos.mpr hu1))
    (by nlinarith : 0 < 1 - ((k : ℝ) + 1) * u)).2
  nlinarith [sq_nonneg u, mul_nonneg (Nat.cast_nonneg k) (sq_nonneg u)]

private lemma gamma_valid_of_le {u : ℝ} {k n : ℕ}
    (hu : 0 ≤ u) (hn : GammaValid u n) (hkn : k ≤ n) :
    GammaValid u k := by
  unfold GammaValid at hn ⊢
  have hcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have := mul_le_mul_of_nonneg_right hcast hu
  linarith

private lemma one_add_mul_error {u : ℝ} {k : ℕ} {e δ : ℝ}
    (hu : 0 ≤ u) (hvalid : GammaValid u (k + 1))
    (he : |e| ≤ gamma u k) (hδ : |δ| ≤ u) :
    |(1 + e) * (1 + δ) - 1| ≤ gamma u (k + 1) := by
  have hkvalid : GammaValid u k :=
    gamma_valid_of_le hu hvalid (Nat.le_succ k)
  have hg : 0 ≤ gamma u k := gamma_nonneg_of_valid hu hkvalid
  calc
    |(1 + e) * (1 + δ) - 1| = |e + δ + e * δ| := by ring_nf
    _ ≤ |e| + |δ| + |e| * |δ| := by
      exact le_trans (abs_add_le _ _)
        (add_le_add (abs_add_le _ _) (le_of_eq (abs_mul _ _)))
    _ ≤ gamma u k + u + gamma u k * u := by
      gcongr
    _ ≤ gamma u (k + 1) := gamma_mul_step hu hvalid

private lemma one_add_div_error {u : ℝ} {k : ℕ} {e δ : ℝ}
    (hu : 0 ≤ u) (hvalid : GammaValid u (k + 1))
    (he : |e| ≤ gamma u k) (hδ : |δ| ≤ u) :
    |(1 + e) / (1 + δ) - 1| ≤ gamma u (k + 1) := by
  unfold GammaValid at hvalid
  norm_num [Nat.cast_add, Nat.cast_one] at hvalid
  have hu1 : u < 1 := by
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith
  have hδlo : -u ≤ δ := le_trans (neg_le_neg hδ) (neg_abs_le δ)
  have hden : 0 < 1 + δ := by nlinarith
  have hkvalid : GammaValid u k := by
    unfold GammaValid
    nlinarith
  have hg : 0 ≤ gamma u k := gamma_nonneg_of_valid hu hkvalid
  have hnum : |e - δ| ≤ gamma u k + u := by
    calc
      |e - δ| ≤ |e| + |δ| := abs_sub e δ
      _ ≤ gamma u k + u := add_le_add he hδ
  have hfrac : |e - δ| / (1 + δ) ≤
      (gamma u k + u) / (1 - u) := by
    exact div_le_div₀ (add_nonneg hg hu) hnum (sub_pos.mpr hu1) (by nlinarith)
  calc
    |(1 + e) / (1 + δ) - 1| = |e - δ| / (1 + δ) := by
      rw [show (1 + e) / (1 + δ) - 1 = (e - δ) / (1 + δ) by
        field_simp [ne_of_gt hden]
        ring]
      rw [abs_div, abs_of_pos hden]
    _ ≤ (gamma u k + u) / (1 - u) := hfrac
    _ ≤ gamma u (k + 1) := gamma_div_step hu (by
      unfold GammaValid
      norm_num [Nat.cast_add, Nat.cast_one]
      exact hvalid)

private lemma gamma_add_bound {u : ℝ} {k l : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u (k + l)) :
    gamma u k + gamma u l + gamma u k * gamma u l ≤
      gamma u (k + l) := by
  unfold GammaValid at hvalid
  norm_num [Nat.cast_add] at hvalid
  have hk : (k : ℝ) * u < 1 := by
    have hl0 : (0 : ℝ) ≤ l := by positivity
    nlinarith
  have hl : (l : ℝ) * u < 1 := by
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith
  have hkpos : 0 < 1 - (k : ℝ) * u := by nlinarith
  have hlpos : 0 < 1 - (l : ℝ) * u := by nlinarith
  have hsumpos : 0 < 1 - ((k : ℝ) + (l : ℝ)) * u := by nlinarith
  have hγk : 1 + gamma u k = 1 / (1 - (k : ℝ) * u) := by
    rw [gamma]
    field_simp [ne_of_gt hkpos]
    ring
  have hγl : 1 + gamma u l = 1 / (1 - (l : ℝ) * u) := by
    rw [gamma]
    field_simp [ne_of_gt hlpos]
    ring
  have hγsum : 1 + gamma u (k + l) =
      1 / (1 - ((k : ℝ) + (l : ℝ)) * u) := by
    rw [gamma]
    norm_num [Nat.cast_add]
    field_simp [ne_of_gt hsumpos]
    ring
  have hden : 1 - ((k : ℝ) + (l : ℝ)) * u ≤
      (1 - (k : ℝ) * u) * (1 - (l : ℝ) * u) := by
    have hklu : 0 ≤ (k : ℝ) * (l : ℝ) * u ^ 2 := by positivity
    nlinarith
  have hfrac :
      1 / ((1 - (k : ℝ) * u) * (1 - (l : ℝ) * u)) ≤
        1 / (1 - ((k : ℝ) + (l : ℝ)) * u) :=
    one_div_le_one_div_of_le hsumpos hden
  have hprod : (1 + gamma u k) * (1 + gamma u l) ≤
      1 + gamma u (k + l) := by
    rw [hγk, hγl, hγsum, div_mul_div_comm]
    norm_num
    simpa [one_div, mul_comm] using hfrac
  nlinarith

private lemma one_add_mul_errors {u : ℝ} {k l : ℕ} {e δ : ℝ}
    (hu : 0 ≤ u) (hvalid : GammaValid u (k + l))
    (he : |e| ≤ gamma u k) (hδ : |δ| ≤ gamma u l) :
    |(1 + e) * (1 + δ) - 1| ≤ gamma u (k + l) := by
  have hkvalid : GammaValid u k :=
    gamma_valid_of_le hu hvalid (Nat.le_add_right k l)
  have hlvalid : GammaValid u l :=
    gamma_valid_of_le hu hvalid (Nat.le_add_left l k)
  have hgk := gamma_nonneg_of_valid hu hkvalid
  have hgl := gamma_nonneg_of_valid hu hlvalid
  calc
    |(1 + e) * (1 + δ) - 1| = |e + δ + e * δ| := by ring_nf
    _ ≤ |e| + |δ| + |e| * |δ| := by
      exact le_trans (abs_add_le _ _)
        (add_le_add (abs_add_le _ _) (le_of_eq (abs_mul _ _)))
    _ ≤ gamma u k + gamma u l + gamma u k * gamma u l := by
      gcongr
    _ ≤ gamma u (k + l) := gamma_add_bound hu hvalid

private lemma rounded_foldl_backward
    (fp : StandardFPModel) (q : ℕ) (a x : Fin q → ℝ) (z : ℝ)
    (hvalid : GammaValid fp.u (q + 1)) :
    ∃ ez : ℝ, ∃ E : Fin q → ℝ,
      Fin.foldl q
          (fun acc i ↦ fp.fl_add acc (fp.fl_mul (a i) (x i))) z =
        z * (1 + ez) + ∑ i : Fin q, a i * x i * (1 + E i) ∧
      |ez| ≤ gamma fp.u q ∧
      ∀ i, |E i| ≤ gamma fp.u (q + 1) := by
  induction q generalizing z with
  | zero =>
      refine ⟨0, fun i ↦ Fin.elim0 i, ?_, ?_, ?_⟩
      · simp [Fin.foldl_zero]
      · simp [gamma]
      · intro i
        exact Fin.elim0 i
  | succ q ih =>
      have htail : GammaValid fp.u (q + 1) :=
        gamma_valid_of_le fp.u_nonneg hvalid (by omega)
      obtain ⟨μ, hμ, hmul⟩ := fp.model_mul (a 0) (x 0)
      obtain ⟨δ, hδ, hadd⟩ :=
        fp.model_add z (fp.fl_mul (a 0) (x 0))
      obtain ⟨et, E, hfold, het, hE⟩ :=
        ih (fun i ↦ a i.succ) (fun i ↦ x i.succ)
          (fp.fl_add z (fp.fl_mul (a 0) (x 0))) htail
      let ez : ℝ := (1 + δ) * (1 + et) - 1
      let e0 : ℝ := (1 + μ) * (1 + δ) * (1 + et) - 1
      let E' : Fin (q + 1) → ℝ := Fin.cases e0 E
      refine ⟨ez, E', ?_, ?_, ?_⟩
      · rw [Fin.foldl_succ, hfold, hadd, hmul, Fin.sum_univ_succ]
        simp only [E', Fin.cases_zero, Fin.cases_succ]
        dsimp [ez, e0]
        ring
      · dsimp [ez]
        simpa [mul_comm] using
          (one_add_mul_error fp.u_nonneg htail het hδ)
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · dsimp [E', e0]
          have htwoValid : GammaValid fp.u (1 + 1) :=
            gamma_valid_of_le fp.u_nonneg hvalid (by omega)
          have honeValid : GammaValid fp.u 1 :=
            gamma_valid_of_le fp.u_nonneg hvalid (by omega)
          have huγ : fp.u ≤ gamma fp.u 1 := by
            have hs := gamma_mul_step fp.u_nonneg honeValid (k := 0)
            simpa [gamma] using hs
          let e2 : ℝ := (1 + μ) * (1 + δ) - 1
          have he2 : |e2| ≤ gamma fp.u (1 + 1) := by
            exact one_add_mul_error fp.u_nonneg htwoValid
              (le_trans hμ huγ) hδ
          have hsumValid : GammaValid fp.u ((1 + 1) + q) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvalid
          have hc := one_add_mul_errors fp.u_nonneg hsumValid he2 het
          dsimp [e2] at hc
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
        · dsimp [E']
          exact le_trans (hE j)
            (gamma_mono_nat fp.u_nonneg hvalid (by omega))

private lemma rounded_dot_backward
    (fp : StandardFPModel) (n : ℕ) (a x : Fin n → ℝ)
    (hvalid : GammaValid fp.u n) :
    ∃ E : Fin n → ℝ,
      roundedDotProduct fp n a x = ∑ i : Fin n, (a i + E i) * x i ∧
      ∀ i, |E i| ≤ gamma fp.u n * |a i| := by
  cases n with
  | zero =>
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · simp [roundedDotProduct]
      · intro i
        exact Fin.elim0 i
  | succ n =>
      obtain ⟨μ, hμ, hmul⟩ := fp.model_mul (a 0) (x 0)
      obtain ⟨ez, D, hfold, hez, hD⟩ :=
        rounded_foldl_backward fp n (fun i ↦ a i.succ)
          (fun i ↦ x i.succ) (fp.fl_mul (a 0) (x 0)) hvalid
      let d0 : ℝ := (1 + μ) * (1 + ez) - 1
      let d : Fin (n + 1) → ℝ := Fin.cases d0 D
      let E : Fin (n + 1) → ℝ := fun i ↦ a i * d i
      have honeValid : GammaValid fp.u 1 :=
        gamma_valid_of_le fp.u_nonneg hvalid (by omega)
      have huγ : fp.u ≤ gamma fp.u 1 := by
        have hs := gamma_mul_step fp.u_nonneg honeValid (k := 0)
        simpa [gamma] using hs
      have hsumValid : GammaValid fp.u (1 + n) := by
        simpa [Nat.add_comm] using hvalid
      have hd0 : |d0| ≤ gamma fp.u (n + 1) := by
        dsimp [d0]
        have hh := one_add_mul_errors fp.u_nonneg hsumValid
          (le_trans hμ huγ) hez
        simpa [Nat.add_comm] using hh
      refine ⟨E, ?_, ?_⟩
      · rw [roundedDotProduct, hfold, hmul, Fin.sum_univ_succ]
        simp only [E, d, Fin.cases_zero, Fin.cases_succ]
        dsimp [d0]
        congr 1
        · ring
        · apply Finset.sum_congr rfl
          intro i hi
          ring
      · intro i
        simp only [E, abs_mul]
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_right
        · refine Fin.cases ?_ (fun j ↦ ?_) i
          · simpa [d] using hd0
          · simpa [d] using hD j
        · exact abs_nonneg _

private lemma p15_frob_bound_of_entrywise {m n : ℕ}
    (g : ℝ) (hg : 0 ≤ g) (A E : P15RectMatrix m n)
    (hE : ∀ i j, |E i j| ≤ g * |A i j|) :
    p15RectFrobNorm E ≤ g * p15RectFrobNorm A := by
  have hsq : ∀ i j, E i j ^ 2 ≤ g ^ 2 * A i j ^ 2 := by
    intro i j
    have habs : |E i j| ≤ abs (g * abs (A i j)) := by
      simpa [abs_mul, abs_of_nonneg hg] using hE i j
    have h := (sq_le_sq).2 habs
    simpa [mul_pow, sq_abs] using h
  have hsum : (∑ i : Fin m, ∑ j : Fin n, E i j ^ 2) ≤
      g ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
    calc
      (∑ i : Fin m, ∑ j : Fin n, E i j ^ 2) ≤
          ∑ i : Fin m, ∑ j : Fin n, g ^ 2 * A i j ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            apply Finset.sum_le_sum
            intro j hj
            exact hsq i j
      _ = g ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
        simp_rw [Finset.mul_sum]
  unfold p15RectFrobNorm
  calc
    √(∑ i : Fin m, ∑ j : Fin n, E i j ^ 2) ≤
        √(g ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)) :=
      Real.sqrt_le_sqrt hsum
    _ = g * √(∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg g), Real.sqrt_sq hg]

private lemma rounded_rect_mat_vec_backward
    (fp : StandardFPModel) {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hvalid : GammaValid fp.u n) :
    ∃ E : P15RectMatrix m n,
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A E) x ∧
      p15RectFrobNorm E ≤ gamma fp.u n * p15RectFrobNorm A := by
  classical
  choose E hEq hBound using fun i ↦
    rounded_dot_backward fp n (A i) x hvalid
  refine ⟨fun i j ↦ E i j, ?_, ?_⟩
  · funext i
    simpa [p15RoundedRectMatVec, roundedMatVec, p15RectMatVec,
      p15RectAdd] using hEq i
  · apply p15_frob_bound_of_entrywise (gamma fp.u n)
      (gamma_nonneg_of_valid fp.u_nonneg hvalid)
    intro i j
    exact hBound i j

private lemma roundedForwardSubSteps_preserves_lt
    (fp : StandardFPModel) (n : ℕ) (L : Fin n → Fin n → ℝ)
    (rhs : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      i.val < n - k →
      roundedForwardSubSteps fp n L rhs k hk x i = x i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      rfl
  | succ k ih =>
      intro hk x i hi
      rw [roundedForwardSubSteps]
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) ↦
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (rhs ik)
      let x' := Function.update x ik (fp.fl_div s (L ik ik))
      rw [ih (Nat.le_of_succ_le hk) x' i (by omega)]
      dsimp [x']
      apply Function.update_of_ne
      intro heq
      have hv : i.val = ik.val := congrArg Fin.val heq
      dsimp [ik] at hv
      omega

private lemma roundedForwardSubSteps_row
    (fp : StandardFPModel) (n : ℕ) (L : Fin n → Fin n → ℝ)
    (rhs : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      n - k ≤ i.val →
      let y := roundedForwardSubSteps fp n L rhs k hk x
      y i = fp.fl_div
        (Fin.foldl i.val
          (fun acc (t : Fin i.val) ↦
            fp.fl_sub acc
              (fp.fl_mul (L i ⟨t.val, by omega⟩)
                (y ⟨t.val, by omega⟩)))
          (rhs i))
        (L i i) := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      omega
  | succ k ih =>
      intro hk x i hi
      rw [roundedForwardSubSteps]
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) ↦
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (rhs ik)
      let x' := Function.update x ik (fp.fl_div s (L ik ik))
      let y := roundedForwardSubSteps fp n L rhs k
        (Nat.le_of_succ_le hk) x'
      change y i = _
      by_cases hei : i = ik
      · rw [hei]
        have hyik : y ik = x' ik := by
          dsimp only [y]
          apply roundedForwardSubSteps_preserves_lt
          dsimp [ik]
          omega
        rw [hyik]
        have hfun :
            (fun acc (t : Fin ik.val) ↦
              fp.fl_sub acc
                (fp.fl_mul (L ik ⟨t.val, by omega⟩)
                  (y ⟨t.val, by omega⟩))) =
            (fun acc (t : Fin ik.val) ↦
              fp.fl_sub acc
                (fp.fl_mul (L ik ⟨t.val, by omega⟩)
                  (x ⟨t.val, by omega⟩))) := by
          funext acc t
          have hyt : y ⟨t.val, by omega⟩ = x ⟨t.val, by omega⟩ := by
            dsimp only [y]
            rw [roundedForwardSubSteps_preserves_lt]
            · dsimp [x']
              apply Function.update_of_ne
              intro heq
              have hv := congrArg Fin.val heq
              dsimp [ik] at hv
              omega
            · dsimp [ik]
              omega
          rw [hyt]
        rw [hfun]
        dsimp [x', s]
        rw [Function.update_self]
      · have hilower : n - k ≤ i.val := by
          have hvne : i.val ≠ ik.val := by
            intro hv
            apply hei
            exact Fin.ext hv
          dsimp [ik] at hvne
          omega
        exact ih (Nat.le_of_succ_le hk) x' i hilower

private lemma roundedForwardSub_row
    (fp : StandardFPModel) (n : ℕ) (L : Fin n → Fin n → ℝ)
    (rhs : Fin n → ℝ) (i : Fin n) :
    let y := roundedForwardSub fp n L rhs
    y i = fp.fl_div
      (Fin.foldl i.val
        (fun acc (t : Fin i.val) ↦
          fp.fl_sub acc
            (fp.fl_mul (L i ⟨t.val, by omega⟩)
              (y ⟨t.val, by omega⟩)))
        (rhs i))
      (L i i) := by
  unfold roundedForwardSub
  apply roundedForwardSubSteps_row
  omega

private lemma rounded_sub_foldl_backward
    (fp : StandardFPModel) (q : ℕ) (a x : Fin q → ℝ) (z : ℝ)
    (hvalid : GammaValid fp.u q) :
    ∃ es : ℝ, ∃ E : Fin q → ℝ,
      z = Fin.foldl q
          (fun acc i ↦ fp.fl_sub acc (fp.fl_mul (a i) (x i))) z *
            (1 + es) +
          ∑ i : Fin q, a i * x i * (1 + E i) ∧
      |es| ≤ gamma fp.u q ∧
      ∀ i, |E i| ≤ gamma fp.u q := by
  induction q generalizing z with
  | zero =>
      refine ⟨0, fun i ↦ Fin.elim0 i, ?_, ?_, ?_⟩
      · simp [Fin.foldl_zero]
      · simp [gamma]
      · intro i
        exact Fin.elim0 i
  | succ q ih =>
      have htail : GammaValid fp.u q :=
        gamma_valid_of_le fp.u_nonneg hvalid (Nat.le_succ q)
      obtain ⟨μ, hμ, hmul⟩ := fp.model_mul (a 0) (x 0)
      obtain ⟨δ, hδ, hsub⟩ :=
        fp.model_sub z (fp.fl_mul (a 0) (x 0))
      let z' := fp.fl_sub z (fp.fl_mul (a 0) (x 0))
      obtain ⟨es, E, hfold, hes, hE⟩ :=
        ih (fun i ↦ a i.succ) (fun i ↦ x i.succ) z' htail
      let es' : ℝ := (1 + es) / (1 + δ) - 1
      let E' : Fin (q + 1) → ℝ :=
        Fin.cases μ (fun i ↦ (1 + E i) / (1 + δ) - 1)
      have hu1 : fp.u < 1 := by
        unfold GammaValid at hvalid
        norm_num [Nat.cast_add, Nat.cast_one] at hvalid
        have hq0 : (0 : ℝ) ≤ q := by positivity
        nlinarith
      have hden : 1 + δ ≠ 0 := by
        have hδlo : -fp.u ≤ δ := le_trans (neg_le_neg hδ) (neg_abs_le δ)
        nlinarith
      have hz : z = z' / (1 + δ) + a 0 * x 0 * (1 + μ) := by
        dsimp [z']
        rw [hsub, hmul]
        field_simp [hden]
        ring
      have hfirst :
          (Fin.foldl q
              (fun acc i ↦
                fp.fl_sub acc (fp.fl_mul (a i.succ) (x i.succ))) z') *
                (1 + es) / (1 + δ) =
            (Fin.foldl q
              (fun acc i ↦
                fp.fl_sub acc (fp.fl_mul (a i.succ) (x i.succ))) z') *
                (1 + es') := by
        dsimp [es']
        field_simp [hden]
        ring
      have hsum :
          (∑ i : Fin q, a i.succ * x i.succ * (1 + E i)) /
              (1 + δ) =
            ∑ i : Fin q,
              a i.succ * x i.succ *
                (1 + ((1 + E i) / (1 + δ) - 1)) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [hden]
        ring
      refine ⟨es', E', ?_, ?_, ?_⟩
      · rw [Fin.foldl_succ, Fin.sum_univ_succ]
        simp only [E', Fin.cases_zero, Fin.cases_succ]
        calc
          z = z' / (1 + δ) + a 0 * x 0 * (1 + μ) := hz
          _ = _ := by
            rw [hfold, add_div, hfirst, hsum]
            ring
      · dsimp [es']
        exact one_add_div_error fp.u_nonneg hvalid hes hδ
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · dsimp [E']
          have honeValid : GammaValid fp.u 1 :=
            gamma_valid_of_le fp.u_nonneg hvalid (by omega)
          have huγ : fp.u ≤ gamma fp.u 1 := by
            have hs := gamma_mul_step fp.u_nonneg honeValid (k := 0)
            simpa [gamma] using hs
          exact le_trans hμ
            (le_trans huγ (gamma_mono_nat fp.u_nonneg hvalid (by omega)))
        · dsimp [E']
          exact one_add_div_error fp.u_nonneg hvalid (hE j) hδ

private lemma fin_sum_eq_sum_before_add {n : ℕ} (f : Fin n → ℝ)
    (i : Fin n) (hzero : ∀ j : Fin n, i.val < j.val → f j = 0) :
    (∑ j : Fin n, f j) =
      (∑ t : Fin i.val, f ⟨t.val, by omega⟩) + f i := by
  classical
  let F : ℕ → ℝ := fun k ↦ if hk : k < n then f ⟨k, hk⟩ else 0
  have hall : (∑ j : Fin n, f j) = ∑ k ∈ Finset.range n, F k := by
    simpa [F] using (Fin.sum_univ_eq_sum_range F n)
  have hprefix : (∑ t : Fin i.val, f ⟨t.val, by omega⟩) =
      ∑ k ∈ Finset.range i.val, F k := by
    rw [← Fin.sum_univ_eq_sum_range F i.val]
    apply Finset.sum_congr rfl
    intro t ht
    have htN : t.val < n := lt_trans t.isLt i.isLt
    simp [F, htN]
  have hsubset : Finset.range (i.val + 1) ⊆ Finset.range n := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have hrange : (∑ k ∈ Finset.range (i.val + 1), F k) =
      ∑ k ∈ Finset.range n, F k := by
    apply Finset.sum_subset hsubset
    intro k hkn hki
    simp only [Finset.mem_range] at hkn hki
    rw [show F k = f ⟨k, hkn⟩ by simp [F, hkn]]
    apply hzero
    dsimp
    omega
  calc
    (∑ j : Fin n, f j) = ∑ k ∈ Finset.range n, F k := hall
    _ = ∑ k ∈ Finset.range (i.val + 1), F k := hrange.symm
    _ = (∑ k ∈ Finset.range i.val, F k) + F i.val := by
      rw [Finset.sum_range_succ]
    _ = (∑ t : Fin i.val, f ⟨t.val, by omega⟩) + f i := by
      rw [← hprefix]
      simp [F]

private lemma rounded_forward_sub_row_backward
    (fp : StandardFPModel) (n : ℕ) (L : P15Matrix n)
    (rhs : P15Vector n) (hdiag : ∀ i, L i i ≠ 0)
    (hlower : p15LowerTriangular L) (hvalid : GammaValid fp.u n)
    (i : Fin n) :
    let y := roundedForwardSub fp n L rhs
    ∃ Ei : Fin n → ℝ,
      (∑ j : Fin n, (L i j + Ei j) * y j) = rhs i ∧
      ∀ j, |Ei j| ≤ gamma fp.u n * |L i j| := by
  let y := roundedForwardSub fp n L rhs
  let q := i.val
  let a : Fin q → ℝ := fun t ↦ L i ⟨t.val, by omega⟩
  let xx : Fin q → ℝ := fun t ↦ y ⟨t.val, by omega⟩
  let s := Fin.foldl q
    (fun acc t ↦ fp.fl_sub acc (fp.fl_mul (a t) (xx t))) (rhs i)
  have hqvalid : GammaValid fp.u q :=
    gamma_valid_of_le fp.u_nonneg hvalid (by dsimp [q]; omega)
  have hq1valid : GammaValid fp.u (q + 1) :=
    gamma_valid_of_le fp.u_nonneg hvalid (by dsimp [q]; omega)
  obtain ⟨es, D, hfold, hes, hD⟩ :=
    rounded_sub_foldl_backward fp q a xx (rhs i) hqvalid
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div s (L i i) (hdiag i)
  have hrow : y i = fp.fl_div s (L i i) := by
    dsimp only [y]
    rw [roundedForwardSub_row]
  have hu1 : fp.u < 1 := by
    unfold GammaValid at hq1valid
    norm_num [Nat.cast_add, Nat.cast_one] at hq1valid
    have hq0 : (0 : ℝ) ≤ q := by positivity
    nlinarith
  have hδlo : -fp.u ≤ δ := le_trans (neg_le_neg hδ) (neg_abs_le δ)
  have hden : 1 + δ ≠ 0 := by nlinarith
  have hs : s = L i i * y i / (1 + δ) := by
    rw [hrow, hdiv]
    field_simp [hdiag i, hden]
  let ediag : ℝ := (1 + es) / (1 + δ) - 1
  let d : Fin n → ℝ := fun j ↦
    if hj : j.val < i.val then D ⟨j.val, hj⟩
    else if j = i then ediag else 0
  let Ei : Fin n → ℝ := fun j ↦ L i j * d j
  have hediag : |ediag| ≤ gamma fp.u (q + 1) := by
    dsimp [ediag]
    exact one_add_div_error fp.u_nonneg hq1valid hes hδ
  have hdBound : ∀ j, |d j| ≤ gamma fp.u n := by
    intro j
    dsimp [d]
    split
    next hj =>
      exact le_trans (hD ⟨j.val, hj⟩)
        (gamma_mono_nat fp.u_nonneg hvalid (by dsimp [q]; omega))
    next hj =>
      split
      next hji =>
        exact le_trans hediag
          (gamma_mono_nat fp.u_nonneg hvalid (by dsimp [q]; omega))
      next hji =>
        simpa using gamma_nonneg_of_valid fp.u_nonneg hvalid
  refine ⟨Ei, ?_, ?_⟩
  · have hsum := fin_sum_eq_sum_before_add
        (fun j : Fin n ↦ (L i j + Ei j) * y j) i (by
          intro j hij
          have hL : L i j = 0 := hlower i j hij
          simp [Ei, hL])
    rw [hsum]
    have hprev :
        (∑ t : Fin i.val,
            (L i ⟨t.val, by omega⟩ + Ei ⟨t.val, by omega⟩) *
              y ⟨t.val, by omega⟩) =
          ∑ t : Fin q, a t * xx t * (1 + D t) := by
      dsimp [q]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [Ei, d, a, xx]
      split
      next hj => ring
      next hj => omega
    rw [hprev]
    have hdiagterm : (L i i + Ei i) * y i =
        L i i * y i * (1 + ediag) := by
      simp only [Ei, d]
      split
      next hi => omega
      next hi =>
        simp only [↓reduceIte]
        ring
    change (∑ t : Fin q, a t * xx t * (1 + D t)) +
      (L i i + Ei i) * y i = rhs i
    rw [hdiagterm]
    change rhs i = s * (1 + es) +
      ∑ t : Fin q, a t * xx t * (1 + D t) at hfold
    rw [hfold, hs]
    dsimp [ediag]
    field_simp [hden]
    ring
  · intro j
    simp only [Ei, abs_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hdBound j) (abs_nonneg _)

private lemma rounded_forward_sub_backward
    (fp : StandardFPModel) (n : ℕ) (L : P15Matrix n)
    (rhs : P15Vector n) (hdiag : ∀ i, L i i ≠ 0)
    (hlower : p15LowerTriangular L) (hvalid : GammaValid fp.u n) :
    ∃ E : P15Matrix n,
      p15RectFrobNorm E ≤ gamma fp.u n * p15RectFrobNorm L ∧
      p15RectMatVec (p15RectAdd L E)
        (roundedForwardSub fp n L rhs) = rhs := by
  classical
  choose E hEq hBound using fun i ↦
    rounded_forward_sub_row_backward fp n L rhs hdiag hlower hvalid i
  refine ⟨fun i j ↦ E i j, ?_, ?_⟩
  · apply p15_frob_bound_of_entrywise (gamma fp.u n)
      (gamma_nonneg_of_valid fp.u_nonneg hvalid)
    intro i j
    exact hBound i j
  · funext i
    simpa [p15RectMatVec, p15RectAdd] using hEq i

private lemma p15_rect_mat_mul_vec {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  simp only [p15RectMatVec, p15RectMatMul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- P15-T2: the two-block instance of equation (4.22) in the proof of
Theorem 4.4, with the source's low-rank and triangular-solve perturbations. -/
theorem p15_t2_two_block_equation_4_22
    {b r : ℕ} (fp : StandardFPModel)
    (T₀ T₁ : P15Matrix b) (X Y : P15RectMatrix b r)
    (v₀ v₁ : P15Vector b)
    (hT₀diag : ∀ i, T₀ i i ≠ 0)
    (hT₁diag : ∀ i, T₁ i i ≠ 0)
    (hT₀lower : p15LowerTriangular T₀)
    (hT₁lower : p15LowerTriangular T₁)
    (hb : GammaValid fp.u b) (hr : GammaValid fp.u r) :
    let x₀ := roundedForwardSub fp b T₀ v₀
    let wInner := p15RoundedRectMatVec fp (p15RectTranspose Y) x₀
    let wHat := p15RoundedRectMatVec fp X wInner
    let rhsHat := fun i ↦ fp.fl_sub (v₁ i) (wHat i)
    let x₁ := roundedForwardSub fp b T₁ rhsHat
    ∃ ΔT₀ : P15Matrix b, ∃ ΔYT : P15RectMatrix r b,
      ∃ ΔX : P15RectMatrix b r, ∃ θ : P15Vector b,
      ∃ ΔT₁ : P15Matrix b, ∃ ΔT₁₀ : P15Matrix b,
        p15RectFrobNorm ΔT₀ ≤ gamma fp.u b * p15RectFrobNorm T₀ ∧
        p15RectFrobNorm ΔYT ≤
          gamma fp.u b * p15RectFrobNorm (p15RectTranspose Y) ∧
        p15RectFrobNorm ΔX ≤ gamma fp.u r * p15RectFrobNorm X ∧
        (∀ i, |θ i| ≤ fp.u) ∧
        p15RectFrobNorm ΔT₁ ≤ gamma fp.u b * p15RectFrobNorm T₁ ∧
        p15RectMatVec (p15RectAdd T₀ ΔT₀) x₀ = v₀ ∧
        wInner = p15RectMatVec
          (p15RectAdd (p15RectTranspose Y) ΔYT) x₀ ∧
        wHat = p15RectMatVec (p15RectAdd X ΔX) wInner ∧
        (∀ i, rhsHat i = (v₁ i - wHat i) * (1 + θ i)) ∧
        p15RectMatVec (p15RectAdd T₁ ΔT₁) x₁ = rhsHat ∧
        (∀ i j,
          p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j =
            (1 + θ i) *
              p15RectMatMul (p15RectAdd X ΔX)
                (p15RectAdd (p15RectTranspose Y) ΔYT) i j) ∧
        ∀ i,
          p15RectMatVec
                (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i +
              p15RectMatVec (p15RectAdd T₁ ΔT₁) x₁ i =
            v₁ i * (1 + θ i) := by
  -- PROOF_START P15-T2-H001
  dsimp only
  obtain ⟨ΔT₀, hΔT₀, hsolve₀⟩ :=
    rounded_forward_sub_backward fp b T₀ v₀ hT₀diag hT₀lower hb
  obtain ⟨ΔYT, hwInner, hΔYT⟩ :=
    rounded_rect_mat_vec_backward fp (p15RectTranspose Y)
      (roundedForwardSub fp b T₀ v₀) hb
  obtain ⟨ΔX, hwHat, hΔX⟩ :=
    rounded_rect_mat_vec_backward fp X
      (p15RoundedRectMatVec fp (p15RectTranspose Y)
        (roundedForwardSub fp b T₀ v₀)) hr
  choose θ hθ hrhs using fun i ↦ fp.model_sub (v₁ i)
    (p15RoundedRectMatVec fp X
      (p15RoundedRectMatVec fp (p15RectTranspose Y)
        (roundedForwardSub fp b T₀ v₀)) i)
  obtain ⟨ΔT₁, hΔT₁, hsolve₁⟩ :=
    rounded_forward_sub_backward fp b T₁
      (fun i ↦ fp.fl_sub (v₁ i)
        (p15RoundedRectMatVec fp X
          (p15RoundedRectMatVec fp (p15RectTranspose Y)
            (roundedForwardSub fp b T₀ v₀)) i))
      hT₁diag hT₁lower hb
  let ΔT₁₀ : P15Matrix b := fun i j ↦
    (1 + θ i) *
        p15RectMatMul (p15RectAdd X ΔX)
          (p15RectAdd (p15RectTranspose Y) ΔYT) i j -
      p15LowRankMatrix X Y i j
  refine ⟨ΔT₀, ΔYT, ΔX, θ, ΔT₁, ΔT₁₀,
    hΔT₀, hΔYT, hΔX, hθ, hΔT₁, hsolve₀, hwInner, hwHat,
    hrhs, hsolve₁, ?_, ?_⟩
  · intro i j
    simp only [p15RectAdd, ΔT₁₀]
    ring
  · intro i
    let x₀ := roundedForwardSub fp b T₀ v₀
    let wInner := p15RoundedRectMatVec fp (p15RectTranspose Y) x₀
    let wHat := p15RoundedRectMatVec fp X wInner
    let rhsHat : P15Vector b := fun k ↦ fp.fl_sub (v₁ k) (wHat k)
    have hproduct :
        p15RectMatVec
            (p15RectMatMul (p15RectAdd X ΔX)
              (p15RectAdd (p15RectTranspose Y) ΔYT)) x₀ = wHat := by
      rw [p15_rect_mat_mul_vec]
      change p15RectMatVec (p15RectAdd X ΔX)
        (p15RectMatVec (p15RectAdd (p15RectTranspose Y) ΔYT) x₀) =
          wHat
      rw [← hwInner]
      exact hwHat.symm
    have hlow :
        p15RectMatVec
            (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i =
          (1 + θ i) * wHat i := by
      simp only [p15RectMatVec]
      apply Eq.trans ?_ (congrArg (fun z : ℝ ↦ (1 + θ i) * z)
        (congrFun hproduct i))
      change (∑ j : Fin b,
          p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j * x₀ j) =
        (1 + θ i) *
          (∑ j : Fin b,
            p15RectMatMul (p15RectAdd X ΔX)
              (p15RectAdd (p15RectTranspose Y) ΔYT) i j * x₀ j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [p15RectAdd, ΔT₁₀]
      ring
    change
      p15RectMatVec
            (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i +
          p15RectMatVec (p15RectAdd T₁ ΔT₁)
            (roundedForwardSub fp b T₁ rhsHat) i =
        v₁ i * (1 + θ i)
    rw [hlow]
    have hsolve₁i := congrFun hsolve₁ i
    change p15RectMatVec (p15RectAdd T₁ ΔT₁)
      (roundedForwardSub fp b T₁ rhsHat) i = rhsHat i at hsolve₁i
    rw [hsolve₁i]
    have hrhsi := hrhs i
    change rhsHat i = (v₁ i - wHat i) * (1 + θ i) at hrhsi
    rw [hrhsi]
    ring

end HighamBench
