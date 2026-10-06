import HighamBench.P15Definitions

namespace HighamBench

private lemma gamma_nonneg_of_valid {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (h : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at h
  unfold gamma
  have hden : 0 < 1 - (n : ℝ) * u := by linarith
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hden.le

private lemma abs_le_gamma_one {u d : ℝ} (hu : 0 ≤ u)
    (hvalid : GammaValid u 1) (hd : |d| ≤ u) : |d| ≤ gamma u 1 := by
  unfold GammaValid at hvalid
  unfold gamma
  norm_num at hvalid ⊢
  have hden : 0 < 1 - u := by linarith
  calc
    |d| ≤ u := hd
    _ ≤ u / (1 - u) := by
      rw [le_div_iff₀ hden]
      nlinarith

private lemma abs_le_gamma_succ {u d : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hvalid : GammaValid u (n + 1)) (hd : |d| ≤ u) :
    |d| ≤ gamma u (n + 1) := by
  unfold GammaValid at hvalid
  unfold gamma
  push_cast at hvalid ⊢
  have hden : 0 < 1 - ((n : ℝ) + 1) * u := by linarith
  calc
    |d| ≤ u := hd
    _ ≤ ((n : ℝ) + 1) * u / (1 - ((n : ℝ) + 1) * u) := by
      rw [le_div_iff₀ hden]
      have hn : 1 ≤ (n : ℝ) + 1 := by norm_num
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) hu]

private lemma gamma_compose {u a d : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hvalid : GammaValid u (n + 1))
    (ha : |a| ≤ gamma u n) (hd : |d| ≤ u) :
    |a + d + a * d| ≤ gamma u (n + 1) := by
  have hn : GammaValid u n := by
    unfold GammaValid at hvalid ⊢
    push_cast at hvalid ⊢
    nlinarith
  have hgn := gamma_nonneg_of_valid hu hn
  have habs : |a + d + a * d| ≤
      gamma u n + u + gamma u n * u := by
    calc
      |a + d + a * d| ≤ |a| + |d| + |a| * |d| := by
        calc
          |a + d + a * d| ≤ |a| + |d| + |a * d| := by
            calc
              |a + d + a * d| ≤ |a + d| + |a * d| := abs_add_le _ _
              _ ≤ (|a| + |d|) + |a * d| := by
                gcongr
                exact abs_add_le _ _
          _ = |a| + |d| + |a| * |d| := by rw [abs_mul]
      _ ≤ gamma u n + u + gamma u n * u := by
        gcongr
  apply habs.trans
  unfold GammaValid at hvalid hn
  unfold gamma
  push_cast at hvalid hn ⊢
  have hd1 : 0 < 1 - (n : ℝ) * u := by linarith
  have hd2 : 0 < 1 - ((n : ℝ) + 1) * u := by linarith
  rw [le_div_iff₀ hd2]
  field_simp [ne_of_gt hd1]
  ring_nf
  nlinarith

private lemma gamma_mono {u : ℝ} {k n : ℕ} (hu : 0 ≤ u)
    (hkn : k ≤ n) (hvalid : GammaValid u n) : gamma u k ≤ gamma u n := by
  have hkvalid : GammaValid u k := by
    unfold GammaValid at hvalid ⊢
    have hcast : (k : ℝ) ≤ n := by exact_mod_cast hkn
    nlinarith [mul_le_mul_of_nonneg_right hcast hu]
  unfold GammaValid at hvalid hkvalid
  unfold gamma
  have hdk : 0 < 1 - (k : ℝ) * u := by linarith
  have hdn : 0 < 1 - (n : ℝ) * u := by linarith
  rw [div_le_div_iff₀ hdk hdn]
  have hcast : (k : ℝ) ≤ n := by exact_mod_cast hkn
  nlinarith [mul_le_mul_of_nonneg_right hcast hu]

private lemma gamma_inverse_compose {u a d : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hvalid : GammaValid u (n + 1))
    (ha : |a| ≤ gamma u n) (hd : |d| ≤ u) :
    |(1 + a) / (1 + d) - 1| ≤ gamma u (n + 1) := by
  have hn : GammaValid u n := by
    unfold GammaValid at hvalid ⊢
    push_cast at hvalid ⊢
    nlinarith
  have hu_lt_one : u < 1 := by
    unfold GammaValid at hvalid
    push_cast at hvalid
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hn1 hu]
  have hdlo : -u ≤ d := (abs_le.mp hd).1
  have hden : 0 < 1 + d := by linarith
  have hgn := gamma_nonneg_of_valid hu hn
  have hnum : |a - d| ≤ gamma u n + u := by
    calc
      |a - d| = |a + -d| := by ring_nf
      _ ≤ |a| + |-d| := abs_add_le _ _
      _ = |a| + |d| := by rw [abs_neg]
      _ ≤ gamma u n + u := add_le_add ha hd
  rw [show (1 + a) / (1 + d) - 1 = (a - d) / (1 + d) by
    field_simp
    ring]
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  apply hnum.trans
  unfold GammaValid at hvalid hn
  unfold gamma
  push_cast at hvalid hn ⊢
  have hd0 : 0 < 1 - (n : ℝ) * u := by linarith
  have hd1 : 0 < 1 - ((n : ℝ) + 1) * u := by linarith
  have halg :
      (n : ℝ) * u / (1 - (n : ℝ) * u) + u ≤
        (((n : ℝ) + 1) * u / (1 - ((n : ℝ) + 1) * u)) * (1 - u) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hd1]
    field_simp [ne_of_gt hd0]
    ring_nf
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg u)]
  calc
    (n : ℝ) * u / (1 - (n : ℝ) * u) + u ≤
        (((n : ℝ) + 1) * u / (1 - ((n : ℝ) + 1) * u)) * (1 - u) := halg
    _ ≤ ((n : ℝ) + 1) * u / (1 - ((n : ℝ) + 1) * u) * (1 + d) := by
      apply mul_le_mul_of_nonneg_left
      · linarith
      · exact div_nonneg (mul_nonneg (by positivity) hu) hd1.le

private lemma roundedDotProduct_backward (fp : StandardFPModel) :
    ∀ (n : ℕ) (x y : Fin n → ℝ), GammaValid fp.u n →
      ∃ θ : Fin n → ℝ,
        (∀ i, |θ i| ≤ gamma fp.u n) ∧
        roundedDotProduct fp n x y =
          ∑ i : Fin n, (x i * (1 + θ i)) * y i := by
  intro n
  induction n with
  | zero =>
      intro x y h
      refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp [roundedDotProduct]
  | succ n ih =>
      cases n with
      | zero =>
          intro x y hvalid
          obtain ⟨d, hd, heq⟩ := fp.model_mul (x 0) (y 0)
          refine ⟨fun _ => d, ?_, ?_⟩
          · intro i
            exact abs_le_gamma_one fp.u_nonneg hvalid hd
          · simp [roundedDotProduct, heq]
            ring
      | succ n =>
          intro x y hvalid
          let x' : Fin (n + 1) → ℝ := fun i => x i.castSucc
          let y' : Fin (n + 1) → ℝ := fun i => y i.castSucc
          have hprev : GammaValid fp.u (n + 1) := by
            unfold GammaValid at hvalid ⊢
            push_cast at hvalid ⊢
            nlinarith [fp.u_nonneg]
          obtain ⟨a, ha, hfold⟩ := ih x' y' hprev
          obtain ⟨dm, hdm, hm⟩ :=
            fp.model_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))
          obtain ⟨da, hda, hadd⟩ := fp.model_add
            (roundedDotProduct fp (n + 1) x' y')
            (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1))))
          let anew : Fin (n + 1) → ℝ := fun i => a i + da + a i * da
          let alast : ℝ := dm + da + dm * da
          let θ : Fin (n + 2) → ℝ := Fin.lastCases alast anew
          refine ⟨θ, ?_, ?_⟩
          · intro i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simpa only [θ, Fin.lastCases_last, alast] using
                (gamma_compose fp.u_nonneg hvalid
                  (abs_le_gamma_succ fp.u_nonneg hprev hdm) hda)
            · simpa only [θ, Fin.lastCases_castSucc, anew] using
                (gamma_compose fp.u_nonneg hvalid (ha j) hda)
          · rw [show roundedDotProduct fp (n + 2) x y =
                fp.fl_add (roundedDotProduct fp (n + 1) x' y')
                  (fp.fl_mul (x (Fin.last (n + 1)))
                    (y (Fin.last (n + 1)))) by
                simp only [roundedDotProduct, Fin.foldl_succ_last]
                rfl]
            rw [hadd, hfold, hm]
            rw [Fin.sum_univ_castSucc
              (fun i : Fin (n + 2) => (x i * (1 + θ i)) * y i)]
            simp only [θ, Fin.lastCases_castSucc, Fin.lastCases_last, anew, alast,
              x', y']
            rw [add_mul, Finset.sum_mul]
            apply congrArg₂ (· + ·)
            · apply Finset.sum_congr rfl
              intro i hi
              ring
            · ring

private lemma roundedRectMatVec_backward (fp : StandardFPModel)
    {m n : ℕ} (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hvalid : GammaValid fp.u n) :
    ∃ Δ : P15RectMatrix m n,
      p15RectFrobNorm Δ ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x = p15RectMatVec (p15RectAdd A Δ) x := by
  have hrow : ∀ i : Fin m, ∃ θ : Fin n → ℝ,
      (∀ j, |θ j| ≤ gamma fp.u n) ∧
      roundedDotProduct fp n (A i) x =
        ∑ j : Fin n, (A i j * (1 + θ j)) * x j := by
    intro i
    exact roundedDotProduct_backward fp n (A i) x hvalid
  choose θ hθ hdot using hrow
  let Δ : P15RectMatrix m n := fun i j => A i j * θ i j
  refine ⟨Δ, ?_, ?_⟩
  · have hg := gamma_nonneg_of_valid fp.u_nonneg hvalid
    have hterm : ∀ i : Fin m, ∀ j : Fin n,
        (Δ i j) ^ 2 ≤ (gamma fp.u n) ^ 2 * (A i j) ^ 2 := by
      intro i j
      have hsθ : (θ i j) ^ 2 ≤ (gamma fp.u n) ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg hg] using hθ i j
      dsimp [Δ]
      rw [mul_pow]
      nlinarith [mul_le_mul_of_nonneg_left hsθ (sq_nonneg (A i j))]
    unfold p15RectFrobNorm
    have hsums : (∑ i : Fin m, ∑ j : Fin n, (Δ i j) ^ 2) ≤
        (gamma fp.u n) ^ 2 * (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2) := by
      calc
        (∑ i : Fin m, ∑ j : Fin n, (Δ i j) ^ 2) ≤
            ∑ i : Fin m, ∑ j : Fin n,
              (gamma fp.u n) ^ 2 * (A i j) ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact hterm i j
        _ = (gamma fp.u n) ^ 2 *
            (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2) := by
          rw [Finset.mul_sum]
          congr 1
          funext i
          rw [Finset.mul_sum]
    calc
      Real.sqrt (∑ i : Fin m, ∑ j : Fin n, (Δ i j) ^ 2) ≤
          Real.sqrt ((gamma fp.u n) ^ 2 *
            (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2)) :=
        Real.sqrt_le_sqrt hsums
      _ = gamma fp.u n *
          Real.sqrt (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
          abs_of_nonneg hg]
  · funext i
    change roundedDotProduct fp n (A i) x =
      ∑ j : Fin n, (A i j + Δ i j) * x j
    rw [hdot i]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [Δ]
    ring

private lemma roundedForwardSubSteps_preserve (fp : StandardFPModel)
    (n : ℕ) (L : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      i.val < n - k →
      roundedForwardSubSteps fp n L v k hk x i = x i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      simp [roundedForwardSubSteps]
  | succ k ih =>
      intro hk x i hi
      rw [roundedForwardSubSteps]
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (v ik)
      rw [ih]
      · have hne : i ≠ ik := by
          intro heq
          have : i.val = ik.val := congrArg Fin.val heq
          dsimp [ik] at this
          omega
        simp [Function.update, hne, ik]
      · dsimp [ik]
        omega

private lemma roundedForwardSubSteps_row (fp : StandardFPModel)
    (n : ℕ) (L : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      let y := roundedForwardSubSteps fp n L v k hk x
      ∀ i : Fin n, n - k ≤ i.val →
        y i = fp.fl_div
          (Fin.foldl i.val
            (fun acc (t : Fin i.val) =>
              fp.fl_sub acc
                (fp.fl_mul (L i ⟨t.val, by omega⟩)
                  (y ⟨t.val, by omega⟩)))
            (v i))
          (L i i) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      dsimp
      intro i hi
      omega
  | succ k ih =>
      intro hk x
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (v ik)
      let x' := Function.update x ik (fp.fl_div s (L ik ik))
      let y := roundedForwardSubSteps fp n L v k (Nat.le_of_succ_le hk) x'
      have hydef : roundedForwardSubSteps fp n L v (k + 1) hk x = y := by
        rw [roundedForwardSubSteps]
      dsimp only
      intro i hi
      rw [hydef]
      by_cases hieq : i = ik
      · subst i
        have hiklt : ik.val < n - k := by
          dsimp [ik]
          omega
        have hyik : y ik = x' ik :=
          roundedForwardSubSteps_preserve fp n L v k
            (Nat.le_of_succ_le hk) x' ik hiklt
        rw [hyik]
        have hxik : x' ik = fp.fl_div s (L ik ik) := by
          simp [x']
        rw [hxik]
        congr 2
        have hfold :
            Fin.foldl (n - k - 1)
                (fun acc (t : Fin (n - k - 1)) =>
                  fp.fl_sub acc
                    (fp.fl_mul (L ik ⟨t.val, by omega⟩)
                      (x ⟨t.val, by omega⟩))) (v ik) =
              Fin.foldl (n - k - 1)
                (fun acc (t : Fin (n - k - 1)) =>
                  fp.fl_sub acc
                    (fp.fl_mul (L ik ⟨t.val, by omega⟩)
                      (y ⟨t.val, by omega⟩))) (v ik) := by
          apply congrArg (fun f : ℝ → Fin (n - k - 1) → ℝ =>
            Fin.foldl (n - k - 1) f (v ik))
          funext a t
          congr 3
          have htlt : (⟨t.val, by omega⟩ : Fin n).val < n - k := by
            change t.val < n - k
            exact lt_trans t.isLt (by omega)
          have hyt := roundedForwardSubSteps_preserve fp n L v k
            (Nat.le_of_succ_le hk) x' (⟨t.val, by omega⟩ : Fin n) htlt
          have hne : (⟨t.val, by omega⟩ : Fin n) ≠ ik := by
            intro heq
            have := congrArg Fin.val heq
            dsimp [ik] at this
            omega
          symm
          calc
            y (⟨t.val, by omega⟩ : Fin n) =
                x' (⟨t.val, by omega⟩ : Fin n) := by simpa [y] using hyt
            _ = x (⟨t.val, by omega⟩ : Fin n) := by simp [x', hne]
        simpa only [s, show ik.val = n - k - 1 by rfl] using hfold
      · have hilt : n - k ≤ i.val := by
          have hiq : n - k - 1 ≤ i.val := by
            dsimp [ik] at hi ⊢
            omega
          have hneval : i.val ≠ n - k - 1 := by
            intro he
            apply hieq
            apply Fin.ext
            simpa [ik]
          omega
        exact ih (Nat.le_of_succ_le hk) x' i hilt

private lemma roundedSubFold_backward (fp : StandardFPModel) :
    ∀ (k : ℕ) (a x : Fin k → ℝ) (v : ℝ), GammaValid fp.u k →
      ∃ c : ℝ, ∃ e : Fin k → ℝ,
        |c| ≤ gamma fp.u k ∧
        (∀ j, |e j| ≤ gamma fp.u k) ∧
        (1 + c) *
            Fin.foldl k
              (fun acc j => fp.fl_sub acc (fp.fl_mul (a j) (x j))) v +
          ∑ j : Fin k, (a j * (1 + e j)) * x j = v := by
  intro k
  induction k with
  | zero =>
      intro a x v hvalid
      refine ⟨0, fun j => Fin.elim0 j, ?_, ?_, ?_⟩
      · simp [gamma]
      · intro j
        exact Fin.elim0 j
      · simp
  | succ k ih =>
      intro a x v hvalid
      let a' : Fin k → ℝ := fun j => a j.castSucc
      let x' : Fin k → ℝ := fun j => x j.castSucc
      have hprev : GammaValid fp.u k := by
        unfold GammaValid at hvalid ⊢
        push_cast at hvalid ⊢
        nlinarith [fp.u_nonneg]
      obtain ⟨c, e, hc, he, hEq⟩ := ih a' x' v hprev
      let sPrev := Fin.foldl k
        (fun acc j => fp.fl_sub acc (fp.fl_mul (a' j) (x' j))) v
      obtain ⟨dm, hdm, hm⟩ :=
        fp.model_mul (a (Fin.last k)) (x (Fin.last k))
      obtain ⟨ds, hds, hs⟩ := fp.model_sub sPrev
        (fp.fl_mul (a (Fin.last k)) (x (Fin.last k)))
      let cnew := (1 + c) / (1 + ds) - 1
      let enew := c + dm + c * dm
      let eall : Fin (k + 1) → ℝ := Fin.lastCases enew e
      refine ⟨cnew, eall, ?_, ?_, ?_⟩
      · exact gamma_inverse_compose fp.u_nonneg hvalid hc hds
      · intro j
        refine Fin.lastCases ?_ (fun t => ?_) j
        · simpa only [eall, Fin.lastCases_last, enew] using
            (gamma_compose fp.u_nonneg hvalid hc hdm)
        · simpa only [eall, Fin.lastCases_castSucc] using
            (he t |>.trans (gamma_mono fp.u_nonneg (Nat.le_succ k) hvalid))
      · rw [Fin.foldl_succ_last]
        change (1 + cnew) *
              fp.fl_sub sPrev
                (fp.fl_mul (a (Fin.last k)) (x (Fin.last k))) +
            ∑ j : Fin (k + 1), (a j * (1 + eall j)) * x j = v
        rw [hs, hm, Fin.sum_univ_castSucc]
        simp only [eall, Fin.lastCases_castSucc, Fin.lastCases_last, a', x']
        rw [← add_assoc]
        have hu_lt_one : fp.u < 1 := by
          unfold GammaValid at hvalid
          push_cast at hvalid
          have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by norm_num
          nlinarith [mul_le_mul_of_nonneg_right hk1 fp.u_nonneg]
        have hdslo : -fp.u ≤ ds := (abs_le.mp hds).1
        have hden : 1 + ds ≠ 0 := by linarith
        calc
          (1 + cnew) *
                  ((sPrev - a (Fin.last k) * x (Fin.last k) * (1 + dm)) *
                    (1 + ds)) +
                (∑ j : Fin k, (a j.castSucc * (1 + e j)) * x j.castSucc) +
              a (Fin.last k) * (1 + enew) * x (Fin.last k) =
              (1 + c) * sPrev +
                ∑ j : Fin k, (a' j * (1 + e j)) * x' j := by
            dsimp [cnew, enew, a', x']
            field_simp [hden]
            ring
          _ = v := hEq

private lemma finSum_eq_prefix_add_of_zero {n : ℕ} (f : Fin n → ℝ)
    (i : Fin n) (hzero : ∀ j : Fin n, i.val < j.val → f j = 0) :
    (∑ j : Fin n, f j) =
      (∑ t : Fin i.val, f ⟨t.val, lt_trans t.isLt i.isLt⟩) + f i := by
  classical
  let g : ℕ → ℝ := fun k => if hk : k < n then f ⟨k, hk⟩ else 0
  have hall : (∑ j : Fin n, f j) = ∑ k ∈ Finset.range n, g k := by
    rw [← Fin.sum_univ_eq_sum_range g n]
    apply Finset.sum_congr rfl
    intro j hj
    simp [g]
  have hsub : Finset.range (i.val + 1) ⊆ Finset.range n := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have hrange : (∑ k ∈ Finset.range n, g k) =
      ∑ k ∈ Finset.range (i.val + 1), g k := by
    symm
    apply Finset.sum_subset hsub
    intro k hkn hki
    have hkle : i.val < k := by
      simpa only [Finset.mem_range, not_lt] using hki
    have hkn' : k < n := Finset.mem_range.mp hkn
    simp [g, hkn', hzero ⟨k, hkn'⟩ hkle]
  rw [hall, hrange, Finset.sum_range_succ]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range g i.val]
    apply Finset.sum_congr rfl
    intro t ht
    have htN : t.val < n := lt_trans t.isLt i.isLt
    simp only [g, dif_pos htN]
  · simp [g]

private lemma roundedForwardSub_backward (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (v : P15Vector n)
    (hdiag : ∀ i, L i i ≠ 0) (hlower : p15LowerTriangular L)
    (hvalid : GammaValid fp.u n) :
    ∃ Δ : P15Matrix n,
      p15RectFrobNorm Δ ≤ gamma fp.u n * p15RectFrobNorm L ∧
      p15RectMatVec (p15RectAdd L Δ) (roundedForwardSub fp n L v) = v := by
  let xhat := roundedForwardSub fp n L v
  have hxrow : ∀ i : Fin n,
      xhat i = fp.fl_div
        (Fin.foldl i.val
          (fun acc (t : Fin i.val) =>
            fp.fl_sub acc
              (fp.fl_mul (L i ⟨t.val, by omega⟩)
                (xhat ⟨t.val, by omega⟩)))
          (v i))
        (L i i) := by
    intro i
    simpa only [xhat, roundedForwardSub] using
      (roundedForwardSubSteps_row fp n L v n (le_refl n) (fun _ => 0)
        i (by omega))
  have hrow : ∀ i : Fin n, ∃ eall : Fin n → ℝ,
      (∀ j, |eall j| ≤ gamma fp.u n) ∧
      (∑ j : Fin n, (L i j * (1 + eall j)) * xhat j) = v i := by
    intro i
    let a : Fin i.val → ℝ := fun t => L i ⟨t.val, lt_trans t.isLt i.isLt⟩
    let xx : Fin i.val → ℝ := fun t => xhat ⟨t.val, lt_trans t.isLt i.isLt⟩
    have hvalidi : GammaValid fp.u i.val := by
      unfold GammaValid at hvalid ⊢
      have hi : (i.val : ℝ) ≤ n := by
        exact_mod_cast (Nat.le_of_lt i.isLt)
      nlinarith [mul_le_mul_of_nonneg_right hi fp.u_nonneg]
    obtain ⟨c, e, hc, he, hfold⟩ :=
      roundedSubFold_backward fp i.val a xx (v i) hvalidi
    let s := Fin.foldl i.val
      (fun acc (t : Fin i.val) =>
        fp.fl_sub acc (fp.fl_mul (a t) (xx t))) (v i)
    obtain ⟨dd, hdd, hdiv⟩ := fp.model_div s (L i i) (hdiag i)
    have hvalidSucc : GammaValid fp.u (i.val + 1) := by
      unfold GammaValid at hvalid ⊢
      have hi : ((i.val + 1 : ℕ) : ℝ) ≤ n := by
        exact_mod_cast i.isLt
      nlinarith [mul_le_mul_of_nonneg_right hi fp.u_nonneg]
    let ediag := (1 + c) / (1 + dd) - 1
    let eall : Fin n → ℝ := fun j =>
      if hj : j.val < i.val then e ⟨j.val, hj⟩
      else if j = i then ediag else 0
    refine ⟨eall, ?_, ?_⟩
    · intro j
      dsimp only [eall]
      split_ifs with hj hji
      · exact (he ⟨j.val, hj⟩).trans
          (gamma_mono fp.u_nonneg (Nat.le_of_lt i.isLt) hvalid)
      · simpa only [ediag] using
          (gamma_inverse_compose fp.u_nonneg hvalidSucc hc hdd |>.trans
            (gamma_mono fp.u_nonneg (Nat.succ_le_iff.mpr i.isLt) hvalid))
      · simpa using gamma_nonneg_of_valid fp.u_nonneg hvalid
    · have hsum := finSum_eq_prefix_add_of_zero
          (fun j : Fin n => (L i j * (1 + eall j)) * xhat j) i
          (by
            intro j hij
            dsimp only
            rw [hlower i j hij]
            ring)
      rw [hsum]
      have hsdef : s = Fin.foldl i.val
          (fun acc (t : Fin i.val) =>
            fp.fl_sub acc
              (fp.fl_mul
                (L i ⟨t.val, lt_trans t.isLt i.isLt⟩)
                (xhat ⟨t.val, lt_trans t.isLt i.isLt⟩))) (v i) := rfl
      have hx : xhat i = s / L i i * (1 + dd) := by
        rw [hxrow i, hdiv]
      have hu_lt_one : fp.u < 1 := by
        unfold GammaValid at hvalidSucc
        push_cast at hvalidSucc
        have hi1 : (1 : ℝ) ≤ (i.val : ℝ) + 1 := by norm_num
        nlinarith [mul_le_mul_of_nonneg_right hi1 fp.u_nonneg]
      have hddlo : -fp.u ≤ dd := (abs_le.mp hdd).1
      have hddne : 1 + dd ≠ 0 := by linarith
      have hterm : (L i i * (1 + ediag)) * xhat i = (1 + c) * s := by
        rw [hx]
        dsimp [ediag]
        field_simp [hdiag i, hddne]
        ring
      have hprefix :
          (∑ t : Fin i.val,
              (L i ⟨t.val, lt_trans t.isLt i.isLt⟩ *
                (1 + eall ⟨t.val, lt_trans t.isLt i.isLt⟩)) *
                xhat ⟨t.val, lt_trans t.isLt i.isLt⟩) =
            ∑ t : Fin i.val, (a t * (1 + e t)) * xx t := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [eall, dif_pos t.isLt, a, xx]
      rw [hprefix]
      have hdiagE : eall i = ediag := by
        simp [eall]
      change (∑ t : Fin i.val, (a t * (1 + e t)) * xx t) +
        (L i i * (1 + eall i)) * xhat i = v i
      rw [hdiagE, hterm]
      rw [add_comm]
      exact hfold
  choose e he hEq using hrow
  let Δ : P15Matrix n := fun i j => L i j * e i j
  refine ⟨Δ, ?_, ?_⟩
  · have hg := gamma_nonneg_of_valid fp.u_nonneg hvalid
    unfold p15RectFrobNorm
    have hsums : (∑ i : Fin n, ∑ j : Fin n, (Δ i j) ^ 2) ≤
        (gamma fp.u n) ^ 2 * (∑ i : Fin n, ∑ j : Fin n, (L i j) ^ 2) := by
      calc
        (∑ i : Fin n, ∑ j : Fin n, (Δ i j) ^ 2) ≤
            ∑ i : Fin n, ∑ j : Fin n,
              (gamma fp.u n) ^ 2 * (L i j) ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          have hse : (e i j) ^ 2 ≤ (gamma fp.u n) ^ 2 := by
            rw [sq_le_sq]
            simpa [abs_of_nonneg hg] using he i j
          dsimp [Δ]
          rw [mul_pow]
          nlinarith [mul_le_mul_of_nonneg_left hse (sq_nonneg (L i j))]
        _ = (gamma fp.u n) ^ 2 *
            (∑ i : Fin n, ∑ j : Fin n, (L i j) ^ 2) := by
          rw [Finset.mul_sum]
          congr 1
          funext i
          rw [Finset.mul_sum]
    calc
      Real.sqrt (∑ i : Fin n, ∑ j : Fin n, (Δ i j) ^ 2) ≤
          Real.sqrt ((gamma fp.u n) ^ 2 *
            (∑ i : Fin n, ∑ j : Fin n, (L i j) ^ 2)) :=
        Real.sqrt_le_sqrt hsums
      _ = gamma fp.u n *
          Real.sqrt (∑ i : Fin n, ∑ j : Fin n, (L i j) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
          abs_of_nonneg hg]
  · funext i
    change (∑ j : Fin n, (L i j + Δ i j) * xhat j) = v i
    rw [← hEq i]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [Δ]
    ring

private lemma p15RectMatVec_mul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  unfold p15RectMatVec p15RectMatMul
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

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
  set x₀ := roundedForwardSub fp b T₀ v₀
  set wInner := p15RoundedRectMatVec fp (p15RectTranspose Y) x₀
  set wHat := p15RoundedRectMatVec fp X wInner
  set rhsHat : P15Vector b := fun i => fp.fl_sub (v₁ i) (wHat i)
  set x₁ := roundedForwardSub fp b T₁ rhsHat
  obtain ⟨ΔT₀, hΔT₀, hsolve₀⟩ :=
    roundedForwardSub_backward fp b T₀ v₀ hT₀diag hT₀lower hb
  obtain ⟨ΔYT, hΔYT, hInner⟩ :=
    roundedRectMatVec_backward fp (p15RectTranspose Y) x₀ hb
  obtain ⟨ΔX, hΔX, hHat⟩ :=
    roundedRectMatVec_backward fp X wInner hr
  have hsubExists : ∀ i : Fin b, ∃ d : ℝ,
      |d| ≤ fp.u ∧ rhsHat i = (v₁ i - wHat i) * (1 + d) := by
    intro i
    simpa only [rhsHat] using fp.model_sub (v₁ i) (wHat i)
  choose θ hθ hrhs using hsubExists
  obtain ⟨ΔT₁, hΔT₁, hsolve₁⟩ :=
    roundedForwardSub_backward fp b T₁ rhsHat hT₁diag hT₁lower hb
  let ΔT₁₀ : P15Matrix b := fun i j =>
    (1 + θ i) *
        p15RectMatMul (p15RectAdd X ΔX)
          (p15RectAdd (p15RectTranspose Y) ΔYT) i j -
      p15LowRankMatrix X Y i j
  have hblock : ∀ i j,
      p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j =
        (1 + θ i) *
          p15RectMatMul (p15RectAdd X ΔX)
            (p15RectAdd (p15RectTranspose Y) ΔYT) i j := by
    intro i j
    simp only [p15RectAdd, ΔT₁₀]
    ring
  refine ⟨ΔT₀, ΔYT, ΔX, θ, ΔT₁, ΔT₁₀,
    hΔT₀, hΔYT, hΔX, hθ, hΔT₁, ?_, ?_, ?_, hrhs, ?_, hblock, ?_⟩
  · simpa only [x₀] using hsolve₀
  · simpa only [wInner, x₀] using hInner
  · simpa only [wHat, wInner] using hHat
  · simpa only [x₁] using hsolve₁
  · intro i
    have hlowrank :
        p15RectMatVec
            (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i =
          (1 + θ i) * wHat i := by
      change (∑ j : Fin b,
          p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j * x₀ j) =
        (1 + θ i) * wHat i
      simp_rw [hblock i]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      have hassoc := p15RectMatVec_mul
        (p15RectAdd X ΔX)
        (p15RectAdd (p15RectTranspose Y) ΔYT) x₀
      have hinner' :
          p15RectMatVec (p15RectAdd (p15RectTranspose Y) ΔYT) x₀ =
            wInner := hInner.symm
      have hhat' : p15RectMatVec (p15RectAdd X ΔX) wInner = wHat :=
        hHat.symm
      change (1 + θ i) *
          p15RectMatVec
            (p15RectMatMul (p15RectAdd X ΔX)
              (p15RectAdd (p15RectTranspose Y) ΔYT)) x₀ i =
        (1 + θ i) * wHat i
      rw [hassoc, hinner', hhat']
    rw [hlowrank, hsolve₁]
    rw [hrhs]
    ring

end HighamBench
