import HighamBench.P15Definitions

namespace HighamBench

lemma p15_gamma_nonneg {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (h : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at h
  rw [gamma]
  have hden : 0 < 1 - (n : ℝ) * u := by linarith
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hden.le

lemma p15_gamma_mono {u : ℝ} {k n : ℕ} (hu : 0 ≤ u)
    (hkn : k ≤ n) (hn : GammaValid u n) : gamma u k ≤ gamma u n := by
  unfold GammaValid at hn
  have hku : (k : ℝ) * u ≤ (n : ℝ) * u := by
    gcongr
  have hkden : 0 < 1 - (k : ℝ) * u := by linarith
  have hnden : 0 < 1 - (n : ℝ) * u := by linarith
  rw [gamma, gamma]
  apply (div_le_div_iff₀ hkden hnden).2
  nlinarith

lemma p15_u_le_gamma {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hn : GammaValid u n) (hnpos : 1 ≤ n) : u ≤ gamma u n := by
  have h1 : GammaValid u 1 := by
    unfold GammaValid at hn ⊢
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    have := mul_le_mul_of_nonneg_right this hu
    norm_num at this ⊢
    linarith
  have hm := p15_gamma_mono hu hnpos hn
  have hden : 0 < 1 - u := by simpa [GammaValid] using h1
  have hu1 : u ≤ gamma u 1 := by
    rw [gamma]
    norm_num
    exact (le_div_iff₀ hden).2 (by nlinarith)
  exact hu1.trans hm

lemma p15_gamma_succ_bound {u : ℝ} {k n : ℕ} (hu : 0 ≤ u)
    (hks : k + 1 ≤ n) (hn : GammaValid u n) :
    gamma u k + u + gamma u k * u ≤ gamma u (k + 1) := by
  unfold GammaValid at hn
  have hku : ((k + 1 : ℕ) : ℝ) * u ≤ (n : ℝ) * u := by
    gcongr
  have hkden : 0 < 1 - (k : ℝ) * u := by
    have hk : (k : ℝ) * u ≤ ((k + 1 : ℕ) : ℝ) * u := by
      norm_num at *
      nlinarith
    linarith
  have hsden : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
  have hsden' : 0 < 1 - ((k : ℝ) + 1) * u := by
    simpa [Nat.cast_add] using hsden
  rw [gamma, gamma]
  norm_num [Nat.cast_add, Nat.cast_one]
  change (k : ℝ) * u / (1 - (k : ℝ) * u) + u +
      (k : ℝ) * u / (1 - (k : ℝ) * u) * u ≤
    ((k : ℝ) + 1) * u / (1 - ((k : ℝ) + 1) * u)
  have heq : (k : ℝ) * u / (1 - (k : ℝ) * u) + u +
      (k : ℝ) * u / (1 - (k : ℝ) * u) * u =
      ((k : ℝ) + 1) * u / (1 - (k : ℝ) * u) := by
    field_simp [ne_of_gt hkden]
    ring
  rw [heq]
  apply div_le_div_of_nonneg_left (by positivity) hsden'
  nlinarith

lemma p15_compose_error {u : ℝ} {k n : ℕ} (hu : 0 ≤ u)
    (hks : k + 1 ≤ n) (hn : GammaValid u n)
    {e d : ℝ} (he : |e| ≤ gamma u k) (hd : |d| ≤ u) :
    |(1 + e) * (1 + d) - 1| ≤ gamma u (k + 1) := by
  have hgn := p15_gamma_nonneg hu (show GammaValid u k by
    unfold GammaValid at hn ⊢
    have hk : (k : ℝ) * u ≤ (n : ℝ) * u := by
      gcongr
      exact_mod_cast (Nat.le_trans (Nat.le_add_right k 1) hks)
    linarith)
  calc
    |(1 + e) * (1 + d) - 1| = |e + d + e * d| := by ring_nf
    _ ≤ |e| + |d| + |e| * |d| := by
      calc
        |e + d + e * d| ≤ |e + d| + |e * d| := abs_add_le _ _
        _ ≤ (|e| + |d|) + |e * d| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ = |e| + |d| + |e| * |d| := by rw [abs_mul]
    _ ≤ gamma u k + u + gamma u k * u := by gcongr
    _ ≤ gamma u (k + 1) := p15_gamma_succ_bound hu hks hn

lemma p15_fin_foldl_eq_list {n : ℕ} {R : Type*}
    (f : R → Fin n → R) (z : R) :
    Fin.foldl n f z = (List.ofFn fun i : Fin n ↦ i).foldl f z := by
  induction n generalizing R z with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
      rw [Fin.foldl_succ]
      simp only [List.ofFn_succ, List.foldl_cons]
      have hof : (List.ofFn fun i : Fin n ↦ i.succ) =
          (List.ofFn fun i : Fin n ↦ i).map Fin.succ := by
        rw [List.map_ofFn]
        rfl
      rw [hof, List.foldl_map]
      exact ih (fun x i ↦ f x i.succ) (f z 0)

noncomputable def p15RoundedDotList (fp : StandardFPModel)
    (l : List (ℝ × ℝ)) : ℝ :=
  match l with
  | [] => 0
  | z :: zs => zs.foldl
      (fun acc q ↦ fp.fl_add acc (fp.fl_mul q.1 q.2))
      (fp.fl_mul z.1 z.2)

def p15PerturbedDotList (l : List (ℝ × ℝ)) (es : List ℝ) : ℝ :=
  (List.zipWith (fun z e ↦ z.1 * z.2 * (1 + e)) l es).sum

lemma p15RoundedDotList_append {fp : StandardFPModel}
    (l : List (ℝ × ℝ)) (z : ℝ × ℝ) (hl : l ≠ []) :
    p15RoundedDotList fp (l ++ [z]) =
      fp.fl_add (p15RoundedDotList fp l) (fp.fl_mul z.1 z.2) := by
  cases l with
  | nil => contradiction
  | cons a l => simp [p15RoundedDotList, List.foldl_append]

lemma p15PerturbedDotList_map_compose (l : List (ℝ × ℝ))
    (es : List ℝ) (s : ℝ) :
    p15PerturbedDotList l (es.map (fun e ↦ (1 + e) * (1 + s) - 1)) =
      p15PerturbedDotList l es * (1 + s) := by
  unfold p15PerturbedDotList
  rw [List.zipWith_map_right]
  induction l generalizing es with
  | nil => simp
  | cons q qs ih =>
      cases es with
      | nil => simp
      | cons e es =>
          simp only [List.zipWith_cons_cons, List.sum_cons]
          rw [ih]
          ring

lemma p15PerturbedDotList_append (l : List (ℝ × ℝ))
    (es : List ℝ) (z : ℝ × ℝ) (e : ℝ)
    (h : l.length = es.length) :
    p15PerturbedDotList (l ++ [z]) (es ++ [e]) =
      p15PerturbedDotList l es + z.1 * z.2 * (1 + e) := by
  unfold p15PerturbedDotList
  rw [List.zipWith_append h]
  simp

lemma p15RoundedDotList_backward (fp : StandardFPModel)
    (l : List (ℝ × ℝ)) :
    ∀ n, l.length ≤ n → GammaValid fp.u n →
      ∃ es : List ℝ, es.length = l.length ∧
        (∀ e ∈ es, |e| ≤ gamma fp.u n) ∧
        p15RoundedDotList fp l = p15PerturbedDotList l es := by
  induction l using List.reverseRecOn with
  | nil =>
      intro n hlen hn
      exact ⟨[], rfl, by simp, by simp [p15RoundedDotList, p15PerturbedDotList]⟩
  | append_singleton l z ih =>
      intro n hlen hn
      by_cases hl : l = []
      · subst l
        obtain ⟨d, hd, hmul⟩ := fp.model_mul z.1 z.2
        refine ⟨[d], by simp, ?_, ?_⟩
        · intro e he
          simp only [List.mem_singleton] at he
          subst e
          exact hd.trans (p15_u_le_gamma fp.u_nonneg hn (by simpa using hlen))
        · simpa [p15RoundedDotList, p15PerturbedDotList] using hmul
      · have hlpos : 1 ≤ l.length := (List.length_pos_iff.2 hl)
        have hsucc : l.length + 1 ≤ n := by simpa using hlen
        have hllen : l.length ≤ n := le_trans (Nat.le_add_right _ _) hsucc
        have hvalidl : GammaValid fp.u l.length := by
          unfold GammaValid at hn ⊢
          have hmul : (l.length : ℝ) * fp.u ≤ (n : ℝ) * fp.u := by
            gcongr
            exact fp.u_nonneg
          linarith
        obtain ⟨es, heslen, hesbd, hdot⟩ := ih l.length le_rfl hvalidl
        obtain ⟨mu, hmu, hmul⟩ := fp.model_mul z.1 z.2
        obtain ⟨sig, hsig, hadd⟩ :=
          fp.model_add (p15RoundedDotList fp l) (fp.fl_mul z.1 z.2)
        let upd : ℝ → ℝ := fun e ↦ (1 + e) * (1 + sig) - 1
        let enew : ℝ := (1 + mu) * (1 + sig) - 1
        refine ⟨es.map upd ++ [enew], ?_, ?_, ?_⟩
        · simp [heslen]
        · intro e he
          simp only [List.mem_append, List.mem_map, List.mem_singleton] at he
          rcases he with he | rfl
          · rcases he with ⟨e0, he0, rfl⟩
            have hb0 := p15_compose_error fp.u_nonneg
              (n := l.length + 1) (k := l.length) (by omega)
              (show GammaValid fp.u (l.length + 1) by
                unfold GammaValid at hn ⊢
                have hm : ((l.length + 1 : ℕ) : ℝ) * fp.u ≤
                    (n : ℝ) * fp.u := by
                  gcongr
                  exact fp.u_nonneg
                linarith)
              (hesbd e0 he0) hsig
            exact hb0.trans (p15_gamma_mono fp.u_nonneg hsucc hn)
          · have hv2 : GammaValid fp.u 2 := by
              unfold GammaValid at hn ⊢
              have h2n : 2 ≤ n := by omega
              have h2nr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2n
              have hm : (2 : ℝ) * fp.u ≤ (n : ℝ) * fp.u := by
                exact mul_le_mul_of_nonneg_right h2nr fp.u_nonneg
              norm_num at hn ⊢
              linarith
            have hmu1 : |mu| ≤ gamma fp.u 1 :=
              hmu.trans (p15_u_le_gamma fp.u_nonneg
                (show GammaValid fp.u 1 by
                  unfold GammaValid at hv2 ⊢
                  norm_num at hv2 ⊢
                  nlinarith [fp.u_nonneg]) (by omega))
            have hb2 := p15_compose_error fp.u_nonneg
              (n := 2) (k := 1) (by omega) hv2 hmu1 hsig
            exact hb2.trans (p15_gamma_mono fp.u_nonneg (by omega) hn)
        · rw [p15RoundedDotList_append l z hl, hadd, hdot, hmul]
          rw [p15PerturbedDotList_append _ _ _ _ (by simp [heslen])]
          have hold := p15PerturbedDotList_map_compose l es sig
          change p15PerturbedDotList l (es.map upd) = _ at hold
          rw [hold]
          dsimp [enew]
          ring

lemma p15RoundedDotProduct_eq_list (fp : StandardFPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    roundedDotProduct fp n x y =
      p15RoundedDotList fp (List.ofFn fun i ↦ (x i, y i)) := by
  cases n with
  | zero => simp [roundedDotProduct, p15RoundedDotList]
  | succ n =>
      rw [roundedDotProduct]
      rw [p15_fin_foldl_eq_list]
      simp only [List.ofFn_succ]
      rw [p15RoundedDotList]
      have ht : (List.ofFn fun i : Fin n ↦ (x i.succ, y i.succ)) =
          (List.ofFn fun i : Fin n ↦ i).map
            (fun i ↦ (x i.succ, y i.succ)) := by
        rw [List.map_ofFn]
        rfl
      rw [ht, List.foldl_map]

lemma p15RoundedDotProduct_backward (fp : StandardFPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hn : GammaValid fp.u n) :
    ∃ e : Fin n → ℝ, (∀ j, |e j| ≤ gamma fp.u n) ∧
      roundedDotProduct fp n x y = ∑ j, x j * (1 + e j) * y j := by
  let l : List (ℝ × ℝ) := List.ofFn fun j ↦ (x j, y j)
  obtain ⟨es, heslen, hesbd, heq⟩ :=
    p15RoundedDotList_backward fp l n (by simp [l]) hn
  have hesn : es.length = n := by simpa [l] using heslen
  let e : Fin n → ℝ := fun j ↦ es.get ⟨j.val, by rw [hesn]; exact j.isLt⟩
  refine ⟨e, ?_, ?_⟩
  · intro j
    apply hesbd
    exact List.get_mem _ _
  · rw [p15RoundedDotProduct_eq_list, heq]
    unfold p15PerturbedDotList
    have hes : es = List.ofFn e := by
      apply List.ext_get
      · simp [hesn]
      · intro j hje hjof
        simp only [List.length_ofFn] at hjof
        rw [List.get_ofFn]
        rfl
    rw [hes]
    have hz : List.zipWith (fun z e ↦ z.1 * z.2 * (1 + e))
          (List.ofFn fun j ↦ (x j, y j)) (List.ofFn e) =
        List.ofFn (fun j ↦ x j * y j * (1 + e j)) := by
      apply List.ext_get
      · simp
      · intro j hj1 hj2
        simp at *
    rw [hz, List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro j hj
    ring

lemma p15_frob_mul_error_bound {m n : ℕ} (A E : P15RectMatrix m n)
    (g : ℝ) (hg : 0 ≤ g) (hE : ∀ i j, |E i j| ≤ g) :
    p15RectFrobNorm (fun i j ↦ A i j * E i j) ≤
      g * p15RectFrobNorm A := by
  unfold p15RectFrobNorm
  have hsum : (∑ i : Fin m, ∑ j : Fin n, (A i j * E i j) ^ 2) ≤
      g ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
    calc
      (∑ i : Fin m, ∑ j : Fin n, (A i j * E i j) ^ 2) ≤
          ∑ i : Fin m, ∑ j : Fin n, g ^ 2 * A i j ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            apply Finset.sum_le_sum
            intro j hj
            have he2 : E i j ^ 2 ≤ g ^ 2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hg] using hE i j)
            nlinarith [sq_nonneg (A i j)]
      _ = g ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
        simp_rw [Finset.mul_sum]
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact hsum

lemma p15RoundedRectMatVec_backward (fp : StandardFPModel) {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hn : GammaValid fp.u n) :
    ∃ Δ : P15RectMatrix m n,
      p15RectFrobNorm Δ ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A Δ) x := by
  classical
  have hrow : ∀ i : Fin m, ∃ e : Fin n → ℝ,
      (∀ j, |e j| ≤ gamma fp.u n) ∧
      roundedDotProduct fp n (A i) x =
        ∑ j, A i j * (1 + e j) * x j :=
    fun i ↦ p15RoundedDotProduct_backward fp n (A i) x hn
  choose e hebd heq using hrow
  let Δ : P15RectMatrix m n := fun i j ↦ A i j * e i j
  refine ⟨Δ, ?_, ?_⟩
  · exact p15_frob_mul_error_bound A e (gamma fp.u n)
      (p15_gamma_nonneg fp.u_nonneg hn) hebd
  · funext i
    rw [show p15RoundedRectMatVec fp A x i =
        roundedDotProduct fp n (A i) x by rfl, heq]
    unfold p15RectMatVec p15RectAdd Δ
    apply Finset.sum_congr rfl
    intro j hj
    ring

lemma p15ForwardSubSteps_spec (fp : StandardFPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      let y := roundedForwardSubSteps fp n L v k hk x
      (∀ q, q.val < n - k → y q = x q) ∧
      (∀ q, n - k ≤ q.val →
        y q = fp.fl_div
          (Fin.foldl q.val
            (fun acc (t : Fin q.val) ↦
              fp.fl_sub acc
                (fp.fl_mul (L q ⟨t.val, lt_trans t.isLt q.isLt⟩)
                  (y ⟨t.val, lt_trans t.isLt q.isLt⟩)))
            (v q))
          (L q q)) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      constructor
      · intro q hq
        rfl
      · intro q hq
        omega
  | succ k ih =>
      intro hk x
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) ↦
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (v ik)
      let x' := Function.update x ik (fp.fl_div s (L ik ik))
      have ihr := ih (Nat.le_of_succ_le hk) x'
      change
        (∀ q, q.val < n - (k + 1) →
          roundedForwardSubSteps fp n L v k (Nat.le_of_succ_le hk) x' q = x q) ∧
        ∀ q, n - (k + 1) ≤ q.val →
          roundedForwardSubSteps fp n L v k (Nat.le_of_succ_le hk) x' q =
            fp.fl_div
              (Fin.foldl q.val
                (fun acc (t : Fin q.val) ↦ fp.fl_sub acc
                  (fp.fl_mul (L q ⟨t.val, lt_trans t.isLt q.isLt⟩)
                    (roundedForwardSubSteps fp n L v k
                      (Nat.le_of_succ_le hk) x'
                      ⟨t.val, lt_trans t.isLt q.isLt⟩)))
                (v q))
              (L q q)
      constructor
      · intro q hq
        rw [ihr.1 q (by omega)]
        have hne : q ≠ ik := by
          intro heq
          have := congr_arg Fin.val heq
          dsimp [ik] at this
          omega
        exact Function.update_of_ne hne _ _
      · intro q hq
        by_cases hqi : q.val = n - k - 1
        · have hqik : q = ik := by
            apply Fin.ext
            simpa [ik] using hqi
          subst q
          rw [ihr.1 ik (by dsimp [ik]; omega)]
          simp only [x', Function.update_self]
          congr 1
          dsimp [s, ik]
          apply congrArg (fun f ↦ Fin.foldl (n - k - 1) f (v ⟨n - k - 1, by omega⟩))
          funext acc t
          congr 3
          have ht : t.val < n - k := lt_trans t.isLt (by omega)
          have hy := ihr.1 ⟨t.val, by omega⟩ ht
          rw [hy]
          have hne : (⟨t.val, by omega⟩ : Fin n) ≠ ik := by
            intro heq
            have := congr_arg Fin.val heq
            dsimp [ik] at this
            omega
          exact (Function.update_of_ne hne _ _).symm
        · exact ihr.2 q (by omega)

lemma p15ForwardSub_spec (fp : StandardFPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    ∀ q, roundedForwardSub fp n L v q = fp.fl_div
      (Fin.foldl q.val
        (fun acc (t : Fin q.val) ↦
          fp.fl_sub acc
            (fp.fl_mul (L q ⟨t.val, lt_trans t.isLt q.isLt⟩)
              (roundedForwardSub fp n L v
                ⟨t.val, lt_trans t.isLt q.isLt⟩)))
        (v q))
      (L q q) := by
  intro q
  exact (p15ForwardSubSteps_spec fp n L v n le_rfl (fun _ ↦ 0)).2 q (by omega)

def p15ProductInterval (u : ℝ) (k : ℕ) (z : ℝ) : Prop :=
  1 - (k : ℝ) * u ≤ z ∧ z ≤ 1 / (1 - (k : ℝ) * u)

lemma p15ProductInterval_pos {u z : ℝ} {k n : ℕ}
    (hu : 0 ≤ u) (hkn : k ≤ n) (hn : GammaValid u n)
    (hz : p15ProductInterval u k z) : 0 < z := by
  unfold GammaValid at hn
  have hmul : (k : ℝ) * u ≤ (n : ℝ) * u := by
    gcongr
  exact lt_of_lt_of_le (by linarith) hz.1

lemma p15ProductInterval_update {u z d : ℝ} {k n : ℕ}
    (hu : 0 ≤ u) (hks : k + 1 ≤ n) (hn : GammaValid u n)
    (hz : p15ProductInterval u k z) (hd : |d| ≤ u) :
    p15ProductInterval u (k + 1) (z * (1 + d)) := by
  unfold GammaValid at hn
  have hk : k ≤ n := Nat.le_trans (Nat.le_add_right _ _) hks
  have hku : (k : ℝ) * u ≤ (n : ℝ) * u := by gcongr
  have hsku : ((k + 1 : ℕ) : ℝ) * u ≤ (n : ℝ) * u := by gcongr
  have hkden : 0 < 1 - (k : ℝ) * u := by linarith
  have hsden : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
  have hdlo : -u ≤ d := (abs_le.1 hd).1
  have hdhi : d ≤ u := (abs_le.1 hd).2
  have hu1 : u < 1 := by
    have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hm := mul_le_mul_of_nonneg_right h1n hu
    norm_num at hm
    linarith
  have hfac : 0 ≤ 1 + d := by
    linarith
  have hbase : 0 ≤ 1 - u := by linarith
  have hznonneg : 0 ≤ z := le_trans (by linarith) hz.1
  constructor
  · calc
      1 - ((k + 1 : ℕ) : ℝ) * u ≤
          (1 - (k : ℝ) * u) * (1 - u) := by
            norm_num [Nat.cast_add]
            have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
            nlinarith [mul_nonneg hk0 (sq_nonneg u)]
      _ ≤ z * (1 + d) := by
        exact mul_le_mul hz.1 (by linarith) hbase hznonneg
  · have hfrac : (1 + u) / (1 - (k : ℝ) * u) ≤
        1 / (1 - ((k + 1 : ℕ) : ℝ) * u) := by
        apply (div_le_div_iff₀ hkden hsden).2
        norm_num [Nat.cast_add]
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        have hk10 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
        nlinarith [mul_nonneg hk10 (sq_nonneg u)]
    calc
      z * (1 + d) ≤ (1 / (1 - (k : ℝ) * u)) * (1 + u) := by
        apply mul_le_mul hz.2 (by linarith) hfac
        positivity
      _ = (1 + u) / (1 - (k : ℝ) * u) := by ring
      _ ≤ _ := hfrac

lemma p15ProductInterval_error {u z : ℝ} {k n : ℕ}
    (hu : 0 ≤ u) (hkn : k ≤ n) (hkpos : 1 ≤ k)
    (hn : GammaValid u n) (hz : p15ProductInterval u k z) :
    |z - 1| ≤ gamma u k := by
  unfold GammaValid at hn
  have hku : (k : ℝ) * u ≤ (n : ℝ) * u := by gcongr
  have hkden : 0 < 1 - (k : ℝ) * u := by linarith
  rw [abs_le]
  constructor
  · have hmulnonneg : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
    have hkg : (k : ℝ) * u ≤ gamma u k := by
      rw [gamma]
      exact (le_div_iff₀ hkden).2 (by nlinarith)
    linarith [hz.1]
  · rw [gamma]
    have := hz.2
    rw [one_div] at this
    have hid : (1 - (k : ℝ) * u)⁻¹ - 1 =
        ((k : ℝ) * u) / (1 - (k : ℝ) * u) := by
      field_simp [ne_of_gt hkden]
      ring
    linarith

lemma p15ProductInterval_div {u z d : ℝ} {k n : ℕ}
    (hu : 0 ≤ u) (hks : k + 1 ≤ n) (hn : GammaValid u n)
    (hz : p15ProductInterval u k z) (hd : |d| ≤ u) :
    |(1 + d) / z - 1| ≤ gamma u (k + 1) := by
  have hk_le_n : k ≤ n := by omega
  have hzpos := p15ProductInterval_pos hu hk_le_n hn hz
  have hp : p15ProductInterval u (k + 1) ((1 + d) / z) := by
    have hzlo := hz.1
    have hzhi := hz.2
    unfold GammaValid at hn
    have hku : (k : ℝ) * u ≤ (n : ℝ) * u := by gcongr
    have hsku : ((k + 1 : ℕ) : ℝ) * u ≤ (n : ℝ) * u := by gcongr
    have hkden : 0 < 1 - (k : ℝ) * u := by linarith
    have hsden : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
    have hdlo := (abs_le.1 hd).1
    have hdhi := (abs_le.1 hd).2
    constructor
    · apply (le_div_iff₀ hzpos).2
      calc
        (1 - ((k + 1 : ℕ) : ℝ) * u) * z ≤
            (1 - ((k + 1 : ℕ) : ℝ) * u) /
              (1 - (k : ℝ) * u) := by
                rw [div_eq_mul_inv]
                exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hzhi) hsden.le
        _ ≤ 1 - u := by
          apply (div_le_iff₀ hkden).2
          norm_num [Nat.cast_add]
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
          nlinarith [mul_nonneg hk0 (sq_nonneg u)]
        _ ≤ 1 + d := by linarith
    · apply (div_le_iff₀ hzpos).2
      have hzlower : 1 - (k : ℝ) * u ≤ z := hz.1
      have haux : (1 + u) * (1 - ((k + 1 : ℕ) : ℝ) * u) ≤
          1 - (k : ℝ) * u := by
        norm_num [Nat.cast_add]
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        have hk10 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
        nlinarith [mul_nonneg hk10 (sq_nonneg u)]
      have : (1 + d) * (1 - ((k + 1 : ℕ) : ℝ) * u) ≤ z := by
        calc
          _ ≤ (1 + u) * (1 - ((k + 1 : ℕ) : ℝ) * u) := by
            gcongr
          _ ≤ 1 - (k : ℝ) * u := haux
          _ ≤ z := hzlower
      rw [show 1 / (1 - ((k + 1 : ℕ) : ℝ) * u) * z =
        z / (1 - ((k + 1 : ℕ) : ℝ) * u) by ring]
      exact (le_div_iff₀ hsden).2 this
  exact p15ProductInterval_error hu hks (by omega) hn hp

lemma p15ProductInterval_inv_update {u z d : ℝ} {k n : ℕ}
    (hu : 0 ≤ u) (hks : k + 1 ≤ n) (hn : GammaValid u n)
    (hz : p15ProductInterval u k z) (hd : |d| ≤ u) :
    |1 / ((1 + d) * z) - 1| ≤ gamma u (k + 1) := by
  have hp := p15ProductInterval_update hu hks hn hz hd
  have hppos := p15ProductInterval_pos hu hks hn hp
  have hinv : p15ProductInterval u (k + 1) (1 / ((1 + d) * z)) := by
    unfold p15ProductInterval at hp ⊢
    have hsden : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by
      unfold GammaValid at hn
      have hm : ((k + 1 : ℕ) : ℝ) * u ≤ (n : ℝ) * u := by gcongr
      linarith
    constructor
    · rw [mul_comm (1 + d) z]
      apply (le_div_iff₀ hppos).2
      have hpa := (le_div_iff₀ hsden).1 hp.2
      nlinarith
    · rw [mul_comm (1 + d) z]
      exact one_div_le_one_div_of_le hsden hp.1
  exact p15ProductInterval_error hu hks (by omega) hn hinv

noncomputable def p15RoundedSubList (fp : StandardFPModel) (v : ℝ)
    (l : List (ℝ × ℝ)) : ℝ :=
  l.foldl (fun acc q ↦ fp.fl_sub acc (fp.fl_mul q.1 q.2)) v

def p15PerturbedSubList (v : ℝ) (l : List (ℝ × ℝ))
    (es : List ℝ) : ℝ :=
  v - (List.zipWith (fun z e ↦ z.1 * (1 + e) * z.2) l es).sum

lemma p15RoundedSubList_append (fp : StandardFPModel) (v : ℝ)
    (l : List (ℝ × ℝ)) (z : ℝ × ℝ) :
    p15RoundedSubList fp v (l ++ [z]) =
      fp.fl_sub (p15RoundedSubList fp v l) (fp.fl_mul z.1 z.2) := by
  simp [p15RoundedSubList, List.foldl_append]

lemma p15PerturbedSubList_append (v : ℝ) (l : List (ℝ × ℝ))
    (es : List ℝ) (z : ℝ × ℝ) (e : ℝ)
    (h : l.length = es.length) :
    p15PerturbedSubList v (l ++ [z]) (es ++ [e]) =
      p15PerturbedSubList v l es - z.1 * (1 + e) * z.2 := by
  unfold p15PerturbedSubList
  rw [List.zipWith_append h]
  simp
  ring

lemma p15RoundedSubList_backward (fp : StandardFPModel) (v : ℝ)
    (l : List (ℝ × ℝ)) :
    ∀ n, l.length ≤ n → GammaValid fp.u n →
      ∃ rho : ℝ, ∃ es : List ℝ,
        p15ProductInterval fp.u l.length rho ∧
        es.length = l.length ∧
        (∀ e ∈ es, |e| ≤ gamma fp.u n) ∧
        p15RoundedSubList fp v l = rho * p15PerturbedSubList v l es := by
  induction l using List.reverseRecOn with
  | nil =>
      intro n hlen hn
      refine ⟨1, [], ?_, by simp, by simp, ?_⟩
      · constructor <;> norm_num
      · simp [p15RoundedSubList, p15PerturbedSubList]
  | append_singleton l z ih =>
      intro n hlen hn
      have hsucc : l.length + 1 ≤ n := by simpa using hlen
      have hvalid : GammaValid fp.u l.length := by
        unfold GammaValid at hn ⊢
        have hln : l.length ≤ n := by omega
        have hlnr : (l.length : ℝ) ≤ (n : ℝ) := by exact_mod_cast hln
        have hm : (l.length : ℝ) * fp.u ≤ (n : ℝ) * fp.u := by
          exact mul_le_mul_of_nonneg_right hlnr fp.u_nonneg
        linarith
      obtain ⟨rho, es, hrho, heslen, hesbd, heq⟩ :=
        ih l.length le_rfl hvalid
      obtain ⟨mu, hmu, hmul⟩ := fp.model_mul z.1 z.2
      obtain ⟨sig, hsig, hsub⟩ :=
        fp.model_sub (p15RoundedSubList fp v l) (fp.fl_mul z.1 z.2)
      let enew : ℝ := (1 + mu) / rho - 1
      refine ⟨rho * (1 + sig), es ++ [enew], ?_, ?_, ?_, ?_⟩
      · simpa using p15ProductInterval_update fp.u_nonneg (by omega)
          (show GammaValid fp.u (l.length + 1) by
            unfold GammaValid at hn ⊢
            have hm : ((l.length + 1 : ℕ) : ℝ) * fp.u ≤
                (n : ℝ) * fp.u := by
              gcongr
              exact fp.u_nonneg
            linarith) hrho hsig
      · simp [heslen]
      · intro e he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact (hesbd e he).trans
            (p15_gamma_mono fp.u_nonneg (by omega) hn)
        · have hnew := p15ProductInterval_div fp.u_nonneg (by omega)
              (show GammaValid fp.u (l.length + 1) by
                unfold GammaValid at hn ⊢
                have hm : ((l.length + 1 : ℕ) : ℝ) * fp.u ≤
                    (n : ℝ) * fp.u := by
                  gcongr
                  exact fp.u_nonneg
                linarith) hrho hmu
          exact hnew.trans (p15_gamma_mono fp.u_nonneg hsucc hn)
      · rw [p15RoundedSubList_append, hsub, heq, hmul,
          p15PerturbedSubList_append _ _ _ _ _ heslen.symm]
        have hrhopos := p15ProductInterval_pos fp.u_nonneg
          (show l.length ≤ n by omega) hn hrho
        dsimp [enew]
        field_simp [ne_of_gt hrhopos]
        ring

lemma p15RoundedSubFold_backward (fp : StandardFPModel) (k : ℕ)
    (a x : Fin k → ℝ) (v : ℝ) (hn : GammaValid fp.u k) :
    ∃ rho : ℝ, ∃ e : Fin k → ℝ,
      p15ProductInterval fp.u k rho ∧
      (∀ j, |e j| ≤ gamma fp.u k) ∧
      Fin.foldl k
          (fun acc j ↦ fp.fl_sub acc (fp.fl_mul (a j) (x j))) v =
        rho * (v - ∑ j, a j * (1 + e j) * x j) := by
  let l : List (ℝ × ℝ) := List.ofFn fun j ↦ (a j, x j)
  obtain ⟨rho, es, hrho, heslen, hesbd, heq⟩ :=
    p15RoundedSubList_backward fp v l k (by simp [l]) hn
  have hesk : es.length = k := by simpa [l] using heslen
  let e : Fin k → ℝ := fun j ↦ es.get ⟨j.val, by rw [hesk]; exact j.isLt⟩
  refine ⟨rho, e, by simpa [l] using hrho, ?_, ?_⟩
  · intro j
    apply hesbd
    exact List.get_mem _ _
  · rw [p15_fin_foldl_eq_list]
    have hfl : (List.ofFn fun j : Fin k ↦ j).foldl
          (fun acc j ↦ fp.fl_sub acc (fp.fl_mul (a j) (x j))) v =
        p15RoundedSubList fp v l := by
      unfold p15RoundedSubList l
      have hl : (List.ofFn fun j : Fin k ↦ (a j, x j)) =
          (List.ofFn fun j : Fin k ↦ j).map (fun j ↦ (a j, x j)) := by
        rw [List.map_ofFn]
        rfl
      rw [hl, List.foldl_map]
    rw [hfl, heq]
    congr 1
    unfold p15PerturbedSubList
    have hes : es = List.ofFn e := by
      apply List.ext_get
      · simp [hesk]
      · intro j hj1 hj2
        simp only [List.length_ofFn] at hj2
        rw [List.get_ofFn]
        rfl
    rw [hes]
    have hz : List.zipWith (fun z e ↦ z.1 * (1 + e) * z.2)
          (List.ofFn fun j ↦ (a j, x j)) (List.ofFn e) =
        List.ofFn (fun j ↦ a j * (1 + e j) * x j) := by
      apply List.ext_get
      · simp
      · intro j hj1 hj2
        simp at *
    rw [hz, List.sum_ofFn]

lemma p15_sum_eq_lower_add_diag {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ j, i.val < j.val → f j = 0) :
    (∑ j : Fin n, f j) =
      (∑ t : Fin i.val, f ⟨t.val, lt_trans t.isLt i.isLt⟩) + f i := by
  let g : ℕ → ℝ := fun k ↦ if hk : k < n then f ⟨k, hk⟩ else 0
  have hall : (∑ j : Fin n, f j) = ∑ k ∈ Finset.range n, g k := by
    rw [← Fin.sum_univ_eq_sum_range g n]
    apply Finset.sum_congr rfl
    intro j hj
    simp [g]
  have hlow : (∑ t : Fin i.val, f ⟨t.val, lt_trans t.isLt i.isLt⟩) =
      ∑ k ∈ Finset.range i.val, g k := by
    rw [← Fin.sum_univ_eq_sum_range g i.val]
    apply Finset.sum_congr rfl
    intro t ht
    have htn : t.val < n := lt_trans t.isLt i.isLt
    simp [g, htn]
  have htail : (∑ k ∈ Finset.Ico (i.val + 1) n, g k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hki : i.val < k := by
      have := (Finset.mem_Ico.1 hk).1
      omega
    have hkn : k < n := (Finset.mem_Ico.1 hk).2
    simp only [g, dif_pos hkn]
    exact hzero ⟨k, hkn⟩ hki
  calc
    (∑ j : Fin n, f j) = ∑ k ∈ Finset.range n, g k := hall
    _ = (∑ k ∈ Finset.range (i.val + 1), g k) +
          ∑ k ∈ Finset.Ico (i.val + 1) n, g k :=
      (Finset.sum_range_add_sum_Ico g (Nat.succ_le_of_lt i.isLt)).symm
    _ = ∑ k ∈ Finset.range (i.val + 1), g k := by rw [htail, add_zero]
    _ = (∑ k ∈ Finset.range i.val, g k) + g i.val :=
      Finset.sum_range_succ g i.val
    _ = (∑ t : Fin i.val, f ⟨t.val, lt_trans t.isLt i.isLt⟩) + f i := by
      rw [← hlow]
      simp [g]

lemma p15ForwardSub_row_backward (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (v : P15Vector n)
    (hdiag : ∀ i, L i i ≠ 0) (hlower : p15LowerTriangular L)
    (hn : GammaValid fp.u n) (i : Fin n) :
    ∃ e : Fin n → ℝ, (∀ j, |e j| ≤ gamma fp.u n) ∧
      (∑ j : Fin n, L i j * (1 + e j) * roundedForwardSub fp n L v j) = v i := by
  classical
  let sol := roundedForwardSub fp n L v
  let a : Fin i.val → ℝ := fun t ↦ L i ⟨t.val, lt_trans t.isLt i.isLt⟩
  let x : Fin i.val → ℝ := fun t ↦ sol ⟨t.val, lt_trans t.isLt i.isLt⟩
  have hvi : GammaValid fp.u i.val := by
    unfold GammaValid at hn ⊢
    have hle : (i.val : ℝ) * fp.u ≤ (n : ℝ) * fp.u := by
      have hir : (i.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_lt i.isLt)
      exact mul_le_mul_of_nonneg_right hir fp.u_nonneg
    linarith
  obtain ⟨rho, elo, hrho, helobd, hs⟩ :=
    p15RoundedSubFold_backward fp i.val a x (v i) hvi
  obtain ⟨d, hd, hdiv⟩ := fp.model_div
    (Fin.foldl i.val
      (fun acc (t : Fin i.val) ↦
        fp.fl_sub acc (fp.fl_mul (a t) (x t))) (v i)) (L i i) (hdiag i)
  have hspec := p15ForwardSub_spec fp n L v i
  change sol i = _ at hspec
  change sol i =
    fp.fl_div
      (Fin.foldl i.val
        (fun acc (t : Fin i.val) ↦
          fp.fl_sub acc (fp.fl_mul (a t) (x t))) (v i)) (L i i) at hspec
  have hxdiv : sol i =
      ((Fin.foldl i.val
        (fun acc (t : Fin i.val) ↦
          fp.fl_sub acc (fp.fl_mul (a t) (x t))) (v i)) / L i i) * (1 + d) := by
    rw [hspec, hdiv]
  let ediag : ℝ := 1 / ((1 + d) * rho) - 1
  have hediag : |ediag| ≤ gamma fp.u n := by
    have hlocal := p15ProductInterval_inv_update fp.u_nonneg
      (show i.val + 1 ≤ n by omega) hn hrho hd
    exact hlocal.trans
      (p15_gamma_mono fp.u_nonneg (show i.val + 1 ≤ n by omega) hn)
  let e : Fin n → ℝ := fun j ↦
    if hji : j.val < i.val then elo ⟨j.val, hji⟩
    else if j = i then ediag else 0
  refine ⟨e, ?_, ?_⟩
  · intro j
    by_cases hji : j.val < i.val
    · simp only [e, dif_pos hji]
      exact (helobd ⟨j.val, hji⟩).trans
        (p15_gamma_mono fp.u_nonneg (Nat.le_of_lt i.isLt) hn)
    · by_cases hji_eq : j = i
      · simp [e, hji, hji_eq, hediag]
      · simp only [e, dif_neg hji, if_neg hji_eq, abs_zero]
        exact p15_gamma_nonneg fp.u_nonneg hn
  · change (∑ j : Fin n, L i j * (1 + e j) * sol j) = v i
    rw [p15_sum_eq_lower_add_diag i
      (fun j ↦ L i j * (1 + e j) * sol j) (by
        intro j hij
        change L i j * (1 + e j) * sol j = 0
        rw [hlower i j hij]
        ring)]
    have hlowsum :
        (∑ t : Fin i.val,
          L i ⟨t.val, lt_trans t.isLt i.isLt⟩ *
            (1 + e ⟨t.val, lt_trans t.isLt i.isLt⟩) *
            sol ⟨t.val, lt_trans t.isLt i.isLt⟩) =
        ∑ t : Fin i.val, a t * (1 + elo t) * x t := by
      apply Finset.sum_congr rfl
      intro t ht
      have he : e ⟨t.val, lt_trans t.isLt i.isLt⟩ = elo t := by
        unfold e
        split
        · rfl
        · rename_i h
          exact False.elim (h t.isLt)
      rw [he]
    rw [hlowsum]
    have heii : e i = ediag := by simp [e]
    rw [heii]
    have hprod := p15ProductInterval_update fp.u_nonneg
      (show i.val + 1 ≤ n by omega) hn hrho hd
    have hprodpos := p15ProductInterval_pos fp.u_nonneg
      (show i.val + 1 ≤ n by omega) hn hprod
    have hrhopos := p15ProductInterval_pos fp.u_nonneg
      (Nat.le_of_lt i.isLt) hn hrho
    change (Fin.foldl i.val
      (fun acc (t : Fin i.val) ↦
        fp.fl_sub acc (fp.fl_mul (a t) (x t))) (v i)) =
      rho * (v i - ∑ t : Fin i.val, a t * (1 + elo t) * x t) at hs
    let S := Fin.foldl i.val
      (fun acc (t : Fin i.val) ↦
        fp.fl_sub acc (fp.fl_mul (a t) (x t))) (v i)
    let low := ∑ t : Fin i.val, a t * (1 + elo t) * x t
    have hfacrho : (1 + d) * rho ≠ 0 := by
      rw [mul_comm]
      exact ne_of_gt hprodpos
    have hfac : 1 + d ≠ 0 := (mul_ne_zero_iff.mp hfacrho).1
    have hterm : L i i * (1 + ediag) * sol i = S / rho := by
      rw [hxdiv]
      dsimp [ediag, S]
      field_simp [hdiag i, ne_of_gt hrhopos, hfacrho, hfac]
      ring
    rw [hterm]
    have hsdiv : S / rho = v i - low := by
      change S = rho * (v i - low) at hs
      rw [hs]
      field_simp [ne_of_gt hrhopos]
    rw [hsdiv]
    dsimp [low]
    ring

lemma p15ForwardSub_backward (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (v : P15Vector n)
    (hdiag : ∀ i, L i i ≠ 0) (hlower : p15LowerTriangular L)
    (hn : GammaValid fp.u n) :
    ∃ Δ : P15Matrix n,
      p15RectFrobNorm Δ ≤ gamma fp.u n * p15RectFrobNorm L ∧
      p15RectMatVec (p15RectAdd L Δ) (roundedForwardSub fp n L v) = v := by
  classical
  have hrow : ∀ i : Fin n, ∃ e : Fin n → ℝ,
      (∀ j, |e j| ≤ gamma fp.u n) ∧
      (∑ j : Fin n, L i j * (1 + e j) * roundedForwardSub fp n L v j) = v i :=
    fun i ↦ p15ForwardSub_row_backward fp n L v hdiag hlower hn i
  choose e hebd heq using hrow
  let Δ : P15Matrix n := fun i j ↦ L i j * e i j
  refine ⟨Δ, ?_, ?_⟩
  · exact p15_frob_mul_error_bound L e (gamma fp.u n)
      (p15_gamma_nonneg fp.u_nonneg hn) hebd
  · funext i
    unfold p15RectMatVec p15RectAdd Δ
    rw [← heq i]
    apply Finset.sum_congr rfl
    intro j hj
    ring

lemma p15RectMatVec_mul_assoc {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  unfold p15RectMatVec p15RectMatMul
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
  obtain ⟨ΔT₀, hΔT₀, hT₀eq⟩ :=
    p15ForwardSub_backward fp b T₀ v₀ hT₀diag hT₀lower hb
  obtain ⟨ΔYT, hΔYT, hYTeq⟩ :=
    p15RoundedRectMatVec_backward fp (p15RectTranspose Y)
      (roundedForwardSub fp b T₀ v₀) hb
  obtain ⟨ΔX, hΔX, hXeq⟩ :=
    p15RoundedRectMatVec_backward fp X
      (p15RoundedRectMatVec fp (p15RectTranspose Y)
        (roundedForwardSub fp b T₀ v₀)) hr
  have hsub : ∀ i : Fin b, ∃ d : ℝ, |d| ≤ fp.u ∧
      fp.fl_sub (v₁ i)
          (p15RoundedRectMatVec fp X
            (p15RoundedRectMatVec fp (p15RectTranspose Y)
              (roundedForwardSub fp b T₀ v₀)) i) =
        (v₁ i -
          p15RoundedRectMatVec fp X
            (p15RoundedRectMatVec fp (p15RectTranspose Y)
              (roundedForwardSub fp b T₀ v₀)) i) * (1 + d) :=
    fun i ↦ fp.model_sub _ _
  choose θ hθ hsubeq using hsub
  let rhsHat : P15Vector b := fun i ↦ fp.fl_sub (v₁ i)
    (p15RoundedRectMatVec fp X
      (p15RoundedRectMatVec fp (p15RectTranspose Y)
        (roundedForwardSub fp b T₀ v₀)) i)
  obtain ⟨ΔT₁, hΔT₁, hT₁eq⟩ :=
    p15ForwardSub_backward fp b T₁ rhsHat hT₁diag hT₁lower hb
  let ΔT₁₀ : P15Matrix b := fun i j ↦
    (1 + θ i) *
        p15RectMatMul (p15RectAdd X ΔX)
          (p15RectAdd (p15RectTranspose Y) ΔYT) i j -
      p15LowRankMatrix X Y i j
  refine ⟨ΔT₀, ΔYT, ΔX, θ, ΔT₁, ΔT₁₀,
    hΔT₀, hΔYT, hΔX, hθ, hΔT₁, hT₀eq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hYTeq
  · exact hXeq
  · intro i
    exact hsubeq i
  · exact hT₁eq
  · intro i j
    change p15LowRankMatrix X Y i j +
        ((1 + θ i) *
          p15RectMatMul (p15RectAdd X ΔX)
            (p15RectAdd (p15RectTranspose Y) ΔYT) i j -
          p15LowRankMatrix X Y i j) = _
    ring
  · intro i
    let x₀ := roundedForwardSub fp b T₀ v₀
    let wInner := p15RoundedRectMatVec fp (p15RectTranspose Y) x₀
    let wHat := p15RoundedRectMatVec fp X wInner
    let x₁ := roundedForwardSub fp b T₁ rhsHat
    have hinner : wInner =
        p15RectMatVec (p15RectAdd (p15RectTranspose Y) ΔYT) x₀ := by
      exact hYTeq
    have hhat : wHat = p15RectMatVec (p15RectAdd X ΔX) wInner := by
      exact hXeq
    have hassoc := p15RectMatVec_mul_assoc (p15RectAdd X ΔX)
      (p15RectAdd (p15RectTranspose Y) ΔYT) x₀
    have hprodvec :
        p15RectMatVec
            (p15RectMatMul (p15RectAdd X ΔX)
              (p15RectAdd (p15RectTranspose Y) ΔYT)) x₀ = wHat := by
      rw [hassoc, ← hinner, ← hhat]
    have hblock :
        p15RectMatVec (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i =
          (1 + θ i) * wHat i := by
      unfold p15RectMatVec
      calc
        (∑ j : Fin b,
            p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j * x₀ j) =
            ∑ j : Fin b,
              ((1 + θ i) *
                p15RectMatMul (p15RectAdd X ΔX)
                  (p15RectAdd (p15RectTranspose Y) ΔYT) i j) * x₀ j := by
              apply Finset.sum_congr rfl
              intro j hj
              change (p15LowRankMatrix X Y i j +
                ((1 + θ i) *
                  p15RectMatMul (p15RectAdd X ΔX)
                    (p15RectAdd (p15RectTranspose Y) ΔYT) i j -
                  p15LowRankMatrix X Y i j)) * x₀ j = _
              ring
        _ = (1 + θ i) *
            p15RectMatVec
              (p15RectMatMul (p15RectAdd X ΔX)
                (p15RectAdd (p15RectTranspose Y) ΔYT)) x₀ i := by
              unfold p15RectMatVec
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = (1 + θ i) * wHat i := by rw [hprodvec]
    change p15RectMatVec
          (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i +
        p15RectMatVec (p15RectAdd T₁ ΔT₁) x₁ i =
      v₁ i * (1 + θ i)
    rw [hblock]
    have hT₁i : p15RectMatVec (p15RectAdd T₁ ΔT₁) x₁ i =
        rhsHat i := congrFun hT₁eq i
    rw [hT₁i]
    have hrhs : rhsHat i = (v₁ i - wHat i) * (1 + θ i) := hsubeq i
    rw [hrhs]
    ring

end HighamBench
