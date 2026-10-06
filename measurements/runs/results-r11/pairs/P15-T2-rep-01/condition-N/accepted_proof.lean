import HighamBench.P15Definitions
namespace HighamBench

lemma gammaValid_mono {u : ℝ} {m n : ℕ} (hu : 0 ≤ u)
    (hmn : m ≤ n) (hn : GammaValid u n) : GammaValid u m := by
  unfold GammaValid at *
  have hc : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  nlinarith

lemma gamma_nonneg {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hn : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at hn
  rw [gamma]
  have hd : 0 < 1 - (n : ℝ) * u := by linarith
  positivity

lemma gamma_mono {u : ℝ} {m n : ℕ} (hu : 0 ≤ u)
    (hmn : m ≤ n) (hn : GammaValid u n) : gamma u m ≤ gamma u n := by
  unfold GammaValid at hn
  rw [gamma, gamma]
  have hc : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hdm : 0 < 1 - (m : ℝ) * u := by nlinarith
  have hdn : 0 < 1 - (n : ℝ) * u := by linarith
  apply (div_le_div_iff₀ hdm hdn).2
  nlinarith

lemma u_le_gamma {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hnpos : 1 ≤ n) (hn : GammaValid u n) : u ≤ gamma u n := by
  have h := gamma_mono hu hnpos hn
  rw [gamma] at h
  norm_num at h ⊢
  have hd : 0 < 1 - u := by
    unfold GammaValid at hn
    have hc : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    nlinarith
  have : u ≤ u / (1-u) := by
    apply (le_div_iff₀ hd).2
    nlinarith [mul_nonneg hu hu]
  exact this.trans h

lemma gamma_comp_step {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hv : GammaValid u (n+1)) :
    gamma u n + u + gamma u n * u ≤ gamma u (n+1) := by
  have hvn := gammaValid_mono hu (Nat.le_succ n) hv
  unfold GammaValid at hv hvn
  rw [gamma, gamma]
  have hdn : 0 < 1 - (n : ℝ) * u := by linarith
  have hdS : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by linarith
  have heq :
      (n : ℝ) * u / (1 - (n : ℝ) * u) + u +
          (n : ℝ) * u / (1 - (n : ℝ) * u) * u =
        ((n : ℝ) + 1) * u / (1 - (n : ℝ) * u) := by
    field_simp [ne_of_gt hdn]
    ring
  rw [heq]
  apply (div_le_div_iff₀ hdn hdS).2
  push_cast
  have hnum : 0 ≤ ((n : ℝ) + 1) * u := mul_nonneg (by positivity) hu
  have hden : 1 - ((n : ℝ) + 1) * u ≤ 1 - (n : ℝ) * u := by
    nlinarith
  exact mul_le_mul_of_nonneg_left hden hnum

lemma rel_comp_step {u a d : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hv : GammaValid u (n+1)) (ha : |a| ≤ gamma u n) (hd : |d| ≤ u) :
    |(1+a)*(1+d)-1| ≤ gamma u (n+1) := by
  calc
   |(1+a)*(1+d)-1| = |a+d+a*d| := by ring_nf
   _ ≤ |a| + |d| + |a| * |d| := by
     calc
       |a + d + a * d| ≤ |a + d| + |a * d| := abs_add_le _ _
       _ ≤ (|a| + |d|) + |a| * |d| := by
         rw [abs_mul]
         gcongr
         exact abs_add_le _ _
   _ ≤ gamma u n + u + gamma u n * u := by
     gcongr
     exact gamma_nonneg hu (gammaValid_mono hu (Nat.le_succ n) hv)
   _ ≤ gamma u (n+1) := gamma_comp_step hu hv

end HighamBench


namespace HighamBench
open scoped BigOperators

lemma roundedDotProduct_succ (fp : StandardFPModel) (n : ℕ)
    (x y : Fin (n+1) → ℝ) :
 roundedDotProduct fp (n+1) x y =
  match n with
  | 0 => fp.fl_mul (x 0) (y 0)
  | k+1 => fp.fl_add
      (roundedDotProduct fp (k+1) (fun i => x i.castSucc) (fun i => y i.castSucc))
      (fp.fl_mul (x (Fin.last (k+1))) (y (Fin.last (k+1)))) := by
 cases n with
 | zero => simp [roundedDotProduct]
 | succ k =>
   simp only [roundedDotProduct, Fin.foldl_succ_last]
   congr 1

lemma roundedDotProduct_succ_succ (fp : StandardFPModel) (k : ℕ)
    (x y : Fin (k+2) → ℝ) :
 roundedDotProduct fp (k+2) x y = fp.fl_add
      (roundedDotProduct fp (k+1) (fun i => x i.castSucc) (fun i => y i.castSucc))
      (fp.fl_mul (x (Fin.last (k+1))) (y (Fin.last (k+1)))) := by
  simp only [roundedDotProduct, Fin.foldl_succ_last]
  congr 1

lemma roundedDotProduct_backward_rel (fp : StandardFPModel) (n : ℕ)
    (hv : GammaValid fp.u n) (x y : Fin n → ℝ) :
    ∃ e : Fin n → ℝ,
      (∀ i, |e i| ≤ gamma fp.u n) ∧
      roundedDotProduct fp n x y = ∑ i, (x i + x i * e i) * y i := by
  induction n with
  | zero =>
      refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp [roundedDotProduct]
  | succ n ih =>
      cases n with
      | zero =>
          obtain ⟨d, hd, hmul⟩ := fp.model_mul (x 0) (y 0)
          refine ⟨fun _ => d, ?_, ?_⟩
          · intro i
            exact hd.trans (u_le_gamma fp.u_nonneg (by omega) hv)
          · rw [roundedDotProduct_succ]
            simpa [Fin.sum_univ_succ, hmul] using (show
              (x 0 * y 0) * (1+d) = (x 0 + x 0*d) * y 0 by ring)
      | succ k =>
          have hvprev : GammaValid fp.u (k+1) :=
            gammaValid_mono fp.u_nonneg (by omega) hv
          obtain ⟨e, he, hdot⟩ := ih hvprev
            (fun i => x i.castSucc) (fun i => y i.castSucc)
          obtain ⟨dm, hdm, hmul⟩ := fp.model_mul
            (x (Fin.last (k+1))) (y (Fin.last (k+1)))
          obtain ⟨da, hda, hadd⟩ := fp.model_add
            (roundedDotProduct fp (k+1) (fun i => x i.castSucc)
              (fun i => y i.castSucc))
            (fp.fl_mul (x (Fin.last (k+1))) (y (Fin.last (k+1))))
          let e' : Fin (k+2) → ℝ := Fin.lastCases
            ((1+dm)*(1+da)-1) (fun i => (1+e i)*(1+da)-1)
          refine ⟨e', ?_, ?_⟩
          · intro i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simp only [e', Fin.lastCases_last]
              apply rel_comp_step fp.u_nonneg hv
              · exact hdm.trans (u_le_gamma fp.u_nonneg (by omega) hvprev)
              · exact hda
            · simp only [e', Fin.lastCases_castSucc]
              apply rel_comp_step fp.u_nonneg hv (he j) hda
          · rw [roundedDotProduct_succ_succ]
            rw [hadd, hmul, hdot]
            nth_rewrite 2 [Fin.sum_univ_castSucc]
            simp only [e', Fin.lastCases_castSucc, Fin.lastCases_last]
            rw [add_mul, Finset.sum_mul]
            apply congrArg₂ (· + ·)
            · apply Finset.sum_congr rfl
              intro i hi
              ring
            · ring

end HighamBench

namespace HighamBench
open scoped BigOperators

lemma p15RectFrobNorm_le_of_pointwise {m n : ℕ}
    (A D : P15RectMatrix m n) (g : ℝ) (hg : 0 ≤ g)
    (h : ∀ i j, |D i j| ≤ g * |A i j|) :
    p15RectFrobNorm D ≤ g * p15RectFrobNorm A := by
  unfold p15RectFrobNorm
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hsum : (∑ i : Fin m, ∑ j : Fin n, D i j ^ 2) ≤
        g^2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have habs : |D i j| ≤ abs (g * abs (A i j)) := by
        simpa [abs_of_nonneg (mul_nonneg hg (abs_nonneg _))] using h i j
      have hij := (sq_le_sq).2 habs
      calc
        D i j ^ 2 ≤ (g * |A i j|)^2 := hij
        _ = g^2 * A i j ^ 2 := by rw [mul_pow, sq_abs]
    calc
      (∑ i : Fin m, ∑ j : Fin n, D i j ^ 2) ≤
          g^2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := hsum
      _ = (g * √(∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt]
        positivity

lemma p15RoundedRectMatVec_backward (fp : StandardFPModel) {m n : ℕ}
    (hv : GammaValid fp.u n) (A : P15RectMatrix m n) (x : Fin n → ℝ) :
    ∃ D : P15RectMatrix m n,
      p15RectFrobNorm D ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x = p15RectMatVec (p15RectAdd A D) x := by
  classical
  have hw : ∀ i : Fin m, ∃ e : Fin n → ℝ,
      (∀ j, |e j| ≤ gamma fp.u n) ∧
      roundedDotProduct fp n (A i) x = ∑ j, (A i j + A i j * e j) * x j := by
    intro i
    exact roundedDotProduct_backward_rel fp n hv (A i) x
  choose e he heq using hw
  let D : P15RectMatrix m n := fun i j => A i j * e i j
  refine ⟨D, ?_, ?_⟩
  · apply p15RectFrobNorm_le_of_pointwise A D (gamma fp.u n)
      (gamma_nonneg fp.u_nonneg hv)
    intro i j
    simp only [D, abs_mul]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left (he i j) (abs_nonneg (A i j)))
  · funext i
    exact heq i

end HighamBench

namespace HighamBench

lemma gamma_inv_step_bound {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hv : GammaValid u (n+1)) :
    (gamma u n + u) / (1-u) ≤ gamma u (n+1) := by
  have hvn := gammaValid_mono hu (Nat.le_succ n) hv
  unfold GammaValid at hv hvn
  have hu1 : u < 1 := by
    have hc : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hc hu]
  rw [gamma, gamma]
  have hdn : 0 < 1 - (n : ℝ) * u := by linarith
  have hdS : 0 < 1 - ((n+1 : ℕ) : ℝ) * u := by linarith
  have huD : 0 < 1-u := by linarith
  norm_num [Nat.cast_add, Nat.cast_one] at hdS ⊢
  have hdSpos : 0 < 1 - ((n : ℝ) + 1) * u := by linarith
  rw [← sub_nonneg]
  have hid :
      ((n : ℝ) + 1) * u / (1 - ((n : ℝ) + 1) * u) -
          (((n : ℝ) * u / (1 - (n : ℝ) * u) + u) / (1-u)) =
        (n : ℝ) * u^2 /
          ((1 - ((n : ℝ) + 1) * u) *
            (1 - (n : ℝ) * u) * (1-u)) := by
    field_simp [ne_of_gt hdn, ne_of_gt hdSpos, ne_of_gt huD]
    ring
  rw [hid]
  positivity

lemma rel_inv_comp_step {u q d : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hv : GammaValid u (n+1)) (hq : |q-1| ≤ gamma u n) (hd : |d| ≤ u) :
    |q/(1+d)-1| ≤ gamma u (n+1) := by
  have hu1 : u < 1 := by
    unfold GammaValid at hv
    have hc : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hc hu]
  have hden : 0 < 1+d := by
    have := (abs_le.mp hd).1
    nlinarith
  calc
    |q/(1+d)-1| = |(q-1)-d| / |1+d| := by
      have heq : q/(1+d)-1 = ((q-1)-d)/(1+d) := by
        field_simp [ne_of_gt hden]
        ring
      rw [heq, abs_div]
    _ ≤ (gamma u n + u) / (1-u) := by
      rw [abs_of_pos hden]
      apply (div_le_div_iff₀ hden (by linarith)).2
      have hnum : |(q-1)-d| ≤ gamma u n + u := by
        calc
          |(q-1)-d| ≤ |q-1| + |d| := abs_sub _ _
          _ ≤ gamma u n + u := add_le_add hq hd
      have hleft : 0 ≤ |(q-1)-d| := abs_nonneg _
      have hgam : 0 ≤ gamma u n + u :=
        add_nonneg (gamma_nonneg hu (gammaValid_mono hu (Nat.le_succ n) hv)) hu
      calc
        |q - 1 - d| * (1-u) ≤ (gamma u n + u) * (1-u) :=
          mul_le_mul_of_nonneg_right hnum (by linarith)
        _ ≤ (gamma u n + u) * (1+d) := by
          apply mul_le_mul_of_nonneg_left _ hgam
          have := (abs_le.mp hd).1
          linarith
    _ ≤ gamma u (n+1) := gamma_inv_step_bound hu hv

end HighamBench

namespace HighamBench
open scoped BigOperators

lemma roundedSubFold_backward (fp : StandardFPModel) (n : ℕ)
    (hv : GammaValid fp.u n) (a x : Fin n → ℝ) (z : ℝ) :
    ∃ q : ℝ, ∃ e : Fin n → ℝ,
      |q-1| ≤ gamma fp.u n ∧
      (∀ i, |e i| ≤ gamma fp.u n) ∧
      z = q * Fin.foldl n
          (fun acc i => fp.fl_sub acc (fp.fl_mul (a i) (x i))) z +
        ∑ i, (a i + a i * e i) * x i := by
  induction n with
  | zero =>
      refine ⟨1, (fun i => Fin.elim0 i), ?_, ?_, ?_⟩
      · simp [gamma]
      · intro i
        exact Fin.elim0 i
      · simp
  | succ n ih =>
      have hvprev := gammaValid_mono fp.u_nonneg (Nat.le_succ n) hv
      obtain ⟨q, e, hq, he, hprev⟩ := ih hvprev
        (fun i => a i.castSucc) (fun i => x i.castSucc)
      let sold := Fin.foldl n
        (fun acc (i : Fin n) =>
          fp.fl_sub acc (fp.fl_mul (a i.castSucc) (x i.castSucc))) z
      obtain ⟨dm, hdm, hmul⟩ := fp.model_mul
        (a (Fin.last n)) (x (Fin.last n))
      obtain ⟨ds, hds, hsub⟩ := fp.model_sub sold
        (fp.fl_mul (a (Fin.last n)) (x (Fin.last n)))
      have hu1 : fp.u < 1 := by
        unfold GammaValid at hv
        have hc : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by norm_num
        nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
      have hden : 1+ds ≠ 0 := by
        have := (abs_le.mp hds).1
        nlinarith
      let q' := q/(1+ds)
      let e' : Fin (n+1) → ℝ := Fin.lastCases
        (q*(1+dm)-1) e
      refine ⟨q', e', ?_, ?_, ?_⟩
      · exact rel_inv_comp_step fp.u_nonneg hv hq hds
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [e', Fin.lastCases_last]
          convert (rel_comp_step fp.u_nonneg hv hq hdm) using 1 <;> ring
        · simp only [e', Fin.lastCases_castSucc]
          exact (he j).trans (gamma_mono fp.u_nonneg (Nat.le_succ n) hv)
      · rw [Fin.foldl_succ_last]
        change z = q' * fp.fl_sub sold
            (fp.fl_mul (a (Fin.last n)) (x (Fin.last n))) + _
        rw [hsub, hmul]
        rw [Fin.sum_univ_castSucc]
        simp only [e', Fin.lastCases_castSucc, Fin.lastCases_last]
        change z = q * sold + _ at hprev
        have hcanon : ∀ j : Fin n,
            (a j.castSucc + a j.castSucc * e j) * x j.castSucc =
              a j.castSucc * (1 + e j) * x j.castSucc := by
          intro j
          ring
        simp_rw [hcanon] at hprev ⊢
        dsimp only [q']
        field_simp [hden]
        rw [hprev]
        ring

end HighamBench

namespace HighamBench
open scoped BigOperators

lemma roundedSolveRow_backward (fp : StandardFPModel) (n : ℕ)
    (hv : GammaValid fp.u (n+1)) (a x : Fin n → ℝ)
    (z diag : ℝ) (hdiag : diag ≠ 0) :
    let s := Fin.foldl n
      (fun acc i => fp.fl_sub acc (fp.fl_mul (a i) (x i))) z
    let sol := fp.fl_div s diag
    ∃ ed : ℝ, ∃ e : Fin n → ℝ,
      |ed| ≤ gamma fp.u (n+1) ∧
      (∀ i, |e i| ≤ gamma fp.u (n+1)) ∧
      z = (diag + diag*ed)*sol + ∑ i, (a i + a i*e i)*x i := by
  dsimp only
  have hvprev := gammaValid_mono fp.u_nonneg (Nat.le_succ n) hv
  obtain ⟨q, e, hq, he, hfold⟩ :=
    roundedSubFold_backward fp n hvprev a x z
  let s := Fin.foldl n
      (fun acc i => fp.fl_sub acc (fp.fl_mul (a i) (x i))) z
  obtain ⟨dd, hdd, hdiv⟩ := fp.model_div s diag hdiag
  have hu1 : fp.u < 1 := by
    unfold GammaValid at hv
    have hc : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
  have hden : 1+dd ≠ 0 := by
    have := (abs_le.mp hdd).1
    nlinarith
  let ed := q/(1+dd)-1
  refine ⟨ed, e, ?_, ?_, ?_⟩
  · exact rel_inv_comp_step fp.u_nonneg hv hq hdd
  · intro i
    exact (he i).trans (gamma_mono fp.u_nonneg (Nat.le_succ n) hv)
  · change z = (diag + diag*ed) * fp.fl_div s diag + _
    have hs : s = diag/(1+dd) * fp.fl_div s diag := by
      rw [hdiv]
      field_simp [hdiag, hden]
    change z = q * s + _ at hfold
    rw [hfold]
    nth_rewrite 1 [hs]
    dsimp only [ed]
    field_simp [hden]
    ring

end HighamBench

namespace HighamBench

noncomputable def p15RoundedRowValue (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (b : P15Vector n) (x : P15Vector n)
    (i : Fin n) : ℝ :=
  let s := Fin.foldl i.val
    (fun acc (t : Fin i.val) =>
      fp.fl_sub acc
        (fp.fl_mul (L i ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
    (b i)
  fp.fl_div s (L i i)

lemma roundedForwardSubSteps_unchanged (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (b : P15Vector n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : P15Vector n) (i : Fin n),
      i.val < n-k →
      roundedForwardSubSteps fp n L b k hk x i = x i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      rfl
  | succ k ih =>
      intro hk x i hi
      simp only [roundedForwardSubSteps]
      rw [ih (Nat.le_of_succ_le hk) _ i (by omega)]
      rw [Function.update_of_ne]
      intro heq
      have hv : i.val = n-k-1 := congrArg Fin.val heq
      omega

end HighamBench

namespace HighamBench

lemma p15RoundedRowValue_congr (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (b : P15Vector n) (x y : P15Vector n)
    (i : Fin n) (hxy : ∀ j : Fin n, j.val < i.val → x j = y j) :
    p15RoundedRowValue fp n L b x i = p15RoundedRowValue fp n L b y i := by
  dsimp only [p15RoundedRowValue]
  apply congrArg (fun s => fp.fl_div s (L i i))
  congr 1
  funext acc t
  congr 3
  apply hxy
  exact t.isLt

end HighamBench

namespace HighamBench

lemma roundedForwardSubSteps_row (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (b : P15Vector n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : P15Vector n) (i : Fin n),
      n-k ≤ i.val →
      let y := roundedForwardSubSteps fp n L b k hk x
      y i = p15RoundedRowValue fp n L b y i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      omega
  | succ k ih =>
      intro hk x i hi
      let idx : Fin n := ⟨n-k-1, by omega⟩
      let s := Fin.foldl (n-k-1)
        (fun acc (t : Fin (n-k-1)) =>
          fp.fl_sub acc
            (fp.fl_mul (L idx ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (b idx)
      let x' := Function.update x idx (fp.fl_div s (L idx idx))
      let y := roundedForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'
      have hydef : roundedForwardSubSteps fp n L b (k+1) hk x = y := by
        simp only [roundedForwardSubSteps]
        rfl
      rw [hydef]
      dsimp only
      by_cases hieq : i = idx
      · rw [hieq]
        have hyidx : y idx = x' idx := by
          apply roundedForwardSubSteps_unchanged fp n L b k
            (Nat.le_of_succ_le hk) x' idx
          dsimp only [idx]
          omega
        rw [hyidx]
        have hxidx : x' idx = fp.fl_div s (L idx idx) := by
          exact Function.update_self idx _ x
        rw [hxidx]
        have hrowx : p15RoundedRowValue fp n L b x idx =
            fp.fl_div s (L idx idx) := by
          dsimp only [p15RoundedRowValue, s, idx]
        rw [← hrowx]
        apply p15RoundedRowValue_congr fp n L b x y idx
        intro j hj
        have hyj : y j = x' j := by
          apply roundedForwardSubSteps_unchanged fp n L b k
            (Nat.le_of_succ_le hk) x' j
          dsimp only [idx] at hj ⊢
          omega
        rw [hyj]
        symm
        apply Function.update_of_ne
        intro heq
        have hv : j.val = idx.val := congrArg Fin.val heq
        omega
      · apply ih (Nat.le_of_succ_le hk) x' i
        dsimp only [idx] at hieq
        have hneval : i.val ≠ n-k-1 := by
          intro heq
          apply hieq
          apply Fin.ext
          exact heq
        omega

lemma roundedForwardSub_row (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (b : P15Vector n) (i : Fin n) :
    let x := roundedForwardSub fp n L b
    x i = p15RoundedRowValue fp n L b x i := by
  dsimp only [roundedForwardSub]
  apply roundedForwardSubSteps_row fp n L b n (le_refl n)
  omega

end HighamBench

namespace HighamBench
open scoped BigOperators

lemma fin_sum_eq_lower_add_diag {n : ℕ} (f : Fin n → ℝ) (i : Fin n)
    (hupper : ∀ j : Fin n, i.val < j.val → f j = 0) :
    (∑ j : Fin n, f j) =
      (∑ t : Fin i.val, f ⟨t.val, by omega⟩) + f i := by
  let g : ℕ → ℝ := fun k => if hk : k < n then f ⟨k, hk⟩ else 0
  have hall : (∑ j : Fin n, f j) = ∑ k ∈ Finset.range n, g k := by
    rw [Finset.sum_fin_eq_sum_range]
  have hsub : Finset.range (i.val+1) ⊆ Finset.range n := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have hsmall : (∑ k ∈ Finset.range (i.val+1), g k) =
      ∑ k ∈ Finset.range n, g k := by
    apply Finset.sum_subset hsub
    intro k hkn hknot
    simp only [Finset.mem_range] at hkn
    have hik : i.val < k := by
      by_contra hle
      apply hknot
      simp only [Finset.mem_range]
      omega
    simp only [g, dif_pos hkn]
    apply hupper
    exact hik
  have hlower : (∑ t : Fin i.val, f ⟨t.val, by omega⟩) =
      ∑ k ∈ Finset.range i.val, g k := by
    rw [← Fin.sum_univ_eq_sum_range g i.val]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [g]
    split
    · congr
    · rename_i hbad
      exfalso
      apply hbad
      omega
  rw [hall, ← hsmall, Finset.sum_range_succ, ← hlower]
  simp only [g, dif_pos i.isLt]

end HighamBench

namespace HighamBench
open scoped BigOperators

lemma roundedForwardSub_backward (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (b : P15Vector n)
    (hdiag : ∀ i, L i i ≠ 0) (hlower : p15LowerTriangular L)
    (hv : GammaValid fp.u n) :
    let x := roundedForwardSub fp n L b
    ∃ D : P15Matrix n,
      p15RectFrobNorm D ≤ gamma fp.u n * p15RectFrobNorm L ∧
      p15RectMatVec (p15RectAdd L D) x = b := by
  classical
  dsimp only
  let x := roundedForwardSub fp n L b
  have hw : ∀ i : Fin n, ∃ ed : ℝ, ∃ e : Fin i.val → ℝ,
      |ed| ≤ gamma fp.u n ∧
      (∀ t, |e t| ≤ gamma fp.u n) ∧
      b i = (L i i + L i i * ed) * x i +
        ∑ t : Fin i.val,
          (L i ⟨t.val, by omega⟩ + L i ⟨t.val, by omega⟩ * e t) *
            x ⟨t.val, by omega⟩ := by
    intro i
    have hvi : GammaValid fp.u (i.val+1) :=
      gammaValid_mono fp.u_nonneg (by omega) hv
    obtain ⟨ed, e, hed, he, heq⟩ := roundedSolveRow_backward fp i.val hvi
      (fun t => L i ⟨t.val, by omega⟩)
      (fun t => x ⟨t.val, by omega⟩) (b i) (L i i) (hdiag i)
    refine ⟨ed, e, hed.trans ?_, (fun t => (he t).trans ?_), ?_⟩
    · exact gamma_mono fp.u_nonneg (by omega) hv
    · exact gamma_mono fp.u_nonneg (by omega) hv
    · have hrow := roundedForwardSub_row fp n L b i
      dsimp only [p15RoundedRowValue] at hrow
      rw [← hrow] at heq
      exact heq
  choose ed e hed he heq using hw
  let D : P15Matrix n := fun i j =>
    if hji : j.val < i.val then L i j * e i ⟨j.val, hji⟩
    else if j = i then L i i * ed i else 0
  refine ⟨D, ?_, ?_⟩
  · apply p15RectFrobNorm_le_of_pointwise L D (gamma fp.u n)
      (gamma_nonneg fp.u_nonneg hv)
    intro i j
    dsimp only [D]
    split
    · rename_i hji
      rw [abs_mul]
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left (he i ⟨j.val, hji⟩) (abs_nonneg (L i j)))
    · rename_i hnlt
      split
      · rename_i hji
        subst j
        rw [abs_mul]
        simpa [mul_comm] using
          (mul_le_mul_of_nonneg_left (hed i) (abs_nonneg (L i i)))
      · simp only [abs_zero]
        exact mul_nonneg (gamma_nonneg fp.u_nonneg hv) (abs_nonneg _)
  · funext i
    unfold p15RectMatVec
    rw [fin_sum_eq_lower_add_diag (i := i)]
    · have hsum :
          (∑ t : Fin i.val,
              p15RectAdd L D i ⟨t.val, by omega⟩ * x ⟨t.val, by omega⟩) =
            ∑ t : Fin i.val,
              (L i ⟨t.val, by omega⟩ +
                L i ⟨t.val, by omega⟩ * e i t) * x ⟨t.val, by omega⟩ := by
          apply Finset.sum_congr rfl
          intro t ht
          simp only [p15RectAdd, D, dif_pos t.isLt]
      have hdiagD : p15RectAdd L D i i = L i i + L i i * ed i := by
        simp only [p15RectAdd, D, lt_self_iff_false, dite_false, if_pos]
      change
        (∑ t : Fin i.val,
            p15RectAdd L D i ⟨t.val, by omega⟩ * x ⟨t.val, by omega⟩) +
          p15RectAdd L D i i * x i = b i
      rw [hsum, hdiagD, heq i]
      ring
    · intro j hij
      have hL : L i j = 0 := hlower i j hij
      have hnlt : ¬ j.val < i.val := by omega
      have hne : j ≠ i := by
        intro hji
        subst j
        omega
      simp only [p15RectAdd, D, hL, hnlt, dite_false, hne, if_false,
        zero_add, zero_mul]

end HighamBench

namespace HighamBench
open scoped BigOperators

lemma p15RectMatVec_matMul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  unfold p15RectMatVec p15RectMatMul
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end HighamBench

namespace HighamBench

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
  let x₀ := roundedForwardSub fp b T₀ v₀
  let wInner := p15RoundedRectMatVec fp (p15RectTranspose Y) x₀
  let wHat := p15RoundedRectMatVec fp X wInner
  let rhsHat := fun i ↦ fp.fl_sub (v₁ i) (wHat i)
  let x₁ := roundedForwardSub fp b T₁ rhsHat
  obtain ⟨ΔT₀, hΔT₀, hx₀⟩ :=
    roundedForwardSub_backward fp b T₀ v₀ hT₀diag hT₀lower hb
  obtain ⟨ΔYT, hΔYT, hwInner⟩ :=
    p15RoundedRectMatVec_backward fp hb (p15RectTranspose Y) x₀
  obtain ⟨ΔX, hΔX, hwHat⟩ :=
    p15RoundedRectMatVec_backward fp hr X wInner
  have hsub : ∀ i : Fin b, ∃ d : ℝ,
      |d| ≤ fp.u ∧ rhsHat i = (v₁ i - wHat i) * (1+d) := by
    intro i
    exact fp.model_sub (v₁ i) (wHat i)
  choose θ hθ hrhs using hsub
  obtain ⟨ΔT₁, hΔT₁, hx₁⟩ :=
    roundedForwardSub_backward fp b T₁ rhsHat hT₁diag hT₁lower hb
  let ΔT₁₀ : P15Matrix b := fun i j =>
    (1 + θ i) *
      p15RectMatMul (p15RectAdd X ΔX)
        (p15RectAdd (p15RectTranspose Y) ΔYT) i j -
      p15LowRankMatrix X Y i j
  refine ⟨ΔT₀, ΔYT, ΔX, θ, ΔT₁, ΔT₁₀,
    hΔT₀, hΔYT, hΔX, hθ, hΔT₁, hx₀, hwInner, hwHat, hrhs, hx₁, ?_, ?_⟩
  · intro i j
    simp only [p15RectAdd, ΔT₁₀]
    ring
  · intro i
    have hscaled :
        p15RectMatVec
            (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i =
          (1 + θ i) * wHat i := by
      unfold p15RectMatVec
      simp_rw [show ∀ j,
          p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j =
            (1 + θ i) *
              p15RectMatMul (p15RectAdd X ΔX)
                (p15RectAdd (p15RectTranspose Y) ΔYT) i j by
        intro j
        simp only [p15RectAdd, ΔT₁₀]
        ring]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      have hassoc := p15RectMatVec_matMul
        (p15RectAdd X ΔX) (p15RectAdd (p15RectTranspose Y) ΔYT) x₀
      have hi := congrFun hassoc i
      change (1 + θ i) *
        p15RectMatVec
          (p15RectMatMul (p15RectAdd X ΔX)
            (p15RectAdd (p15RectTranspose Y) ΔYT)) x₀ i = _
      rw [hi]
      rw [← hwInner, ← hwHat]
    rw [hscaled]
    have hx₁i := congrFun hx₁ i
    rw [hx₁i, hrhs i]
    ring

end HighamBench
