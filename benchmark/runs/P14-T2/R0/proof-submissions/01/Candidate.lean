import Mathlib

namespace HighamBenchCandidate

noncomputable section

/- The exact denominator and componentwise softmax of (1.2). -/
def exactDenominator {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, Real.exp (x j)

def softmax {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.exp (x j) / exactDenominator x

/- Algorithm 3.1 starts with zero and adds exponentials in index order. The
   addition of the first computed exponential to zero is exact; every later
   addition has the relative error of the standard model (1.7). -/
def roundedDenominator {n : ℕ} (w : Fin n → ℝ) (addErr : Fin n → ℝ) : ℝ :=
  (List.finRange n).foldl
    (fun s j => if j.val = 0 then w j else (s + w j) * (1 + addErr j)) 0

def infinityNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  (List.finRange n).foldl (fun m j => max m |v j|) 0

/- Relative models for exponential evaluation (3.1), recursive summation,
   and the final divisions. These models apply in the stipulated absence of
   overflow and underflow. -/
def computedExp {n : ℕ} (x : Fin n → ℝ) (expErr : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.exp (x j) * (1 + expErr j)

def computedSoftmax {n : ℕ} (x : Fin n → ℝ)
    (expErr addErr divErr : Fin n → ℝ) (j : Fin n) : ℝ :=
  (computedExp x expErr j /
    roundedDenominator (computedExp x expErr) addErr) * (1 + divErr j)


private theorem step_bound {r s w e u B : ℝ}
    (hs : 0 ≤ s) (hw : 0 ≤ w) (hu : 0 ≤ u) (hB : 0 ≤ B)
    (hr : |r-s| ≤ s*B) (he : |e| ≤ u) :
    |(r+w)*(1+e)-(s+w)| ≤ (s+w)*((1+u)*B+u) := by
  have hse : 0 ≤ s+w := by positivity
  have h1 : |1+e| ≤ 1+u := by
    calc
      |1+e| ≤ |(1:ℝ)| + |e| := abs_add_le _ _
      _ ≤ 1+u := by simpa using add_le_add_left he 1
  have h2 : |r-s| * |1+e| ≤ (s*B)*(1+u) := by
    apply mul_le_mul hr h1 (abs_nonneg _) (by positivity)
  have h3 : |s+w| * |e| ≤ (s+w)*u := by
    rw [abs_of_nonneg hse]
    exact mul_le_mul_of_nonneg_left he hse
  calc
    |(r+w)*(1+e)-(s+w)| = |(r-s)*(1+e)+(s+w)*e| := by congr 1 <;> ring
    _ ≤ |r-s| * |1+e| + |s+w| * |e| := by simpa only [abs_mul] using abs_add_le ((r-s)*(1+e)) ((s+w)*e)
    _ ≤ (s*B)*(1+u) + (s+w)*u := add_le_add h2 h3
    _ ≤ (s+w)*((1+u)*B+u) := by nlinarith [mul_nonneg hw hB]

private theorem fold_bound_aux {α : Type*} (w e : α → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hw : ∀ j, 0 ≤ w j) (he : ∀ j, |e j| ≤ u)
    (l : List α) (r s : ℝ) (k : ℕ) (hs : 0 ≤ s)
    (hr : |r-s| ≤ s * ((1+u)^k-1)) :
    |l.foldl (fun a j => (a+w j)*(1+e j)) r - (s+(l.map w).sum)| ≤
      (s+(l.map w).sum) * ((1+u)^(k+l.length)-1) := by
  induction l generalizing r s k with
  | nil => simpa using hr
  | cons j tail ih =>
      have hB : 0 ≤ (1+u)^k-1 := by
        have := one_le_pow₀ (by linarith : (1:ℝ) ≤ 1+u) (n := k)
        linarith
      have hstep := step_bound hs (hw j) hu hB hr (he j)
      have hstep' : |(r+w j)*(1+e j)-(s+w j)| ≤
          (s+w j)*((1+u)^(k+1)-1) := by
        convert hstep using 1
        rw [pow_succ]
        ring
      have h := ih ((r+w j)*(1+e j)) (s+w j) (k+1) (by linarith [hw j]) hstep'
      simpa only [List.foldl_cons, List.map_cons, List.sum_cons, List.length_cons,
        add_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem fold_bound {α : Type*} (w e : α → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hw : ∀ j, 0 ≤ w j) (he : ∀ j, |e j| ≤ u)
    (l : List α) :
    |l.foldl (fun a j => (a+w j)*(1+e j)) 0 - (l.map w).sum| ≤
      (l.map w).sum * ((1+u)^l.length-1) := by
  simpa using fold_bound_aux w e u hu hw he l 0 0 0 (le_refl 0) (by simp)

private theorem finRange_sum {n : ℕ} (w : Fin n → ℝ) :
    ((List.finRange n).map w).sum = ∑ j : Fin n, w j := by
  rw [← List.sum_toFinset _ (List.nodup_finRange n), List.toFinset_finRange]

private theorem pow_quad (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (1+u)^n ≤ 1+(n:ℝ)*u+K*u^2 := by
  induction n with
  | zero =>
      refine ⟨0, le_refl 0, ?_⟩
      intro u hu hu1
      simp
  | succ n ih =>
      obtain ⟨K, hK, hbound⟩ := ih
      refine ⟨(n:ℝ)+2*K+1, by positivity, ?_⟩
      intro u hu hu1
      have hp := mul_le_mul_of_nonneg_right (hbound u hu hu1) (by linarith : 0 ≤ 1+u)
      have hu2 : 0 ≤ u^2 := sq_nonneg u
      have hu3 : u^3 ≤ u^2 := by nlinarith [mul_nonneg hu2 (sub_nonneg.mpr hu1)]
      have hK3 := mul_le_mul_of_nonneg_left hu3 hK
      rw [pow_succ] at hp ⊢
      push_cast
      nlinarith

private theorem sum_perturb {n : ℕ} (a e : Fin n → ℝ) (u : ℝ)
    (ha : ∀ j, 0 ≤ a j) (he : ∀ j, |e j| ≤ u) :
    |(∑ j, a j*(1+e j)) - ∑ j, a j| ≤ (∑ j, a j)*u := by
  have hrew : (∑ j, a j*(1+e j)) - ∑ j, a j = ∑ j, a j*e j := by
    simp_rw [mul_add, mul_one, Finset.sum_add_distrib]
    ring
  rw [hrew]
  calc
    |∑ j, a j*e j| ≤ ∑ j, |a j*e j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, a j*u := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (ha j)]
      exact mul_le_mul_of_nonneg_left (he j) (ha j)
    _ = (∑ j, a j)*u := by rw [Finset.sum_mul]

private theorem rounded_bound {n : ℕ} (w e : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hw : ∀ j, 0 ≤ w j) (he : ∀ j, |e j| ≤ u) :
    |roundedDenominator w e - ∑ j, w j| ≤
      (∑ j, w j)*((1+u)^n-1) := by
  cases n with
  | zero => simp [roundedDenominator]
  | succ n =>
      let l : List (Fin (n+1)) := (List.finRange n).map Fin.succ
      have h := fold_bound_aux w e u hu hw he l (w 0) (w 0) 0
        (hw 0) (by simp)
      have hlen : l.length = n := by simp [l]
      have hsum : w 0 + (l.map w).sum = ∑ j, w j := by
        rw [Fin.sum_univ_succ]
        simp [l, finRange_sum]
      have hrun : roundedDenominator w e =
          l.foldl (fun a j => (a+w j)*(1+e j)) (w 0) := by
        unfold roundedDenominator
        rw [List.finRange_succ, List.foldl_cons]
        simp only [Fin.val_zero, ↓reduceIte]
        simp [l, List.foldl_map]
      rw [hlen, hsum] at h
      have hS : 0 ≤ ∑ j, w j := Finset.sum_nonneg (by intro j hj; exact hw j)
      have hp : (1+u)^n ≤ (1+u)^(n+1) := by
        rw [pow_succ]
        nlinarith [pow_nonneg (by linarith : 0 ≤ 1+u) n]
      rw [hrun]
      calc
        |l.foldl (fun a j => (a+w j)*(1+e j)) (w 0) - ∑ j, w j| ≤
            (∑ j, w j)*((1+u)^n-1) := by simpa using h
        _ ≤ (∑ j, w j)*((1+u)^(n+1)-1) :=
          mul_le_mul_of_nonneg_left (by linarith) hS

private theorem exactDenominator_pos {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    0 < exactDenominator x := by
  unfold exactDenominator
  apply Finset.sum_pos
  · intro j hj
    exact Real.exp_pos _
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

private theorem denominator_error {n : ℕ} (x : Fin n → ℝ)
    (u K : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) (hK : 0 ≤ K)
    (hpow : (1+u)^n ≤ 1+(n:ℝ)*u+K*u^2)
    (expErr addErr : Fin n → ℝ)
    (he : ∀ j, |expErr j| ≤ u) (ha : ∀ j, |addErr j| ≤ u) :
    |roundedDenominator (computedExp x expErr) addErr - exactDenominator x| ≤
      exactDenominator x * (((n:ℝ)+1)*u+((n:ℝ)+2*K)*u^2) := by
  let w := computedExp x expErr
  let W := ∑ j, w j
  let S := exactDenominator x
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    have := abs_le.mp (he j)
    dsimp [w, computedExp]
    apply mul_nonneg (Real.exp_pos _).le
    linarith
  have hS : 0 ≤ S := by
    dsimp [S, exactDenominator]
    exact Finset.sum_nonneg (by intro j hj; exact (Real.exp_pos _).le)
  have hW : 0 ≤ W := Finset.sum_nonneg (by intro j hj; exact hw j)
  have hExp : |W-S| ≤ S*u := by
    simpa only [W, S, w, computedExp, exactDenominator] using
      sum_perturb (fun j => Real.exp (x j)) expErr u
        (fun j => (Real.exp_pos _).le) he
  have hWup : W ≤ S*(1+u) := by
    have := (abs_le.mp hExp).2
    nlinarith
  have hRound := rounded_bound w addErr u hu hw ha
  have hfac : 0 ≤ (n:ℝ)*u+K*u^2 := by positivity
  have hDW : |roundedDenominator w addErr-W| ≤ W*((n:ℝ)*u+K*u^2) := by
    calc
      |roundedDenominator w addErr-W| ≤ W*((1+u)^n-1) := hRound
      _ ≤ W*((n:ℝ)*u+K*u^2) :=
        mul_le_mul_of_nonneg_left (by linarith) hW
  have htri : |roundedDenominator w addErr-S| ≤
      |roundedDenominator w addErr-W|+|W-S| := by
    convert abs_add_le (roundedDenominator w addErr-W) (W-S) using 1 <;> ring
  have hmult := mul_le_mul_of_nonneg_right hWup hfac
  have hu3 : u^3 ≤ u^2 := by nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu1)]
  have hKu := mul_le_mul_of_nonneg_left hu3 hK
  change |roundedDenominator w addErr-S| ≤ S*(((n:ℝ)+1)*u+((n:ℝ)+2*K)*u^2)
  nlinarith [htri]

private theorem scalar_error
    {S D a b u N K C : ℝ}
    (hS : 0 < S) (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hsmall : (N+1+K)*u ≤ 1/2)
    (hC : 2*((N+3)*(N+1+K)+K+1) ≤ C)
    (ha : |a| ≤ u) (hb : |b| ≤ u)
    (hDerr : |D-S| ≤ S*((N+1)*u+K*u^2)) :
    0 < D ∧
      |S*(1+a)*(1+b)/D-1| ≤ (N+3)*u+C*u^2 := by
  let H := N+1+K
  let h := (N+1)*u+K*u^2
  let B := (N+3)*u+C*u^2
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hC0 : 0 ≤ C := by nlinarith [mul_nonneg (by linarith : 0 ≤ N+3) hH]
  have hu2 : u^2 ≤ u := by nlinarith [mul_nonneg hu (sub_nonneg.mpr hu1)]
  have hh : h ≤ H*u := by
    dsimp [h, H]
    nlinarith [mul_le_mul_of_nonneg_left hu2 hK]
  have hhalf : h ≤ 1/2 := le_trans hh hsmall
  have hDlow : S*(1-h) ≤ D := by
    have := (abs_le.mp hDerr).1
    dsimp [h] at *
    nlinarith
  have hD : 0 < D := by
    have hpos : 0 < S*(1-h) := mul_pos hS (by linarith)
    linarith
  have hab : |a*b| ≤ u^2 := by
    rw [abs_mul, sq]
    exact mul_le_mul ha hb (abs_nonneg _) hu
  have hfac : |(1+a)*(1+b)-1| ≤ 2*u+u^2 := by
    have h1 : |a+b+a*b| ≤ |a|+|b|+|a*b| := by
      calc
        |a+b+a*b| ≤ |a+b|+|a*b| := abs_add_le _ _
        _ ≤ |a|+|b|+|a*b| := by linarith [abs_add_le a b]
    have heq : (1+a)*(1+b)-1 = a+b+a*b := by ring
    rw [heq]
    linarith
  have hnum : |S*(1+a)*(1+b)-D| ≤ S*((N+3)*u+(K+1)*u^2) := by
    have htri : |S*(1+a)*(1+b)-D| ≤
        S*|(1+a)*(1+b)-1|+|D-S| := by
      calc
        |S*(1+a)*(1+b)-D| ≤ |S*(1+a)*(1+b)-S|+|S-D| := abs_sub_le _ _ _
        _ = S*|(1+a)*(1+b)-1|+|D-S| := by
          have heq : S*(1+a)*(1+b)-S = S*((1+a)*(1+b)-1) := by ring
          rw [heq, abs_mul, abs_of_pos hS, abs_sub_comm S D]
    nlinarith [mul_le_mul_of_nonneg_left hfac hS.le]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCu : C*H*u ≤ C/2 := by
    have := mul_le_mul_of_nonneg_left hsmall hC0
    dsimp [H] at *
    nlinarith
  have hBh : B*h ≤ B*(H*u) := mul_le_mul_of_nonneg_left hh hB
  have hbig : (N+3)*u+(K+1)*u^2 ≤ B*(1-h) := by
    have hextra := mul_le_mul_of_nonneg_right hCu (sq_nonneg u)
    dsimp [B] at *
    nlinarith [sq_nonneg u, mul_nonneg hu (sq_nonneg u)]
  have hmul := mul_le_mul_of_nonneg_left hbig hS.le
  have hBmul := mul_le_mul_of_nonneg_left hDlow hB
  have hgoal : |S*(1+a)*(1+b)-D| ≤ B*D := by
    nlinarith [hnum, hmul, hBmul]
  constructor
  · exact hD
  · have heq : S*(1+a)*(1+b)/D-1 = (S*(1+a)*(1+b)-D)/D := by
      field_simp
    rw [heq, abs_div, abs_of_pos hD, div_le_iff₀ hD]
    exact hgoal

private theorem fold_max_bound {α : Type*} (l : List α)
    (v g : α → ℝ) (B a b : ℝ) (hB : 0 ≤ B) (hab : a ≤ B*b)
    (h : ∀ j, |v j| ≤ B*|g j|) :
    l.foldl (fun m j => max m |v j|) a ≤
      B * l.foldl (fun m j => max m |g j|) b := by
  induction l generalizing a b with
  | nil => simpa using hab
  | cons j tail ih =>
      simp only [List.foldl_cons]
      apply ih
      apply max_le
      · exact le_trans hab (mul_le_mul_of_nonneg_left (le_max_left b |g j|) hB)
      · exact le_trans (h j) (mul_le_mul_of_nonneg_left (le_max_right b |g j|) hB)

private theorem infinityNorm_bound {n : ℕ} (v g : Fin n → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (h : ∀ j, |v j| ≤ B*|g j|) :
    infinityNorm v ≤ B*infinityNorm g := by
  unfold infinityNorm
  exact fold_max_bound (List.finRange n) v g B 0 0 hB (by simp) h

private theorem fold_max_ge {α : Type*} (l : List α) (v : α → ℝ) (a : ℝ) :
    a ≤ l.foldl (fun m j => max m |v j|) a := by
  induction l generalizing a with
  | nil => simp
  | cons j tail ih =>
      simp only [List.foldl_cons]
      exact le_trans (le_max_left a |v j|) (ih _)

private theorem infinityNorm_pos {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    0 < infinityNorm (softmax x) := by
  cases n with
  | zero => omega
  | succ n =>
      have hs := exactDenominator_pos (Nat.zero_lt_succ n) x
      have hg : 0 < softmax x 0 := div_pos (Real.exp_pos _) hs
      unfold infinityNorm
      rw [List.finRange_succ, List.foldl_cons]
      have hfirst : 0 < max (0:ℝ) |softmax x 0| := by
        exact lt_of_lt_of_le (by simpa [abs_of_pos hg] using hg) (le_max_right _ _)
      exact lt_of_lt_of_le hfirst
        (fold_max_ge ((List.finRange n).map Fin.succ) (softmax x) _)

theorem target :
    ∀ (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ),
      ∃ C : ℝ, 0 < C ∧ ∃ u₀ : ℝ, 0 < u₀ ∧
        ∀ (u : ℝ), 0 < u → u ≤ u₀ →
          ∀ (expErr addErr divErr : Fin n → ℝ),
            (∀ j, |expErr j| ≤ u) →
            (∀ j, |addErr j| ≤ u) →
            (∀ j, |divErr j| ≤ u) →
              (∀ j, ∃ τ : ℝ,
                computedSoftmax x expErr addErr divErr j = softmax x j * (1 + τ) ∧
                |τ| ≤ ((n : ℝ) + 3) * u + C * u ^ 2) ∧
              infinityNorm (fun j =>
                softmax x j - computedSoftmax x expErr addErr divErr j) /
                infinityNorm (softmax x) ≤ ((n : ℝ) + 3) * u + C * u ^ 2 := by
  intro n hn x
  obtain ⟨K, hK, hpowK⟩ := pow_quad n
  let Kd : ℝ := (n:ℝ)+2*K
  let H : ℝ := (n:ℝ)+1+Kd
  let C : ℝ := 2*(((n:ℝ)+3)*H+Kd+1)+1
  let u₀ : ℝ := min 1 (1/(2*H))
  have hKd : 0 ≤ Kd := by dsimp [Kd]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hu0 : 0 < u₀ := by dsimp [u₀]; positivity
  refine ⟨C, hC, u₀, hu0, ?_⟩
  intro u hu hu0' expErr addErr divErr he ha hd
  have hu1 : u ≤ 1 := le_trans hu0' (by dsimp [u₀]; exact min_le_left _ _)
  have hsmall : H*u ≤ 1/2 := by
    have huH : u ≤ 1/(2*H) := le_trans hu0' (by dsimp [u₀]; exact min_le_right _ _)
    calc
      H*u ≤ H*(1/(2*H)) := mul_le_mul_of_nonneg_left huH hH.le
      _ = 1/2 := by field_simp
  have hpow : (1+u)^n ≤ 1+(n:ℝ)*u+K*u^2 := hpowK u hu.le hu1
  have hden := denominator_error x u K hu.le hu1 hK hpow expErr addErr he ha
  have hS := exactDenominator_pos hn x
  let D := roundedDenominator (computedExp x expErr) addErr
  let B : ℝ := ((n:ℝ)+3)*u+C*u^2
  have hsc (j : Fin n) :
      0 < D ∧
      |exactDenominator x*(1+expErr j)*(1+divErr j)/D-1| ≤ B := by
    have hCbound : 2*(((n:ℝ)+3)*(((n:ℝ)+1)+Kd)+Kd+1) ≤ C := by
      dsimp [C, H]
      linarith
    have hsmall' : (((n:ℝ)+1)+Kd)*u ≤ 1/2 := by simpa [H] using hsmall
    simpa only [D, B, Kd] using
      scalar_error (S := exactDenominator x) (D := D)
        (a := expErr j) (b := divErr j) (u := u)
        (N := (n:ℝ)) (K := Kd) (C := C)
        hS (by positivity) hKd hu.le hu1 hsmall' hCbound (he j) (hd j)
        (by simpa [D, Kd] using hden)
  have hcomp : ∀ j : Fin n, ∃ τ : ℝ,
      computedSoftmax x expErr addErr divErr j = softmax x j*(1+τ) ∧
      |τ| ≤ B := by
    intro j
    let τ : ℝ := exactDenominator x*(1+expErr j)*(1+divErr j)/D-1
    refine ⟨τ, ?_, (hsc j).2⟩
    have hD := (hsc j).1
    dsimp [computedSoftmax, computedExp, softmax, τ, D]
    field_simp
    ring
  constructor
  · simpa only [B] using hcomp
  · have hB : 0 ≤ B := by dsimp [B]; positivity
    have hAbs : ∀ j : Fin n,
        |softmax x j-computedSoftmax x expErr addErr divErr j| ≤
          B*|softmax x j| := by
      intro j
      obtain ⟨τ, hEq, hτ⟩ := hcomp j
      rw [hEq]
      have heq : softmax x j-softmax x j*(1+τ) = -(softmax x j)*τ := by ring
      rw [heq, abs_mul, abs_neg]
      nlinarith [mul_le_mul_of_nonneg_left hτ (abs_nonneg (softmax x j))]
    have hnorm := infinityNorm_bound
      (fun j => softmax x j-computedSoftmax x expErr addErr divErr j)
      (softmax x) B hB hAbs
    exact (div_le_iff₀ (infinityNorm_pos hn x)).2 (by simpa only [B] using hnorm)


end

end HighamBenchCandidate
