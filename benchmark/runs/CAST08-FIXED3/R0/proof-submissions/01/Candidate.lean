import Mathlib

namespace HighamBenchCandidate

/-- Independent relative errors for the rounded products and for additions at
all three levels of the fixed-block algorithm. -/
structure RoundErrors (b m : ℕ) where
  product : Fin (b * m * m) → ℝ
  innerAdd : Fin m → Fin m → Fin b → ℝ
  blockAdd : Fin m → Fin m → ℝ
  superAdd : Fin m → ℝ

/-- The standard relative-error model for multiplication and addition, with
unit roundoff `u`. The first addition to a zero accumulator is exact. -/
def RoundErrors.Valid {b m : ℕ} (e : RoundErrors b m) (u : ℝ) : Prop :=
  (∀ k, |e.product k| ≤ u) ∧
  (∀ s j i, |e.innerAdd s j i| ≤ u) ∧
  (∀ s j, |e.blockAdd s j| ≤ u) ∧
  (∀ s, |e.superAdd s| ≤ u)

/-- The consecutive position of entry `i` of block `j` of superblock `s`. -/
def flatIndex {b m : ℕ} (s j : Fin m) (i : Fin b) : Fin (b * m * m) :=
  finCongr (by ac_rfl) (finProdFinEquiv (finProdFinEquiv (s, j), i))

/-- Recursive summation in list order. An initial zero plus the first term is
exact, as for floating-point addition without overflow or underflow. -/
def roundedSum {n : ℕ} (term : Fin n → ℝ) (δ : Fin n → ℝ) : ℝ :=
  ((List.finRange n).foldl
    (fun acc k =>
      match acc with
      | none => some (term k)
      | some a => some ((a + term k) * (1 + δ k)))
    (none : Option ℝ)).getD 0

/-- Rounded length-`b` inner dot product for one consecutive block. -/
def innerDot {b m : ℕ} (x y : Fin (b * m * m) → ℝ)
    (e : RoundErrors b m) (s j : Fin m) : ℝ :=
  roundedSum
    (fun i => (x (flatIndex s j i) * y (flatIndex s j i)) *
      (1 + e.product (flatIndex s j i)))
    (e.innerAdd s j)

/-- Three-level fixed-`b` superblock dot product, retaining the input order. -/
def superblockDot {b m : ℕ} (x y : Fin (b * m * m) → ℝ)
    (e : RoundErrors b m) : ℝ :=
  roundedSum
    (fun s => roundedSum (fun j => innerDot x y e s j) (e.blockAdd s))
    e.superAdd

/-- Higham's `γ_k = ku/(1-ku)` bound. -/
noncomputable def gamma (u : ℝ) (k : ℕ) : ℝ := (k * u) / (1 - k * u)

private lemma gm (u : ℝ) (hu : 0 ≤ u) {a b : ℕ} (hab : a ≤ b)
    (hb : (b:ℝ)*u < 1) : gamma u a ≤ gamma u b := by
  have hcast : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
  have ha : 0 < 1 - (a:ℝ)*u := by nlinarith
  have hb' : 0 < 1 - (b:ℝ)*u := by linarith
  unfold gamma
  apply (div_le_div_iff₀ ha hb').2
  nlinarith
private lemma gs (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : ((k+1:ℕ):ℝ)*u < 1) :
    gamma u k + u*(1+gamma u k) ≤ gamma u (k+1) := by
  have hkn : (k:ℝ)*u < 1 := by push_cast at hk ⊢; nlinarith
  have hd : 0 < 1-(k:ℝ)*u := by linarith
  have hd' : 0 < 1-((k+1:ℕ):ℝ)*u := by linarith
  have hident : gamma u k + u*(1+gamma u k) =
      (((k+1:ℕ):ℝ)*u)/(1-(k:ℝ)*u) := by
    unfold gamma
    field_simp
    push_cast
    ring
  rw [hident]
  unfold gamma
  apply (div_le_div_iff₀ hd hd').2
  push_cast
  nlinarith [sq_nonneg u]
private lemma gn (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : (k:ℝ)*u < 1) : 0 ≤ gamma u k := by
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma stepBound (u : ℝ) (hu : 0 ≤ u) (p k : ℕ) (hpk : p ≤ k)
    (hk : ((k+1:ℕ):ℝ)*u < 1) (a s A g f W δ : ℝ)
    (hA : 0 ≤ A) (hs : |s| ≤ A)
    (ha : |a-s| ≤ gamma u k * A)
    (hW : |f| ≤ W) (hg : |g-f| ≤ gamma u p * W) (hδ : |δ| ≤ u) :
    |(a+g)*(1+δ) - (s+f)| ≤ gamma u (k+1) * (A+W) := by
  have hk0 : (k:ℝ)*u < 1 := by push_cast at hk ⊢; nlinarith
  have hp : gamma u p ≤ gamma u k := gm u hu hpk hk0
  have hgn : 0 ≤ gamma u k := gn u hu k hk0
  have hW0 : 0 ≤ W := (abs_nonneg f).trans hW
  have hnon : 0 ≤ A + W := add_nonneg hA hW0
  have habs : |a+g| ≤ (1+gamma u k)*(A+W) := by
    calc
      |a+g| = |(s+f)+((a-s)+(g-f))| := congrArg abs (by ring)
      _ ≤ |s+f| + (|a-s|+|g-f|) := by
        calc
          _ ≤ |s+f| + |(a-s)+(g-f)| := abs_add_le _ _
          _ ≤ |s+f| + (|a-s|+|g-f|) := by gcongr; exact abs_add_le _ _
      _ ≤ (1+gamma u k)*(A+W) := by
        have hsf : |s+f| ≤ A+W := by linarith [abs_add_le s f]
        nlinarith [mul_nonneg (sub_nonneg.mpr hp) hW0]
  have hmul : |δ| * |a+g| ≤ u * ((1+gamma u k)*(A+W)) := by
    calc
      |δ| * |a+g| ≤ u * |a+g| := mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
      _ ≤ u * ((1+gamma u k)*(A+W)) := mul_le_mul_of_nonneg_left habs hu
  have herr : |(a+g)*(1+δ) - (s+f)| ≤
      gamma u k * A + gamma u p * W +
        u * ((1+gamma u k)*(A+W)) := by
    have heq : (a+g)*(1+δ) - (s+f) = (a-s)+(g-f)+δ*(a+g) := by ring
    rw [heq]
    calc
      |(a-s)+(g-f)+δ*(a+g)| ≤ |a-s|+|g-f|+|δ*(a+g)| := by
        calc
          _ ≤ |(a-s)+(g-f)| + |δ*(a+g)| := abs_add_le _ _
          _ ≤ |a-s|+|g-f|+|δ*(a+g)| := by linarith [abs_add_le (a-s) (g-f)]
      _ ≤ _ := by rw [abs_mul]; linarith
  have hnext := gs u hu k hk
  have hgap : 0 ≤ (gamma u k - gamma u p)*W := mul_nonneg (sub_nonneg.mpr hp) hW0
  calc
    _ ≤ gamma u k * A + gamma u p * W +
        u * ((1+gamma u k)*(A+W)) := herr
    _ ≤ (gamma u k + u*(1+gamma u k))*(A+W) := by nlinarith
    _ ≤ gamma u (k+1)*(A+W) := mul_le_mul_of_nonneg_right hnext hnon

private lemma foldBound {α : Type*} (l : List α) (f g w δ : α → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (p q : ℕ)
    (hvalid : (((p+q+l.length):ℕ):ℝ)*u < 1)
    (hweight : ∀ i ∈ l, |f i| ≤ w i)
    (hterm : ∀ i ∈ l, |g i-f i| ≤ gamma u p * w i)
    (hδ : ∀ i ∈ l, |δ i| ≤ u)
    (a s A : ℝ) (hA : 0 ≤ A) (hs : |s| ≤ A)
    (ha : |a-s| ≤ gamma u (p+q)*A) :
    |l.foldl (fun acc i => (acc+g i)*(1+δ i)) a - (s+(l.map f).sum)| ≤
      gamma u (p+q+l.length) * (A+(l.map w).sum) := by
  induction l generalizing q a s A with
  | nil => simpa using ha
  | cons i l ih =>
      have hlim : (((p+q+1):ℕ):ℝ)*u < 1 := by
        have hle : p+q+1 ≤ p+q+(i::l).length := by simp
        have hcast : ((p+q+1:ℕ):ℝ) ≤ ((p+q+(i::l).length:ℕ):ℝ) := by exact_mod_cast hle
        nlinarith
      have hstep := stepBound u hu p (p+q) (by omega) (by simpa [add_assoc] using hlim)
        a s A (g i) (f i) (w i) (δ i) hA hs ha
        (hweight i (by simp)) (hterm i (by simp)) (hδ i (by simp))
      have hnewA : 0 ≤ A+w i := add_nonneg hA ((abs_nonneg _).trans (hweight i (by simp)))
      have hnewS : |s+f i| ≤ A+w i := by linarith [abs_add_le s (f i), hweight i (by simp)]
      have hrest : (((p+(q+1)+l.length):ℕ):ℝ)*u < 1 := by
        simpa [List.length_cons, add_assoc, add_left_comm, add_comm] using hvalid
      have hr := ih (q+1) hrest
        (fun j hj => hweight j (by simp [hj]))
        (fun j hj => hterm j (by simp [hj]))
        (fun j hj => hδ j (by simp [hj]))
        ((a+g i)*(1+δ i)) (s+f i) (A+w i) hnewA hnewS
        (by simpa [add_assoc] using hstep)
      simpa [List.foldl_cons, List.map_cons, List.sum_cons,
        List.length_cons, add_assoc, add_left_comm, add_comm] using hr
private lemma foldSome {α : Type*} (l : List α) (g δ : α → ℝ) (a : ℝ) :
    l.foldl (fun acc i => match acc with
      | none => some (g i)
      | some v => some ((v+g i)*(1+δ i))) (some a) =
    some (l.foldl (fun acc i => (acc+g i)*(1+δ i)) a) := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih => simpa [List.foldl_cons] using ih ((a+g i)*(1+δ i))

private lemma roundListBound {α : Type*} (i : α) (l : List α)
    (f g w δ : α → ℝ) (u : ℝ) (hu : 0 ≤ u) (p : ℕ)
    (hvalid : (((p+l.length):ℕ):ℝ)*u < 1)
    (hweight : ∀ j ∈ i::l, |f j| ≤ w j)
    (hterm : ∀ j ∈ i::l, |g j-f j| ≤ gamma u p * w j)
    (hδ : ∀ j ∈ i::l, |δ j| ≤ u) :
    abs (((i::l).foldl (fun acc j => match acc with
        | none => some (g j)
        | some v => some ((v+g j)*(1+δ j))) (none : Option ℝ)).getD 0 -
        ((i::l).map f).sum) ≤
      gamma u (p+l.length) * (((i::l).map w).sum) := by
  have h := foldBound l f g w δ u hu p 0
    (by simpa using hvalid)
    (fun j hj => hweight j (by simp [hj]))
    (fun j hj => hterm j (by simp [hj]))
    (fun j hj => hδ j (by simp [hj]))
    (g i) (f i) (w i) ((abs_nonneg _).trans (hweight i (by simp)))
    (hweight i (by simp)) (by simpa using hterm i (by simp))
  rw [List.foldl_cons, foldSome]
  simpa only [Option.getD_some, List.map_cons, List.sum_cons, zero_add,
    add_assoc] using h

private lemma sumFinRange {n : ℕ} (f : Fin n → ℝ) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  simp only [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

private lemma roundedSumBound {n : ℕ} (hn : 0 < n)
    (f g w δ : Fin n → ℝ) (u : ℝ) (hu : 0 ≤ u) (p : ℕ)
    (hvalid : (((p+n-1):ℕ):ℝ)*u < 1)
    (hweight : ∀ i, |f i| ≤ w i)
    (hterm : ∀ i, |g i-f i| ≤ gamma u p * w i)
    (hδ : ∀ i, |δ i| ≤ u) :
    |roundedSum g δ - ∑ i : Fin n, f i| ≤
      gamma u (p+n-1) * ∑ i : Fin n, w i := by
  cases hlist : List.finRange n with
  | nil =>
      have hlen : (List.finRange n).length = n := by simp
      simp [hlist] at hlen
      omega
  | cons i l =>
      have hlen : (List.finRange n).length = n := by simp
      rw [hlist] at hlen
      simp only [List.length_cons] at hlen
      have hnum : p+l.length = p+n-1 := by omega
      have h := roundListBound i l f g w δ u hu p
        (by simpa [hnum] using hvalid)
        (fun j _ => hweight j)
        (fun j _ => hterm j) (fun j _ => hδ j)
      unfold roundedSum
      rw [hlist]
      rw [← sumFinRange f, ← sumFinRange w]
      simpa [hlist, hnum] using h

private lemma productBound (u z δ : ℝ) (hu : 0 ≤ u)
    (hu1 : u < 1) (hδ : |δ| ≤ u) :
    |z*(1+δ)-z| ≤ gamma u 1 * |z| := by
  have hγ : u ≤ gamma u 1 := by
    have hs := gs u hu 0 (by simpa using hu1)
    simpa [gamma] using hs
  have heq : z*(1+δ)-z = z*δ := by ring
  rw [heq, abs_mul]
  calc
    |z| * |δ| ≤ |z| * u := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ ≤ gamma u 1 * |z| := by simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hγ (abs_nonneg z))

private lemma innerBound {b m : ℕ} (hb : 0 < b)
    (x y : Fin (b*m*m) → ℝ) (e : RoundErrors b m)
    (u : ℝ) (hu : 0 ≤ u) (he : e.Valid u)
    (hbu : (b:ℝ)*u < 1) (s j : Fin m) :
    |innerDot x y e s j -
        ∑ i : Fin b, x (flatIndex s j i) * y (flatIndex s j i)| ≤
      gamma u b *
        ∑ i : Fin b, |x (flatIndex s j i) * y (flatIndex s j i)| := by
  have hu1 : u < 1 := by
    have hb1 : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
    nlinarith
  have hnum : 1+b-1=b := by omega
  have h := roundedSumBound hb
    (fun i : Fin b => x (flatIndex s j i) * y (flatIndex s j i))
    (fun i : Fin b => (x (flatIndex s j i) * y (flatIndex s j i)) *
      (1+e.product (flatIndex s j i)))
    (fun i : Fin b => |x (flatIndex s j i) * y (flatIndex s j i)|)
    (e.innerAdd s j) u hu 1 (by simpa [hnum] using hbu)
    (fun i => le_refl _)
    (fun i => productBound u _ _ hu hu1 (he.1 (flatIndex s j i)))
    (fun i => he.2.1 s j i)
  simpa [innerDot, hnum] using h

private lemma validMono (u : ℝ) (hu : 0 ≤ u) {a k : ℕ}
    (hak : a ≤ k) (hk : (k:ℝ)*u < 1) : (a:ℝ)*u < 1 := by
  have hcast : (a:ℝ) ≤ (k:ℝ) := by exact_mod_cast hak
  have hmul := mul_le_mul_of_nonneg_right hcast hu
  exact lt_of_le_of_lt hmul hk

private lemma blockBound {b m : ℕ} (hb : 0 < b) (hm : 0 < m)
    (x y : Fin (b*m*m) → ℝ) (e : RoundErrors b m)
    (u : ℝ) (hu : 0 ≤ u) (he : e.Valid u)
    (hmid : (((b+m-1):ℕ):ℝ)*u < 1) (s : Fin m) :
    |roundedSum (fun j => innerDot x y e s j) (e.blockAdd s) -
      ∑ j : Fin m, ∑ i : Fin b,
        x (flatIndex s j i) * y (flatIndex s j i)| ≤
      gamma u (b+m-1) *
        ∑ j : Fin m, ∑ i : Fin b,
          |x (flatIndex s j i) * y (flatIndex s j i)| := by
  have hbu : (b:ℝ)*u < 1 := validMono u hu (by omega : b ≤ b+m-1) hmid
  let f : Fin m → ℝ := fun j => ∑ i : Fin b,
    x (flatIndex s j i) * y (flatIndex s j i)
  let w : Fin m → ℝ := fun j => ∑ i : Fin b,
    |x (flatIndex s j i) * y (flatIndex s j i)|
  have hweight : ∀ j, |f j| ≤ w j := by
    intro j
    simpa [f, w] using (Finset.abs_sum_le_sum_abs
      (fun i : Fin b => x (flatIndex s j i) * y (flatIndex s j i)) Finset.univ)
  have hnum : b+m-1=b+m-1 := rfl
  have h := roundedSumBound hm f (fun j => innerDot x y e s j) w
    (e.blockAdd s) u hu b (by simpa using hmid) hweight
    (fun j => innerBound hb x y e u hu he hbu s j)
    (fun j => he.2.2.1 s j)
  simpa [f, w] using h

private lemma sumFlat {b m : ℕ} (f : Fin (b*m*m) → ℝ) :
    (∑ s : Fin m, ∑ j : Fin m, ∑ i : Fin b,
      f (flatIndex s j i)) = ∑ k : Fin (b*m*m), f k := by
  let e : Fin (m*m*b) ≃ Fin (b*m*m) := finCongr (by ac_rfl)
  calc
    _ = ∑ sj : Fin m × Fin m, ∑ i : Fin b,
          f (flatIndex sj.1 sj.2 i) := by
            symm
            exact Fintype.sum_prod_type _
    _ = ∑ q : Fin (m*m), ∑ i : Fin b,
          f (e (finProdFinEquiv (q,i))) := by
            simpa [flatIndex, e] using
              (Equiv.sum_comp (finProdFinEquiv : Fin m × Fin m ≃ Fin (m*m))
                (fun q : Fin (m*m) => ∑ i : Fin b,
                  f (e (finProdFinEquiv (q,i)))))
    _ = ∑ qi : Fin (m*m) × Fin b,
          f (e (finProdFinEquiv qi)) := by
            symm
            exact Fintype.sum_prod_type _
    _ = ∑ k : Fin (m*m*b), f (e k) := by
          exact Equiv.sum_comp (finProdFinEquiv : Fin (m*m) × Fin b ≃ Fin (m*m*b))
            (fun k => f (e k))
    _ = ∑ k : Fin (b*m*m), f k := Equiv.sum_comp e f

/-- Section 3.1 of Castaldo, Whaley, and Chronopoulos (2008), for Figure 3.1(b).
Here `N = b*m*m`, with positive integral block size `b` and `m` blocks per
superblock and superblocks in total. -/
theorem target :
    ∀ (b m : ℕ), 0 < b → 0 < m →
    ∀ (u : ℝ), 0 ≤ u →
    ∀ (x y : Fin (b * m * m) → ℝ) (e : RoundErrors b m),
      e.Valid u →
      (((b + 2 * (m - 1) : ℕ) : ℝ) * u < 1) →
      |superblockDot x y e - ∑ k : Fin (b * m * m), x k * y k| ≤
        gamma u (b + 2 * (m - 1)) *
          ∑ k : Fin (b * m * m), |x k * y k| := by
  intro b m hb hm u hu x y e he hvalid
  have hnum : (b+m-1)+m-1 = b+2*(m-1) := by omega
  have hmid : (((b+m-1):ℕ):ℝ)*u < 1 :=
    validMono u hu (by omega : b+m-1 ≤ b+2*(m-1)) hvalid
  let f : Fin m → ℝ := fun s => ∑ j : Fin m, ∑ i : Fin b,
    x (flatIndex s j i) * y (flatIndex s j i)
  let w : Fin m → ℝ := fun s => ∑ j : Fin m, ∑ i : Fin b,
    |x (flatIndex s j i) * y (flatIndex s j i)|
  let g : Fin m → ℝ := fun s =>
    roundedSum (fun j => innerDot x y e s j) (e.blockAdd s)
  have hweight : ∀ s, |f s| ≤ w s := by
    intro s
    have houter : |f s| ≤ ∑ j : Fin m,
        |∑ i : Fin b, x (flatIndex s j i) * y (flatIndex s j i)| := by
      simpa [f] using (Finset.abs_sum_le_sum_abs
        (fun j : Fin m => ∑ i : Fin b,
          x (flatIndex s j i) * y (flatIndex s j i)) Finset.univ)
    have hinner : (∑ j : Fin m,
        |∑ i : Fin b, x (flatIndex s j i) * y (flatIndex s j i)|) ≤ w s := by
      apply Finset.sum_le_sum
      intro j hj
      simpa [w] using (Finset.abs_sum_le_sum_abs
        (fun i : Fin b => x (flatIndex s j i) * y (flatIndex s j i)) Finset.univ)
    exact houter.trans hinner
  have h := roundedSumBound hm f g w e.superAdd u hu (b+m-1)
    (by simpa [hnum] using hvalid)
    hweight
    (fun s => blockBound hb hm x y e u hu he hmid s)
    (fun s => he.2.2.2 s)
  dsimp [f, g, w] at h
  rw [sumFlat (fun k => x k * y k),
      sumFlat (fun k => |x k * y k|), hnum] at h
  exact h

end HighamBenchCandidate
