import Mathlib

namespace HighamBenchCandidate

/-- The paper's standard relative-error model for floating-point addition and
multiplication, with unit roundoff `u` and no overflow or underflow. -/
def RelativeRounding (u : ℝ) (roundAdd roundMul : ℝ → ℝ → ℝ) : Prop :=
  (∀ a b : ℝ, ∃ δ : ℝ, |δ| ≤ u ∧
    roundAdd a b = (a + b) * (1 + δ)) ∧
  (∀ a b : ℝ, ∃ δ : ℝ, |δ| ≤ u ∧
    roundMul a b = (a * b) * (1 + δ))

/-- A left-to-right block sum. The first value initializes the accumulator;
adding it to zero is exact in the source's model. -/
def roundBlock (roundAdd : ℝ → ℝ → ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: as => as.foldl roundAdd a

/-- The equal-block hierarchy: at each of `levels` levels, combine `blockSize`
consecutive child totals in their natural order. At level zero there is one
already rounded product. -/
def superblock (roundAdd : ℝ → ℝ → ℝ) (blockSize : ℕ) :
    (levels : ℕ) → List ℝ → ℝ
  | 0, values => values.headD 0
  | levels + 1, values =>
      roundBlock roundAdd
        ((List.range blockSize).map fun j =>
          superblock roundAdd blockSize levels
            ((values.drop (j * blockSize ^ levels)).take (blockSize ^ levels)))

/-- Round every input product before the `levels`-level summation. -/
def superblockDot (roundAdd roundMul : ℝ → ℝ → ℝ)
    (levels blockSize : ℕ) (x y : Fin (blockSize ^ levels) → ℝ) : ℝ :=
  superblock roundAdd blockSize levels
    (List.ofFn fun i : Fin (blockSize ^ levels) => roundMul (x i) (y i))

/-- Higham's gamma factor for an error counter `k`. -/
noncomputable def gamma (u : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) * u / (1 - (k : ℝ) * u)

private lemma round_add_step (u C a b s t A B : ℝ)
    (hu : 0 ≤ u) (hC : 1 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : |s| ≤ A) (ht : |t| ≤ B)
    (ha : |a - s| ≤ (C - 1) * A)
    (hb : |b - t| ≤ (C - 1) * B)
    (roundAdd : ℝ → ℝ → ℝ)
    (hround : ∀ a b : ℝ, ∃ δ : ℝ, |δ| ≤ u ∧
      roundAdd a b = (a + b) * (1 + δ)) :
    |roundAdd a b - (s + t)| ≤ (C * (1 + u) - 1) * (A + B) := by
  obtain ⟨δ, hδ, hr⟩ := hround a b
  have he : |(a + b) - (s + t)| ≤ (C - 1) * (A + B) := by
    calc
      |(a + b) - (s + t)| = |(a - s) + (b - t)| := by congr 1 <;> ring
      _ ≤ |a - s| + |b - t| := abs_add_le _ _
      _ ≤ (C - 1) * (A + B) := by nlinarith [ha, hb]
  have hst : |s + t| ≤ A + B := by
    linarith [abs_add_le s t]
  have hab : |a + b| ≤ C * (A + B) := by
    have h := abs_add_le ((a + b) - (s + t)) (s + t)
    have : |a + b| ≤ |(a + b) - (s + t)| + |s + t| := by
      convert h using 1 <;> ring
    nlinarith [he, hst]
  rw [hr]
  calc
    |(a + b) * (1 + δ) - (s + t)| = |((a + b) - (s + t)) + δ * (a + b)| := by
      congr 1 <;> ring
    _ ≤ |(a + b) - (s + t)| + |δ * (a + b)| := abs_add_le _ _
    _ = |(a + b) - (s + t)| + |δ| * |a + b| := by rw [abs_mul]
    _ ≤ (C - 1) * (A + B) + u * (C * (A + B)) := by
      have hmul := mul_le_mul hδ hab (abs_nonneg _) hu
      nlinarith [he, hmul]
    _ = (C * (1 + u) - 1) * (A + B) := by ring

private structure Approx where
  value : ℝ
  exact : ℝ
  scale : ℝ

private lemma fold_approx_bound (u Cbase : ℝ) (roundAdd : ℝ → ℝ → ℝ)
    (hu : 0 ≤ u) (hbase : 1 ≤ Cbase)
    (hround : ∀ a b : ℝ, ∃ δ : ℝ, |δ| ≤ u ∧
      roundAdd a b = (a + b) * (1 + δ))
    (l : List Approx)
    (hl : ∀ z ∈ l, 0 ≤ z.scale ∧ |z.exact| ≤ z.scale ∧
      |z.value - z.exact| ≤ (Cbase - 1) * z.scale)
    (a s A C : ℝ) (hC : Cbase ≤ C) (hA : 0 ≤ A)
    (hs : |s| ≤ A) (ha : |a - s| ≤ (C - 1) * A) :
    |(l.map Approx.value).foldl roundAdd a - (s + (l.map Approx.exact).sum)| ≤
      (C * (1 + u) ^ l.length - 1) * (A + (l.map Approx.scale).sum) := by
  induction l generalizing a s A C with
  | nil => simpa using ha
  | cons z zs ih =>
      have hz := hl z (by simp)
      have htail : ∀ z ∈ zs, 0 ≤ z.scale ∧ |z.exact| ≤ z.scale ∧
          |z.value - z.exact| ≤ (Cbase - 1) * z.scale := by
        intro w hw
        exact hl w (by simp [hw])
      have hC1 : 1 ≤ C := le_trans hbase hC
      have hzerr : |z.value - z.exact| ≤ (C - 1) * z.scale := by
        nlinarith [hz.1, hz.2.2]
      have hstep := round_add_step u C a z.value s z.exact A z.scale
        hu hC1 hA hz.1 hs hz.2.1 ha hzerr roundAdd hround
      have hCnext : Cbase ≤ C * (1 + u) := by nlinarith
      have hAnext : 0 ≤ A + z.scale := by linarith
      have hsnext : |s + z.exact| ≤ A + z.scale := by
        linarith [abs_add_le s z.exact, hz.2.1]
      have hrec := ih htail (roundAdd a z.value) (s + z.exact)
        (A + z.scale) (C * (1 + u)) hCnext hAnext hsnext hstep
      simpa only [List.map_cons, List.foldl_cons, List.sum_cons, List.length_cons,
        pow_succ] using (show
        |(zs.map Approx.value).foldl roundAdd (roundAdd a z.value) -
            (s + (z.exact + (zs.map Approx.exact).sum))| ≤
          (C * (1 + u) ^ (zs.length + 1) - 1) *
            (A + (z.scale + (zs.map Approx.scale).sum)) from by
              convert hrec using 1 <;> ring)

private lemma roundBlock_approx_bound (u Cbase : ℝ) (roundAdd : ℝ → ℝ → ℝ)
    (hu : 0 ≤ u) (hbase : 1 ≤ Cbase)
    (hround : ∀ a b : ℝ, ∃ δ : ℝ, |δ| ≤ u ∧
      roundAdd a b = (a + b) * (1 + δ))
    (z : Approx) (zs : List Approx)
    (hl : ∀ w ∈ z :: zs, 0 ≤ w.scale ∧ |w.exact| ≤ w.scale ∧
      |w.value - w.exact| ≤ (Cbase - 1) * w.scale) :
    |roundBlock roundAdd ((z :: zs).map Approx.value) -
        ((z :: zs).map Approx.exact).sum| ≤
      (Cbase * (1 + u) ^ zs.length - 1) *
        ((z :: zs).map Approx.scale).sum := by
  have hz := hl z (by simp)
  have htail : ∀ w ∈ zs, 0 ≤ w.scale ∧ |w.exact| ≤ w.scale ∧
      |w.value - w.exact| ≤ (Cbase - 1) * w.scale := by
    intro w hw
    exact hl w (by simp [hw])
  have h := fold_approx_bound u Cbase roundAdd hu hbase hround zs htail
    z.value z.exact z.scale Cbase le_rfl hz.1 hz.2.1 hz.2.2
  simpa [roundBlock] using h

private lemma chunked_sum {α : Type*} (l : List α) (f : α → ℝ) (n w : ℕ) :
    (((List.range n).map fun j =>
      (((l.drop (j * w)).take w).map f).sum).sum) =
      ((l.take (n * w)).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      rw [ih]
      rw [Nat.succ_mul, List.take_add, List.map_append, List.sum_append]

private lemma chunk_length {α : Type*} (l : List α) (n w j : ℕ)
    (hl : l.length = n * w) (hj : j < n) :
    ((l.drop (j * w)).take w).length = w := by
  have hbound : j * w + w ≤ l.length := by
    rw [hl]
    calc
      j * w + w = (j + 1) * w := by ring
      _ ≤ n * w := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hj)
  simp only [List.length_take, List.length_drop]
  omega

private lemma approx_sum_bound (l : List Approx)
    (hl : ∀ z ∈ l, 0 ≤ z.scale ∧ |z.exact| ≤ z.scale) :
    0 ≤ (l.map Approx.scale).sum ∧
      |(l.map Approx.exact).sum| ≤ (l.map Approx.scale).sum := by
  induction l with
  | nil => simp
  | cons z zs ih =>
      have hz := hl z (by simp)
      have htail : ∀ w ∈ zs, 0 ≤ w.scale ∧ |w.exact| ≤ w.scale := by
        intro w hw
        exact hl w (by simp [hw])
      obtain ⟨hscale, hexact⟩ := ih htail
      simp only [List.map_cons, List.sum_cons]
      constructor
      · linarith
      · linarith [abs_add_le z.exact ((zs.map Approx.exact).sum)]

private lemma superblock_approx_bound (u Cbase : ℝ)
    (roundAdd : ℝ → ℝ → ℝ) (blockSize : ℕ)
    (hu : 0 ≤ u) (hbase : 1 ≤ Cbase) (hblock : 0 < blockSize)
    (hround : ∀ a b : ℝ, ∃ δ : ℝ, |δ| ≤ u ∧
      roundAdd a b = (a + b) * (1 + δ))
    (levels : ℕ) (values : List Approx)
    (hlen : values.length = blockSize ^ levels)
    (hl : ∀ z ∈ values, 0 ≤ z.scale ∧ |z.exact| ≤ z.scale ∧
      |z.value - z.exact| ≤ (Cbase - 1) * z.scale) :
    |superblock roundAdd blockSize levels (values.map Approx.value) -
        (values.map Approx.exact).sum| ≤
      (Cbase * (1 + u) ^ (levels * (blockSize - 1)) - 1) *
        (values.map Approx.scale).sum := by
  induction levels generalizing values with
  | zero =>
      cases values with
      | nil => simp at hlen
      | cons z zs =>
          have hzs : zs = [] := by simpa using hlen
          subst zs
          simpa [superblock] using (hl z (by simp)).2.2
  | succ levels ih =>
      let width := blockSize ^ levels
      let part (j : ℕ) : List Approx :=
        (values.drop (j * width)).take width
      let children : List Approx :=
        (List.range blockSize).map fun j =>
          ⟨superblock roundAdd blockSize levels ((part j).map Approx.value),
            ((part j).map Approx.exact).sum,
            ((part j).map Approx.scale).sum⟩
      have hlen' : values.length = blockSize * width := by
        simpa [width, pow_succ, mul_comm] using hlen
      have hchildren : children.length = blockSize := by simp [children]
      have hchild : ∀ z ∈ children,
          0 ≤ z.scale ∧ |z.exact| ≤ z.scale ∧
          |z.value - z.exact| ≤
            (Cbase * (1 + u) ^ (levels * (blockSize - 1)) - 1) * z.scale := by
        intro z hz
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
        have hj' : j < blockSize := List.mem_range.mp hj
        have hpartlen : (part j).length = width :=
          chunk_length values blockSize width j hlen' hj'
        have hpart : ∀ q ∈ part j, 0 ≤ q.scale ∧ |q.exact| ≤ q.scale ∧
            |q.value - q.exact| ≤ (Cbase - 1) * q.scale := by
          intro q hq
          exact hl q (List.mem_of_mem_drop (List.mem_of_mem_take hq))
        have hsum := approx_sum_bound (part j) (by
          intro q hq
          exact ⟨(hpart q hq).1, (hpart q hq).2.1⟩)
        have herr := ih (part j) (by simpa [width] using hpartlen) hpart
        exact ⟨hsum.1, hsum.2, herr⟩
      have hexact : (children.map Approx.exact).sum =
          (values.map Approx.exact).sum := by
        simp only [children, List.map_map, Function.comp_def]
        rw [chunked_sum values Approx.exact blockSize width]
        simp [List.take_of_length_le, hlen']
      have hscale : (children.map Approx.scale).sum =
          (values.map Approx.scale).sum := by
        simp only [children, List.map_map, Function.comp_def]
        rw [chunked_sum values Approx.scale blockSize width]
        simp [List.take_of_length_le, hlen']
      have hbase' : 1 ≤ Cbase * (1 + u) ^ (levels * (blockSize - 1)) := by
        have hp : 1 ≤ (1 + u) ^ (levels * (blockSize - 1)) := by
          exact one_le_pow₀ (by linarith)
        nlinarith [mul_nonneg (sub_nonneg.mpr hbase) (sub_nonneg.mpr hp)]
      cases hcs : children with
      | nil => simp [hcs] at hchildren; omega
      | cons z zs =>
          have hzslen : zs.length = blockSize - 1 := by
            rw [hcs] at hchildren
            simp only [List.length_cons] at hchildren
            omega
          have hblockbound := roundBlock_approx_bound u
            (Cbase * (1 + u) ^ (levels * (blockSize - 1)))
            roundAdd hu hbase' hround z zs (by
              intro q hq
              exact hchild q (by simpa [hcs] using hq))
          have hpow :
              Cbase * (1 + u) ^ (levels * (blockSize - 1)) *
                  (1 + u) ^ zs.length =
                Cbase * (1 + u) ^ ((levels + 1) * (blockSize - 1)) := by
            rw [hzslen, mul_assoc, ← pow_add]
            congr 1
            ring
          have hvalues : (children.map Approx.value) =
              (List.range blockSize).map (fun j =>
                superblock roundAdd blockSize levels
                  (((values.map Approx.value).drop (j * width)).take width)) := by
            simp [children, part, List.map_map, List.map_take, List.map_drop]
          change |roundBlock roundAdd
            ((List.range blockSize).map (fun j =>
              superblock roundAdd blockSize levels
                (((values.map Approx.value).drop (j * width)).take width))) -
                (values.map Approx.exact).sum| ≤
              (Cbase * (1 + u) ^ ((levels + 1) * (blockSize - 1)) - 1) *
                (values.map Approx.scale).sum
          rw [← hvalues, ← hexact, ← hscale, hcs]
          simpa [hpow] using hblockbound

private lemma pow_one_add_mul_one_sub_le_one (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : (k : ℝ) * u < 1) :
    (1 + u) ^ k * (1 - (k : ℝ) * u) ≤ 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hk' : (k : ℝ) * u < 1 := by
        push_cast at hk
        nlinarith
      have hcoef : (1 + u) * (1 - ((k + 1 : ℕ) : ℝ) * u) ≤
          1 - (k : ℝ) * u := by
        push_cast
        nlinarith [mul_nonneg (Nat.cast_nonneg k) (sq_nonneg u)]
      calc
        (1 + u) ^ (k + 1) * (1 - ((k + 1 : ℕ) : ℝ) * u) =
            (1 + u) ^ k * ((1 + u) * (1 - ((k + 1 : ℕ) : ℝ) * u)) := by
              rw [pow_succ]; ring
        _ ≤ (1 + u) ^ k * (1 - (k : ℝ) * u) :=
          mul_le_mul_of_nonneg_left hcoef (pow_nonneg (by linarith) _)
        _ ≤ 1 := ih hk'

private lemma pow_sub_one_le_gamma (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : (k : ℝ) * u < 1) :
    (1 + u) ^ k - 1 ≤ gamma u k := by
  unfold gamma
  apply (le_div_iff₀ (by linarith : 0 < 1 - (k : ℝ) * u)).2
  nlinarith [pow_one_add_mul_one_sub_le_one u hu k hk]

/-- Castaldo–Whaley–Chronopoulos, Proposition 3.2 and (3.2), for every
integral equal-block `t`-level superblock dot product. Figure 3.1(a)'s
`j`-loop skips level zero; this follows the hierarchy in the surrounding
prose, Figure 3.2, and Proposition 3.1 instead. -/
theorem target
    (levels blockSize : ℕ) (hlevels : 0 < levels) (hblock : 0 < blockSize)
    (u : ℝ) (hu : 0 ≤ u)
    (roundAdd roundMul : ℝ → ℝ → ℝ)
    (hround : RelativeRounding u roundAdd roundMul)
    (hgamma : ((levels * (blockSize - 1) + 1 : ℕ) : ℝ) * u < 1)
    (x y : Fin (blockSize ^ levels) → ℝ) :
    |superblockDot roundAdd roundMul levels blockSize x y -
        ∑ i : Fin (blockSize ^ levels), x i * y i| ≤
      gamma u (levels * (blockSize - 1) + 1) *
        ∑ i : Fin (blockSize ^ levels), |x i * y i| := by
  let values : List Approx :=
    List.ofFn fun i : Fin (blockSize ^ levels) =>
      ⟨roundMul (x i) (y i), x i * y i, |x i * y i|⟩
  have hlen : values.length = blockSize ^ levels := by simp [values]
  have hgood : ∀ z ∈ values, 0 ≤ z.scale ∧ |z.exact| ≤ z.scale ∧
      |z.value - z.exact| ≤ ((1 + u) - 1) * z.scale := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    dsimp only
    refine ⟨abs_nonneg _, le_rfl, ?_⟩
    obtain ⟨δ, hδ, hr⟩ := hround.2 (x i) (y i)
    rw [hr]
    have heq : (x i * y i) * (1 + δ) - x i * y i = (x i * y i) * δ := by ring
    rw [heq, abs_mul]
    have hmul := mul_le_mul_of_nonneg_left hδ (abs_nonneg (x i * y i))
    nlinarith
  have hbound := superblock_approx_bound u (1 + u) roundAdd blockSize
    hu (by linarith) hblock hround.1 levels values hlen hgood
  let k := levels * (blockSize - 1) + 1
  have hpow : (1 + u) * (1 + u) ^ (levels * (blockSize - 1)) =
      (1 + u) ^ k := by
    dsimp [k]
    rw [pow_succ]
    ring
  have hscale : 0 ≤ ∑ i : Fin (blockSize ^ levels), |x i * y i| := by
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcomparison := pow_sub_one_le_gamma u hu k (by simpa [k] using hgamma)
  have hscaled := mul_le_mul_of_nonneg_right hcomparison hscale
  calc
    |superblockDot roundAdd roundMul levels blockSize x y -
        ∑ i : Fin (blockSize ^ levels), x i * y i| =
      |superblock roundAdd blockSize levels (values.map Approx.value) -
        (values.map Approx.exact).sum| := by
          simp [superblockDot, values, List.map_ofFn, List.sum_ofFn,
            Function.comp_def]
    _ ≤ ((1 + u) ^ k - 1) *
        ∑ i : Fin (blockSize ^ levels), |x i * y i| := by
          simpa [values, List.map_ofFn, List.sum_ofFn, hpow] using hbound
    _ ≤ gamma u k *
        ∑ i : Fin (blockSize ^ levels), |x i * y i| := hscaled

end HighamBenchCandidate
