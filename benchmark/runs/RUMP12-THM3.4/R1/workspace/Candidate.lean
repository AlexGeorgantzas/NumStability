import Mathlib.Tactic
import NumStability.Analysis.HighamChapter2GradualUnderflowExact

namespace HighamBenchCandidate

open NumStability
open scoped BigOperators

/-- The finite binary format, extended above its largest exponent solely to
describe rounding before the paper's no-overflow condition is imposed. This
retains subnormal values at the lower end. -/
def roundingRange (fmt : FloatingPointFormat) (x : ℝ) : Prop :=
  fmt.finiteSystem x ∨
    ∃ (negative : Bool) (m : ℕ) (e : ℤ),
      fmt.normalizedMantissa m ∧ fmt.emax < e ∧
        x = fmt.normalizedValue negative m e

/-- Algorithm 3.1, starting with the first input. Each addition is rounded to
nearest with arbitrary tie choice; all computed values are finite, expressing
the paper's no-overflow convention. The extended rounding range permits an
exact sum just above the largest finite value to round back to that value. -/
def recursiveTrace (fmt : FloatingPointFormat) (n : ℕ) (hn : 0 < n)
    (p s : Fin n → ℝ) : Prop :=
  s ⟨0, hn⟩ = p ⟨0, hn⟩ ∧
    (∀ i : Fin (n - 1),
      FloatingPointFormat.nearestRoundingIn (roundingRange fmt)
        (s ⟨i.val, by omega⟩ + p ⟨i.val + 1, by omega⟩)
        (s ⟨i.val + 1, by omega⟩)) ∧
    (∀ i : Fin n, fmt.finiteSystem (s i))

private lemma maxFinite_eq_next_mul_one_sub_u
    (fmt : FloatingPointFormat) (hβ : fmt.beta = 2) :
    fmt.maxFiniteMagnitude =
      fmt.betaR ^ fmt.emax * (1 - fmt.unitRoundoff) := by
  have hpow : fmt.betaR ^ (1 - (fmt.t : ℤ)) =
      fmt.betaR * fmt.betaR ^ (-(fmt.t : ℤ)) := by
    rw [show (1 : ℤ) - fmt.t = 1 + (-fmt.t) by omega,
      zpow_add₀ (by exact ne_of_gt fmt.betaR_pos), zpow_one]
  rw [FloatingPointFormat.maxFiniteMagnitude,
    FloatingPointFormat.unitRoundoff,
    FloatingPointFormat.machineEpsilon, hpow]
  simp [FloatingPointFormat.betaR, hβ]

private lemma unitRoundoff_le_half
    (fmt : FloatingPointFormat) (hβ : fmt.beta = 2) :
    fmt.unitRoundoff ≤ (1 / 2 : ℝ) := by
  have ht : (1 : ℤ) - fmt.t ≤ 0 := by
    have htpos : (1 : ℤ) ≤ fmt.t := by exact_mod_cast fmt.t_pos
    omega
  have heps : (2 : ℝ) ^ (1 - (fmt.t : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) ht
  unfold FloatingPointFormat.unitRoundoff
    FloatingPointFormat.machineEpsilon FloatingPointFormat.betaR
  simpa [hβ] using
    (mul_le_mul_of_nonneg_left heps (by norm_num : (0 : ℝ) ≤ 1 / 2))

private lemma nearest_upper_pos_rel_error
    (fmt : FloatingPointFormat) (hβ : fmt.beta = 2)
    {x y : ℝ} (hx : fmt.maxFiniteMagnitude < x)
    (hy : fmt.finiteSystem y)
    (hround : FloatingPointFormat.nearestRoundingIn
      (roundingRange fmt) x y) :
    |y - x| ≤ fmt.unitRoundoff * |x| := by
  let M := fmt.maxFiniteMagnitude
  let N := fmt.betaR ^ fmt.emax
  let u := fmt.unitRoundoff
  have hMfin : roundingRange fmt M :=
    Or.inl (Or.inr (Or.inl fmt.maxFiniteMagnitude_mem_normalizedSystem))
  have hNfin : roundingRange fmt N := by
    right
    refine ⟨false, fmt.minNormalMantissa, fmt.emax + 1,
      fmt.minNormalMantissa_normalized, by omega, ?_⟩
    exact (fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow fmt.emax).symm
  have hMN : M < N := fmt.maxFiniteMagnitude_lt_beta_pow_emax
  have hNpos : 0 < N := fmt.betaR_zpow_pos fmt.emax
  have hu0 : 0 ≤ u := fmt.unitRoundoff_nonneg
  have huHalf : u ≤ (1 / 2 : ℝ) := unitRoundoff_le_half fmt hβ
  have hM_eq : M = N * (1 - u) := maxFinite_eq_next_mul_one_sub_u fmt hβ
  have hyM : y ≤ M := (abs_le.mp (fmt.finiteSystem_abs_le_maxFiniteMagnitude hy)).2
  have hnearM : |x - y| ≤ |x - M| :=
    FloatingPointFormat.nearestRoundingIn_minimal hround hMfin
  have hyEq : y = M := by
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y),
      abs_of_nonneg (by linarith : 0 ≤ x - M)] at hnearM
    linarith
  have hnearN : |x - M| ≤ |x - N| := by
    simpa [hyEq] using
      (FloatingPointFormat.nearestRoundingIn_minimal hround hNfin)
  have hxN : x ≤ N := by
    by_contra h
    have hNx : N < x := lt_of_not_ge h
    rw [abs_of_nonneg (by linarith : 0 ≤ x - M),
      abs_of_nonneg (by linarith : 0 ≤ x - N)] at hnearN
    linarith
  have hhalfGap : x - M ≤ (N - M) / 2 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ x - M),
      abs_of_nonpos (by linarith : x - N ≤ 0)] at hnearN
    linarith
  have hgap : N - M = u * N := by rw [hM_eq]; ring
  have hMhalf : N / 2 ≤ M := by
    rw [hM_eq]
    nlinarith [mul_nonneg (show 0 ≤ N by linarith)
      (show 0 ≤ 1 / 2 - u by linarith)]
  have hlocal : x - M ≤ u * x := by
    have h1 : (N - M) / 2 ≤ u * M := by
      rw [hgap]
      nlinarith [mul_nonneg hu0 (show 0 ≤ M - N / 2 by linarith)]
    have h2 : u * M ≤ u * x := mul_le_mul_of_nonneg_left (le_of_lt hx) hu0
    linarith
  rw [hyEq, abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ x - M),
    abs_of_pos (by linarith : 0 < x)]
  exact hlocal

private lemma roundingRange_neg (fmt : FloatingPointFormat) {x : ℝ}
    (hx : roundingRange fmt x) : roundingRange fmt (-x) := by
  rcases hx with hfinite | ⟨negative, m, e, hm, he, hrepr⟩
  · exact Or.inl (fmt.finiteSystem_neg hfinite)
  · right
    refine ⟨!negative, m, e, hm, he, ?_⟩
    rw [hrepr, fmt.normalizedValue_not_eq_neg]

private lemma nearest_neg (fmt : FloatingPointFormat) {x y : ℝ}
    (hround : FloatingPointFormat.nearestRoundingIn
      (roundingRange fmt) x y) :
    FloatingPointFormat.nearestRoundingIn
      (roundingRange fmt) (-x) (-y) := by
  constructor
  · exact roundingRange_neg fmt hround.1
  · intro z hz
    have hnegz : roundingRange fmt (-z) := roundingRange_neg fmt hz
    have h := hround.2 (-z) hnegz
    calc
      |(-x) - (-y)| = |x - y| := by
        rw [show (-x) - (-y) = -(x - y) by ring, abs_neg]
      _ ≤ |x - (-z)| := h
      _ = |(-x) - z| := by rw [show (-x) - z = -(x - (-z)) by ring, abs_neg]

private lemma nearest_add_rel_error
    (fmt : FloatingPointFormat) (hβ : fmt.beta = 2)
    {a b y : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hy : fmt.finiteSystem y)
    (hround : FloatingPointFormat.nearestRoundingIn
      (roundingRange fmt) (a + b) y) :
    |y - (a + b)| ≤ fmt.unitRoundoff * |a + b| := by
  by_cases hunder : fmt.finiteUnderflowRange (a + b)
  · have hexact : fmt.finiteSystem (a + b) :=
      fmt.finiteSystem_add_finiteSystem_of_finiteUnderflowRange ha hb hunder
    have hzero : |(a + b) - y| ≤ 0 := by
      simpa using (FloatingPointFormat.nearestRoundingIn_minimal
        hround (Or.inl hexact))
    have hyEq : y = a + b := by
      have : (a + b) - y = 0 := abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
      linarith
    simp only [hyEq, sub_self, abs_zero]
    exact mul_nonneg fmt.unitRoundoff_nonneg (abs_nonneg _)
  · by_cases hover : fmt.finiteOverflowRange (a + b)
    · change fmt.maxFiniteMagnitude < |a + b| at hover
      rcases le_total 0 (a + b) with hpos | hneg
      · have hx : fmt.maxFiniteMagnitude < a + b := by
          simpa [abs_of_nonneg hpos] using hover
        exact nearest_upper_pos_rel_error fmt hβ hx hy hround
      · have hx : fmt.maxFiniteMagnitude < -(a + b) := by
          simpa [abs_of_nonpos hneg] using hover
        have h := nearest_upper_pos_rel_error fmt hβ hx
          (fmt.finiteSystem_neg hy) (nearest_neg fmt hround)
        simpa only [neg_sub_neg, abs_sub_comm, abs_neg] using h
    · have hnormal : fmt.finiteNormalRange (a + b) := by
        constructor
        · exact le_of_not_gt hunder
        · exact le_of_not_gt hover
      have hfiniteRound : fmt.nearestRoundingToFinite (a + b) y := by
        refine ⟨hy, ?_⟩
        intro z hz
        exact hround.2 z (Or.inl hz)
      obtain ⟨δ, hδ, hrepr⟩ :=
        fmt.nearestRoundingToFinite_signedRelErrorWitness_of_finiteNormalRange
          hfiniteRound hnormal
      have herror : y - (a + b) = (a + b) * δ := by
        unfold signedRelErrorWitness at hrepr
        rw [hrepr]
        ring
      rw [herror, abs_mul]
      exact (mul_le_mul_of_nonneg_left hδ (abs_nonneg _)).trans_eq
        (mul_comm _ _)

private lemma abstract_recursive_bound
    (u : ℝ) (hu : 0 ≤ u) (n : ℕ) (hn : 0 < n)
    (p s : ℕ → ℝ)
    (hfirst : s 0 = p 0)
    (hsmall : ∀ i, i + 1 < n →
      |s (i + 1) - (s i + p (i + 1))| ≤ |p (i + 1)|)
    (hrelative : ∀ i, i + 1 < n →
      |s (i + 1) - (s i + p (i + 1))| ≤ u * |s i + p (i + 1)|) :
    |s (n - 1) - ∑ i ∈ Finset.range n, p i| ≤
      ((n - 1 : ℕ) : ℝ) * u *
        ∑ i ∈ Finset.range n, |p i| := by
  have hmain : ∀ k : ℕ, 0 < k → k ≤ n →
      |s (k - 1) - ∑ i ∈ Finset.range k, p i| ≤
        ((k - 1 : ℕ) : ℝ) * u *
          ∑ i ∈ Finset.range k, |p i| := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro _hk hkn
      by_cases hk0 : k = 0
      · subst k
        simp [hfirst]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hklt : k < n := by omega
        have hprev := ih hkpos (Nat.le_of_lt hklt)
        let A : ℝ := ∑ i ∈ Finset.range k, p i
        let E : ℝ := ∑ i ∈ Finset.range k, |p i|
        let a : ℝ := s (k - 1)
        let b : ℝ := p k
        let c : ℝ := s k
        let P : ℝ := |a - A|
        let L : ℝ := |c - (a + b)|
        have hE : 0 ≤ E := Finset.sum_nonneg (by
          intro i hi; exact abs_nonneg _)
        have hA : |A| ≤ E := by
          simpa [A, E] using
            (Finset.abs_sum_le_sum_abs (s := Finset.range k) p)
        have hsmall' : L ≤ |b| := by
          simpa [L, a, b, c, Nat.sub_add_cancel hkpos] using
            hsmall (k - 1) (by omega)
        have hrelative' : L ≤ u * |a + b| := by
          simpa [L, a, b, c, Nat.sub_add_cancel hkpos] using
            hrelative (k - 1) (by omega)
        have hprev' : P ≤ ((k - 1 : ℕ) : ℝ) * u * E := by
          simpa [P, a, A, E] using hprev
        have htri : |c - (A + b)| ≤ L + P := by
          have hdecomp : c - (A + b) = (c - (a + b)) + (a - A) := by ring
          rw [hdecomp]
          exact abs_add_le _ _
        have hab : |a + b| ≤ P + E + |b| := by
          have hdecomp : a + b = (a - A) + (A + b) := by ring
          rw [hdecomp]
          calc
            |(a - A) + (A + b)| ≤ |a - A| + |A + b| := abs_add_le _ _
            _ ≤ P + (|A| + |b|) := by
              have := abs_add_le A b
              dsimp [P]
              linarith
            _ ≤ P + E + |b| := by linarith
        have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ k)]
          norm_num
        have hR : 0 ≤ ((k - 1 : ℕ) : ℝ) := by positivity
        have hkR : (0 : ℝ) ≤ k := by positivity
        have htarget : |c - (A + b)| ≤ (k : ℝ) * u * (E + |b|) := by
          by_cases hbsmall : |b| ≤ u * E
          · have hlocal : L ≤ u * E := hsmall'.trans hbsmall
            have hmul : 0 ≤ (k : ℝ) * u * |b| :=
              mul_nonneg (mul_nonneg hkR hu) (abs_nonneg _)
            calc
              |c - (A + b)| ≤ L + P := htri
              _ ≤ u * E + ((k - 1 : ℕ) : ℝ) * u * E :=
                add_le_add hlocal hprev'
              _ = (k : ℝ) * u * E := by rw [hcast]; ring
              _ ≤ (k : ℝ) * u * (E + |b|) := by nlinarith
          · have hbdom : u * E ≤ |b| := le_of_lt (lt_of_not_ge hbsmall)
            have hscaled : (1 + u) * P ≤
                (1 + u) * (((k - 1 : ℕ) : ℝ) * u * E) :=
              mul_le_mul_of_nonneg_left hprev' (by linarith)
            have hmult : ((k - 1 : ℕ) : ℝ) * u * (u * E) ≤
                ((k - 1 : ℕ) : ℝ) * u * |b| :=
              mul_le_mul_of_nonneg_left hbdom (mul_nonneg hR hu)
            have hlocal : L ≤ u * (P + E + |b|) :=
              hrelative'.trans (mul_le_mul_of_nonneg_left hab hu)
            have hcombine : L + P ≤ (1 + u) * P + u * E + u * |b| := by
              nlinarith [hlocal]
            calc
              |c - (A + b)| ≤ L + P := htri
              _ ≤ (1 + u) * P + u * E + u * |b| := hcombine
              _ ≤ (1 + u) * (((k - 1 : ℕ) : ℝ) * u * E) +
                    u * E + u * |b| := by linarith
              _ = (k : ℝ) * u * E +
                    ((k - 1 : ℕ) : ℝ) * u * (u * E) + u * |b| := by
                      rw [hcast]; ring
              _ ≤ (k : ℝ) * u * E +
                    ((k - 1 : ℕ) : ℝ) * u * |b| + u * |b| := by
                      linarith
              _ = (k : ℝ) * u * (E + |b|) := by rw [hcast]; ring
        simpa [A, E, b, c, Finset.sum_range_succ,
          Nat.succ_sub_one] using htarget
  exact hmain n hn le_rfl

/-- Rump, Theorem 3.4, equation (3.5). The library's recursive-sum definition
uses an abstract relative-error model; its concrete finite trace fixes ties to
even. This trace states the paper's nearest-rounding and no-overflow domain. -/
theorem target :
    ∀ (fmt : FloatingPointFormat), fmt.beta = 2 →
      ∀ (n : ℕ) (hn : 0 < n) (p s : Fin n → ℝ),
        (∀ i : Fin n, fmt.finiteSystem (p i)) →
        recursiveTrace fmt n hn p s →
        |s ⟨n - 1, by omega⟩ - ∑ i : Fin n, p i| ≤
          ((n - 1 : ℕ) : ℝ) * fmt.unitRoundoff *
            ∑ i : Fin n, |p i| := by
  intro fmt hβ n hn p s hp htrace
  let pn : ℕ → ℝ := fun i => if hi : i < n then p ⟨i, hi⟩ else 0
  let sn : ℕ → ℝ := fun i => if hi : i < n then s ⟨i, hi⟩ else 0
  have hpn (i : ℕ) (hi : i < n) : pn i = p ⟨i, hi⟩ := by
    simp [pn, hi]
  have hsn (i : ℕ) (hi : i < n) : sn i = s ⟨i, hi⟩ := by
    simp [sn, hi]
  have hfirst : sn 0 = pn 0 := by
    simpa [hsn 0 hn, hpn 0 hn] using htrace.1
  have hsmall : ∀ i, i + 1 < n →
      |sn (i + 1) - (sn i + pn (i + 1))| ≤ |pn (i + 1)| := by
    intro i hi
    have hij : i < n - 1 := by omega
    have hii : i < n := by omega
    have hnear := htrace.2.1 ⟨i, hij⟩
    have hcandidate : roundingRange fmt (s ⟨i, hii⟩) :=
      Or.inl (htrace.2.2 ⟨i, hii⟩)
    have h := FloatingPointFormat.nearestRoundingIn_minimal hnear hcandidate
    have h' : |s ⟨i + 1, hi⟩ - (s ⟨i, hii⟩ + p ⟨i + 1, hi⟩)| ≤
        |p ⟨i + 1, hi⟩| := by
      calc
        |s ⟨i + 1, hi⟩ - (s ⟨i, hii⟩ + p ⟨i + 1, hi⟩)| =
            |(s ⟨i, hii⟩ + p ⟨i + 1, hi⟩) - s ⟨i + 1, hi⟩| :=
              abs_sub_comm _ _
        _ ≤ |(s ⟨i, hii⟩ + p ⟨i + 1, hi⟩) - s ⟨i, hii⟩| := by
          simpa only [Fin.val_mk] using h
        _ = |p ⟨i + 1, hi⟩| := by congr 1; ring
    simpa [hsn i hii, hsn (i + 1) hi, hpn (i + 1) hi] using h'
  have hrelative : ∀ i, i + 1 < n →
      |sn (i + 1) - (sn i + pn (i + 1))| ≤
        fmt.unitRoundoff * |sn i + pn (i + 1)| := by
    intro i hi
    have hij : i < n - 1 := by omega
    have hii : i < n := by omega
    have hnear := htrace.2.1 ⟨i, hij⟩
    have h := nearest_add_rel_error fmt hβ
      (htrace.2.2 ⟨i, hii⟩) (hp ⟨i + 1, hi⟩)
      (htrace.2.2 ⟨i + 1, hi⟩) hnear
    simpa [hsn i hii, hsn (i + 1) hi, hpn (i + 1) hi] using h
  have hbound := abstract_recursive_bound fmt.unitRoundoff
    fmt.unitRoundoff_nonneg n hn pn sn hfirst hsmall hrelative
  have hsum : (∑ i ∈ Finset.range n, pn i) = ∑ i : Fin n, p i := by
    rw [← Fin.sum_univ_eq_sum_range pn n]
    apply Finset.sum_congr rfl
    intro i _
    exact hpn i.val i.isLt
  have hsumAbs : (∑ i ∈ Finset.range n, |pn i|) =
      ∑ i : Fin n, |p i| := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => |pn i|) n]
    apply Finset.sum_congr rfl
    intro i _
    rw [hpn i.val i.isLt]
  rw [hsn (n - 1) (by omega), hsum, hsumAbs] at hbound
  exact hbound

end HighamBenchCandidate
