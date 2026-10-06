-- Algorithms/Cholesky/Higham11RookSourceClosure.lean
--
-- Source closure for the three properties following Higham Algorithm 11.5.
-- Search termination and the global multiplier-origin bound live in
-- `HighamChapter11`; this file supplies the exact 2-by-2 condition-number
-- proof and the size-weighted rook growth recursion.

import NumStability.Algorithms.HighamChapter11

namespace NumStability

open scoped BigOperators

/-- A symmetric real `2 × 2` matrix is bounded in operator 2-norm by a
common bound on its two absolute row sums.  The proof is the sharp weighted
Cauchy estimate, rather than the weaker Frobenius `sqrt 2` comparison. -/
theorem higham11_5_symmetricTwoByTwo_opNorm2Le_of_row_bounds
    (a b d C : ℝ) (hC : 0 ≤ C)
    (ha : |a| + |b| ≤ C) (hd : |b| + |d| ≤ C) :
    opNorm2Le (higham11_4_twoByTwoPivotBlock a b d) C := by
  have hSq : ∀ x : Fin 2 → ℝ,
      vecNorm2Sq
          (rectMatMulVec (higham11_4_twoByTwoPivotBlock a b d) x) ≤
        C ^ 2 * vecNorm2Sq x := by
    intro x
    let X : ℝ := |x 0|
    let Y : ℝ := |x 1|
    let p : ℝ := |a|
    let q : ℝ := |b|
    let r : ℝ := |d|
    have hX : 0 ≤ X := abs_nonneg _
    have hY : 0 ≤ Y := abs_nonneg _
    have hp : 0 ≤ p := abs_nonneg _
    have hq : 0 ≤ q := abs_nonneg _
    have hr : 0 ≤ r := abs_nonneg _
    have hrow0 : p + q ≤ C := by simpa [p, q] using ha
    have hrow1 : q + r ≤ C := by simpa [q, r] using hd
    have hact0 : |a * x 0 + b * x 1| ≤ p * X + q * Y := by
      calc
        |a * x 0 + b * x 1| ≤ |a * x 0| + |b * x 1| := abs_add_le _ _
        _ = p * X + q * Y := by simp [p, q, X, Y, abs_mul]
    have hact1 : |b * x 0 + d * x 1| ≤ q * X + r * Y := by
      calc
        |b * x 0 + d * x 1| ≤ |b * x 0| + |d * x 1| := abs_add_le _ _
        _ = q * X + r * Y := by simp [q, r, X, Y, abs_mul]
    have hact0_nonneg : 0 ≤ p * X + q * Y :=
      add_nonneg (mul_nonneg hp hX) (mul_nonneg hq hY)
    have hact1_nonneg : 0 ≤ q * X + r * Y :=
      add_nonneg (mul_nonneg hq hX) (mul_nonneg hr hY)
    have hact0sq : (a * x 0 + b * x 1) ^ 2 ≤ (p * X + q * Y) ^ 2 := by
      nlinarith [sq_abs (a * x 0 + b * x 1),
        abs_nonneg (a * x 0 + b * x 1)]
    have hact1sq : (b * x 0 + d * x 1) ^ 2 ≤ (q * X + r * Y) ^ 2 := by
      nlinarith [sq_abs (b * x 0 + d * x 1),
        abs_nonneg (b * x 0 + d * x 1)]
    have hyoung0 :
        (p * X + q * Y) ^ 2 ≤ (p + q) * (p * X ^ 2 + q * Y ^ 2) := by
      nlinarith [mul_nonneg (mul_nonneg hp hq) (sq_nonneg (X - Y))]
    have hyoung1 :
        (q * X + r * Y) ^ 2 ≤ (q + r) * (q * X ^ 2 + r * Y ^ 2) := by
      nlinarith [mul_nonneg (mul_nonneg hq hr) (sq_nonneg (X - Y))]
    have hweighted0 : 0 ≤ p * X ^ 2 + q * Y ^ 2 :=
      add_nonneg (mul_nonneg hp (sq_nonneg X))
        (mul_nonneg hq (sq_nonneg Y))
    have hweighted1 : 0 ≤ q * X ^ 2 + r * Y ^ 2 :=
      add_nonneg (mul_nonneg hq (sq_nonneg X))
        (mul_nonneg hr (sq_nonneg Y))
    have hC0 :
        (p + q) * (p * X ^ 2 + q * Y ^ 2) ≤
          C * (p * X ^ 2 + q * Y ^ 2) :=
      mul_le_mul_of_nonneg_right hrow0 hweighted0
    have hC1 :
        (q + r) * (q * X ^ 2 + r * Y ^ 2) ≤
          C * (q * X ^ 2 + r * Y ^ 2) :=
      mul_le_mul_of_nonneg_right hrow1 hweighted1
    have hcols :
        C * (p * X ^ 2 + q * Y ^ 2) +
            C * (q * X ^ 2 + r * Y ^ 2) ≤
          C ^ 2 * (X ^ 2 + Y ^ 2) := by
      nlinarith [
        mul_nonneg hC (mul_nonneg (sub_nonneg.mpr hrow0) (sq_nonneg X)),
        mul_nonneg hC (mul_nonneg (sub_nonneg.mpr hrow1) (sq_nonneg Y))]
    simp only [vecNorm2Sq, rectMatMulVec, Fin.sum_univ_two,
      higham11_4_twoByTwoPivotBlock]
    simp only [Fin.isValue, ↓reduceIte]
    rw [← sq_abs (x 0), ← sq_abs (x 1)]
    change (a * x 0 + b * x 1) ^ 2 + (b * x 0 + d * x 1) ^ 2 ≤
      C ^ 2 * (X ^ 2 + Y ^ 2)
    linarith
  have hrect := rectOpNorm2Le_sqrt_of_vecNorm2Sq_le
    (higham11_4_twoByTwoPivotBlock a b d) (sq_nonneg C) hSq
  simpa [rectOpNorm2Le, rectMatMulVec, opNorm2Le, matMulVec,
    Real.sqrt_sq hC] using hrect

/-- The exact algebraic inverse of the symmetric rook pivot block
`[[e11,e21],[e21,e22]]`. -/
noncomputable def higham11_5_rookTwoByTwoPivotInverse
    (e11 e22 e21 : ℝ) : Fin 2 → Fin 2 → ℝ :=
  higham11_4_twoByTwoPivotBlock
    (e22 / (e11 * e22 - e21 ^ 2))
    (-(e21 / (e11 * e22 - e21 ^ 2)))
    (e11 / (e11 * e22 - e21 ^ 2))

/-- **Algorithm 11.5 property (2).**  A genuine accepted `2 × 2` rook pivot
has an actual two-sided inverse and exact operator-2 condition number at most
`(1+α)/(1-α)`.  Both operator norms are derived from the sharp symmetric-row
sum lemma; no condition-number inequality is assumed. -/
theorem higham11_5_rook_twoByTwo_condition_number_bound
    (e11 e22 e21 ω α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hω : 0 < ω)
    (he11 : |e11| ≤ α * ω) (he22 : |e22| ≤ α * ω)
    (he21 : e21 ^ 2 = ω ^ 2) :
    higham11_2_NonsingularPivotBlock 2
        (higham11_4_twoByTwoPivotBlock e11 e21 e22)
        (higham11_5_rookTwoByTwoPivotInverse e11 e22 e21) ∧
      higham11_5_rookPivotTwoByTwoCondBound α
        (kappa2 (higham11_4_twoByTwoPivotBlock e11 e21 e22)
          (higham11_5_rookTwoByTwoPivotInverse e11 e22 e21)) := by
  let K : ℝ := ((1 - α ^ 2) * ω)⁻¹
  have hαsq : α ^ 2 < 1 := by nlinarith
  have hω0 : 0 ≤ ω := le_of_lt hω
  have hden : 0 < (1 - α ^ 2) * ω := mul_pos (by linarith) hω
  have hKpos : 0 < K := inv_pos.mpr hden
  have hK : (1 - α ^ 2) * ω * K = 1 :=
    mul_inv_cancel₀ (ne_of_gt hden)
  have he21abs : |e21| = ω := by
    have hsquare : |e21| ^ 2 = ω ^ 2 := by simpa [sq_abs] using he21
    nlinarith [abs_nonneg e21]
  have hprodabs : |e11 * e22| ≤ (α * ω) ^ 2 := by
    rw [abs_mul]
    calc
      |e11| * |e22| ≤ (α * ω) * (α * ω) :=
        mul_le_mul he11 he22 (abs_nonneg e22) (mul_nonneg hα0 hω0)
      _ = (α * ω) ^ 2 := by ring
  have hprod : e11 * e22 ≤ (α * ω) ^ 2 :=
    (le_abs_self _).trans hprodabs
  have hdetneg : e11 * e22 - e21 ^ 2 < 0 := by
    rw [he21]
    nlinarith [sq_pos_of_pos hω]
  have hdetne : e11 * e22 - e21 ^ 2 ≠ 0 := ne_of_lt hdetneg
  have hdetne_comm : e22 * e11 - e21 ^ 2 ≠ 0 := by
    simpa [mul_comm] using hdetne
  constructor
  · constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
      simp [higham11_4_twoByTwoPivotBlock,
        higham11_5_rookTwoByTwoPivotInverse, Fin.sum_univ_two] <;>
      field_simp [hdetne, hdetne_comm] <;> ring
  · obtain ⟨hInv22, hInv11, hInv21⟩ :=
      higham11_4_twoByTwo_inverse_entry_bounds
        e11 e22 e21 ω (α * ω) α K
        (mul_nonneg hα0 hω0) hα0 hα1 hω he11 he22 he21
        (le_refl _) hK
    let E := higham11_4_twoByTwoPivotBlock e11 e21 e22
    let Einv := higham11_5_rookTwoByTwoPivotInverse e11 e22 e21
    let cE := (1 + α) * ω
    let cInv := (1 + α) * K
    have hcE : 0 ≤ cE := mul_nonneg (by linarith) hω0
    have hcInv : 0 ≤ cInv :=
      mul_nonneg (by linarith) (le_of_lt hKpos)
    have hEcert : opNorm2Le E cE := by
      apply higham11_5_symmetricTwoByTwo_opNorm2Le_of_row_bounds
      · exact hcE
      · dsimp [E, cE]
        rw [he21abs]
        linarith
      · dsimp [E, cE]
        rw [he21abs]
        linarith
    have hInvcert : opNorm2Le Einv cInv := by
      apply higham11_5_symmetricTwoByTwo_opNorm2Le_of_row_bounds
      · exact hcInv
      · dsimp [Einv, higham11_5_rookTwoByTwoPivotInverse, cInv]
        rw [abs_neg]
        linarith
      · dsimp [Einv, higham11_5_rookTwoByTwoPivotInverse, cInv]
        rw [abs_neg]
        linarith
    have hEop : opNorm2 E ≤ cE :=
      opNorm2_le_of_opNorm2Le E hcE hEcert
    have hInvop : opNorm2 Einv ≤ cInv :=
      opNorm2_le_of_opNorm2Le Einv hcInv hInvcert
    have hkappa : kappa2 E Einv ≤ cE * cInv := by
      unfold kappa2
      exact mul_le_mul hEop hInvop (opNorm2_nonneg Einv) hcE
    have hcprod : cE * cInv = (1 + α) / (1 - α) := by
      have h1a : 1 - α ≠ 0 := ne_of_gt (by linarith)
      dsimp [cE, cInv]
      rw [eq_div_iff h1a]
      nlinarith [hK]
    simpa [higham11_5_rookPivotTwoByTwoCondBound, E, Einv, hcprod] using hkappa

/-- A `1 × 1` rook pivot consumes one active index and a `2 × 2` pivot
consumes two. -/
def higham11_5_rookPivotWidth : PivotSize → ℕ
  | PivotSize.one => 1
  | PivotSize.two => 2

/-- Number of active indices consumed by the first `q` rook pivots. -/
def higham11_5_rookEliminatedCount (s : ℕ → PivotSize) (q : ℕ) : ℕ :=
  ∑ k ∈ Finset.range q, higham11_5_rookPivotWidth (s k)

theorem higham11_5_rookEliminatedCount_succ (s : ℕ → PivotSize) (q : ℕ) :
    higham11_5_rookEliminatedCount s (q + 1) =
      higham11_5_rookEliminatedCount s q +
        higham11_5_rookPivotWidth (s q) := by
  unfold higham11_5_rookEliminatedCount
  rw [Finset.sum_range_succ]

/-- The accepted scalar rook pivot gives exactly the partial-pivoting
one-index growth factor. -/
theorem higham11_5_rook_oneByOne_schur_growth
    (b c1 c2 e μ : ℝ) (hμ : 0 < μ)
    (hb : |b| ≤ μ) (hc1 : |c1| ≤ μ) (hc2 : |c2| ≤ μ)
    (he : higham11_1_bunchParlettAlpha * μ ≤ |e|) :
    |b - c1 * c2 / e| ≤
      (1 + higham11_1_bunchParlettAlpha⁻¹) ^
          higham11_5_rookPivotWidth PivotSize.one * μ := by
  have hα : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  simpa [higham11_5_rookPivotWidth, one_div] using
    higham11_1_oneByOne_schur_growth b c1 c2 e μ
      higham11_1_bunchParlettAlpha hα hμ hb hc1 hc2 he

/-- A genuine `2 × 2` rook pivot gives the square of the one-index growth
factor.  The equality is Higham's balancing identity
`1+2/(1-α)=(1+α⁻¹)^2`. -/
theorem higham11_5_rook_twoByTwo_schur_growth
    (bij ci1 ci2 cj1 cj2 e11 e22 e21 μ : ℝ)
    (hμ : 0 < μ)
    (hb : |bij| ≤ μ)
    (hci1 : |ci1| ≤ μ) (hci2 : |ci2| ≤ μ)
    (hcj1 : |cj1| ≤ μ) (hcj2 : |cj2| ≤ μ)
    (he11 : |e11| ≤ higham11_1_bunchParlettAlpha * μ)
    (he22 : |e22| ≤ higham11_1_bunchParlettAlpha * μ)
    (he21 : e21 ^ 2 = μ ^ 2) :
    |higham11_4_twoByTwoSchurEntry bij ci1 ci2 cj1 cj2
        (e22 / (e11 * e22 - e21 ^ 2))
        (-(e21 / (e11 * e22 - e21 ^ 2)))
        (-(e21 / (e11 * e22 - e21 ^ 2)))
        (e11 / (e11 * e22 - e21 ^ 2))| ≤
      (1 + higham11_1_bunchParlettAlpha⁻¹) ^
          higham11_5_rookPivotWidth PivotSize.two * μ := by
  let α := higham11_1_bunchParlettAlpha
  let K : ℝ := ((1 - α ^ 2) * μ)⁻¹
  have hα0 : 0 ≤ α := by
    exact le_of_lt (by simpa [α, higham11_1_bunchParlettAlpha] using
      bunch_parlett_alpha_pos)
  have hα1 : α < 1 := by
    simpa [α, higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one
  have hden : 0 < (1 - α ^ 2) * μ := by
    apply mul_pos
    · nlinarith
    · exact hμ
  have hK : (1 - α ^ 2) * μ * K = 1 :=
    mul_inv_cancel₀ (ne_of_gt hden)
  have hlocal := higham11_4_twoByTwo_schur_growth_of_block
    bij ci1 ci2 cj1 cj2 e11 e22 e21 μ (α * μ) α K
    (mul_nonneg hα0 (le_of_lt hμ)) hα0 hα1 hμ he11 he22 he21
    (le_refl _) hK hb hci1 hci2 hcj1 hcj2
  calc
    |higham11_4_twoByTwoSchurEntry bij ci1 ci2 cj1 cj2
        (e22 / (e11 * e22 - e21 ^ 2))
        (-(e21 / (e11 * e22 - e21 ^ 2)))
        (-(e21 / (e11 * e22 - e21 ^ 2)))
        (e11 / (e11 * e22 - e21 ^ 2))|
        ≤ (1 + 2 / (1 - α)) * μ := hlocal
    _ = (1 + higham11_1_bunchParlettAlpha⁻¹) ^
          higham11_5_rookPivotWidth PivotSize.two * μ := by
      rw [show α = higham11_1_bunchParlettAlpha by rfl]
      rw [← higham11_1_growth_balance]
      simp [higham11_5_rookPivotWidth, one_div]

/-- The printed rook growth-factor bound, identical to the partial-pivoting
bound after charging a `2 × 2` pivot for its two eliminated indices. -/
def higham11_5_rookGrowthBound (n : ℕ) (ρ : ℝ) : Prop :=
  ρ ≤ (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1)

/-- **Algorithm 11.5 property (3), global growth.**  Iteration over the actual
pivot sizes gives the same bound as partial pivoting.  The local obligations
are produced by `higham11_5_rook_oneByOne_schur_growth` and
`higham11_5_rook_twoByTwo_schur_growth`; `hcount` is the path's dimension
accounting, not an assumed growth conclusion. -/
theorem higham11_5_rookGrowthBound_of_pivot_steps
    (n q : ℕ) (ρ : ℝ) (r : ℕ → ℝ) (s : ℕ → PivotSize)
    (hcount : higham11_5_rookEliminatedCount s q ≤ n - 1)
    (hinitial : r 0 ≤ 1)
    (hfinal : ρ ≤ r q)
    (hstep : ∀ k, k < q →
      r (k + 1) ≤
        (1 + higham11_1_bunchParlettAlpha⁻¹) ^
          higham11_5_rookPivotWidth (s k) * r k) :
    higham11_5_rookGrowthBound n ρ := by
  let f : ℝ := 1 + higham11_1_bunchParlettAlpha⁻¹
  have hα : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  have hf1 : 1 ≤ f := by
    dsimp [f]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (le_of_lt hα))
  have hf0 : 0 ≤ f := zero_le_one.trans hf1
  have hiterate : ∀ k, k ≤ q →
      r k ≤ f ^ higham11_5_rookEliminatedCount s k := by
    intro k hk
    induction k with
    | zero => simpa [higham11_5_rookEliminatedCount] using hinitial
    | succ k ih =>
        have hklt : k < q := Nat.lt_of_succ_le hk
        calc
          r (k + 1) ≤ f ^ higham11_5_rookPivotWidth (s k) * r k := by
            simpa [f] using hstep k hklt
          _ ≤ f ^ higham11_5_rookPivotWidth (s k) *
              f ^ higham11_5_rookEliminatedCount s k :=
            mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hklt))
              (pow_nonneg hf0 _)
          _ = f ^ higham11_5_rookEliminatedCount s (k + 1) := by
            rw [higham11_5_rookEliminatedCount_succ]
            rw [pow_add]
            ring
  have hpower :
      f ^ higham11_5_rookEliminatedCount s q ≤ f ^ (n - 1) :=
    pow_le_pow_right₀ hf1 hcount
  unfold higham11_5_rookGrowthBound
  calc
    ρ ≤ r q := hfinal
    _ ≤ f ^ higham11_5_rookEliminatedCount s q := hiterate q (le_refl _)
    _ ≤ f ^ (n - 1) := hpower
    _ = (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1) := rfl

/-- If the bounded Algorithm 11.5 search selects a genuine `2 × 2` pivot,
its two failed diagonal tests, equal column maxima, and intersection entry
produce exactly the hypotheses used by the condition and growth proofs. -/
theorem higham11_5_rook_twoByTwo_terminal_pivot_data {n : ℕ}
    (α : ℝ) (A : Fin n → Fin n → ℝ) (i : Fin n)
    (hstop : higham11_5_rookSearchStops α A i)
    (hsize : higham11_5_rookPivotSize α A i = PivotSize.two)
    (hω : 0 < higham11_5_rookColumnMax A i) :
    let r := higham11_5_rookColumnArgmax A i
    let ω := higham11_5_rookColumnMax A i
    |A i i| < α * ω ∧
      |A r r| < α * ω ∧
      higham11_5_rookColumnMax A r = ω ∧
      |A r i| = ω := by
  let r := higham11_5_rookColumnArgmax A i
  let ω := higham11_5_rookColumnMax A i
  have hfirst : ¬ |A i i| ≥ α * ω := by
    intro h
    have hone : higham11_5_rookPivotSize α A i = PivotSize.one := by
      simp [higham11_5_rookPivotSize, ω, h]
    rw [hone] at hsize
    contradiction
  have hsecond :
      ¬ |A r r| ≥ α * higham11_5_rookColumnMax A r := by
    intro h
    have hone : higham11_5_rookPivotSize α A i = PivotSize.one := by
      simp [higham11_5_rookPivotSize, r, ω, hfirst, h]
    rw [hone] at hsize
    contradiction
  have heq : higham11_5_rookColumnMax A r = ω := by
    rcases hstop with h | h | h
    · exact False.elim (hfirst h)
    · exact False.elim (hsecond h)
    · simpa [r, ω] using h.symm
  have hrne : r ≠ i := by
    intro hri
    have : ω = 0 := by
      simp [ω, higham11_5_rookColumnMax, r, hri]
    linarith
  have hentry : |A r i| = ω := by
    simp [ω, higham11_5_rookColumnMax, r, hrne]
  dsimp only
  refine ⟨lt_of_not_ge hfirst, ?_, heq, hentry⟩
  have := lt_of_not_ge hsecond
  rwa [heq] at this

/-- End-to-end property-(2) adapter for the pivot returned by the bounded rook
search. -/
theorem higham11_5_rook_terminal_twoByTwo_condition_number_bound {n : ℕ}
    (α : ℝ) (A : Fin n → Fin n → ℝ) (i : Fin n)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hstop : higham11_5_rookSearchStops α A i)
    (hsize : higham11_5_rookPivotSize α A i = PivotSize.two)
    (hω : 0 < higham11_5_rookColumnMax A i) :
    let r := higham11_5_rookColumnArgmax A i
    higham11_2_NonsingularPivotBlock 2
        (higham11_4_twoByTwoPivotBlock (A i i) (A r i) (A r r))
        (higham11_5_rookTwoByTwoPivotInverse (A i i) (A r r) (A r i)) ∧
      higham11_5_rookPivotTwoByTwoCondBound α
        (kappa2
          (higham11_4_twoByTwoPivotBlock (A i i) (A r i) (A r r))
          (higham11_5_rookTwoByTwoPivotInverse (A i i) (A r r) (A r i))) := by
  let r := higham11_5_rookColumnArgmax A i
  let ω := higham11_5_rookColumnMax A i
  obtain ⟨hii, hrr, _heq, hri⟩ :=
    higham11_5_rook_twoByTwo_terminal_pivot_data α A i hstop hsize hω
  have hrisq : (A r i) ^ 2 = ω ^ 2 := by
    rw [← sq_abs, hri]
  exact higham11_5_rook_twoByTwo_condition_number_bound
    (A i i) (A r r) (A r i) ω α hα0 hα1 hω
    (le_of_lt hii) (le_of_lt hrr) hrisq

/-- Property-(2) in the exact shape returned by the bounded Algorithm 11.5
search from an arbitrary starting column. -/
theorem higham11_5_rook_bounded_search_twoByTwo_condition_number_bound {n : ℕ}
    (α : ℝ) (A : Fin n → Fin n → ℝ)
    (hA : IsSymmetricFiniteMatrix A) (i₀ : Fin n)
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    let i := higham11_5_rookSearchPath A i₀
      (higham11_5_rookTerminalStep α A hA i₀)
    higham11_5_rookPivotSize α A i = PivotSize.two →
    0 < higham11_5_rookColumnMax A i →
    let r := higham11_5_rookColumnArgmax A i
    higham11_2_NonsingularPivotBlock 2
        (higham11_4_twoByTwoPivotBlock (A i i) (A r i) (A r r))
        (higham11_5_rookTwoByTwoPivotInverse (A i i) (A r r) (A r i)) ∧
      higham11_5_rookPivotTwoByTwoCondBound α
        (kappa2
          (higham11_4_twoByTwoPivotBlock (A i i) (A r i) (A r r))
          (higham11_5_rookTwoByTwoPivotInverse (A i i) (A r r) (A r i))) := by
  dsimp only
  intro hsize hω
  exact higham11_5_rook_terminal_twoByTwo_condition_number_bound
    α A _ hα0 hα1
    (higham11_5_rookTerminalStep_stops α A hA i₀) hsize hω

/-- Concrete block-diagonal support surface for a rook `D` factor.  Each row
can be nonzero only on its diagonal and at the one partner index belonging to
the same accepted `2 × 2` pivot block. -/
def higham11_5_RookBlockDiagonalSupport {n : ℕ}
    (D : Fin n → Fin n → ℝ) (partner : Fin n → Fin n) : Prop :=
  ∀ k₁ k₂ : Fin n, k₂ ≠ k₁ → k₂ ≠ partner k₁ → D k₁ k₂ = 0

/-- A finite sum supported at no more than two named indices is at most twice
its uniform term bound.  Allowing the indices to coincide covers `1 × 1`
pivot rows without a separate case. -/
theorem higham11_5_sum_le_two_mul_of_two_index_support {n : ℕ}
    (f : Fin n → ℝ) (a b : Fin n) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, f k ≤ C)
    (hzero : ∀ k, k ≠ a → k ≠ b → f k = 0) :
    (∑ k : Fin n, f k) ≤ 2 * C := by
  calc
    (∑ k : Fin n, f k) ≤
        ∑ k : Fin n, if k = a ∨ k = b then C else 0 := by
      apply Finset.sum_le_sum
      intro k _hk
      by_cases hk : k = a ∨ k = b
      · simpa [hk] using hf k
      · have hka : k ≠ a := fun h => hk (Or.inl h)
        have hkb : k ≠ b := fun h => hk (Or.inr h)
        rw [hzero k hka hkb]
        simp [hk]
    _ ≤ ∑ k : Fin n,
        ((if k = a then C else 0) + (if k = b then C else 0)) := by
      apply Finset.sum_le_sum
      intro k _hk
      by_cases hka : k = a
      · rw [if_pos (Or.inl hka), if_pos hka]
        have hright : 0 ≤ if k = b then C else 0 := by
          split_ifs <;> linarith
        linarith
      · by_cases hkb : k = b
        · rw [if_pos (Or.inr hkb), if_neg hka, if_pos hkb]
          linarith
        · rw [if_neg (by simp [hka, hkb]), if_neg hka, if_neg hkb]
          norm_num
    _ = 2 * C := by
      rw [Finset.sum_add_distrib, Fintype.sum_ite_eq', Fintype.sum_ite_eq']
      ring

/-- At the printed Bunch-Parlett/Bunch-Kaufman value of `α`, the common rook
entry bound `max {1/(1-α),1/α}` is at most `3`. -/
theorem higham11_5_rook_common_L_const_le_three :
    max (1 / (1 - higham11_1_bunchParlettAlpha))
          (1 / higham11_1_bunchParlettAlpha) ≤ 3 := by
  have hα : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  have hα1 : higham11_1_bunchParlettAlpha < 1 := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one
  have hleft : 1 / (1 - higham11_1_bunchParlettAlpha) ≤ 3 := by
    have h := higham11_4_twoByTwo_multiplier_row_sum_const_le_six
    have hden : 0 < 1 - higham11_1_bunchParlettAlpha := by linarith
    rw [div_le_iff₀ hden] at h ⊢
    nlinarith
  have hright : 1 / higham11_1_bunchParlettAlpha ≤ 3 := by
    have h := higham11_4_recip_alpha_lt_two
    linarith
  exact max_le hleft hright

/-- **Algorithm 11.5 property (3), Theorem 11.4 product certificate.**
The global multiplier origins give `|Lᵢⱼ|≤3`; block-diagonal `D` has at most
two nonzeros in each row; and the rook growth scale bounds every accepted
pivot entry by `ρ‖A‖_M`.  Consequently
`‖|L||D||Lᵀ|‖_M ≤ 36 n ρ ‖A‖_M`, the exact certificate consumed by Higham's
Theorem 11.4 backward-error interface. -/
theorem higham11_5_rook_theorem11_4_product_bound {n : ℕ}
    (hn : 0 < n) (L D : Fin n → Fin n → ℝ)
    (partner : Fin n → Fin n) (ρ Amax : ℝ)
    (hρ : 0 ≤ ρ) (hAmax : 0 ≤ Amax)
    (horigin : ∀ i j,
      higham11_5_RookMultiplierOrigin higham11_1_bunchParlettAlpha (L i j))
    (hDsupport : higham11_5_RookBlockDiagonalSupport D partner)
    (hDgrowth : ∀ k₁ k₂ : Fin n, |D k₁ k₂| ≤ ρ * Amax) :
    higham11_4_bunchKaufmanMaxEntryProductBound n
      (higham11_4_bunchKaufmanProductMax n hn L D) ρ Amax := by
  let α := higham11_1_bunchParlettAlpha
  let c : ℝ := max (1 / (1 - α)) (1 / α)
  let Dmax : ℝ := ρ * Amax
  let C : ℝ := c * Dmax * c
  have hα : 0 < α := by
    simpa [α, higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  have hα1 : α < 1 := by
    simpa [α, higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact (div_nonneg zero_le_one (le_of_lt hα)).trans (le_max_right _ _)
  have hc3 : c ≤ 3 := by
    simpa [c, α] using higham11_5_rook_common_L_const_le_three
  have hcSq : c ^ 2 ≤ 9 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3)
      (add_nonneg hc0 (by norm_num : (0 : ℝ) ≤ 3))]
  have hcoeff : 2 * c * c ≤ 36 := by
    nlinarith [hcSq]
  have hDmax0 : 0 ≤ Dmax := mul_nonneg hρ hAmax
  have hC0 : 0 ≤ C :=
    mul_nonneg (mul_nonneg hc0 hDmax0) hc0
  have hL : higham11_5_rookPivotLBound n α L :=
    higham11_5_rookPivotLBound_of_origins α L hα hα1 horigin
  have hentries : ∀ i j : Fin n,
      higham11_4_bunchKaufmanProductEntry n L D i j ≤
        36 * (n : ℝ) * ρ * Amax := by
    intro i j
    have hterm : ∀ k₁ k₂ : Fin n,
        |L i k₁| * |D k₁ k₂| * |L j k₂| ≤ C := by
      intro k₁ k₂
      have hfirst : |L i k₁| * |D k₁ k₂| ≤ c * Dmax := by
        exact mul_le_mul (hL i k₁) (by simpa [Dmax] using hDgrowth k₁ k₂)
          (abs_nonneg _) hc0
      exact mul_le_mul hfirst (hL j k₂) (abs_nonneg _)
        (mul_nonneg hc0 hDmax0)
    have hinner : ∀ k₁ : Fin n,
        (∑ k₂ : Fin n, |L i k₁| * |D k₁ k₂| * |L j k₂|) ≤ 2 * C := by
      intro k₁
      apply higham11_5_sum_le_two_mul_of_two_index_support
        (fun k₂ => |L i k₁| * |D k₁ k₂| * |L j k₂|)
        k₁ (partner k₁) C hC0 (hterm k₁)
      intro k₂ hkdiag hkpartner
      rw [hDsupport k₁ k₂ hkdiag hkpartner]
      simp
    unfold higham11_4_bunchKaufmanProductEntry
    calc
      (∑ k₁ : Fin n, ∑ k₂ : Fin n,
          |L i k₁| * |D k₁ k₂| * |L j k₂|)
          ≤ ∑ _k₁ : Fin n, 2 * C :=
        Finset.sum_le_sum (fun k₁ _ => hinner k₁)
      _ = (n : ℝ) * (2 * C) := by simp
      _ = (2 * c * c) * ((n : ℝ) * Dmax) := by
        dsimp [C]
        ring
      _ ≤ 36 * ((n : ℝ) * Dmax) :=
        mul_le_mul_of_nonneg_right hcoeff
          (mul_nonneg (Nat.cast_nonneg n) hDmax0)
      _ = 36 * (n : ℝ) * ρ * Amax := by
        dsimp [Dmax]
        ring
  exact higham11_4_bunchKaufmanMaxEntryProductBound_of_product_entries
    n hn L D ρ Amax hentries

/-- End-to-end Theorem 11.4 factorization-error transfer for rook pivoting.
The only floating-point input is the generic Chapter 11.3 block-LDLT error
certificate; all algorithm-specific product control is produced above from
rook multiplier origins, block support, and growth. -/
theorem higham11_5_rook_theorem11_4_backward_error {n : ℕ}
    (hn : 0 < n) (A L D : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (partner : Fin n → Fin n)
    (ε ρ Amax : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hAmax : 0 ≤ Amax)
    (hbe : BlockLDLTBackwardError n A L D σ ε)
    (horigin : ∀ i j,
      higham11_5_RookMultiplierOrigin higham11_1_bunchParlettAlpha (L i j))
    (hDsupport : higham11_5_RookBlockDiagonalSupport D partner)
    (hDgrowth : ∀ k₁ k₂ : Fin n, |D k₁ k₂| ≤ ρ * Amax) :
    ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        |ΔA1 i j| ≤ ε * (36 * (n : ℝ) * ρ * Amax)) ∧
      (∀ i j : Fin n,
        |ΔA2 i j| ≤ ε * (36 * (n : ℝ) * ρ * Amax)) ∧
      (∀ i j : Fin n,
        ∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * D k₁ k₂ * L j k₂ =
          A (σ i) (σ j) + ΔA1 i j) :=
  higham11_3_block_ldlt_backward_error_interface_of_BlockLDLTBackwardError_of_higham_product_bound
    n hn A L D σ ε ρ Amax hε hbe
    (higham11_5_rook_theorem11_4_product_bound hn L D partner ρ Amax
      hρ hAmax horigin hDsupport hDgrowth)

end NumStability
