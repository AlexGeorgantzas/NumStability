import NumStability.Algorithms.HighamChapter10

namespace NumStability

open scoped BigOperators

/-!
# Source-facing closure for Higham Lemma 10.11

The source assumes that the first `r` complete-pivoting choices have no ties.
Since all index sets are finite, strict separation and positive pivots give one
uniform positive diagonal gap, one uniform positive pivot floor, and one finite
entry cap.  This file constructs those constants rather than asking a caller to
supply them.  It then packages pivot preservation for operator-norm-small
perturbations of either sign and supplies signed versions of the displayed
leading-block perturbation identities.
-/

/-- Literal finite no-ties condition for the first `r` exact
complete-pivoting stages. -/
def Higham10_11NoTies {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (r : ℕ) : Prop :=
  ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
    cpState hn A t i i <
      cpState hn A t (cpPivot hn A t) (cpPivot hn A t)

/-- Finiteness turns the source's strict no-ties condition, together with the
visible nonbreakdown condition for its first `r` stages, into the uniform gap,
pivot floor, and entry cap consumed by the quantitative state-machine proof.
No target stability statement occurs among the assumptions. -/
theorem higham10_11_finite_noTies_gap_floor_cap {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (r : ℕ)
    (hpivot : ∀ t : ℕ, t < r →
      0 < cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hnoTies : Higham10_11NoTies hn A r) :
    ∃ δ ρ c : ℝ,
      0 < δ ∧ δ ≤ ρ ∧ 0 ≤ c ∧
      (∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
        cpState hn A t i i + δ ≤
          cpState hn A t (cpPivot hn A t) (cpPivot hn A t)) ∧
      (∀ t : ℕ, t < r →
        ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t)) ∧
      (∀ t : ℕ, t < r → ∀ i j : Fin n,
        |cpState hn A t i j| ≤ c) := by
  classical
  let margin : Fin r × Fin n → ℝ := fun q =>
    let p := cpPivot hn A q.1.val
    if q.2 = p then cpState hn A q.1.val p p
    else cpState hn A q.1.val p p - cpState hn A q.1.val q.2 q.2
  have hmargin : ∀ q : Fin r × Fin n, 0 < margin q := by
    intro q
    by_cases hq : q.2 = cpPivot hn A q.1.val
    · simp only [margin, hq, ↓reduceIte]
      exact hpivot q.1.val q.1.isLt
    · simp only [margin, hq, ↓reduceIte]
      exact sub_pos.mpr (hnoTies q.1.val q.1.isLt q.2 hq)
  let factor : Fin r × Fin n → ℝ := fun q => min 1 (margin q)
  have hfactor_pos : ∀ q : Fin r × Fin n, 0 < factor q := by
    intro q
    exact lt_min one_pos (hmargin q)
  have hfactor_nonneg : ∀ q : Fin r × Fin n, 0 ≤ factor q :=
    fun q => (hfactor_pos q).le
  have hfactor_le_one : ∀ q : Fin r × Fin n, factor q ≤ 1 :=
    fun q => min_le_left _ _
  let δ : ℝ := ∏ q : Fin r × Fin n, factor q
  have hδ : 0 < δ := by
    exact Finset.prod_pos fun q _ => hfactor_pos q
  have hδ_le_margin : ∀ q : Fin r × Fin n, δ ≤ margin q := by
    intro q
    have hrest0 : 0 ≤ ∏ x ∈ Finset.univ.erase q, factor x :=
      Finset.prod_nonneg fun x _ => hfactor_nonneg x
    have hrest1 : (∏ x ∈ Finset.univ.erase q, factor x) ≤ 1 :=
      Finset.prod_le_one
        (fun x _ => hfactor_nonneg x)
        (fun x _ => hfactor_le_one x)
    calc
      δ = factor q * ∏ x ∈ Finset.univ.erase q, factor x := by
        exact (Finset.mul_prod_erase Finset.univ factor
          (Finset.mem_univ q)).symm
      _ ≤ factor q * 1 :=
        mul_le_mul_of_nonneg_left hrest1 (hfactor_nonneg q)
      _ = factor q := mul_one _
      _ ≤ margin q := min_le_right _ _
  let c : ℝ := ∑ t : Fin r, ∑ i : Fin n, ∑ j : Fin n,
    |cpState hn A t.val i j|
  have hc : 0 ≤ c := by
    exact Finset.sum_nonneg fun t _ =>
      Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨δ, δ, c, hδ, le_rfl, hc, ?_, ?_, ?_⟩
  · intro t ht i hi
    let tf : Fin r := ⟨t, ht⟩
    have hle := hδ_le_margin (tf, i)
    have hmargin_eq : margin (tf, i) =
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t) -
          cpState hn A t i i := by
      simp [margin, tf, hi]
    rw [hmargin_eq] at hle
    linarith
  · intro t ht
    let tf : Fin r := ⟨t, ht⟩
    let p := cpPivot hn A t
    have hle := hδ_le_margin (tf, p)
    have hmargin_eq : margin (tf, p) = cpState hn A t p p := by
      simp [margin, tf, p]
    simpa [hmargin_eq, p] using hle
  · intro t ht i j
    let tf : Fin r := ⟨t, ht⟩
    have hj : |cpState hn A t i j| ≤
        ∑ j' : Fin n, |cpState hn A t i j'| :=
      Finset.single_le_sum
        (f := fun j' : Fin n => |cpState hn A t i j'|)
        (fun j' _ => abs_nonneg _)
        (Finset.mem_univ j)
    have hi : (∑ j' : Fin n, |cpState hn A t i j'|) ≤
        ∑ i' : Fin n, ∑ j' : Fin n, |cpState hn A t i' j'| :=
      Finset.single_le_sum
        (f := fun i' : Fin n =>
          ∑ j' : Fin n, |cpState hn A t i' j'|)
        (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _)
        (Finset.mem_univ i)
    have ht' : (∑ i' : Fin n, ∑ j' : Fin n,
          |cpState hn A t i' j'|) ≤ c := by
      exact Finset.single_le_sum
        (f := fun t' : Fin r => ∑ i' : Fin n, ∑ j' : Fin n,
          |cpState hn A t'.val i' j'|)
        (fun t' _ => Finset.sum_nonneg fun i' _ =>
          Finset.sum_nonneg fun j' _ => abs_nonneg _)
        (Finset.mem_univ tf)
    exact hj.trans (hi.trans ht')

/-- Source-strength pivot preservation.  The finite no-ties and nonbreakdown
hypotheses alone produce a positive radius.  Any perturbation whose operator
2-norm is at most that radius preserves all first-`r` pivots, for both `A + E`
and `A - E`. -/
theorem higham10_11_cp_pivot_sequence_stable_of_noTies_two_sided
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (hpivot : ∀ t : ℕ, t < r →
      0 < cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hnoTies : Higham10_11NoTies hn A r) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ E : Fin n → Fin n → ℝ, opNorm2 E ≤ ε₀ →
        (∀ s : ℕ, s < r →
          cpPivot hn A s = cpPivot hn (fun i j => A i j + E i j) s) ∧
        (∀ s : ℕ, s < r →
          cpPivot hn A s = cpPivot hn (fun i j => A i j - E i j) s) := by
  obtain ⟨δ, ρ, c, hδ, hδρ, hc, hgap, hfloor, hcap⟩ :=
    higham10_11_finite_noTies_gap_floor_cap hn A r hpivot hnoTies
  obtain ⟨ε₀, hε₀, hstable⟩ := higham10_11_cp_pivot_sequence_stable
    hn A r δ ρ c hδ hδρ hc hgap hfloor hcap
  refine ⟨ε₀, hε₀, ?_⟩
  intro E hE
  have hentry : ∀ i j : Fin n, |E i j| ≤ ε₀ := by
    intro i j
    exact (higham9_15_abs_entry_le_opNorm2 E i j).trans hE
  constructor
  · apply hstable (fun i j => A i j + E i j)
    intro i j
    simpa using hentry i j
  · apply hstable (fun i j => A i j - E i j)
    intro i j
    simpa using hentry i j

/-- Signed version of the displayed leading-block perturbation.  The source
allows `|γ|` to be small, so the linear term retains the sign of `γ` while the
remainder is controlled by `|γ|²`. -/
theorem higham10_11_schur_perturbation_leadingBlock_signed {k m : ℕ}
    (A11 M X : Matrix (Fin k) (Fin k) ℝ)
    (A21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 : Matrix (Fin k) (Fin m) ℝ)
    (A22 : Matrix (Fin m) (Fin m) ℝ)
    (γ : ℝ)
    (hM : M * A11 = 1)
    (hXi : (A11 + γ • (1 : Matrix (Fin k) (Fin k) ℝ)) * X = 1)
    (α μ χ : ℝ) (hα : 0 ≤ α) (hμ : 0 ≤ μ) (hχ : 0 ≤ χ)
    (hA21 : ∀ i j, |A21 i j| ≤ α) (hA12 : ∀ i j, |A12 i j| ≤ α)
    (hMb : ∀ i j, |M i j| ≤ μ) (hXb : ∀ i j, |X i j| ≤ χ) :
    ∃ R : Matrix (Fin m) (Fin m) ℝ,
      A22 - A21 * X * A12 =
        (A22 - A21 * M * A12) + γ • (A21 * (M * M) * A12) + R ∧
      ∀ i j : Fin m, |R i j| ≤
        ((k : ℝ) ^ 2 * μ + (k : ℝ) ^ 6 * α ^ 2 * μ ^ 2 * χ
          + 2 * ((k : ℝ) ^ 4 * α * μ * χ)
          + (k : ℝ) ^ 4 * μ * χ * |γ|) * |γ| ^ 2 := by
  obtain ⟨R, hEq, hR⟩ :=
    higham10_10_schur_complement_perturbation A11
      (γ • (1 : Matrix (Fin k) (Fin k) ℝ)) M X
      A21 (0 : Matrix (Fin m) (Fin k) ℝ)
      A12 (0 : Matrix (Fin k) (Fin m) ℝ)
      A22 (0 : Matrix (Fin m) (Fin m) ℝ)
      hM hXi α μ χ |γ| hα hμ hχ (abs_nonneg γ)
      hA21 hA12
      (by intro i j; simp [abs_nonneg γ])
      (by intro i j; simp [abs_nonneg γ])
      (by
        intro i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij, abs_nonneg γ])
      hMb hXb
  refine ⟨R, ?_, hR⟩
  have hterm : A21 *
      (M * (γ • (1 : Matrix (Fin k) (Fin k) ℝ)) * M) * A12 =
        γ • (A21 * (M * M) * A12) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hLHS : A22 - A21 * X * A12 =
      (A22 + (0 : Matrix (Fin m) (Fin m) ℝ)) -
        (A21 + 0) * X * (A12 + 0) := by simp
  rw [hLHS, hEq]
  simp

/-- Operator-2 remainder version of the signed leading-block perturbation. -/
theorem higham10_11_schur_perturbation_opNorm2_signed {k m : ℕ}
    (A11 M X : Matrix (Fin k) (Fin k) ℝ)
    (A21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 : Matrix (Fin k) (Fin m) ℝ)
    (A22 : Matrix (Fin m) (Fin m) ℝ)
    (γ : ℝ)
    (hM : M * A11 = 1)
    (hXi : (A11 + γ • (1 : Matrix (Fin k) (Fin k) ℝ)) * X = 1)
    (α μ χ : ℝ) (hα : 0 ≤ α) (hμ : 0 ≤ μ) (hχ : 0 ≤ χ)
    (hA21 : ∀ i j, |A21 i j| ≤ α) (hA12 : ∀ i j, |A12 i j| ≤ α)
    (hMb : ∀ i j, |M i j| ≤ μ) (hXb : ∀ i j, |X i j| ≤ χ) :
    ∃ R : Matrix (Fin m) (Fin m) ℝ,
      A22 - A21 * X * A12 =
        (A22 - A21 * M * A12) + γ • (A21 * (M * M) * A12) + R ∧
      opNorm2Le R
        (((k : ℝ) ^ 2 * μ + (k : ℝ) ^ 6 * α ^ 2 * μ ^ 2 * χ
          + 2 * ((k : ℝ) ^ 4 * α * μ * χ)
          + (k : ℝ) ^ 4 * μ * χ * |γ|) * |γ| ^ 2 * (m : ℝ)) := by
  obtain ⟨R, hEq, hR⟩ :=
    higham10_11_schur_perturbation_leadingBlock_signed
      A11 M X A21 A12 A22 γ hM hXi α μ χ hα hμ hχ
      hA21 hA12 hMb hXb
  refine ⟨R, hEq, ?_⟩
  set b : ℝ := ((k : ℝ) ^ 2 * μ + (k : ℝ) ^ 6 * α ^ 2 * μ ^ 2 * χ
      + 2 * ((k : ℝ) ^ 4 * α * μ * χ)
      + (k : ℝ) ^ 4 * μ * χ * |γ|) * |γ| ^ 2 with hb
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hones := opNorm2Le_smul m (fun _ _ : Fin m => (1 : ℝ))
    (m : ℝ) b hb0 (higham10_7_onesMatrix_opNorm2Le m)
  exact opNorm2Le_of_abs_le m R (fun _ _ => b * 1)
    (fun i j => by rw [mul_one]; exact hR i j) (b * (m : ℝ)) hones

open scoped Matrix.Norms.L2Operator in
/-- The signed first-order coefficient has norm `|γ| ‖W‖₂²`. -/
theorem higham10_11_firstOrder_opNorm2_signed {k m : ℕ}
    (W : Matrix (Fin k) (Fin m) ℝ) (γ : ℝ) :
    opNorm2 (γ • (Matrix.transpose W * W)) = |γ| * (‖W‖ * ‖W‖) := by
  have htr : Matrix.transpose W = Matrix.conjTranspose W := by
    ext i j
    simp [Matrix.transpose_apply, Matrix.conjTranspose_apply]
  show ‖γ • (Matrix.transpose W * W)‖ = |γ| * (‖W‖ * ‖W‖)
  rw [htr, norm_smul, Real.norm_eq_abs,
    Matrix.l2_opNorm_conjTranspose_mul_self]

open scoped Matrix.Norms.L2Operator in
/-- The displayed signed block perturbation has operator 2-norm `|γ|`. -/
theorem higham10_11_leadingBlockPerturbation_opNorm2_signed {k m : ℕ}
    (hk : 0 < k) (γ : ℝ) :
    opNorm2 (higham10_11_leadingBlockPerturbation k m γ) = |γ| := by
  have hscale : higham10_11_leadingBlockPerturbation k m γ =
      γ • higham10_11_leadingBlockPerturbation k m 1 := by
    funext i j
    unfold higham10_11_leadingBlockPerturbation
    by_cases h : i = j ∧ (i : ℕ) < k <;> simp [h]
  rw [hscale]
  change ‖γ • Matrix.of (higham10_11_leadingBlockPerturbation k m 1)‖ = |γ|
  rw [norm_smul, Real.norm_eq_abs]
  change |γ| * opNorm2 (higham10_11_leadingBlockPerturbation k m 1) = |γ|
  rw [higham10_11_leadingBlockPerturbation_opNorm2 hk 1 (by norm_num), mul_one]

end NumStability
