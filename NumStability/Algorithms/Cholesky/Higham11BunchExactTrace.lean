import NumStability.Algorithms.Cholesky.Higham11Chapter9BridgeClosure

/-!
# Higham Algorithm 11.1: exact Bunch--Parlett complete-pivoting trace

This module gives the sharp-growth argument an implementation-facing input.
Every nonempty constructor performs the two complete searches printed in
Algorithm 11.1, records the printed branch test, applies the corresponding
symmetric interchange, and recurses on the exact Schur complement.  Thus a
consumer cannot manufacture a sequence of block boundaries independently of
the matrices on which the algorithm actually runs.

The trace is intentionally nondeterministic only at ties: `p,q` and `r` are
witnesses attaining the complete entry and diagonal maxima.  This is exactly
the freedom present in the source algorithm.
-/

namespace NumStability

abbrev Higham11BunchMatrix (n : ℕ) := Fin n → Fin n → ℝ

def higham11_1_bunchSymmetricPermute {n : ℕ} (A : Higham11BunchMatrix n)
    (p : Equiv.Perm (Fin n)) : Higham11BunchMatrix n :=
  fun i j => A (p i) (p j)

theorem higham11_1_bunchSymmetricPermute_symmetric {n : ℕ}
    (A : Higham11BunchMatrix n) (p : Equiv.Perm (Fin n))
    (hA : IsSymmetricFiniteMatrix A) :
    IsSymmetricFiniteMatrix (higham11_1_bunchSymmetricPermute A p) := by
  intro i j
  exact hA (p i) (p j)

/-- The symmetric interchange that moves a selected scalar pivot to zero. -/
def higham11_1_bunchOnePerm {n : ℕ} (r : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap 0 r

/-- The two symmetric interchanges that move distinct selected indices to
zero and one.  The second swap is expressed in the coordinates after the
first swap. -/
def higham11_1_bunchTwoPerm {n : ℕ} (p q : Fin (n + 2)) :
    Equiv.Perm (Fin (n + 2)) :=
  let s0 : Equiv.Perm (Fin (n + 2)) := Equiv.swap 0 p
  (Equiv.swap 1 (s0 q)).trans s0

@[simp] theorem higham11_1_bunchOnePerm_zero {n : ℕ} (r : Fin (n + 1)) :
    higham11_1_bunchOnePerm r 0 = r := by
  simp [higham11_1_bunchOnePerm]

theorem higham11_1_bunchTwoPerm_zero {n : ℕ} (p q : Fin (n + 2))
    (hpq : p ≠ q) :
    higham11_1_bunchTwoPerm p q 0 = p := by
  have hs0q : Equiv.swap (0 : Fin (n + 2)) p q ≠ 0 := by
    intro h
    apply hpq
    apply (Equiv.swap (0 : Fin (n + 2)) p).injective
    rw [h]
    simp
  change (Equiv.swap 0 p) ((Equiv.swap 1 ((Equiv.swap 0 p) q)) 0) = p
  rw [Equiv.swap_apply_of_ne_of_ne (by simp) (Ne.symm hs0q)]
  simp

@[simp] theorem higham11_1_bunchTwoPerm_one {n : ℕ} (p q : Fin (n + 2)) :
    higham11_1_bunchTwoPerm p q 1 = q := by
  change (Equiv.swap 0 p) ((Equiv.swap 1 ((Equiv.swap 0 p) q)) 1) = q
  simp

noncomputable def higham11_1_bunchOneActive {n : ℕ}
    (A : Higham11BunchMatrix (n + 1)) (r : Fin (n + 1)) :
    Higham11BunchMatrix (n + 1) :=
  higham11_1_bunchSymmetricPermute A (higham11_1_bunchOnePerm r)

noncomputable def higham11_1_bunchTwoActive {n : ℕ}
    (A : Higham11BunchMatrix (n + 2)) (p q : Fin (n + 2)) :
    Higham11BunchMatrix (n + 2) :=
  higham11_1_bunchSymmetricPermute A (higham11_1_bunchTwoPerm p q)

/-- The exact one-by-one Schur complement after the selected pivot has been
moved to the leading position. -/
noncomputable def higham11_1_bunchSchurOne {n : ℕ}
    (A : Higham11BunchMatrix (n + 1)) : Higham11BunchMatrix n :=
  fun i j => A i.succ j.succ - A i.succ 0 * A j.succ 0 / A 0 0

theorem higham11_1_bunchSchurOne_symmetric {n : ℕ}
    (A : Higham11BunchMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A) :
    IsSymmetricFiniteMatrix (higham11_1_bunchSchurOne A) := by
  intro i j
  simp only [higham11_1_bunchSchurOne]
  rw [hA i.succ j.succ]
  ring

/-- A row of `C E⁻¹` for the leading two-by-two pivot block `E`. -/
noncomputable def higham11_1_bunchMultTwo {n : ℕ}
    (A : Higham11BunchMatrix (n + 2)) (i : Fin n) : Fin 2 → ℝ :=
  let e11 := A 0 0
  let e21 := A (Fin.succ 0) 0
  let e22 := A (Fin.succ 0) (Fin.succ 0)
  let c1 := A i.succ.succ 0
  let c2 := A i.succ.succ (Fin.succ 0)
  fun t => Fin.cases
    (c1 * (e22 / (e11 * e22 - e21 ^ 2)) +
      c2 * (-(e21 / (e11 * e22 - e21 ^ 2))))
    (fun _ =>
      c1 * (-(e21 / (e11 * e22 - e21 ^ 2))) +
        c2 * (e11 / (e11 * e22 - e21 ^ 2))) t

@[simp] theorem higham11_1_bunchMultTwo_zero {n : ℕ}
    (A : Higham11BunchMatrix (n + 2)) (i : Fin n) :
    higham11_1_bunchMultTwo A i 0 =
      A i.succ.succ 0 *
          (A (Fin.succ 0) (Fin.succ 0) /
            (A 0 0 * A (Fin.succ 0) (Fin.succ 0) - A (Fin.succ 0) 0 ^ 2)) +
        A i.succ.succ (Fin.succ 0) *
          (-(A (Fin.succ 0) 0 /
            (A 0 0 * A (Fin.succ 0) (Fin.succ 0) - A (Fin.succ 0) 0 ^ 2))) := by
  rfl

@[simp] theorem higham11_1_bunchMultTwo_one {n : ℕ}
    (A : Higham11BunchMatrix (n + 2)) (i : Fin n) :
    higham11_1_bunchMultTwo A i 1 =
      A i.succ.succ 0 *
          (-(A (Fin.succ 0) 0 /
            (A 0 0 * A (Fin.succ 0) (Fin.succ 0) - A (Fin.succ 0) 0 ^ 2))) +
        A i.succ.succ (Fin.succ 0) *
          (A 0 0 /
            (A 0 0 * A (Fin.succ 0) (Fin.succ 0) - A (Fin.succ 0) 0 ^ 2)) := by
  rfl

/-- The exact two-by-two Schur complement after the selected block has been
moved to the leading positions. -/
noncomputable def higham11_1_bunchSchurTwo {n : ℕ}
    (A : Higham11BunchMatrix (n + 2)) : Higham11BunchMatrix n :=
  fun i j =>
    A i.succ.succ j.succ.succ -
      (higham11_1_bunchMultTwo A i 0 * A j.succ.succ 0 +
        higham11_1_bunchMultTwo A i 1 * A j.succ.succ (Fin.succ 0))

theorem higham11_1_bunchSchurTwo_symmetric {n : ℕ}
    (A : Higham11BunchMatrix (n + 2)) (hA : IsSymmetricFiniteMatrix A) :
    IsSymmetricFiniteMatrix (higham11_1_bunchSchurTwo A) := by
  intro i j
  simp only [higham11_1_bunchSchurTwo, higham11_1_bunchMultTwo_zero,
    higham11_1_bunchMultTwo_one]
  rw [hA i.succ.succ j.succ.succ]
  rw [hA i.succ.succ 0, hA i.succ.succ (Fin.succ 0)]
  rw [hA j.succ.succ 0, hA j.succ.succ (Fin.succ 0)]
  ring

/-- An exact successful execution of Algorithm 11.1.  The positivity premise
rules out a singular all-zero active matrix; it is the ordinary successful
factorization domain, not a growth conclusion. -/
inductive Higham11ExactBunchTrace :
    {n : ℕ} → (A : Higham11BunchMatrix n) → Type
  | nil (A : Higham11BunchMatrix 0) : Higham11ExactBunchTrace A
  | one {n : ℕ} (A : Higham11BunchMatrix (n + 1))
      (hA : IsSymmetricFiniteMatrix A)
      (p q r : Fin (n + 1))
      (hentry : ∀ i j, |A i j| ≤ |A p q|)
      (hdiag : ∀ i, |A i i| ≤ |A r r|)
      (hmaxPos : 0 < |A p q|)
      (hchoice : higham11_1_BunchParlettCompletePivotChoice
        higham11_1_bunchParlettAlpha |A p q| |A r r| PivotSize.one)
      (tail : Higham11ExactBunchTrace
        (higham11_1_bunchSchurOne (higham11_1_bunchOneActive A r))) :
      Higham11ExactBunchTrace A
  | two {n : ℕ} (A : Higham11BunchMatrix (n + 2))
      (hA : IsSymmetricFiniteMatrix A)
      (p q r : Fin (n + 2))
      (hentry : ∀ i j, |A i j| ≤ |A p q|)
      (hdiag : ∀ i, |A i i| ≤ |A r r|)
      (hmaxPos : 0 < |A p q|)
      (hchoice : higham11_1_BunchParlettCompletePivotChoice
        higham11_1_bunchParlettAlpha |A p q| |A r r| PivotSize.two)
      (tail : Higham11ExactBunchTrace
        (higham11_1_bunchSchurTwo (higham11_1_bunchTwoActive A p q))) :
      Higham11ExactBunchTrace A

namespace Higham11ExactBunchTrace

/-- Block widths in elimination order. -/
noncomputable def widths : {n : ℕ} → {A : Higham11BunchMatrix n} →
    Higham11ExactBunchTrace A → List ℕ
  | _, _, .nil _ => []
  | _, _, .one _ _ _ _ _ _ _ _ _ tail => 1 :: widths tail
  | _, _, .two _ _ _ _ _ _ _ _ _ tail => 2 :: widths tail

/-- Active max-entry magnitudes in elimination order. -/
noncomputable def stageMaxes : {n : ℕ} → {A : Higham11BunchMatrix n} →
    Higham11ExactBunchTrace A → List ℝ
  | _, _, .nil _ => []
  | _, _, .one A _ p q _ _ _ _ _ tail => |A p q| :: stageMaxes tail
  | _, _, .two A _ p q _ _ _ _ _ tail => |A p q| :: stageMaxes tail

/-- Absolute determinants of accepted pivot blocks in elimination order. -/
noncomputable def pivotDetAbs : {n : ℕ} → {A : Higham11BunchMatrix n} →
    Higham11ExactBunchTrace A → List ℝ
  | _, _, .nil _ => []
  | _, _, .one A _ _ _ r _ _ _ _ tail => |A r r| :: pivotDetAbs tail
  | _, _, .two A _ p q _ _ _ _ _ tail =>
      |A p p * A q q - A p q ^ 2| :: pivotDetAbs tail

@[simp] theorem sum_widths : {n : ℕ} → {A : Higham11BunchMatrix n} →
    (trace : Higham11ExactBunchTrace A) → trace.widths.sum = n
  | _, _, .nil _ => by simp [widths]
  | _, _, .one _ _ _ _ _ _ _ _ _ tail => by
      simp [widths, sum_widths tail, Nat.add_comm]
  | _, _, .two _ _ _ _ _ _ _ _ _ tail => by
      simp [widths, sum_widths tail, Nat.add_comm]

theorem two_indices_ne {n : ℕ} (A : Higham11BunchMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A) (p q r : Fin (n + 2))
    (hentry : ∀ i j, |A i j| ≤ |A p q|)
    (hdiag : ∀ i, |A i i| ≤ |A r r|)
    (hmaxPos : 0 < |A p q|)
    (hchoice : higham11_1_BunchParlettCompletePivotChoice
      higham11_1_bunchParlettAlpha |A p q| |A r r| PivotSize.two) :
    p ≠ q := by
  intro hpq
  subst q
  have hpr := hdiag p
  have hrp := hentry r r
  have ha : higham11_1_bunchParlettAlpha < 1 := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one
  simp only [higham11_1_BunchParlettCompletePivotChoice,
    BunchParlettCompletePivotChoice] at hchoice
  nlinarith

theorem one_pivot_lower {n : ℕ} (A : Higham11BunchMatrix (n + 1))
    (p q r : Fin (n + 1))
    (hchoice : higham11_1_BunchParlettCompletePivotChoice
      higham11_1_bunchParlettAlpha |A p q| |A r r| PivotSize.one) :
    higham11_1_bunchParlettAlpha * |A p q| ≤ |A r r| := by
  exact hchoice

private theorem bunchAlpha_sq_le_one_sub_sq :
    higham11_1_bunchParlettAlpha ^ 2 ≤
      1 - higham11_1_bunchParlettAlpha ^ 2 := by
  have hsq := bunch_parlett_alpha_sq
  have hlt : higham11_1_bunchParlettAlpha < 1 := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one
  change bunchParlettAlpha ^ 2 ≤ 1 - bunchParlettAlpha ^ 2
  nlinarith

/-- The two-by-two Algorithm 11.1 branch supplies the determinant lower
bound needed at a genuine block boundary. -/
theorem two_pivot_lower {n : ℕ} (A : Higham11BunchMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A) (p q r : Fin (n + 2))
    (hentry : ∀ i j, |A i j| ≤ |A p q|)
    (hdiag : ∀ i, |A i i| ≤ |A r r|)
    (hchoice : higham11_1_BunchParlettCompletePivotChoice
      higham11_1_bunchParlettAlpha |A p q| |A r r| PivotSize.two) :
    (1 - higham11_1_bunchParlettAlpha ^ 2) * |A p q| ^ 2 ≤
      |A p p * A q q - A p q ^ 2| := by
  have hmu1 : 0 ≤ |A r r| := abs_nonneg _
  have ha0 : 0 ≤ higham11_1_bunchParlettAlpha := by
    exact le_of_lt (by
      simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
  have ha1 : higham11_1_bunchParlettAlpha < 1 := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one
  have hpp := hdiag p
  have hqq := hdiag q
  have hpq : (A p q) ^ 2 = |A p q| ^ 2 := by
    rw [sq_abs]
  have hbranch : |A r r| ≤ higham11_1_bunchParlettAlpha * |A p q| :=
    le_of_lt hchoice
  exact higham11_4_twoByTwo_absdet_lower
    (A p p) (A q q) (A p q) |A p q| |A r r|
    higham11_1_bunchParlettAlpha hmu1 ha0 ha1 hpp hqq hpq hbranch

/-- The weaker `α² μ²` lower bound follows at the printed value of `α`.
The sharp theorem above is retained for Bunch's determinant recurrence. -/
theorem two_pivot_lower_alpha_sq {n : ℕ}
    (A : Higham11BunchMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A) (p q r : Fin (n + 2))
    (hentry : ∀ i j, |A i j| ≤ |A p q|)
    (hdiag : ∀ i, |A i i| ≤ |A r r|)
    (hchoice : higham11_1_BunchParlettCompletePivotChoice
      higham11_1_bunchParlettAlpha |A p q| |A r r| PivotSize.two) :
    higham11_1_bunchParlettAlpha ^ 2 * |A p q| ^ 2 ≤
      |A p p * A q q - A p q ^ 2| := by
  have hdet := two_pivot_lower A hA p q r hentry hdiag hchoice
  have hmuSq : 0 ≤ |A p q| ^ 2 := sq_nonneg _
  calc
    higham11_1_bunchParlettAlpha ^ 2 * |A p q| ^ 2 ≤
        (1 - higham11_1_bunchParlettAlpha ^ 2) * |A p q| ^ 2 :=
      mul_le_mul_of_nonneg_right bunchAlpha_sq_le_one_sub_sq hmuSq
    _ ≤ |A p p * A q q - A p q ^ 2| := hdet

/-- Every accepted block has strictly positive determinant magnitude. -/
theorem two_pivot_pos {n : ℕ} (A : Higham11BunchMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A) (p q r : Fin (n + 2))
    (hentry : ∀ i j, |A i j| ≤ |A p q|)
    (hdiag : ∀ i, |A i i| ≤ |A r r|)
    (hmaxPos : 0 < |A p q|)
    (hchoice : higham11_1_BunchParlettCompletePivotChoice
      higham11_1_bunchParlettAlpha |A p q| |A r r| PivotSize.two) :
    0 < |A p p * A q q - A p q ^ 2| := by
  have ha : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  have hlower := two_pivot_lower_alpha_sq A hA p q r hentry hdiag hchoice
  have hleft : 0 < higham11_1_bunchParlettAlpha ^ 2 * |A p q| ^ 2 := by
    positivity
  exact lt_of_lt_of_le hleft hlower

/-- Symmetric interchanges preserve the complete-search entry bound. -/
theorem one_active_entry_bound {n : ℕ}
    (A : Higham11BunchMatrix (n + 1)) (p q r : Fin (n + 1))
    (hentry : ∀ i j, |A i j| ≤ |A p q|) :
    ∀ i j, |higham11_1_bunchOneActive A r i j| ≤ |A p q| := by
  intro i j
  exact hentry _ _

/-- Symmetric interchanges preserve the complete-search entry bound. -/
theorem two_active_entry_bound {n : ℕ}
    (A : Higham11BunchMatrix (n + 2)) (p q : Fin (n + 2))
    (hentry : ∀ i j, |A i j| ≤ |A p q|) :
    ∀ i j, |higham11_1_bunchTwoActive A p q i j| ≤ |A p q| := by
  intro i j
  exact hentry _ _

/-- The actual one-by-one branch of Algorithm 11.1 has the printed local
Schur-complement growth `(1 + α⁻¹) μ`, where `μ` is the entry maximum found
by the complete search at this stage. -/
theorem one_schur_entry_bound {n : ℕ}
    (A : Higham11BunchMatrix (n + 1))
    (p q r : Fin (n + 1))
    (hentry : ∀ i j, |A i j| ≤ |A p q|)
    (hmaxPos : 0 < |A p q|)
    (hchoice : higham11_1_BunchParlettCompletePivotChoice
      higham11_1_bunchParlettAlpha |A p q| |A r r| PivotSize.one) :
    ∀ i j : Fin n,
      |higham11_1_bunchSchurOne (higham11_1_bunchOneActive A r) i j| ≤
        (1 + higham11_1_bunchParlettAlpha⁻¹) * |A p q| := by
  let B := higham11_1_bunchOneActive A r
  have hB : ∀ i j, |B i j| ≤ |A p q| :=
    one_active_entry_bound A p q r hentry
  have hpivot : higham11_1_bunchParlettAlpha * |A p q| ≤ |B 0 0| := by
    simpa [B, higham11_1_bunchOneActive,
      higham11_1_bunchSymmetricPermute] using hchoice
  have hα : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  intro i j
  change |B i.succ j.succ - B i.succ 0 * B j.succ 0 / B 0 0| ≤
    (1 + higham11_1_bunchParlettAlpha⁻¹) * |A p q|
  simpa [one_div] using
    (higham11_1_oneByOne_schur_growth
      (B i.succ j.succ) (B i.succ 0) (B j.succ 0) (B 0 0)
      |A p q| higham11_1_bunchParlettAlpha hα hmaxPos
      (hB i.succ j.succ) (hB i.succ 0) (hB j.succ 0) hpivot)

/-- The actual two-by-two branch of Algorithm 11.1 has the printed local
two-index Schur-complement growth `(1 + α⁻¹)² μ`, against the complete-search
entry maximum `μ = |A p q|`.  The proof uses the literal accepted pivot block
after the two symmetric interchanges. -/
theorem two_schur_entry_bound {n : ℕ}
    (A : Higham11BunchMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A) (p q r : Fin (n + 2))
    (hentry : ∀ i j, |A i j| ≤ |A p q|)
    (hdiag : ∀ i, |A i i| ≤ |A r r|)
    (hmaxPos : 0 < |A p q|)
    (hchoice : higham11_1_BunchParlettCompletePivotChoice
      higham11_1_bunchParlettAlpha |A p q| |A r r| PivotSize.two) :
    ∀ i j : Fin n,
      |higham11_1_bunchSchurTwo (higham11_1_bunchTwoActive A p q) i j| ≤
        (1 + higham11_1_bunchParlettAlpha⁻¹) ^ 2 * |A p q| := by
  let B := higham11_1_bunchTwoActive A p q
  have hpq : p ≠ q := two_indices_ne A hA p q r hentry hdiag hmaxPos hchoice
  have hB : ∀ i j, |B i j| ≤ |A p q| :=
    two_active_entry_bound A p q hentry
  have hB00 : B 0 0 = A p p := by
    simp [B, higham11_1_bunchTwoActive,
      higham11_1_bunchSymmetricPermute,
      higham11_1_bunchTwoPerm_zero p q hpq]
  have hB11 : B (Fin.succ 0) (Fin.succ 0) = A q q := by
    simp [B, higham11_1_bunchTwoActive,
      higham11_1_bunchSymmetricPermute]
  have hB10 : B (Fin.succ 0) 0 = A p q := by
    rw [show B (Fin.succ 0) 0 = A q p by
      simp [B, higham11_1_bunchTwoActive,
        higham11_1_bunchSymmetricPermute,
        higham11_1_bunchTwoPerm_zero p q hpq]]
    exact hA q p
  have hα0 : 0 ≤ higham11_1_bunchParlettAlpha := by
    exact le_of_lt (by
      simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
  have hα1 : higham11_1_bunchParlettAlpha < 1 := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one
  let K : ℝ :=
    ((1 - higham11_1_bunchParlettAlpha ^ 2) * |A p q|)⁻¹
  have hden : 0 <
      (1 - higham11_1_bunchParlettAlpha ^ 2) * |A p q| := by
    apply mul_pos
    · nlinarith
    · exact hmaxPos
  have hK :
      (1 - higham11_1_bunchParlettAlpha ^ 2) * |A p q| * K = 1 :=
    mul_inv_cancel₀ (ne_of_gt hden)
  have he11 : |B 0 0| ≤ |A r r| := by
    rw [hB00]
    exact hdiag p
  have he22 : |B (Fin.succ 0) (Fin.succ 0)| ≤ |A r r| := by
    rw [hB11]
    exact hdiag q
  have he21 : B (Fin.succ 0) 0 ^ 2 = |A p q| ^ 2 := by
    rw [hB10, sq_abs]
  have hdiagAlpha : |A r r| ≤
      higham11_1_bunchParlettAlpha * |A p q| := le_of_lt hchoice
  intro i j
  have hlocal := higham11_4_twoByTwo_schur_growth_of_block
    (B i.succ.succ j.succ.succ)
    (B i.succ.succ 0) (B i.succ.succ (Fin.succ 0))
    (B j.succ.succ 0) (B j.succ.succ (Fin.succ 0))
    (B 0 0) (B (Fin.succ 0) (Fin.succ 0)) (B (Fin.succ 0) 0)
    |A p q| |A r r| higham11_1_bunchParlettAlpha K
    (abs_nonneg _) hα0 hα1 hmaxPos he11 he22 he21 hdiagAlpha hK
    (hB i.succ.succ j.succ.succ)
    (hB i.succ.succ 0) (hB i.succ.succ (Fin.succ 0))
    (hB j.succ.succ 0) (hB j.succ.succ (Fin.succ 0))
  change
    |B i.succ.succ j.succ.succ -
      (higham11_1_bunchMultTwo B i 0 * B j.succ.succ 0 +
        higham11_1_bunchMultTwo B i 1 *
          B j.succ.succ (Fin.succ 0))| ≤
      (1 + higham11_1_bunchParlettAlpha⁻¹) ^ 2 * |A p q|
  calc
    |B i.succ.succ j.succ.succ -
        (higham11_1_bunchMultTwo B i 0 * B j.succ.succ 0 +
          higham11_1_bunchMultTwo B i 1 *
            B j.succ.succ (Fin.succ 0))| =
        |higham11_4_twoByTwoSchurEntry
          (B i.succ.succ j.succ.succ)
          (B i.succ.succ 0) (B i.succ.succ (Fin.succ 0))
          (B j.succ.succ 0) (B j.succ.succ (Fin.succ 0))
          (B (Fin.succ 0) (Fin.succ 0) /
            (B 0 0 * B (Fin.succ 0) (Fin.succ 0) - B (Fin.succ 0) 0 ^ 2))
          (-(B (Fin.succ 0) 0 /
            (B 0 0 * B (Fin.succ 0) (Fin.succ 0) - B (Fin.succ 0) 0 ^ 2)))
          (-(B (Fin.succ 0) 0 /
            (B 0 0 * B (Fin.succ 0) (Fin.succ 0) - B (Fin.succ 0) 0 ^ 2)))
          (B 0 0 /
            (B 0 0 * B (Fin.succ 0) (Fin.succ 0) - B (Fin.succ 0) 0 ^ 2))| := by
      simp only [higham11_1_bunchMultTwo_zero,
        higham11_1_bunchMultTwo_one, higham11_4_twoByTwoSchurEntry]
      congr 1
      ring
    _ ≤ (1 + 2 / (1 - higham11_1_bunchParlettAlpha)) * |A p q| := hlocal
    _ = (1 + higham11_1_bunchParlettAlpha⁻¹) ^ 2 * |A p q| := by
      rw [show higham11_1_bunchParlettAlpha⁻¹ =
        1 / higham11_1_bunchParlettAlpha by simp]
      rw [higham11_1_growth_balance]

end Higham11ExactBunchTrace

end NumStability
