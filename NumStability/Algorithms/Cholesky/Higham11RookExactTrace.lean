/-
Exact source-faithful closure for Higham Algorithm 11.5.

The trace below runs the literal bounded rook search on each symmetric active
matrix, applies the selected symmetric permutation, and recurses on the exact
Schur complement.  Its derived schedule, multiplier origins, block support,
and active-matrix growth discharge every rook-specific premise of the printed
Theorem 11.4 product bound.
-/

import NumStability.Algorithms.Cholesky.Higham11RookExecutorAdapter

namespace NumStability
namespace Higham11RookExecutorAdapter

open Ch11Closure.Mixed

abbrev Higham11RookMatrix (n : ℕ) := Fin n → Fin n → ℝ

def higham11_5_symmetricPermute {n : ℕ} (A : Higham11RookMatrix n)
    (p : Equiv.Perm (Fin n)) : Higham11RookMatrix n :=
  fun i j => A (p i) (p j)

theorem higham11_5_symmetricPermute_symmetric {n : ℕ}
    (A : Higham11RookMatrix n) (p : Equiv.Perm (Fin n))
    (hA : IsSymmetricFiniteMatrix A) :
    IsSymmetricFiniteMatrix (higham11_5_symmetricPermute A p) := by
  intro i j
  exact hA (p i) (p j)

noncomputable def higham11_5_exactRookTerminalIndex {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A) :
    Fin (n + 1) :=
  higham11_5_rookSearchPath A 0
    (higham11_5_rookTerminalStep higham11_1_bunchParlettAlpha A hA 0)

noncomputable def higham11_5_exactRookNextIndex {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A) :
    Fin (n + 1) :=
  higham11_5_rookColumnArgmax A
    (higham11_5_exactRookTerminalIndex A hA)

noncomputable def higham11_5_exactRookScalarIndex {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A) :
    Fin (n + 1) :=
  let i := higham11_5_exactRookTerminalIndex A hA
  if |A i i| ≥ higham11_1_bunchParlettAlpha *
      higham11_5_rookColumnMax A i then i
  else higham11_5_rookColumnArgmax A i

noncomputable def higham11_5_exactRookOnePerm {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap 0 (higham11_5_exactRookScalarIndex A hA)

noncomputable def higham11_5_exactRookTwoPerm {n : ℕ}
    (A : Higham11RookMatrix (n + 2)) (hA : IsSymmetricFiniteMatrix A) :
    Equiv.Perm (Fin (n + 2)) :=
  let i := higham11_5_exactRookTerminalIndex A hA
  let r := higham11_5_rookColumnArgmax A i
  let s0 : Equiv.Perm (Fin (n + 2)) := Equiv.swap 0 i
  (Equiv.swap 1 (s0 r)).trans s0

theorem higham11_5_rookColumnMax_nonneg {n : ℕ}
    (A : Higham11RookMatrix n) (i : Fin n) :
    0 ≤ higham11_5_rookColumnMax A i := by
  unfold higham11_5_rookColumnMax
  positivity

theorem higham11_5_exactRookTerminal_stops {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A) :
    higham11_5_rookSearchStops higham11_1_bunchParlettAlpha A
      (higham11_5_exactRookTerminalIndex A hA) := by
  exact higham11_5_rookTerminalStep_stops
    higham11_1_bunchParlettAlpha A hA 0

theorem higham11_5_exactRookTwo_omega_pos {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A)
    (hsize : higham11_5_rookPivotSize higham11_1_bunchParlettAlpha A
      (higham11_5_exactRookTerminalIndex A hA) = PivotSize.two) :
    0 < higham11_5_rookColumnMax A
      (higham11_5_exactRookTerminalIndex A hA) := by
  let i := higham11_5_exactRookTerminalIndex A hA
  let omega := higham11_5_rookColumnMax A i
  have homega0 : 0 ≤ omega := higham11_5_rookColumnMax_nonneg A i
  by_contra hnot
  have homega : omega = 0 := le_antisymm (le_of_not_gt hnot) homega0
  change higham11_5_rookColumnMax A i = 0 at homega
  have hone : higham11_5_rookPivotSize higham11_1_bunchParlettAlpha A i =
      PivotSize.one := by
    simp [higham11_5_rookPivotSize, homega]
  rw [hone] at hsize
  contradiction

theorem higham11_5_exactRookTwo_next_ne {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A)
    (hsize : higham11_5_rookPivotSize higham11_1_bunchParlettAlpha A
      (higham11_5_exactRookTerminalIndex A hA) = PivotSize.two) :
    higham11_5_rookColumnArgmax A
        (higham11_5_exactRookTerminalIndex A hA) ≠
      higham11_5_exactRookTerminalIndex A hA := by
  intro h
  have hpos := higham11_5_exactRookTwo_omega_pos A hA hsize
  unfold higham11_5_rookColumnMax at hpos
  rw [if_pos h] at hpos
  simp at hpos

@[simp] theorem higham11_5_exactRookOnePerm_zero {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A) :
    higham11_5_exactRookOnePerm A hA 0 =
      higham11_5_exactRookScalarIndex A hA := by
  simp [higham11_5_exactRookOnePerm]

theorem higham11_5_exactRookTwoPerm_zero {n : ℕ}
    (A : Higham11RookMatrix (n + 2)) (hA : IsSymmetricFiniteMatrix A)
    (hsize : higham11_5_rookPivotSize higham11_1_bunchParlettAlpha A
      (higham11_5_exactRookTerminalIndex A hA) = PivotSize.two) :
    higham11_5_exactRookTwoPerm A hA 0 =
      higham11_5_exactRookTerminalIndex A hA := by
  let i := higham11_5_exactRookTerminalIndex A hA
  let r := higham11_5_rookColumnArgmax A i
  have hri : r ≠ i := higham11_5_exactRookTwo_next_ne A hA hsize
  have hs0r : Equiv.swap (0 : Fin (n + 2)) i r ≠ 0 := by
    intro h
    have := congrArg (Equiv.swap (0 : Fin (n + 2)) i) h
    simp [hri] at this
  change (Equiv.swap 0 i)
      ((Equiv.swap 1 ((Equiv.swap 0 i) r)) 0) = i
  rw [Equiv.swap_apply_of_ne_of_ne (by simp) (Ne.symm hs0r)]
  simp

theorem higham11_5_exactRookTwoPerm_one {n : ℕ}
    (A : Higham11RookMatrix (n + 2)) (hA : IsSymmetricFiniteMatrix A) :
    higham11_5_exactRookTwoPerm A hA 1 =
      higham11_5_rookColumnArgmax A
        (higham11_5_exactRookTerminalIndex A hA) := by
  let i := higham11_5_exactRookTerminalIndex A hA
  let r := higham11_5_rookColumnArgmax A i
  change (Equiv.swap 0 i)
      ((Equiv.swap 1 ((Equiv.swap 0 i) r)) 1) = r
  simp

noncomputable def higham11_5_exactRookOneActive {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A) :
    Higham11RookMatrix (n + 1) :=
  higham11_5_symmetricPermute A (higham11_5_exactRookOnePerm A hA)

noncomputable def higham11_5_exactRookTwoActive {n : ℕ}
    (A : Higham11RookMatrix (n + 2)) (hA : IsSymmetricFiniteMatrix A) :
    Higham11RookMatrix (n + 2) :=
  higham11_5_symmetricPermute A (higham11_5_exactRookTwoPerm A hA)

noncomputable def higham11_5_exactSchurOne {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) : Higham11RookMatrix n :=
  fun i j => A i.succ j.succ - A i.succ 0 * A j.succ 0 / A 0 0

theorem higham11_5_exactSchurOne_symmetric {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A) :
    IsSymmetricFiniteMatrix (higham11_5_exactSchurOne A) := by
  intro i j
  simp only [higham11_5_exactSchurOne]
  rw [hA i.succ j.succ]
  ring

noncomputable def higham11_5_exactMultTwo {n : ℕ}
    (A : Higham11RookMatrix (n + 2)) (i : Fin n) : Fin 2 → ℝ :=
  let e11 := A 0 0
  let e21 := A (Fin.succ 0) 0
  let e22 := A (Fin.succ 0) (Fin.succ 0)
  let c1 := A i.succ.succ 0
  let c2 := A i.succ.succ (Fin.succ 0)
  fun p => Fin.cases
    (c1 * (e22 / (e11 * e22 - e21 ^ 2)) +
      c2 * (-(e21 / (e11 * e22 - e21 ^ 2))))
    (fun _ =>
      c1 * (-(e21 / (e11 * e22 - e21 ^ 2))) +
        c2 * (e11 / (e11 * e22 - e21 ^ 2))) p

@[simp] theorem higham11_5_exactMultTwo_zero {n : ℕ}
    (A : Higham11RookMatrix (n + 2)) (i : Fin n) :
    higham11_5_exactMultTwo A i 0 =
      A i.succ.succ 0 *
          (A (Fin.succ 0) (Fin.succ 0) /
            (A 0 0 * A (Fin.succ 0) (Fin.succ 0) - A (Fin.succ 0) 0 ^ 2)) +
        A i.succ.succ (Fin.succ 0) *
          (-(A (Fin.succ 0) 0 /
            (A 0 0 * A (Fin.succ 0) (Fin.succ 0) - A (Fin.succ 0) 0 ^ 2))) := by
  rfl

@[simp] theorem higham11_5_exactMultTwo_one {n : ℕ}
    (A : Higham11RookMatrix (n + 2)) (i : Fin n) :
    higham11_5_exactMultTwo A i 1 =
      A i.succ.succ 0 *
          (-(A (Fin.succ 0) 0 /
            (A 0 0 * A (Fin.succ 0) (Fin.succ 0) - A (Fin.succ 0) 0 ^ 2))) +
        A i.succ.succ (Fin.succ 0) *
          (A 0 0 /
            (A 0 0 * A (Fin.succ 0) (Fin.succ 0) - A (Fin.succ 0) 0 ^ 2)) := by
  rfl

noncomputable def higham11_5_exactSchurTwo {n : ℕ}
    (A : Higham11RookMatrix (n + 2)) : Higham11RookMatrix n :=
  fun i j =>
    A i.succ.succ j.succ.succ -
      (higham11_5_exactMultTwo A i 0 * A j.succ.succ 0 +
        higham11_5_exactMultTwo A i 1 * A j.succ.succ (Fin.succ 0))

theorem higham11_5_exactSchurTwo_symmetric {n : ℕ}
    (A : Higham11RookMatrix (n + 2)) (hA : IsSymmetricFiniteMatrix A) :
    IsSymmetricFiniteMatrix (higham11_5_exactSchurTwo A) := by
  intro i j
  simp only [higham11_5_exactSchurTwo, higham11_5_exactMultTwo_zero,
    higham11_5_exactMultTwo_one]
  rw [hA i.succ.succ j.succ.succ]
  rw [hA i.succ.succ 0, hA i.succ.succ (Fin.succ 0)]
  rw [hA j.succ.succ 0, hA j.succ.succ (Fin.succ 0)]
  ring

inductive Higham11ExactRookTrace :
    {n : ℕ} → (A : Higham11RookMatrix n) → Type
  | nil (A : Higham11RookMatrix 0) : Higham11ExactRookTrace A
  | one {n : ℕ} (A : Higham11RookMatrix (n + 1))
      (hA : IsSymmetricFiniteMatrix A)
      (hsize : higham11_5_rookPivotSize higham11_1_bunchParlettAlpha
        A (higham11_5_exactRookTerminalIndex A hA) = PivotSize.one)
      (tail : Higham11ExactRookTrace
        (higham11_5_exactSchurOne (higham11_5_exactRookOneActive A hA))) :
      Higham11ExactRookTrace A
  | two {n : ℕ} (A : Higham11RookMatrix (n + 2))
      (hA : IsSymmetricFiniteMatrix A)
      (hsize : higham11_5_rookPivotSize higham11_1_bunchParlettAlpha
        A (higham11_5_exactRookTerminalIndex A hA) = PivotSize.two)
      (tail : Higham11ExactRookTrace
        (higham11_5_exactSchurTwo (higham11_5_exactRookTwoActive A hA))) :
      Higham11ExactRookTrace A

noncomputable def Higham11ExactRookTrace.schedule :
    {n : ℕ} → {A : Higham11RookMatrix n} → Higham11ExactRookTrace A →
      PivotSchedule n
  | _, _, .nil _ => .nil
  | _, _, .one _ _ _ tail => tail.schedule.consOne
  | _, _, .two _ _ _ tail => tail.schedule.consTwo

theorem higham11_5_exactRookPivotSize_finOne
    (A : Higham11RookMatrix 1) (hA : IsSymmetricFiniteMatrix A) :
    higham11_5_rookPivotSize higham11_1_bunchParlettAlpha A
      (higham11_5_exactRookTerminalIndex A hA) = PivotSize.one := by
  let i := higham11_5_exactRookTerminalIndex A hA
  have hi : i = 0 := Fin.eq_zero i
  have harg : higham11_5_rookColumnArgmax A i = i := by
    calc
      higham11_5_rookColumnArgmax A i = 0 := Fin.eq_zero _
      _ = i := hi.symm
  have hcol : higham11_5_rookColumnMax A i = 0 := by
    unfold higham11_5_rookColumnMax
    rw [if_pos harg]
    simp
  change higham11_5_rookPivotSize higham11_1_bunchParlettAlpha A i =
    PivotSize.one
  unfold higham11_5_rookPivotSize
  rw [hcol]
  simp

theorem higham11_5_nonempty_exactRookTrace :
    ∀ {n : ℕ} (A : Higham11RookMatrix n),
      IsSymmetricFiniteMatrix A → Nonempty (Higham11ExactRookTrace A) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro A hA
      cases n with
      | zero =>
          exact ⟨.nil A⟩
      | succ m =>
          let i := higham11_5_exactRookTerminalIndex A hA
          cases hsize : higham11_5_rookPivotSize
              higham11_1_bunchParlettAlpha A i with
          | one =>
              let B := higham11_5_exactRookOneActive A hA
              have hB : IsSymmetricFiniteMatrix B :=
                higham11_5_symmetricPermute_symmetric A _ hA
              let S := higham11_5_exactSchurOne B
              have hS : IsSymmetricFiniteMatrix S :=
                higham11_5_exactSchurOne_symmetric B hB
              let tail : Higham11ExactRookTrace S :=
                Classical.choice (ih m (by omega) S hS)
              exact ⟨.one A hA hsize tail⟩
          | two =>
              cases m with
              | zero =>
                  have hone := higham11_5_exactRookPivotSize_finOne A hA
                  rw [hone] at hsize
                  contradiction
              | succ k =>
                  let B := higham11_5_exactRookTwoActive A hA
                  have hB : IsSymmetricFiniteMatrix B :=
                    higham11_5_symmetricPermute_symmetric A _ hA
                  let S := higham11_5_exactSchurTwo B
                  have hS : IsSymmetricFiniteMatrix S :=
                    higham11_5_exactSchurTwo_symmetric B hB
                  let tail : Higham11ExactRookTrace S :=
                    Classical.choice (ih k (by omega) S hS)
                  exact ⟨.two A hA hsize tail⟩

noncomputable def Higham11ExactRookTrace.L :
    {n : ℕ} → {A : Higham11RookMatrix n} → Higham11ExactRookTrace A →
      Higham11RookMatrix n
  | _, _, .nil _ => fun i _ => Fin.elim0 i
  | _, _, .one A hA _ tail =>
      let B := higham11_5_exactRookOneActive A hA
      fun I J =>
        Fin.cases (Fin.cases 1 (fun _ => 0) J)
          (fun i => Fin.cases (B i.succ 0 / B 0 0)
            (fun j => tail.L i j) J) I
  | _, _, .two A hA _ tail =>
      let B := higham11_5_exactRookTwoActive A hA
      fun I J =>
        Fin.cases
          (Fin.cases 1 (fun l => Fin.cases 0 (fun _ => 0) l) J)
          (fun k => Fin.cases
            (Fin.cases 0 (fun l => Fin.cases 1 (fun _ => 0) l) J)
            (fun i => Fin.cases (higham11_5_exactMultTwo B i 0)
              (fun l => Fin.cases (higham11_5_exactMultTwo B i 1)
                (fun j => tail.L i j) l) J)
            k) I

noncomputable def Higham11ExactRookTrace.D :
    {n : ℕ} → {A : Higham11RookMatrix n} → Higham11ExactRookTrace A →
      Higham11RookMatrix n
  | _, _, .nil _ => fun i _ => Fin.elim0 i
  | _, _, .one A hA _ tail =>
      let B := higham11_5_exactRookOneActive A hA
      fun I J =>
        Fin.cases (Fin.cases (B 0 0) (fun _ => 0) J)
          (fun i => Fin.cases 0 (fun j => tail.D i j) J) I
  | _, _, .two A hA _ tail =>
      let B := higham11_5_exactRookTwoActive A hA
      fun I J =>
        Fin.cases
          (Fin.cases (B 0 0)
            (fun l => Fin.cases (B 0 (Fin.succ 0)) (fun _ => 0) l) J)
          (fun k => Fin.cases
            (Fin.cases (B (Fin.succ 0) 0)
              (fun l => Fin.cases (B (Fin.succ 0) (Fin.succ 0))
                (fun _ => 0) l) J)
            (fun i => Fin.cases 0
              (fun l => Fin.cases 0 (fun j => tail.D i j) l) J)
            k) I

@[simp] theorem Higham11ExactRookTrace.L_one_00 {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) (hA) (hsize) (tail) :
    (Higham11ExactRookTrace.one A hA hsize tail).L 0 0 = 1 := by
  simp [Higham11ExactRookTrace.L]

theorem higham11_5_exactRookOne_pivot_data {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A)
    (hsize : higham11_5_rookPivotSize higham11_1_bunchParlettAlpha A
      (higham11_5_exactRookTerminalIndex A hA) = PivotSize.one) :
    let B := higham11_5_exactRookOneActive A hA
    ∃ omega : ℝ, 0 ≤ omega ∧
      omega = higham11_5_rookColumnMax A
        (higham11_5_exactRookScalarIndex A hA) ∧
      higham11_1_bunchParlettAlpha * omega ≤ |B 0 0| ∧
      ∀ j : Fin n, |B j.succ 0| ≤ omega := by
  let i := higham11_5_exactRookTerminalIndex A hA
  let r := higham11_5_rookColumnArgmax A i
  let q := higham11_5_exactRookScalarIndex A hA
  let p := higham11_5_exactRookOnePerm A hA
  let B := higham11_5_exactRookOneActive A hA
  by_cases hfirst : |A i i| ≥ higham11_1_bunchParlettAlpha *
      higham11_5_rookColumnMax A i
  · have hq : q = i := by
      simp [q, higham11_5_exactRookScalarIndex, i, hfirst]
    have hp0 : p 0 = q := by
      change higham11_5_exactRookScalarIndex A hA = q
      rfl
    refine ⟨higham11_5_rookColumnMax A i,
      higham11_5_rookColumnMax_nonneg A i, ?_, ?_, ?_⟩
    · rw [show higham11_5_exactRookScalarIndex A hA = q by rfl, hq]
    · change higham11_1_bunchParlettAlpha *
        higham11_5_rookColumnMax A i ≤ |A (p 0) (p 0)|
      rw [hp0, hq]
      exact hfirst
    · intro j
      change |A (p j.succ) (p 0)| ≤ higham11_5_rookColumnMax A i
      rw [hp0, hq]
      have hne : p j.succ ≠ i := by
        intro h
        have hp : p j.succ = p 0 := by simpa [hp0, hq] using h
        have := p.injective hp
        simp at this
      simpa [hne] using higham11_5_rookColumnMax_spec A i (p j.succ)
  · have hsecond :
        |A r r| ≥ higham11_1_bunchParlettAlpha *
          higham11_5_rookColumnMax A r := by
      by_contra hnot
      have htwo : higham11_5_rookPivotSize higham11_1_bunchParlettAlpha A i =
          PivotSize.two := by
        simp [higham11_5_rookPivotSize, r, hfirst, hnot]
      rw [htwo] at hsize
      contradiction
    have hq : q = r := by
      simp [q, higham11_5_exactRookScalarIndex, i, r, hfirst]
    have hp0 : p 0 = q := by
      change higham11_5_exactRookScalarIndex A hA = q
      rfl
    refine ⟨higham11_5_rookColumnMax A r,
      higham11_5_rookColumnMax_nonneg A r, ?_, ?_, ?_⟩
    · rw [show higham11_5_exactRookScalarIndex A hA = q by rfl, hq]
    · change higham11_1_bunchParlettAlpha *
        higham11_5_rookColumnMax A r ≤ |A (p 0) (p 0)|
      rw [hp0, hq]
      exact hsecond
    · intro j
      change |A (p j.succ) (p 0)| ≤ higham11_5_rookColumnMax A r
      rw [hp0, hq]
      have hne : p j.succ ≠ r := by
        intro h
        have hp : p j.succ = p 0 := by simpa [hp0, hq] using h
        have := p.injective hp
        simp at this
      simpa [hne] using higham11_5_rookColumnMax_spec A r (p j.succ)

theorem higham11_5_exactRookTwo_pivot_data {n : ℕ}
    (A : Higham11RookMatrix (n + 2)) (hA : IsSymmetricFiniteMatrix A)
    (hsize : higham11_5_rookPivotSize higham11_1_bunchParlettAlpha A
      (higham11_5_exactRookTerminalIndex A hA) = PivotSize.two) :
    let B := higham11_5_exactRookTwoActive A hA
    ∃ omega : ℝ, 0 < omega ∧
      omega = higham11_5_rookColumnMax A
        (higham11_5_exactRookTerminalIndex A hA) ∧
      |B 0 0| ≤ higham11_1_bunchParlettAlpha * omega ∧
      |B (Fin.succ 0) (Fin.succ 0)| ≤
        higham11_1_bunchParlettAlpha * omega ∧
      B (Fin.succ 0) 0 ^ 2 = omega ^ 2 ∧
      ∀ j : Fin n,
        |B j.succ.succ 0| ≤ omega ∧
        |B j.succ.succ (Fin.succ 0)| ≤ omega := by
  let i := higham11_5_exactRookTerminalIndex A hA
  let r := higham11_5_rookColumnArgmax A i
  let omega := higham11_5_rookColumnMax A i
  let p := higham11_5_exactRookTwoPerm A hA
  let B := higham11_5_exactRookTwoActive A hA
  have homega : 0 < omega :=
    higham11_5_exactRookTwo_omega_pos A hA hsize
  have hstop : higham11_5_rookSearchStops higham11_1_bunchParlettAlpha A i :=
    higham11_5_exactRookTerminal_stops A hA
  obtain ⟨hii, hrr, heq, hriabs⟩ :=
    higham11_5_rook_twoByTwo_terminal_pivot_data
      higham11_1_bunchParlettAlpha A i hstop hsize homega
  have hp0 : p 0 = i :=
    higham11_5_exactRookTwoPerm_zero A hA hsize
  have hp1 : p 1 = r :=
    higham11_5_exactRookTwoPerm_one A hA
  refine ⟨omega, homega, rfl, ?_, ?_, ?_, ?_⟩
  · change |A (p 0) (p 0)| ≤ higham11_1_bunchParlettAlpha * omega
    rw [hp0]
    exact le_of_lt hii
  · change |A (p 1) (p 1)| ≤ higham11_1_bunchParlettAlpha * omega
    rw [hp1]
    exact le_of_lt hrr
  · change A (p 1) (p 0) ^ 2 = omega ^ 2
    rw [hp0, hp1, ← sq_abs, hriabs]
  · intro j
    have hpi : p j.succ.succ ≠ i := by
      intro h
      have hp : p j.succ.succ = p 0 := by simpa [hp0] using h
      have := p.injective hp
      simp at this
    have hpr : p j.succ.succ ≠ r := by
      intro h
      have hp : p j.succ.succ = p 1 := by simpa [hp1] using h
      have := p.injective hp
      have hval := congrArg Fin.val this
      simp at hval
    constructor
    · change |A (p j.succ.succ) (p 0)| ≤ omega
      rw [hp0]
      simpa [hpi] using higham11_5_rookColumnMax_spec A i (p j.succ.succ)
    · change |A (p j.succ.succ) (p 1)| ≤ omega
      rw [hp1]
      calc
        |A (p j.succ.succ) r| ≤ higham11_5_rookColumnMax A r := by
          simpa [hpr] using
            higham11_5_rookColumnMax_spec A r (p j.succ.succ)
        _ = omega := heq

theorem Higham11ExactRookTrace.multiplierOrigin
    {n : ℕ} {A : Higham11RookMatrix n} (t : Higham11ExactRookTrace A) :
    ∀ i j : Fin n,
      higham11_5_RookMultiplierOrigin higham11_1_bunchParlettAlpha
        (t.L i j) := by
  induction t with
  | nil A =>
      intro i
      exact Fin.elim0 i
  | @one n A hA hsize tail ih =>
      let B := higham11_5_exactRookOneActive A hA
      obtain ⟨omega, homega, _homega_eq, hpivot, hcolumn⟩ :=
        higham11_5_exactRookOne_pivot_data A hA hsize
      intro i j
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · simpa [Higham11ExactRookTrace.L] using
            (higham11_5_RookMultiplierOrigin.one
              (α := higham11_1_bunchParlettAlpha))
        · simpa [Higham11ExactRookTrace.L] using
            (higham11_5_RookMultiplierOrigin.zero
              (α := higham11_1_bunchParlettAlpha))
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · change higham11_5_RookMultiplierOrigin
            higham11_1_bunchParlettAlpha (B i.succ 0 / B 0 0)
          exact higham11_5_RookMultiplierOrigin.scalar
            (B 0 0) omega (B i.succ 0) homega hpivot (hcolumn i)
        · simpa [Higham11ExactRookTrace.L] using ih i j
  | @two n A hA hsize tail ih =>
      let B := higham11_5_exactRookTwoActive A hA
      obtain ⟨omega, homega, _homega_eq, he11, he22, he21, hcolumn⟩ :=
        higham11_5_exactRookTwo_pivot_data A hA hsize
      intro i j
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · simpa [Higham11ExactRookTrace.L] using
            (higham11_5_RookMultiplierOrigin.one
              (α := higham11_1_bunchParlettAlpha))
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · simpa [Higham11ExactRookTrace.L] using
              (higham11_5_RookMultiplierOrigin.zero
                (α := higham11_1_bunchParlettAlpha))
          · simpa [Higham11ExactRookTrace.L] using
              (higham11_5_RookMultiplierOrigin.zero
                (α := higham11_1_bunchParlettAlpha))
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · simpa [Higham11ExactRookTrace.L] using
              (higham11_5_RookMultiplierOrigin.zero
                (α := higham11_1_bunchParlettAlpha))
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
            · simpa [Higham11ExactRookTrace.L] using
                (higham11_5_RookMultiplierOrigin.one
                  (α := higham11_1_bunchParlettAlpha))
            · simpa [Higham11ExactRookTrace.L] using
                (higham11_5_RookMultiplierOrigin.zero
                  (α := higham11_1_bunchParlettAlpha))
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · change higham11_5_RookMultiplierOrigin
              higham11_1_bunchParlettAlpha
                (higham11_5_exactMultTwo B i 0)
            exact higham11_5_RookMultiplierOrigin.blockLeft
              (B i.succ.succ 0) (B i.succ.succ (Fin.succ 0))
              (B 0 0) (B (Fin.succ 0) (Fin.succ 0))
              (B (Fin.succ 0) 0) omega homega he11 he22 he21
              (hcolumn i).1 (hcolumn i).2
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
            · change higham11_5_RookMultiplierOrigin
                higham11_1_bunchParlettAlpha
                  (higham11_5_exactMultTwo B i 1)
              exact higham11_5_RookMultiplierOrigin.blockRight
                (B i.succ.succ 0) (B i.succ.succ (Fin.succ 0))
                (B 0 0) (B (Fin.succ 0) (Fin.succ 0))
                (B (Fin.succ 0) 0) omega homega he11 he22 he21
                (hcolumn i).1 (hcolumn i).2
            · simpa [Higham11ExactRookTrace.L] using ih i j

theorem Higham11ExactRookTrace.blockDiagonalSupport
    {n : ℕ} {A : Higham11RookMatrix n} (t : Higham11ExactRookTrace A) :
    higham11_5_RookBlockDiagonalSupport t.D
      (mixedSchedulePartner t.schedule) := by
  induction t with
  | nil A =>
      intro i
      exact Fin.elim0 i
  | @one n A hA hsize tail ih =>
      intro i j hji hjpartner
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · exact False.elim (hji rfl)
        · simp [Higham11ExactRookTrace.D]
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · simp [Higham11ExactRookTrace.D]
        · change tail.D i j = 0
          apply ih i j
          · intro h
            apply hji
            exact congrArg Fin.succ h
          · intro h
            apply hjpartner
            simpa [Higham11ExactRookTrace.schedule] using congrArg Fin.succ h
  | @two n A hA hsize tail ih =>
      intro i j hji hjpartner
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · exact False.elim (hji rfl)
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · exact False.elim (hjpartner rfl)
          · simp [Higham11ExactRookTrace.D]
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · exact False.elim (hjpartner rfl)
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
            · exact False.elim (hji rfl)
            · rfl
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · simp [Higham11ExactRookTrace.D]
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
            · rfl
            · change tail.D i j = 0
              apply ih i j
              · intro h
                apply hji
                exact congrArg Fin.succ (congrArg Fin.succ h)
              · intro h
                apply hjpartner
                simpa [Higham11ExactRookTrace.schedule] using
                  congrArg Fin.succ (congrArg Fin.succ h)

theorem higham11_5_rookColumnMax_le_of_entry_bound {n : ℕ}
    (A : Higham11RookMatrix n) (mu : ℝ)
    (hbound : ∀ i j : Fin n, |A i j| ≤ mu) (i : Fin n) :
    higham11_5_rookColumnMax A i ≤ mu := by
  unfold higham11_5_rookColumnMax
  split_ifs with h
  · simpa using (show 0 ≤ mu from (abs_nonneg (A i i)).trans (hbound i i))
  · exact hbound _ _

theorem higham11_5_exactRookOneActive_entry_bound {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A)
    (mu : ℝ) (hbound : ∀ i j, |A i j| ≤ mu) :
    ∀ i j, |higham11_5_exactRookOneActive A hA i j| ≤ mu := by
  intro i j
  exact hbound _ _

theorem higham11_5_exactRookTwoActive_entry_bound {n : ℕ}
    (A : Higham11RookMatrix (n + 2)) (hA : IsSymmetricFiniteMatrix A)
    (mu : ℝ) (hbound : ∀ i j, |A i j| ≤ mu) :
    ∀ i j, |higham11_5_exactRookTwoActive A hA i j| ≤ mu := by
  intro i j
  exact hbound _ _

theorem higham11_5_exactRookOne_schur_entry_bound {n : ℕ}
    (A : Higham11RookMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A)
    (hsize : higham11_5_rookPivotSize higham11_1_bunchParlettAlpha A
      (higham11_5_exactRookTerminalIndex A hA) = PivotSize.one)
    (mu : ℝ) (hmu : 0 ≤ mu) (hbound : ∀ i j, |A i j| ≤ mu) :
    ∀ i j : Fin n,
      |higham11_5_exactSchurOne
        (higham11_5_exactRookOneActive A hA) i j| ≤
      (1 + higham11_1_bunchParlettAlpha⁻¹) * mu := by
  let B := higham11_5_exactRookOneActive A hA
  have hB : ∀ i j, |B i j| ≤ mu :=
    higham11_5_exactRookOneActive_entry_bound A hA mu hbound
  obtain ⟨omega, homega, homega_eq, hpivot, hcolumn⟩ :=
    higham11_5_exactRookOne_pivot_data A hA hsize
  have homega_le : omega ≤ mu := by
    rw [homega_eq]
    exact higham11_5_rookColumnMax_le_of_entry_bound A mu hbound _
  intro i j
  change |B i.succ j.succ - B i.succ 0 * B j.succ 0 / B 0 0| ≤
    (1 + higham11_1_bunchParlettAlpha⁻¹) * mu
  by_cases homega_zero : omega = 0
  · have hci : B i.succ 0 = 0 := by
      apply abs_eq_zero.mp
      exact le_antisymm ((hcolumn i).trans_eq homega_zero) (abs_nonneg _)
    have hcj : B j.succ 0 = 0 := by
      apply abs_eq_zero.mp
      exact le_antisymm ((hcolumn j).trans_eq homega_zero) (abs_nonneg _)
    rw [hci, hcj]
    simp only [zero_mul, zero_div, sub_zero]
    exact (hB i.succ j.succ).trans (le_mul_of_one_le_left hmu (by
      have hα : 0 < higham11_1_bunchParlettAlpha := by
        simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
      exact le_add_of_nonneg_right (inv_nonneg.mpr (le_of_lt hα))))
  · have homega_pos : 0 < omega := lt_of_le_of_ne homega (Ne.symm homega_zero)
    have hα : 0 < higham11_1_bunchParlettAlpha := by
      simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
    have hmult : |B i.succ 0 / B 0 0| ≤
        1 / higham11_1_bunchParlettAlpha :=
      higham11_1_oneByOne_multiplier_bound
        (B i.succ 0) (B 0 0) omega higham11_1_bunchParlettAlpha
        hα homega_pos (hcolumn i) hpivot
    have hcorr : |B i.succ 0 * B j.succ 0 / B 0 0| ≤
        higham11_1_bunchParlettAlpha⁻¹ * mu := by
      rw [show B i.succ 0 * B j.succ 0 / B 0 0 =
          (B i.succ 0 / B 0 0) * B j.succ 0 by ring, abs_mul]
      calc
        |B i.succ 0 / B 0 0| * |B j.succ 0| ≤
            (1 / higham11_1_bunchParlettAlpha) * omega :=
          mul_le_mul hmult (hcolumn j) (abs_nonneg _)
            (by positivity)
        _ ≤ (1 / higham11_1_bunchParlettAlpha) * mu :=
          mul_le_mul_of_nonneg_left homega_le (by positivity)
        _ = higham11_1_bunchParlettAlpha⁻¹ * mu := by
          rw [one_div]
    calc
      |B i.succ j.succ - B i.succ 0 * B j.succ 0 / B 0 0| ≤
          |B i.succ j.succ| + |B i.succ 0 * B j.succ 0 / B 0 0| :=
        abs_sub _ _
      _ ≤ mu + higham11_1_bunchParlettAlpha⁻¹ * mu :=
        add_le_add (hB i.succ j.succ) hcorr
      _ = (1 + higham11_1_bunchParlettAlpha⁻¹) * mu := by ring

theorem higham11_5_exactRookTwo_schur_entry_bound {n : ℕ}
    (A : Higham11RookMatrix (n + 2)) (hA : IsSymmetricFiniteMatrix A)
    (hsize : higham11_5_rookPivotSize higham11_1_bunchParlettAlpha A
      (higham11_5_exactRookTerminalIndex A hA) = PivotSize.two)
    (mu : ℝ) (_hmu : 0 ≤ mu) (hbound : ∀ i j, |A i j| ≤ mu) :
    ∀ i j : Fin n,
      |higham11_5_exactSchurTwo
        (higham11_5_exactRookTwoActive A hA) i j| ≤
      (1 + higham11_1_bunchParlettAlpha⁻¹) ^ 2 * mu := by
  let B := higham11_5_exactRookTwoActive A hA
  have hB : ∀ i j, |B i j| ≤ mu :=
    higham11_5_exactRookTwoActive_entry_bound A hA mu hbound
  obtain ⟨omega, homega, homega_eq, he11, he22, he21, hcolumn⟩ :=
    higham11_5_exactRookTwo_pivot_data A hA hsize
  have homega_le : omega ≤ mu := by
    rw [homega_eq]
    exact higham11_5_rookColumnMax_le_of_entry_bound A mu hbound _
  have hα : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  have hα1 : higham11_1_bunchParlettAlpha < 1 := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one
  let K : ℝ :=
    ((1 - higham11_1_bunchParlettAlpha ^ 2) * omega)⁻¹
  have hden : 0 <
      (1 - higham11_1_bunchParlettAlpha ^ 2) * omega := by
    apply mul_pos
    · nlinarith
    · exact homega
  have hK : (1 - higham11_1_bunchParlettAlpha ^ 2) * omega * K = 1 :=
    mul_inv_cancel₀ (ne_of_gt hden)
  have hrowsum : ∀ i : Fin n,
      |higham11_5_exactMultTwo B i 0| +
          |higham11_5_exactMultTwo B i 1| ≤
        2 / (1 - higham11_1_bunchParlettAlpha) := by
    intro i
    simpa [higham11_5_exactMultTwo_zero,
      higham11_5_exactMultTwo_one] using
      higham11_4_twoByTwo_multiplier_row_sum_bound_of_block
        (B i.succ.succ 0) (B i.succ.succ (Fin.succ 0))
        (B 0 0) (B (Fin.succ 0) (Fin.succ 0))
        (B (Fin.succ 0) 0) omega
        (higham11_1_bunchParlettAlpha * omega)
        higham11_1_bunchParlettAlpha K
        (mul_nonneg (le_of_lt hα) (le_of_lt homega))
        (le_of_lt hα) hα1 homega he11 he22 he21 (le_refl _) hK
        (hcolumn i).1 (hcolumn i).2
  intro i j
  let correction :=
    higham11_5_exactMultTwo B i 0 * B j.succ.succ 0 +
      higham11_5_exactMultTwo B i 1 * B j.succ.succ (Fin.succ 0)
  have hcoeff0 : 0 ≤ 2 / (1 - higham11_1_bunchParlettAlpha) := by
    exact div_nonneg (by norm_num) (le_of_lt (sub_pos.mpr hα1))
  have hcorr : |correction| ≤
      (2 / (1 - higham11_1_bunchParlettAlpha)) * mu := by
    calc
      |correction| ≤
          |higham11_5_exactMultTwo B i 0| * |B j.succ.succ 0| +
            |higham11_5_exactMultTwo B i 1| *
              |B j.succ.succ (Fin.succ 0)| := by
        dsimp [correction]
        simpa [abs_mul] using abs_add_le
          (higham11_5_exactMultTwo B i 0 * B j.succ.succ 0)
          (higham11_5_exactMultTwo B i 1 * B j.succ.succ (Fin.succ 0))
      _ ≤ |higham11_5_exactMultTwo B i 0| * omega +
          |higham11_5_exactMultTwo B i 1| * omega :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hcolumn j).1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hcolumn j).2 (abs_nonneg _))
      _ = (|higham11_5_exactMultTwo B i 0| +
          |higham11_5_exactMultTwo B i 1|) * omega := by ring
      _ ≤ (2 / (1 - higham11_1_bunchParlettAlpha)) * omega :=
        mul_le_mul_of_nonneg_right (hrowsum i) (le_of_lt homega)
      _ ≤ (2 / (1 - higham11_1_bunchParlettAlpha)) * mu :=
        mul_le_mul_of_nonneg_left homega_le hcoeff0
  change |B i.succ.succ j.succ.succ - correction| ≤
    (1 + higham11_1_bunchParlettAlpha⁻¹) ^ 2 * mu
  calc
    |B i.succ.succ j.succ.succ - correction| ≤
        |B i.succ.succ j.succ.succ| + |correction| := abs_sub _ _
    _ ≤ mu + (2 / (1 - higham11_1_bunchParlettAlpha)) * mu :=
      add_le_add (hB i.succ.succ j.succ.succ) hcorr
    _ = (1 + higham11_1_bunchParlettAlpha⁻¹) ^ 2 * mu := by
      rw [show higham11_1_bunchParlettAlpha⁻¹ =
        1 / higham11_1_bunchParlettAlpha by simp]
      rw [higham11_1_growth_balance]
      ring

theorem higham11_5_rookGrowthFactor_one_le :
    1 ≤ 1 + higham11_1_bunchParlettAlpha⁻¹ := by
  have hα : 0 ≤ higham11_1_bunchParlettAlpha := by
    exact le_of_lt (by
      simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
  exact le_add_of_nonneg_right (inv_nonneg.mpr hα)

theorem Higham11ExactRookTrace.D_entry_bound
    {n : ℕ} {A : Higham11RookMatrix n}
    (t : Higham11ExactRookTrace A) :
    ∀ (mu : ℝ), 0 ≤ mu → (∀ i j : Fin n, |A i j| ≤ mu) →
      ∀ i j : Fin n,
        |t.D i j| ≤
          (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1) * mu := by
  induction t with
  | nil A =>
      intro mu hmu hbound i
      exact Fin.elim0 i
  | @one n A hA hsize tail ih =>
      intro mu hmu hbound i j
      let B := higham11_5_exactRookOneActive A hA
      have hB : ∀ i j, |B i j| ≤ mu :=
        higham11_5_exactRookOneActive_entry_bound A hA mu hbound
      have hfactor : 1 ≤ 1 + higham11_1_bunchParlettAlpha⁻¹ :=
        higham11_5_rookGrowthFactor_one_le
      have hmu_le : mu ≤
          (1 + higham11_1_bunchParlettAlpha⁻¹) ^ n * mu := by
        exact le_mul_of_one_le_left hmu (one_le_pow₀ hfactor)
      have htarget_nonneg : 0 ≤
          (1 + higham11_1_bunchParlettAlpha⁻¹) ^ n * mu :=
        hmu.trans hmu_le
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · simpa [Higham11ExactRookTrace.D, B] using
            (hB (0 : Fin (n + 1)) (0 : Fin (n + 1))).trans hmu_le
        · simpa [Higham11ExactRookTrace.D] using htarget_nonneg
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · simpa [Higham11ExactRookTrace.D] using htarget_nonneg
        · have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
          calc
            |(Higham11ExactRookTrace.one A hA hsize tail).D i.succ j.succ| =
                |tail.D i j| := by rfl
            _ ≤ (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1) *
                ((1 + higham11_1_bunchParlettAlpha⁻¹) * mu) :=
              ih ((1 + higham11_1_bunchParlettAlpha⁻¹) * mu)
                (mul_nonneg
                  (le_trans (by norm_num) hfactor) hmu)
                (higham11_5_exactRookOne_schur_entry_bound
                  A hA hsize mu hmu hbound) i j
            _ = (1 + higham11_1_bunchParlettAlpha⁻¹) ^
                  ((n - 1) + 1) * mu := by
              rw [pow_succ]
              ring
            _ = (1 + higham11_1_bunchParlettAlpha⁻¹) ^ n * mu := by
              rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
            _ = (1 + higham11_1_bunchParlettAlpha⁻¹) ^
                  ((n + 1) - 1) * mu := by simp
  | @two n A hA hsize tail ih =>
      intro mu hmu hbound i j
      let B := higham11_5_exactRookTwoActive A hA
      have hB : ∀ i j, |B i j| ≤ mu :=
        higham11_5_exactRookTwoActive_entry_bound A hA mu hbound
      have hfactor : 1 ≤ 1 + higham11_1_bunchParlettAlpha⁻¹ :=
        higham11_5_rookGrowthFactor_one_le
      have hmu_le : mu ≤
          (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n + 1) * mu := by
        exact le_mul_of_one_le_left hmu (one_le_pow₀ hfactor)
      have htarget_nonneg : 0 ≤
          (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n + 1) * mu :=
        hmu.trans hmu_le
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · simpa [Higham11ExactRookTrace.D, B] using
            (hB (0 : Fin (n + 2)) (0 : Fin (n + 2))).trans hmu_le
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · simpa [Higham11ExactRookTrace.D, B] using
              (hB (0 : Fin (n + 2)) (Fin.succ 0)).trans hmu_le
          · simpa [Higham11ExactRookTrace.D] using htarget_nonneg
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · simpa [Higham11ExactRookTrace.D, B] using
              (hB (Fin.succ 0) (0 : Fin (n + 2))).trans hmu_le
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
            · simpa [Higham11ExactRookTrace.D, B] using
                (hB (Fin.succ 0) (Fin.succ 0)).trans hmu_le
            · change |0| ≤
                (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n + 1) * mu
              simpa using htarget_nonneg
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · simpa [Higham11ExactRookTrace.D] using htarget_nonneg
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
            · change |0| ≤
                (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n + 1) * mu
              simpa using htarget_nonneg
            · have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
              calc
                |(Higham11ExactRookTrace.two A hA hsize tail).D
                    i.succ.succ j.succ.succ| = |tail.D i j| := by rfl
                _ ≤ (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1) *
                    ((1 + higham11_1_bunchParlettAlpha⁻¹) ^ 2 * mu) :=
                  ih ((1 + higham11_1_bunchParlettAlpha⁻¹) ^ 2 * mu)
                    (mul_nonneg (pow_nonneg
                      (le_trans (by norm_num) hfactor) _) hmu)
                    (higham11_5_exactRookTwo_schur_entry_bound
                      A hA hsize mu hmu hbound) i j
                _ = (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n + 1) * mu := by
                  rw [← mul_assoc, ← pow_add]
                  congr 2
                  omega
                _ = (1 + higham11_1_bunchParlettAlpha⁻¹) ^
                      ((n + 2) - 1) * mu := by simp

/-- The exact bounded-search trace supplies Higham's Algorithm 11.5 property
(3) without any caller-provided origin, support, or growth certificate. -/
theorem Higham11ExactRookTrace.theorem11_4_product_bound
    {n : ℕ} {A : Higham11RookMatrix n}
    (t : Higham11ExactRookTrace A) (hn : 0 < n)
    (Amax : ℝ) (hAmax : 0 ≤ Amax)
    (hbound : ∀ i j : Fin n, |A i j| ≤ Amax) :
    higham11_4_bunchKaufmanMaxEntryProductBound n
      (higham11_4_bunchKaufmanProductMax n hn t.L t.D)
      ((1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1)) Amax := by
  apply higham11_5_rook_theorem11_4_product_bound hn t.L t.D
    (mixedSchedulePartner t.schedule)
    ((1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1)) Amax
  · exact pow_nonneg
      (le_trans (by norm_num) higham11_5_rookGrowthFactor_one_le) _
  · exact hAmax
  · exact t.multiplierOrigin
  · exact t.blockDiagonalSupport
  · exact t.D_entry_bound Amax hAmax hbound

/-- Every symmetric matrix has a literal bounded-search rook trace whose exact
factors satisfy the printed Theorem 11.4 product certificate. -/
theorem higham11_5_exists_exactRookTrace_theorem11_4_product_bound
    {n : ℕ} (hn : 0 < n) (A : Higham11RookMatrix n)
    (hA : IsSymmetricFiniteMatrix A)
    (Amax : ℝ) (hAmax : 0 ≤ Amax)
    (hbound : ∀ i j : Fin n, |A i j| ≤ Amax) :
    ∃ t : Higham11ExactRookTrace A,
      higham11_4_bunchKaufmanMaxEntryProductBound n
        (higham11_4_bunchKaufmanProductMax n hn t.L t.D)
        ((1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1)) Amax := by
  let t : Higham11ExactRookTrace A :=
    Classical.choice (higham11_5_nonempty_exactRookTrace A hA)
  exact ⟨t, t.theorem11_4_product_bound hn Amax hAmax hbound⟩

/-- Final Theorem 11.4 handoff for a trace-produced exact rook factor pair.
The remaining input is precisely the generic block-LDLᵀ rounding certificate
from Chapter 11.3; all rook-specific numerical certificates are discharged by
the bounded-search trace. -/
theorem Higham11ExactRookTrace.theorem11_4_backward_error
    {n : ℕ} {Atrace : Higham11RookMatrix n}
    (t : Higham11ExactRookTrace Atrace) (hn : 0 < n)
    (A : Higham11RookMatrix n) (σ : Fin n → Fin n)
    (ε Amax : ℝ) (hε : 0 ≤ ε) (hAmax : 0 ≤ Amax)
    (hbound : ∀ i j : Fin n, |Atrace i j| ≤ Amax)
    (hbe : BlockLDLTBackwardError n A t.L t.D σ ε) :
    ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        |ΔA1 i j| ≤ ε *
          (36 * (n : ℝ) *
            ((1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1)) * Amax)) ∧
      (∀ i j : Fin n,
        |ΔA2 i j| ≤ ε *
          (36 * (n : ℝ) *
            ((1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1)) * Amax)) ∧
      (∀ i j : Fin n,
        ∑ k₁ : Fin n, ∑ k₂ : Fin n,
          t.L i k₁ * t.D k₁ k₂ * t.L j k₂ =
            A (σ i) (σ j) + ΔA1 i j) := by
  exact higham11_5_rook_theorem11_4_backward_error hn A t.L t.D σ
    (mixedSchedulePartner t.schedule) ε
    ((1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1)) Amax
    hε (pow_nonneg
      (le_trans (by norm_num) higham11_5_rookGrowthFactor_one_le) _)
    hAmax hbe t.multiplierOrigin
    t.blockDiagonalSupport (t.D_entry_bound Amax hAmax hbound)


end Higham11RookExecutorAdapter
end NumStability
