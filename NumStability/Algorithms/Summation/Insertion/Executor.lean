-- Algorithms/Summation/Insertion/Executor.lean

import NumStability.Algorithms.Summation.Insertion.ActiveList
import NumStability.FloatingPoint.Model

namespace NumStability

/-!
# List executor for insertion summation

This reusable layer implements the rounded remove/add/reinsert loop, proves its
termination and active-list invariants, and exposes `fl_insertionSumList`.
-/

/-- One insertion-summation step: remove the two smallest active
entries, add them in floating-point arithmetic, and reinsert the new sum into
the remaining ordered active list.  Lists of length zero or one are already
terminal. -/
noncomputable def insertionStep (fp : FPModel) : List ℝ → List ℝ
  | a :: b :: rest => insertIncreasingAbs (fp.fl_add a b) rest
  | xs => xs

/-- The two-head insertion step unfolds to the displayed remove/add/reinsert
operation. -/
theorem insertionStep_cons_cons (fp : FPModel) (a b : ℝ)
    (rest : List ℝ) :
    insertionStep fp (a :: b :: rest) =
      insertIncreasingAbs (fp.fl_add a b) rest := by
  rfl

/-- A nonterminal insertion step reduces the active-list length by one. -/
theorem insertionStep_length_cons_cons (fp : FPModel) (a b : ℝ)
    (rest : List ℝ) :
    (insertionStep fp (a :: b :: rest)).length = rest.length + 1 := by
  simp [insertionStep_cons_cons, insertIncreasingAbs_length]

/-- A nonempty active list remains nonempty after one insertion step. -/
theorem insertionStep_ne_nil_of_ne_nil (fp : FPModel) :
    ∀ {xs : List ℝ}, xs ≠ [] → insertionStep fp xs ≠ []
  | [], hne => False.elim (hne rfl)
  | [_], _ => by simp [insertionStep]
  | a :: b :: rest, _ => by
      simpa [insertionStep_cons_cons] using
        insertIncreasingAbs_ne_nil (fp.fl_add a b) rest

/-- One nonterminal insertion step preserves the increasing absolute-value
active-list invariant. -/
theorem insertionStep_preserves_increasingAbs_cons_cons (fp : FPModel)
    (a b : ℝ) (rest : List ℝ)
    (hsorted : IncreasingAbsList (a :: b :: rest)) :
    IncreasingAbsList (insertionStep fp (a :: b :: rest)) := by
  rcases hsorted with ⟨_, htail⟩
  exact insertIncreasingAbs_preserves (fp.fl_add a b) rest
    (IncreasingAbsList.tail htail)

/-- Active list after at most `fuel` insertion-summation steps.  Supplying
`xs.length` as fuel gives the full source loop. -/
noncomputable def insertionActiveAfter (fp : FPModel) :
    ℕ → List ℝ → List ℝ
  | 0, xs => xs
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | fuel + 1, a :: b :: rest =>
      insertionActiveAfter fp fuel (insertionStep fp (a :: b :: rest))

/-- Repeated insertion steps preserve the increasing absolute-value active-list
invariant. -/
theorem insertionActiveAfter_preserves_increasingAbs (fp : FPModel) :
    ∀ fuel xs,
      IncreasingAbsList xs →
        IncreasingAbsList (insertionActiveAfter fp fuel xs) := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs hsorted
      simpa [insertionActiveAfter] using hsorted
  | succ fuel ih =>
      intro xs hsorted
      cases xs with
      | nil => simp [insertionActiveAfter, IncreasingAbsList]
      | cons a xs =>
          cases xs with
          | nil => simp [insertionActiveAfter, IncreasingAbsList]
          | cons b rest =>
              have hstep :=
                insertionStep_preserves_increasingAbs_cons_cons fp a b rest
                  hsorted
              simpa [insertionActiveAfter] using
                ih (insertionStep fp (a :: b :: rest)) hstep

/-- Repeated insertion steps preserve nonemptiness of the active list. -/
theorem insertionActiveAfter_ne_nil_of_ne_nil (fp : FPModel) :
    ∀ fuel {xs : List ℝ},
      xs ≠ [] → insertionActiveAfter fp fuel xs ≠ [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs hne
      simpa [insertionActiveAfter] using hne
  | succ fuel ih =>
      intro xs hne
      cases xs with
      | nil => exact False.elim (hne rfl)
      | cons a xs =>
          cases xs with
          | nil => simp [insertionActiveAfter]
          | cons b rest =>
              have hstep :
                  insertionStep fp (a :: b :: rest) ≠ [] :=
                insertionStep_ne_nil_of_ne_nil fp (by simp)
              simpa [insertionActiveAfter] using ih hstep

/-- If the available fuel is at least one less than the active-list length,
then repeated insertion steps reach a terminal active list of length at most
one. -/
theorem insertionActiveAfter_length_le_one_of_length_le_succ
    (fp : FPModel) :
    ∀ fuel xs,
      xs.length ≤ fuel + 1 →
        (insertionActiveAfter fp fuel xs).length ≤ 1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs hlen
      cases xs with
      | nil => simp [insertionActiveAfter]
      | cons a xs =>
          cases xs with
          | nil => simp [insertionActiveAfter]
          | cons b rest =>
              simp at hlen
  | succ fuel ih =>
      intro xs hlen
      cases xs with
      | nil => simp [insertionActiveAfter]
      | cons a xs =>
          cases xs with
          | nil => simp [insertionActiveAfter]
          | cons b rest =>
              have hstepLen :
                  (insertionStep fp (a :: b :: rest)).length =
                    rest.length + 1 :=
                insertionStep_length_cons_cons fp a b rest
              have hnext :
                  (insertionStep fp (a :: b :: rest)).length ≤ fuel + 1 := by
                rw [hstepLen]
                simpa using hlen
              simpa [insertionActiveAfter] using
                ih (insertionStep fp (a :: b :: rest)) hnext

/-- Supplying `xs.length` fuel is enough for the general source-level
insertion loop to terminate in an active list of length zero or one. -/
theorem insertionActiveAfter_full_length_le_one (fp : FPModel)
    (xs : List ℝ) :
    (insertionActiveAfter fp xs.length xs).length ≤ 1 := by
  exact insertionActiveAfter_length_le_one_of_length_le_succ fp
    xs.length xs (Nat.le_succ xs.length)

/-- For nonempty input, full-fuel insertion summation terminates in exactly
one active value. -/
theorem insertionActiveAfter_full_length_eq_one_of_ne_nil (fp : FPModel)
    {xs : List ℝ} (hne : xs ≠ []) :
    (insertionActiveAfter fp xs.length xs).length = 1 := by
  have hle := insertionActiveAfter_full_length_le_one fp xs
  have hterminal_ne :
      insertionActiveAfter fp xs.length xs ≠ [] :=
    insertionActiveAfter_ne_nil_of_ne_nil fp xs.length hne
  have hpos :
      0 < (insertionActiveAfter fp xs.length xs).length := by
    cases hterminal :
        insertionActiveAfter fp xs.length xs with
    | nil => exact False.elim (hterminal_ne hterminal)
    | cons y ys => simp
  exact Nat.le_antisymm hle (Nat.succ_le_of_lt hpos)

/-- For nonempty input, the full-fuel insertion loop exposes a unique final
active value as a singleton list. -/
theorem insertionActiveAfter_full_eq_singleton_of_ne_nil (fp : FPModel)
    {xs : List ℝ} (hne : xs ≠ []) :
    ∃ y : ℝ, insertionActiveAfter fp xs.length xs = [y] := by
  have hlen := insertionActiveAfter_full_length_eq_one_of_ne_nil fp hne
  cases hterminal : insertionActiveAfter fp xs.length xs with
  | nil =>
      simp [hterminal] at hlen
  | cons y ys =>
      cases ys with
      | nil => exact ⟨y, rfl⟩
      | cons z zs =>
          simp [hterminal] at hlen

/-- General insertion summation on an already sorted active list:
iterate remove/add/reinsert until the active list is terminal, returning the
remaining active value (or zero for the empty input). -/
noncomputable def fl_insertionSumList (fp : FPModel) (xs : List ℝ) : ℝ :=
  match insertionActiveAfter fp xs.length xs with
  | [] => 0
  | y :: _ => y

/-- If the full insertion loop ends in `[y]`, the insertion sum
returns `y`. -/
theorem fl_insertionSumList_eq_of_activeAfter_eq_singleton (fp : FPModel)
    {xs : List ℝ} {y : ℝ}
    (hterminal : insertionActiveAfter fp xs.length xs = [y]) :
    fl_insertionSumList fp xs = y := by
  simp [fl_insertionSumList, hterminal]

/-- On nonempty input, the insertion sum is the unique singleton
value produced by the full insertion loop. -/
theorem fl_insertionSumList_eq_terminal_singleton_of_ne_nil (fp : FPModel)
    {xs : List ℝ} (hne : xs ≠ []) :
    ∃ y : ℝ,
      insertionActiveAfter fp xs.length xs = [y] ∧
        fl_insertionSumList fp xs = y := by
  rcases insertionActiveAfter_full_eq_singleton_of_ne_nil fp hne with
    ⟨y, hterminal⟩
  exact ⟨y, hterminal,
    fl_insertionSumList_eq_of_activeAfter_eq_singleton fp hterminal⟩

/-- Empty insertion summation returns zero. -/
theorem fl_insertionSumList_nil (fp : FPModel) :
    fl_insertionSumList fp [] = 0 := by
  rfl

/-- A singleton active list is already terminal. -/
theorem fl_insertionSumList_singleton (fp : FPModel) (x : ℝ) :
    fl_insertionSumList fp [x] = x := by
  rfl

/-- On two entries, insertion summation performs one rounded addition. -/
theorem fl_insertionSumList_pair (fp : FPModel) (x y : ℝ) :
    fl_insertionSumList fp [x, y] = fp.fl_add x y := by
  simp [fl_insertionSumList, insertionActiveAfter, insertionStep,
    insertIncreasingAbs]

end NumStability
