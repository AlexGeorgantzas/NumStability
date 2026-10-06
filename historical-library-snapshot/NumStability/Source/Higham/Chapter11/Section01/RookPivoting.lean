import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT
import NumStability.Source.Higham.Chapter11.Section01.CompletePivoting

/-!
# Higham Chapter 11: RookPivoting

Canonical owner materialized from the reviewed Chapter 11 route contract.
-/

namespace NumStability

open scoped BigOperators

/-! ## §11.1.3 Rook pivoting -/

/-- **Algorithm 11.5** source decision predicate for symmetric rook pivoting. -/
abbrev higham11_5_SymmetricRookFirstPivotChoice
    (α a11 arr ω1 ωr : ℝ) (s : PivotSize) : Prop :=
  SymmetricRookFirstPivotChoice α a11 arr ω1 ωr s

/-- The deterministic row index `r` selected by one pass of Algorithm 11.5:
it maximizes the magnitude of the off-diagonal entries in column `i`.
The diagonal is replaced by zero, so the definition also covers a zero column. -/
noncomputable def higham11_5_rookColumnArgmax {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) : Fin n :=
  (Finset.exists_max_image Finset.univ
    (fun j : Fin n => |if j = i then 0 else A j i|)
    ⟨i, Finset.mem_univ i⟩).choose

/-- `ωᵢ`, the largest off-diagonal magnitude in column `i`. -/
noncomputable def higham11_5_rookColumnMax {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  |if higham11_5_rookColumnArgmax A i = i then 0
    else A (higham11_5_rookColumnArgmax A i) i|

theorem higham11_5_rookColumnMax_spec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i j : Fin n) :
    |if j = i then 0 else A j i| ≤ higham11_5_rookColumnMax A i := by
  exact ((Finset.exists_max_image Finset.univ
    (fun j : Fin n => |if j = i then 0 else A j i|)
    ⟨i, Finset.mem_univ i⟩).choose_spec.2 j (Finset.mem_univ j))

/-- On a symmetric matrix, following the row/column argmax cannot decrease
`ω`: the selected entry in column `i` occurs, by symmetry, in the next column. -/
theorem higham11_5_rookColumnMax_le_next {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hA : IsSymmetricFiniteMatrix A) (i : Fin n) :
    higham11_5_rookColumnMax A i ≤
      higham11_5_rookColumnMax A (higham11_5_rookColumnArgmax A i) := by
  by_cases hri : higham11_5_rookColumnArgmax A i = i
  · rw [hri]
  · have hspec := higham11_5_rookColumnMax_spec A
      (higham11_5_rookColumnArgmax A i) i
    rw [if_neg (Ne.symm hri)] at hspec
    rw [hA i (higham11_5_rookColumnArgmax A i)] at hspec
    simpa [higham11_5_rookColumnMax, hri] using hspec

/-- The recursive index schedule traversed by Algorithm 11.5's repeat loop. -/
noncomputable def higham11_5_rookSearchPath {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i₀ : Fin n) : ℕ → Fin n
  | 0 => i₀
  | k + 1 => higham11_5_rookColumnArgmax A
      (higham11_5_rookSearchPath A i₀ k)

/-- The three source stopping tests at a current rook-search index: accept the
current diagonal, accept the next diagonal, or accept their intersection as a
`2×2` rook pivot. -/
def higham11_5_rookSearchStops {n : ℕ} (α : ℝ)
    (A : Fin n → Fin n → ℝ) (i : Fin n) : Prop :=
  |A i i| ≥ α * higham11_5_rookColumnMax A i ∨
  |A (higham11_5_rookColumnArgmax A i) (higham11_5_rookColumnArgmax A i)| ≥
    α * higham11_5_rookColumnMax A (higham11_5_rookColumnArgmax A i) ∨
  higham11_5_rookColumnMax A i =
    higham11_5_rookColumnMax A (higham11_5_rookColumnArgmax A i)

/-- **Algorithm 11.5 termination.**  If no stopping test fires, symmetry and
the argmax property make the column maxima strictly increase.  More than `n`
such states would inject `Fin (n+1)` into `Fin n`, so the recursive rook search
must choose a pivot after at most `n` passes. -/
theorem higham11_5_rookSearchStops_exists {n : ℕ} (α : ℝ)
    (A : Fin n → Fin n → ℝ) (hA : IsSymmetricFiniteMatrix A) (i₀ : Fin n) :
    ∃ k, k ≤ n ∧
      higham11_5_rookSearchStops α A (higham11_5_rookSearchPath A i₀ k) := by
  by_contra hnone
  push_neg at hnone
  have hlt : ∀ k, k < n →
      higham11_5_rookColumnMax A (higham11_5_rookSearchPath A i₀ k) <
        higham11_5_rookColumnMax A (higham11_5_rookSearchPath A i₀ (k + 1)) := by
    intro k hk
    have hnostop := hnone k (Nat.le_of_lt hk)
    have hne :
        higham11_5_rookColumnMax A (higham11_5_rookSearchPath A i₀ k) ≠
          higham11_5_rookColumnMax A
            (higham11_5_rookColumnArgmax A (higham11_5_rookSearchPath A i₀ k)) := by
      intro heq
      exact hnostop (Or.inr (Or.inr heq))
    rw [higham11_5_rookSearchPath]
    exact lt_of_le_of_ne
      (higham11_5_rookColumnMax_le_next A hA
        (higham11_5_rookSearchPath A i₀ k)) hne
  let f : Fin (n + 1) → Fin n := fun k => higham11_5_rookSearchPath A i₀ k.val
  let g : Fin (n + 1) → ℝ := fun k => higham11_5_rookColumnMax A (f k)
  have hg : StrictMono g := by
    rw [Fin.strictMono_iff_lt_succ]
    intro k
    change higham11_5_rookColumnMax A (higham11_5_rookSearchPath A i₀ k.val) <
      higham11_5_rookColumnMax A (higham11_5_rookSearchPath A i₀ (k.val + 1))
    exact hlt k.val k.isLt
  have hf : Function.Injective f := by
    intro a b hab
    apply hg.injective
    simp only [g, hab]
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega

/-- The first successful pass of the bounded Algorithm 11.5 search. -/
noncomputable def higham11_5_rookTerminalStep {n : ℕ} (α : ℝ)
    (A : Fin n → Fin n → ℝ) (hA : IsSymmetricFiniteMatrix A) (i₀ : Fin n) : ℕ := by
  classical
  exact Nat.find (higham11_5_rookSearchStops_exists α A hA i₀)

theorem higham11_5_rookTerminalStep_le {n : ℕ} (α : ℝ)
    (A : Fin n → Fin n → ℝ) (hA : IsSymmetricFiniteMatrix A) (i₀ : Fin n) :
    higham11_5_rookTerminalStep α A hA i₀ ≤ n := by
  classical
  exact (Nat.find_spec (higham11_5_rookSearchStops_exists α A hA i₀)).1

theorem higham11_5_rookTerminalStep_stops {n : ℕ} (α : ℝ)
    (A : Fin n → Fin n → ℝ) (hA : IsSymmetricFiniteMatrix A) (i₀ : Fin n) :
    higham11_5_rookSearchStops α A
      (higham11_5_rookSearchPath A i₀
        (higham11_5_rookTerminalStep α A hA i₀)) := by
  classical
  exact (Nat.find_spec (higham11_5_rookSearchStops_exists α A hA i₀)).2

/-- Pivot size selected at a successful rook-search state. -/
noncomputable def higham11_5_rookPivotSize {n : ℕ} (α : ℝ)
    (A : Fin n → Fin n → ℝ) (i : Fin n) : PivotSize :=
  if |A i i| ≥ α * higham11_5_rookColumnMax A i then PivotSize.one
  else if |A (higham11_5_rookColumnArgmax A i) (higham11_5_rookColumnArgmax A i)| ≥
      α * higham11_5_rookColumnMax A (higham11_5_rookColumnArgmax A i)
    then PivotSize.one
  else PivotSize.two

theorem higham11_5_rookSearchStops_choice {n : ℕ} (α : ℝ)
    (A : Fin n → Fin n → ℝ) (i : Fin n)
    (hstop : higham11_5_rookSearchStops α A i) :
    higham11_5_SymmetricRookFirstPivotChoice α (A i i)
      (A (higham11_5_rookColumnArgmax A i) (higham11_5_rookColumnArgmax A i))
      (higham11_5_rookColumnMax A i)
      (higham11_5_rookColumnMax A (higham11_5_rookColumnArgmax A i))
      (higham11_5_rookPivotSize α A i) := by
  rcases hstop with hfirst | hsecond | hequal
  · exact Or.inl ⟨hfirst, by simp [higham11_5_rookPivotSize, hfirst]⟩
  · exact Or.inr (Or.inl ⟨hsecond, by
      simp [higham11_5_rookPivotSize, hsecond]⟩)
  · by_cases hfirst : |A i i| ≥ α * higham11_5_rookColumnMax A i
    · exact Or.inl ⟨hfirst, by simp [higham11_5_rookPivotSize, hfirst]⟩
    · by_cases hsecond :
        |A (higham11_5_rookColumnArgmax A i) (higham11_5_rookColumnArgmax A i)| ≥
          α * higham11_5_rookColumnMax A (higham11_5_rookColumnArgmax A i)
      · exact Or.inr (Or.inl ⟨hsecond, by
          simp [higham11_5_rookPivotSize, hfirst, hsecond]⟩)
      · exact Or.inr (Or.inr ⟨hequal, by
          simp [higham11_5_rookPivotSize, hfirst, hsecond]⟩)

/-- Executable Algorithm 11.5 conclusion: the bounded recursive search returns
a source-certified `1×1` or `2×2` rook pivot. -/
theorem higham11_5_rookTerminalChoice {n : ℕ} (α : ℝ)
    (A : Fin n → Fin n → ℝ) (hA : IsSymmetricFiniteMatrix A) (i₀ : Fin n) :
    let i := higham11_5_rookSearchPath A i₀
      (higham11_5_rookTerminalStep α A hA i₀)
    higham11_5_SymmetricRookFirstPivotChoice α (A i i)
      (A (higham11_5_rookColumnArgmax A i) (higham11_5_rookColumnArgmax A i))
      (higham11_5_rookColumnMax A i)
      (higham11_5_rookColumnMax A (higham11_5_rookColumnArgmax A i))
      (higham11_5_rookPivotSize α A i) := by
  dsimp only
  exact higham11_5_rookSearchStops_choice α A _
    (higham11_5_rookTerminalStep_stops α A hA i₀)

/-- The printed rook-pivoting entry bound for the `L` factor. -/
def higham11_5_rookPivotLBound (n : ℕ) (α : ℝ)
    (L : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, |L i j| ≤ max (1 / (1 - α)) (1 / α)

/-- Algorithm 11.5's accepted `1×1` branch gives the scalar multiplier cap
`|c/a| ≤ 1/α`, hence the printed common rook bound.  The zero-column case is
handled explicitly, so no hidden nonzero-pivot assumption is required. -/
theorem higham11_5_rook_oneByOne_multiplier_bound (α a ω c : ℝ)
    (hα : 0 < α) (hω : 0 ≤ ω)
    (ha : α * ω ≤ |a|) (hc : |c| ≤ ω) :
    |c / a| ≤ max (1 / (1 - α)) (1 / α) := by
  by_cases hω0 : ω = 0
  · have hc0 : c = 0 := by
      apply abs_eq_zero.mp
      exact le_antisymm (hc.trans_eq hω0) (abs_nonneg c)
    rw [hc0, zero_div, abs_zero]
    exact (div_nonneg zero_le_one (le_of_lt hα)).trans (le_max_right _ _)
  · have hωpos : 0 < ω := lt_of_le_of_ne hω (Ne.symm hω0)
    exact
      (higham11_1_oneByOne_multiplier_bound c a ω α hα hωpos hc ha).trans
        (le_max_right _ _)

/-- Algorithm 11.5's genuine `2×2` rook branch gives both entries of a
multiplier row the cap `1/(1-α)`.  This instantiates the already-derived exact
inverse-block bound with `μ₀=ω`, `μ₁=αω`, and
`K=((1-α²)ω)⁻¹`. -/
theorem higham11_5_rook_twoByTwo_multiplier_bound
    (c1 c2 e11 e22 e21 ω α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hω : 0 < ω)
    (he11 : |e11| ≤ α * ω) (he22 : |e22| ≤ α * ω)
    (he21 : e21 ^ 2 = ω ^ 2)
    (hc1 : |c1| ≤ ω) (hc2 : |c2| ≤ ω) :
    |c1 * (e22 / (e11 * e22 - e21 ^ 2)) +
        c2 * (-(e21 / (e11 * e22 - e21 ^ 2)))|
        ≤ max (1 / (1 - α)) (1 / α) ∧
      |c1 * (-(e21 / (e11 * e22 - e21 ^ 2))) +
        c2 * (e11 / (e11 * e22 - e21 ^ 2))|
        ≤ max (1 / (1 - α)) (1 / α) := by
  let K : ℝ := ((1 - α ^ 2) * ω)⁻¹
  have hαsq : α ^ 2 < 1 := by nlinarith
  have hden : 0 < (1 - α ^ 2) * ω := mul_pos (by linarith) hω
  have hK : (1 - α ^ 2) * ω * K = 1 := by
    exact mul_inv_cancel₀ (ne_of_gt hden)
  obtain ⟨hleft, hright⟩ :=
    higham11_4_twoByTwo_multiplier_row_bound_of_block
      c1 c2 e11 e22 e21 ω (α * ω) α K
      (mul_nonneg hα0 (le_of_lt hω)) hα0 hα1 hω
      he11 he22 he21 (le_refl _) hK hc1 hc2
  exact ⟨hleft.trans (le_max_left _ _), hright.trans (le_max_left _ _)⟩

/-- Origin certificate for entries of the global rook-pivoted `L` factor.
It records exactly the unit/zero structural entries and the two algebraic
multiplier forms emitted by accepted `1×1` and `2×2` pivots. -/
inductive higham11_5_RookMultiplierOrigin (α : ℝ) : ℝ → Prop
  | zero : higham11_5_RookMultiplierOrigin α 0
  | one : higham11_5_RookMultiplierOrigin α 1
  | scalar (a ω c : ℝ) (hω : 0 ≤ ω) (ha : α * ω ≤ |a|)
      (hc : |c| ≤ ω) : higham11_5_RookMultiplierOrigin α (c / a)
  | blockLeft (c1 c2 e11 e22 e21 ω : ℝ) (hω : 0 < ω)
      (he11 : |e11| ≤ α * ω) (he22 : |e22| ≤ α * ω)
      (he21 : e21 ^ 2 = ω ^ 2) (hc1 : |c1| ≤ ω) (hc2 : |c2| ≤ ω) :
      higham11_5_RookMultiplierOrigin α
        (c1 * (e22 / (e11 * e22 - e21 ^ 2)) +
          c2 * (-(e21 / (e11 * e22 - e21 ^ 2))))
  | blockRight (c1 c2 e11 e22 e21 ω : ℝ) (hω : 0 < ω)
      (he11 : |e11| ≤ α * ω) (he22 : |e22| ≤ α * ω)
      (he21 : e21 ^ 2 = ω ^ 2) (hc1 : |c1| ≤ ω) (hc2 : |c2| ≤ ω) :
      higham11_5_RookMultiplierOrigin α
        (c1 * (-(e21 / (e11 * e22 - e21 ^ 2))) +
          c2 * (e11 / (e11 * e22 - e21 ^ 2)))

theorem higham11_5_RookMultiplierOrigin.bound {α x : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (hx : higham11_5_RookMultiplierOrigin α x) :
    |x| ≤ max (1 / (1 - α)) (1 / α) := by
  cases hx with
  | zero =>
      simp only [abs_zero]
      exact (div_nonneg zero_le_one (le_of_lt hα)).trans (le_max_right _ _)
  | one =>
      have hright : 1 ≤ 1 / α := by
        rw [le_div_iff₀ hα]
        simpa using le_of_lt hα1
      simpa using hright.trans (le_max_right _ _)
  | scalar a ω c hω ha hc =>
      exact higham11_5_rook_oneByOne_multiplier_bound α a ω c hα hω ha hc
  | blockLeft c1 c2 e11 e22 e21 ω hω he11 he22 he21 hc1 hc2 =>
      exact (higham11_5_rook_twoByTwo_multiplier_bound c1 c2 e11 e22 e21 ω α
        (le_of_lt hα) hα1 hω he11 he22 he21 hc1 hc2).1
  | blockRight c1 c2 e11 e22 e21 ω hω he11 he22 he21 hc1 hc2 =>
      exact (higham11_5_rook_twoByTwo_multiplier_bound c1 c2 e11 e22 e21 ω α
        (le_of_lt hα) hα1 hω he11 he22 he21 hc1 hc2).2

/-- **Algorithm 11.5 global `L` bound.**  Once the recursive factorization
writes every entry of `L` as one of the certified outputs of its accepted rook
pivots, the printed uniform entry bound follows for the whole factor, with no
per-entry inequality assumed separately. -/
theorem higham11_5_rookPivotLBound_of_origins {n : ℕ} (α : ℝ)
    (L : Fin n → Fin n → ℝ) (hα : 0 < α) (hα1 : α < 1)
    (horigin : ∀ i j, higham11_5_RookMultiplierOrigin α (L i j)) :
    higham11_5_rookPivotLBound n α L := by
  intro i j
  exact (horigin i j).bound hα hα1

/-- The printed condition-number bound for accepted 2 by 2 rook pivots. -/
def higham11_5_rookPivotTwoByTwoCondBound (α κ : ℝ) : Prop :=
  κ ≤ (1 + α) / (1 - α)

/-- **Equation (11.7)** source-shaped forward-error bound. -/
def higham11_7_forwardErrorBound
    (relativeError p_n u condAx residualTerm : ℝ) : Prop :=
  relativeError ≤ p_n * u * condAx + residualTerm


end NumStability
