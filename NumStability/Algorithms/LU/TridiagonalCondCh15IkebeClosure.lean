-- Algorithms/LU/TridiagonalCondCh15IkebeClosure.lean
--
-- Source-hypothesis closure of Higham, Theorem 15.9 (Ikebe): the inverse of
-- an irreducible tridiagonal matrix is rank one on each of its two triangles.
--
-- Unlike `Ch15.H15_Theorem15_9`, the endpoint below does not assume an LU
-- factorization or formulas for entries of bidiagonal inverses.  Its only
-- algebraic inputs are the printed tridiagonal irreducibility hypothesis and
-- an actual right-inverse certificate for the displayed inverse matrix.

import NumStability.Algorithms.LU.TridiagonalCondCh15

namespace NumStability.Ch15IkebeClosure

open scoped BigOperators
open NumStability

/-- If a square matrix has a nonzero first superdiagonal and no entries above
that superdiagonal, then the upper triangle of any right inverse has rank one.

The proof is the column-recurrence argument behind Ikebe's theorem.  The last
column is a nonzero reference solution of every homogeneous leading row
equation.  Every other column satisfies the same equations above its diagonal,
so forward induction makes it proportional to the reference column. -/
private theorem upper_triangle_rank_one_of_rightInverse {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv)
    (hUpperZero : ∀ i j : Fin n, i.val + 1 < j.val → A i j = 0)
    (hSuper : ∀ (i : Fin n) (hi : i.val + 1 < n),
      A i ⟨i.val + 1, hi⟩ ≠ 0) :
    ∃ x y : Fin n → ℝ,
      ∀ i j : Fin n, i.val ≤ j.val → A_inv i j = x i * y j := by
  classical
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩

  -- A solution of the homogeneous leading-row recurrence whose first entry
  -- vanishes must vanish everywhere.
  have zero_column_of_first_zero :
      A_inv first last = 0 → ∀ i : Fin n, A_inv i last = 0 := by
    intro hfirst
    have hbyVal : ∀ t : ℕ, ∀ ht : t < n, A_inv ⟨t, ht⟩ last = 0 := by
      intro t
      induction t using Nat.strong_induction_on with
      | h t ih =>
          intro ht
          by_cases ht0 : t = 0
          · subst t
            simpa [first] using hfirst
          · let i : Fin n := ⟨t, ht⟩
            let r : Fin n := ⟨t - 1, by omega⟩
            have hsum_single :
                (∑ k : Fin n, A r k * A_inv k last) = A r i * A_inv i last := by
              apply Finset.sum_eq_single i
              · intro k _ hki
                by_cases hkt : k.val < t
                · rw [ih k.val hkt k.isLt, mul_zero]
                · have hgt : t < k.val := by
                    have hne : k.val ≠ t := by
                      intro hval
                      exact hki (Fin.ext hval)
                    omega
                  rw [hUpperZero r k (by simp [r]; omega), zero_mul]
              · simp
            have hrlast : r ≠ last := by
              intro h
              have hval := congrArg Fin.val h
              simp [r, last] at hval
              omega
            have hsum_zero : ∑ k : Fin n, A r k * A_inv k last = 0 := by
              rw [hRight r last]
              simp [hrlast]
            have hprod : A r i * A_inv i last = 0 := by
              rw [← hsum_single]
              exact hsum_zero
            have hri : A r i ≠ 0 := by
              have hrlt : r.val + 1 < n := by simp [r]; omega
              have hs := hSuper r hrlt
              have hei : (⟨r.val + 1, hrlt⟩ : Fin n) = i := by
                apply Fin.ext
                simp [r, i]
                omega
              rwa [hei] at hs
            exact (mul_eq_zero.mp hprod).resolve_left hri
    intro i
    exact hbyVal i.val i.isLt

  have hfirst_ne : A_inv first last ≠ 0 := by
    intro hfirst
    have hzero := zero_column_of_first_zero hfirst
    have hdiag := hRight last last
    have hsum_zero : ∑ k : Fin n, A last k * A_inv k last = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [hzero k, mul_zero]
    rw [hsum_zero] at hdiag
    simp at hdiag

  -- Cross-multiplication form of proportionality.  It avoids division during
  -- the recurrence induction and is valid for every entry on/above column j.
  have hcross : ∀ j i : Fin n, i.val ≤ j.val →
      A_inv i j * A_inv first last = A_inv i last * A_inv first j := by
    intro j
    have hbyVal : ∀ t : ℕ, ∀ ht : t < n, t ≤ j.val →
        A_inv ⟨t, ht⟩ j * A_inv first last =
          A_inv ⟨t, ht⟩ last * A_inv first j := by
      intro t
      induction t using Nat.strong_induction_on with
      | h t ih =>
          intro ht htj
          by_cases ht0 : t = 0
          · subst t
            have hei : (⟨0, ht⟩ : Fin n) = first := Fin.ext rfl
            rw [hei]
            ring
          · let i : Fin n := ⟨t, ht⟩
            let r : Fin n := ⟨t - 1, by omega⟩
            let z : Fin n → ℝ := fun k =>
              A_inv k j * A_inv first last - A_inv k last * A_inv first j
            have hrj : r ≠ j := by
              intro h
              have hval := congrArg Fin.val h
              simp [r] at hval
              omega
            have hrlast : r ≠ last := by
              intro h
              have hval := congrArg Fin.val h
              simp [r, last] at hval
              omega
            have hsum_zero : ∑ k : Fin n, A r k * z k = 0 := by
              simp only [z, mul_sub]
              simp_rw [← mul_assoc]
              rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
                hRight r j, hRight r last]
              simp [hrj, hrlast]
            have hsum_single :
                (∑ k : Fin n, A r k * z k) = A r i * z i := by
              apply Finset.sum_eq_single i
              · intro k _ hki
                by_cases hkt : k.val < t
                · have hkcross := ih k.val hkt k.isLt (by omega)
                  have hz : z k = 0 := by
                    simp only [z]
                    exact sub_eq_zero.mpr hkcross
                  rw [hz, mul_zero]
                · have hgt : t < k.val := by
                    have hne : k.val ≠ t := by
                      intro hval
                      exact hki (Fin.ext hval)
                    omega
                  rw [hUpperZero r k (by simp [r]; omega), zero_mul]
              · simp
            have hprod : A r i * z i = 0 := by
              rw [← hsum_single]
              exact hsum_zero
            have hri : A r i ≠ 0 := by
              have hrlt : r.val + 1 < n := by simp [r]; omega
              have hs := hSuper r hrlt
              have hei : (⟨r.val + 1, hrlt⟩ : Fin n) = i := by
                apply Fin.ext
                simp [r, i]
                omega
              rwa [hei] at hs
            have hzi : z i = 0 := (mul_eq_zero.mp hprod).resolve_left hri
            exact sub_eq_zero.mp hzi
    intro i hij
    exact hbyVal i.val i.isLt hij

  let x : Fin n → ℝ := fun i => A_inv i last / A_inv first last
  let y : Fin n → ℝ := fun j => A_inv first j
  refine ⟨x, y, ?_⟩
  intro i j hij
  have hc := hcross j i hij
  simp only [x, y]
  field_simp [hfirst_ne]
  exact hc

/-- **Theorem 15.9** (Ikebe; Higham, §15.6, p. 300), at its printed
structural strength.

For a nonempty irreducible tridiagonal matrix `A`, any matrix carrying the
actual certificate `A * A_inv = I` has the rank-one inverse representation

`A_inv i j = x i * y j` for `i ≤ j`, and
`A_inv i j = p i * q j` for `i ≥ j`.

No LU factorization, pivot-nonzero premise, inverse-entry formula, or
target-bearing rank condition is assumed. -/
theorem H15_Theorem15_9_of_irreducible_rightInverse {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    ∃ (x y p q : Fin n → ℝ),
      (∀ i j : Fin n, i.val ≤ j.val → A_inv i j = x i * y j) ∧
      (∀ i j : Fin n, j.val ≤ i.val → A_inv i j = p i * q j) := by
  classical
  let A := tridiag_to_matrix T
  have hUpperZero : ∀ i j : Fin n, i.val + 1 < j.val → A i j = 0 := by
    intro i j hij
    unfold A tridiag_to_matrix
    split_ifs <;> first | omega | rfl
  have hSuper : ∀ (i : Fin n) (hi : i.val + 1 < n),
      A i ⟨i.val + 1, hi⟩ ≠ 0 := by
    intro i hi
    unfold A tridiag_to_matrix
    split_ifs with hdiag hsub hsuper
    · have hbad : i.val + 1 = i.val := by
        change i.val + 1 = i.val at hdiag
        exact hdiag
      omega
    · have hbad : i.val + 1 + 1 = i.val := by simpa using hsub
      omega
    · exact hIrred.2 i hi
    · exfalso
      apply hsuper
      rfl
  obtain ⟨x, y, hxy⟩ :=
    upper_triangle_rank_one_of_rightInverse hn A A_inv hRight hUpperZero hSuper

  -- Transpose the inverse identity.  A right inverse of a finite square
  -- matrix is also a left inverse; transposing that left identity supplies
  -- the right-inverse certificate needed by the same forward recurrence for
  -- the lower triangle.
  have hLeft : IsLeftInverse n A A_inv :=
    isLeftInverse_of_isRightInverse A A_inv hRight
  let AT : Fin n → Fin n → ℝ := fun i j => A j i
  let AinvT : Fin n → Fin n → ℝ := fun i j => A_inv j i
  have hRightT : IsRightInverse n AT AinvT := by
    intro i j
    calc
      ∑ k : Fin n, AT i k * AinvT k j
          = ∑ k : Fin n, A_inv j k * A k i := by
              apply Finset.sum_congr rfl
              intro k _
              simp only [AT, AinvT]
              ring
      _ = if j = i then 1 else 0 := hLeft j i
      _ = if i = j then 1 else 0 := by
            by_cases hij : i = j
            · subst j
              simp
            · have hji : j ≠ i := Ne.symm hij
              simp [hij, hji]
  have hUpperZeroT : ∀ i j : Fin n, i.val + 1 < j.val → AT i j = 0 := by
    intro i j hij
    unfold AT A tridiag_to_matrix
    split_ifs <;> first | omega | rfl
  have hSuperT : ∀ (i : Fin n) (hi : i.val + 1 < n),
      AT i ⟨i.val + 1, hi⟩ ≠ 0 := by
    intro i hi
    unfold AT A tridiag_to_matrix
    split_ifs with hdiag hsub hsuper
    · have hbad : i.val = i.val + 1 := by
        change i.val = i.val + 1 at hdiag
        exact hdiag
      omega
    · exact hIrred.1 i hi
    · have hbad : i.val + 1 + 1 = i.val := by simpa using hsuper
      omega
    · exfalso
      apply hsub
      rfl
  obtain ⟨q, p, hqp⟩ :=
    upper_triangle_rank_one_of_rightInverse hn AT AinvT hRightT hUpperZeroT hSuperT
  refine ⟨x, y, p, q, hxy, ?_⟩
  intro i j hji
  have h := hqp j i hji
  simpa [AinvT, mul_comm] using h

end NumStability.Ch15IkebeClosure
