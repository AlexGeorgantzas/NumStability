import Mathlib.Tactic
import NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.TridiagonalInverse
import NumStability.Source.Higham.Chapter15.Theorem09.Ikebe.IrreducibleRightInverse.RankOneStructure

/-!
# EntryFormulas

Canonical destination for the frozen declaration block of
`NumStability.Algorithms.LU.Higham15Problem15_6`, routed by wave R02 of the August 2026 repository reorganization
completion phase. Declaration names, kinds, visibilities, signatures and
proofs are unchanged; only the module they live in has changed. Private
declarations keep their logical names and are re-mangled against this module,
exactly as recorded in the reviewed private normalization.
-/

/-!
# Higham15Problem15_6 (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.LU.Higham15Problem15_6`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

noncomputable section

namespace NumStability

namespace Higham15Problem15_6

open scoped BigOperators

open NumStability

private theorem sum_nested_ite_two {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i p : ι) (hip : i ≠ p) (f g : ι → ℝ) :
    (∑ x : ι, if x = i then f x else if x = p then g x else 0) =
      f i + g p := by
  calc
    (∑ x : ι, if x = i then f x else if x = p then g x else 0) =
        ∑ x : ι, ((if x = i then f x else 0) +
          (if x = p then g x else 0)) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hxi : x = i
            · subst x
              simp [hip]
            · by_cases hxp : x = p
              · subst x
                simp [Ne.symm hip]
              · simp [hxi, hxp]
    _ = f i + g p := by simp [Finset.sum_add_distrib]

private theorem sum_nested_ite_three {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i p q : ι) (hip : i ≠ p) (hiq : i ≠ q)
    (hpq : p ≠ q) (f g h : ι → ℝ) :
    (∑ x : ι,
      if x = i then f x else if x = p then g x else if x = q then h x else 0) =
      f i + g p + h q := by
  calc
    (∑ x : ι,
      if x = i then f x else if x = p then g x else if x = q then h x else 0) =
        ∑ x : ι, (((if x = i then f x else 0) +
          (if x = p then g x else 0)) + (if x = q then h x else 0)) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hxi : x = i
            · subst x
              simp [hip, hiq]
            · by_cases hxp : x = p
              · subst x
                simp [Ne.symm hip, hpq]
              · by_cases hxq : x = q
                · subst x
                  simp [Ne.symm hiq, Ne.symm hpq]
                · simp [hxi, hxp, hxq]
    _ = f i + g p + h q := by simp [Finset.sum_add_distrib]

/-- Entrywise action of the stored tridiagonal data on a vector.  This local
identity is the bridge from the first/last inverse equations to the scalar
recurrences below. -/
theorem tridiag_mulVec_entry {n : ℕ} (T : TridiagData n)
    (v : Fin n → ℝ) (i : Fin n) :
    (∑ j : Fin n, tridiag_to_matrix T i j * v j) =
      T.d i * v i +
        (if h : 0 < i.val then
          T.a i * v ⟨i.val - 1, by omega⟩ else 0) +
        (if h : i.val + 1 < n then
          T.c i * v ⟨i.val + 1, h⟩ else 0) := by
  classical
  have hdiag : ∀ j : Fin n, (j.val = i.val) ↔ j = i := by
    intro j
    exact Fin.ext_iff.symm
  by_cases hprev : 0 < i.val
  · let p : Fin n := ⟨i.val - 1, by omega⟩
    have hpi : p ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp [p] at hv
      omega
    have hsub : ∀ j : Fin n, (j.val + 1 = i.val) ↔ j = p := by
      intro j
      constructor
      · intro h
        apply Fin.ext
        simp [p]
        omega
      · intro h
        subst j
        simp [p]
        omega
    by_cases hnext : i.val + 1 < n
    · let q : Fin n := ⟨i.val + 1, hnext⟩
      have hqi : q ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        simp [q] at hv
      have hqp : q ≠ p := by
        intro h
        have hv := congrArg Fin.val h
        simp [q, p] at hv
        omega
      have hsuper : ∀ j : Fin n, (i.val + 1 = j.val) ↔ j = q := by
        intro j
        constructor
        · intro h
          exact Fin.ext h.symm
        · intro h
          subst j
          rfl
      simp only [tridiag_to_matrix]
      simp_rw [hdiag, hsub, hsuper]
      simp_rw [ite_mul, zero_mul]
      rw [sum_nested_ite_three i p q (Ne.symm hpi) (Ne.symm hqi)
        (Ne.symm hqp)]
      simp [hprev, hnext, p, q]
    · have hsuper : ∀ j : Fin n, ¬(i.val + 1 = j.val) := by
        intro j h
        omega
      simp only [tridiag_to_matrix]
      simp_rw [hdiag, hsub]
      simp_rw [if_neg (hsuper _)]
      simp_rw [ite_mul, zero_mul]
      rw [sum_nested_ite_two i p (Ne.symm hpi)]
      simp [hprev, hnext, p]
  · have hsub : ∀ j : Fin n, ¬(j.val + 1 = i.val) := by
      intro j h
      omega
    by_cases hnext : i.val + 1 < n
    · let q : Fin n := ⟨i.val + 1, hnext⟩
      have hqi : q ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        simp [q] at hv
      have hsuper : ∀ j : Fin n, (i.val + 1 = j.val) ↔ j = q := by
        intro j
        constructor
        · intro h
          exact Fin.ext h.symm
        · intro h
          subst j
          rfl
      simp only [tridiag_to_matrix]
      simp_rw [hdiag, hsuper]
      simp_rw [if_neg (hsub _)]
      simp_rw [ite_mul, zero_mul]
      rw [sum_nested_ite_two i q (Ne.symm hqi)]
      simp [hprev, hnext, q]
    · have hsuper : ∀ j : Fin n, ¬(i.val + 1 = j.val) := by
        intro j h
        omega
      simp only [tridiag_to_matrix]
      simp_rw [hdiag]
      simp [hprev, hnext, hsub, hsuper]

/-- The corresponding row-vector action, obtained from the same three-term
identity by transposition. -/
theorem tridiag_vecMul_entry {n : ℕ} (T : TridiagData n)
    (v : Fin n → ℝ) (j : Fin n) :
    (∑ i : Fin n, v i * tridiag_to_matrix T i j) =
      T.d j * v j +
        (if h : 0 < j.val then
          T.c ⟨j.val - 1, by omega⟩ * v ⟨j.val - 1, by omega⟩ else 0) +
        (if h : j.val + 1 < n then
          T.a ⟨j.val + 1, h⟩ * v ⟨j.val + 1, h⟩ else 0) := by
  calc
    (∑ i : Fin n, v i * tridiag_to_matrix T i j) =
        ∑ i : Fin n, tridiag_to_matrix (transposeData T) j i * v i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [transposeData_matrix]
          ring
    _ = (transposeData T).d j * v j +
        (if h : 0 < j.val then
          (transposeData T).a j * v ⟨j.val - 1, by omega⟩ else 0) +
        (if h : j.val + 1 < n then
          (transposeData T).c j * v ⟨j.val + 1, h⟩ else 0) :=
      tridiag_mulVec_entry (transposeData T) v j
    _ = _ := by
      simp only [transposeData]
      split_ifs <;> rfl

/-- Irreducibility forces the top-right inverse corner to be nonzero.  This
is the nonbreakdown fact needed to identify the normalized forward recurrence
with the last inverse column. -/
private theorem upper_corner_ne {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv) :
    A_inv ⟨0, hn⟩ ⟨n - 1, by omega⟩ ≠ 0 := by
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  intro hcorner
  have hzero : ∀ i : Fin n, A_inv i last = 0 := by
    have hbyVal : ∀ t : ℕ, ∀ ht : t < n, A_inv ⟨t, ht⟩ last = 0 := by
      intro t
      induction t using Nat.strong_induction_on with
      | h t ih =>
          intro ht
          by_cases ht0 : t = 0
          · subst t
            simpa [first, last] using hcorner
          · let i : Fin n := ⟨t, ht⟩
            let r : Fin n := ⟨t - 1, by omega⟩
            have hsum_single :
                (∑ k : Fin n,
                  tridiag_to_matrix T r k * A_inv k last) =
                  tridiag_to_matrix T r i * A_inv i last := by
              apply Finset.sum_eq_single i
              · intro k hk hki
                by_cases hkt : k.val < t
                · rw [ih k.val hkt k.isLt, mul_zero]
                · have hgt : t < k.val := by
                    have hne : k.val ≠ t := by
                      intro hv
                      exact hki (Fin.ext hv)
                    omega
                  have hz : tridiag_to_matrix T r k = 0 :=
                    tridiag_to_matrix_isTridiagonal T r k (by
                      left
                      simp [r]
                      omega)
                  rw [hz, zero_mul]
              · simp
            have hrlast : r ≠ last := by
              intro h
              have hv := congrArg Fin.val h
              simp [r, last] at hv
              omega
            have hsum_zero :
                ∑ k : Fin n, tridiag_to_matrix T r k * A_inv k last = 0 := by
              rw [hRight r last]
              simp [hrlast]
            have hprod : tridiag_to_matrix T r i * A_inv i last = 0 := by
              rw [← hsum_single]
              exact hsum_zero
            have hri : tridiag_to_matrix T r i ≠ 0 := by
              have hrlt : r.val + 1 < n := by simp [r]; omega
              have hs := hIrred.2 r hrlt
              unfold tridiag_to_matrix
              split_ifs with hdiag hsub hsuper
              · have hv : i.val = r.val := by simpa using hdiag
                simp [i, r] at hv
                omega
              · have hv : i.val + 1 = r.val := by simpa using hsub
                simp [i, r] at hv
                omega
              · simpa [i, r] using hs
              · exfalso
                apply hsuper
                simp [i, r]
                omega
            exact (mul_eq_zero.mp hprod).resolve_left hri
    intro i
    exact hbyVal i.val i.isLt
  have hdiag := hRight last last
  have hsum_zero :
      (∑ k : Fin n, tridiag_to_matrix T last k * A_inv k last) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hzero k, mul_zero]
  rw [hsum_zero] at hdiag
  simp at hdiag

end Higham15Problem15_6
end NumStability

end
