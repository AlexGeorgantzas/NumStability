-- Algorithms/LU/Higham15Problem15_6.lean
--
-- Higham, 2nd ed., Chapter 15, Problem 15.6 (printed p. 304).
-- The source asks for the forward/backward scalar recurrences obtained from
-- the last column of A A⁻¹ = I and the first row of A⁻¹ A = I, followed by an
-- O(n) computation of ‖|A⁻¹|d‖∞ for d ≥ 0.

import Mathlib.Tactic
import NumStability.Algorithms.LU.TridiagonalCondCh15IkebeClosure

namespace NumStability.Higham15Problem15_6

open scoped BigOperators
open NumStability

noncomputable section

/-! ## Tridiagonal scalar action -/

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

/-- Stored tridiagonal data for the transpose. -/
def transposeData {n : ℕ} (T : TridiagData n) : TridiagData n where
  a := fun i => if h : 0 < i.val then
    T.c ⟨i.val - 1, by omega⟩ else 0
  d := T.d
  c := fun i => if h : i.val + 1 < n then
    T.a ⟨i.val + 1, h⟩ else 0

theorem transposeData_matrix {n : ℕ} (T : TridiagData n)
    (i j : Fin n) :
    tridiag_to_matrix (transposeData T) i j =
      tridiag_to_matrix T j i := by
  by_cases hdiag : j.val = i.val
  · have hij : j = i := Fin.ext hdiag
    subst j
    simp [tridiag_to_matrix, transposeData]
  · by_cases hsub : j.val + 1 = i.val
    · have hi : 0 < i.val := by omega
      have hnotrev : i.val + 1 ≠ j.val := by omega
      simp only [tridiag_to_matrix]
      rw [if_neg hdiag, if_pos hsub]
      have hdiag' : i.val ≠ j.val := Ne.symm hdiag
      rw [if_neg hdiag', if_neg hnotrev, if_pos hsub]
      simp only [transposeData, hi, dif_pos]
      congr 1
      apply Fin.ext
      simp
      omega
    · by_cases hsuper : i.val + 1 = j.val
      · have hnext : i.val + 1 < n := by omega
        have hnotrev : j.val + 1 ≠ i.val := by omega
        simp only [tridiag_to_matrix]
        rw [if_neg hdiag, if_neg hsub, if_pos hsuper]
        have hdiag' : i.val ≠ j.val := Ne.symm hdiag
        rw [if_neg hdiag', if_pos hsuper]
        simp only [transposeData, hnext, dif_pos]
        congr 1
        apply Fin.ext
        exact hsuper
      · have hdiag' : i.val ≠ j.val := Ne.symm hdiag
        simp [tridiag_to_matrix, transposeData, hdiag, hdiag', hsub,
          hsuper]

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

/-! ## Executable forward/backward inverse recurrences -/

/-- Totalized accessors let the scalar recurrences be ordinary structurally
recursive functions on `ℕ`; every correctness theorem below only evaluates
them at source-valid indices. -/
def diagAt {n : ℕ} (T : TridiagData n) (k : ℕ) : ℝ :=
  if h : k < n then T.d ⟨k, h⟩ else 0

def subAt {n : ℕ} (T : TridiagData n) (k : ℕ) : ℝ :=
  if h : k < n then T.a ⟨k, h⟩ else 0

def superAt {n : ℕ} (T : TridiagData n) (k : ℕ) : ℝ :=
  if h : k < n then T.c ⟨k, h⟩ else 0

@[simp] theorem diagAt_of_lt {n : ℕ} (T : TridiagData n) (k : ℕ)
    (hk : k < n) : diagAt T k = T.d ⟨k, hk⟩ := by
  simp [diagAt, hk]

@[simp] theorem subAt_of_lt {n : ℕ} (T : TridiagData n) (k : ℕ)
    (hk : k < n) : subAt T k = T.a ⟨k, hk⟩ := by
  simp [subAt, hk]

@[simp] theorem superAt_of_lt {n : ℕ} (T : TridiagData n) (k : ℕ)
    (hk : k < n) : superAt T k = T.c ⟨k, hk⟩ := by
  simp [superAt, hk]

/-- Forward homogeneous recurrence from the last column of `A A⁻¹ = I`,
normalized by `x₀=1`:

`x₁=-d₀/c₀`,
`x_{i+1}=-(aᵢx_{i-1}+dᵢxᵢ)/cᵢ`. -/
def forwardColumnNat {n : ℕ} (T : TridiagData n) : ℕ → ℝ
  | 0 => 1
  | 1 => -diagAt T 0 / superAt T 0
  | k + 2 =>
      -(subAt T (k + 1) * forwardColumnNat T k +
          diagAt T (k + 1) * forwardColumnNat T (k + 1)) /
        superAt T (k + 1)

/-- Backward homogeneous recurrence for the first row of `A⁻¹ A = I`.
The argument is distance from the last index, so `0` stores the last entry. -/
def backwardRowNat {n : ℕ} (T : TridiagData n) : ℕ → ℝ
  | 0 => 1
  | 1 => -diagAt T (n - 1) / superAt T (n - 2)
  | k + 2 =>
      let i := n - (k + 2);
      -(diagAt T i * backwardRowNat T (k + 1) +
          subAt T (i + 1) * backwardRowNat T k) /
        superAt T (i - 1)

/-- Backward homogeneous recurrence from the first column of `A A⁻¹ = I`,
again indexed by distance from the last entry. -/
def backwardColumnNat {n : ℕ} (T : TridiagData n) : ℕ → ℝ
  | 0 => 1
  | 1 => -diagAt T (n - 1) / subAt T (n - 1)
  | k + 2 =>
      let i := n - (k + 2);
      -(diagAt T i * backwardColumnNat T (k + 1) +
          superAt T i * backwardColumnNat T k) /
        subAt T i

/-- Forward homogeneous recurrence for the last row of `A⁻¹ A = I`. -/
def forwardRowNat {n : ℕ} (T : TridiagData n) : ℕ → ℝ
  | 0 => 1
  | 1 => -diagAt T 0 / subAt T 1
  | k + 2 =>
      -(superAt T k * forwardRowNat T k +
          diagAt T (k + 1) * forwardRowNat T (k + 1)) /
        subAt T (k + 2)

/-- The forward `x` vector requested explicitly in Problem 15.6. -/
def problem15_6_x {n : ℕ} (T : TridiagData n) : Fin n → ℝ :=
  fun i => forwardColumnNat T i.val

/-- Unnormalized backward first-row solution. -/
def problem15_6_yBar {n : ℕ} (T : TridiagData n) : Fin n → ℝ :=
  fun i => backwardRowNat T (n - 1 - i.val)

/-- Its first-column residual.  Dividing by this scalar changes the
homogeneous row equations into `y A = e₀ᵀ`. -/
def problem15_6_yResidual {n : ℕ} (T : TridiagData n) : ℝ :=
  if hn : n = 0 then 1
  else if hn1 : n = 1 then diagAt T 0
  else diagAt T 0 * backwardRowNat T (n - 1) +
    subAt T 1 * backwardRowNat T (n - 2)

/-- The normalized backward `y` vector requested in Problem 15.6. -/
def problem15_6_y {n : ℕ} (T : TridiagData n) : Fin n → ℝ :=
  fun i => problem15_6_yBar T i / problem15_6_yResidual T

/-- The analogous backward factor for the lower inverse triangle. -/
def problem15_6_p {n : ℕ} (T : TridiagData n) : Fin n → ℝ :=
  fun i => backwardColumnNat T (n - 1 - i.val)

/-- Unnormalized forward last-row solution. -/
def problem15_6_qBar {n : ℕ} (T : TridiagData n) : Fin n → ℝ :=
  fun i => forwardRowNat T i.val

/-- Last-column residual used to normalize the last inverse row. -/
def problem15_6_qResidual {n : ℕ} (T : TridiagData n) : ℝ :=
  if hn : n = 0 then 1
  else if hn1 : n = 1 then diagAt T 0
  else superAt T (n - 2) * forwardRowNat T (n - 2) +
    diagAt T (n - 1) * forwardRowNat T (n - 1)

/-- The normalized lower-triangle row factor. -/
def problem15_6_q {n : ℕ} (T : TridiagData n) : Fin n → ℝ :=
  fun i => problem15_6_qBar T i / problem15_6_qResidual T

/-- The four recurrences are a concrete producer depending only on the
`3n-2` stored tridiagonal entries. -/
structure Problem15_6Factors (n : ℕ) where
  x : Fin n → ℝ
  y : Fin n → ℝ
  p : Fin n → ℝ
  q : Fin n → ℝ

def problem15_6_factors {n : ℕ} (T : TridiagData n) :
    Problem15_6Factors n :=
  ⟨problem15_6_x T, problem15_6_y T,
    problem15_6_p T, problem15_6_q T⟩

/-! ## Correctness against the actual inverse -/

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

end

end NumStability.Higham15Problem15_6
