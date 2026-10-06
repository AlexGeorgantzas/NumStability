/-
Analysis/MatrixPowersLaszlo.lean

László's nearest-normal Frobenius bound quoted by Higham, *Accuracy and
Stability of Numerical Algorithms*, 2nd ed., §18.1, p. 345:

    Δ_F(A) / sqrt(n) ≤ ν(A) ≤ Δ_F(A).

Rather than assuming an abstract value for the distance `ν(A)`, this module
proves its two defining facts: every normal competitor is at least
`Δ_F(A)/sqrt(n)` away, and a concrete normal matrix attains distance `Δ_F(A)`.
The proof is carried out first in Schur coordinates and then transported back
by the unitary Schur factor.
-/

import NumStability.Analysis.HenriciExtremal
import NumStability.Analysis.MatrixPowersHenriciNormal

open scoped BigOperators Matrix
open Matrix Complex

namespace NumStability

variable {n : ℕ}

/-- Strict-upper part of a complex matrix. -/
def strictUpperPart (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i < j then M i j else 0

/-- Squared Frobenius mass strictly above the diagonal. -/
def strictUpperSq (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  frobSq (strictUpperPart M)

/-- Squared Frobenius mass strictly below the diagonal. -/
noncomputable def strictLowerSq (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  strictUpperSq Mᴴ

lemma strictUpperPart_spec (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    strictUpperPart M i j = if j > i then M i j else 0 := rfl

lemma strictUpperSq_nonneg (M : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ strictUpperSq M := frobSq_nonneg _

lemma strictLowerSq_nonneg (M : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ strictLowerSq M := strictUpperSq_nonneg _

/-- A general cut identity.  The partial trace of `MᴴM-MMᴴ` over indices below
the cut equals lower cross-cut mass minus upper cross-cut mass. -/
lemma partialTrace_eq_lowerBlock_sub_upperBlock
    (M : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m), commDiagRe M i)
      = blockMass Mᴴ m - blockMass M m := by
  classical
  set Slt : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => i.val < m) with hSlt
  set Sge : Finset (Fin n) :=
    Finset.univ.filter (fun j : Fin n => m ≤ j.val) with hSge
  have hsplit : ∀ i : Fin n,
      commDiagRe M i =
        (∑ k ∈ Slt, (Complex.normSq (M k i) - Complex.normSq (M i k))) +
        (∑ k ∈ Sge, (Complex.normSq (M k i) - Complex.normSq (M i k))) := by
    intro i
    unfold commDiagRe
    rw [← Finset.sum_sub_distrib]
    have huniv : Slt ∪ Sge = Finset.univ := by
      ext x
      simp only [hSlt, hSge, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, iff_true]
      exact Nat.lt_or_ge x.val m
    have hdisj : Disjoint Slt Sge := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [hSlt, hSge, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
      omega
    rw [← huniv, Finset.sum_union hdisj]
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
  have hA : (∑ i ∈ Slt, ∑ k ∈ Slt,
      (Complex.normSq (M k i) - Complex.normSq (M i k))) = 0 := by
    have hswap : (∑ i ∈ Slt, ∑ k ∈ Slt,
        (Complex.normSq (M k i) - Complex.normSq (M i k))) =
        - ∑ i ∈ Slt, ∑ k ∈ Slt,
          (Complex.normSq (M k i) - Complex.normSq (M i k)) := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    linarith [hswap]
  have hB : (∑ i ∈ Slt, ∑ k ∈ Sge,
      (Complex.normSq (M k i) - Complex.normSq (M i k))) =
      blockMass Mᴴ m - blockMass M m := by
    unfold blockMass
    rw [← hSlt, ← hSge, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  rw [hA, hB, zero_add]

/-- A normal matrix has equal Frobenius mass across every cut in the two
directions. -/
lemma normal_blockMass_eq_conjTranspose_blockMass
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ * M = M * Mᴴ) (m : ℕ) :
    blockMass M m = blockMass Mᴴ m := by
  have hcomm : selfComm M = 0 := by
    unfold selfComm
    rw [hM, sub_self]
  have hdiag : ∀ i : Fin n, commDiagRe M i = 0 := by
    intro i
    have h := commDiag_ofReal M i
    rw [hcomm, Matrix.zero_apply] at h
    exact_mod_cast h.symm
  have hcut := partialTrace_eq_lowerBlock_sub_upperBlock M m
  simp [hdiag] at hcut
  linarith

/-- A cross-cut block is contained in the strict-upper support. -/
lemma blockMass_le_strictUpperSq
    (M : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    blockMass M m ≤ strictUpperSq M := by
  classical
  set Slt : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => i.val < m) with hSlt
  set Sge : Finset (Fin n) :=
    Finset.univ.filter (fun j : Fin n => m ≤ j.val) with hSge
  have hentry : ∀ i ∈ Slt, ∀ j ∈ Sge,
      Complex.normSq (M i j) = Complex.normSq (strictUpperPart M i j) := by
    intro i hi j hj
    have hij : i < j := by
      simp only [hSlt, hSge, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      exact Fin.lt_def.mpr (lt_of_lt_of_le hi hj)
    simp [strictUpperPart, hij]
  unfold blockMass strictUpperSq frobSq
  rw [← hSlt, ← hSge]
  calc
    (∑ i ∈ Slt, ∑ j ∈ Sge, Complex.normSq (M i j)) =
        ∑ i ∈ Slt, ∑ j ∈ Sge, Complex.normSq (strictUpperPart M i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hentry i hi j hj
    _ ≤ ∑ i ∈ Slt, ∑ j, Complex.normSq (strictUpperPart M i j) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Sge)
        (fun j _ _ => Complex.normSq_nonneg _)
    _ ≤ ∑ i, ∑ j, Complex.normSq (strictUpperPart M i j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Slt)
        (fun i _ _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)

lemma blockMass_zero (M : Matrix (Fin n) (Fin n) ℂ) :
    blockMass M 0 = 0 := by
  simp [blockMass]

/-- Summing cross-cut masses counts any strict-upper entry at most `n-1`
times. -/
lemma sum_blockMass_le_natPred_mul_strictUpperSq
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    (∑ m ∈ Finset.range n, blockMass M m) ≤
      ((n - 1 : ℕ) : ℝ) * strictUpperSq M := by
  have hmem : 0 ∈ Finset.range n := Finset.mem_range.mpr hn
  calc
    (∑ m ∈ Finset.range n, blockMass M m) =
        ∑ m ∈ (Finset.range n).erase 0, blockMass M m := by
      rw [← Finset.sum_erase_add _ _ hmem, blockMass_zero, add_zero]
    _ ≤ ∑ _m ∈ (Finset.range n).erase 0, strictUpperSq M := by
      exact Finset.sum_le_sum fun m _ => blockMass_le_strictUpperSq M m
    _ = (((Finset.range n).erase 0).card : ℝ) * strictUpperSq M := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((n - 1 : ℕ) : ℝ) * strictUpperSq M := by
      rw [Finset.card_erase_of_mem hmem, Finset.card_range]

/-- For a normal matrix, strict-upper Frobenius mass is at most `(n-1)` times
strict-lower mass. -/
lemma normal_strictUpperSq_le_natPred_mul_strictLowerSq
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (hM : Mᴴ * M = M * Mᴴ) :
    strictUpperSq M ≤ ((n - 1 : ℕ) : ℝ) * strictLowerSq M := by
  calc
    strictUpperSq M ≤ ∑ m ∈ Finset.range n, blockMass M m :=
      frobSq_strictUpper_le_sum_blockMass M (strictUpperPart M)
        (strictUpperPart_spec M)
    _ = ∑ m ∈ Finset.range n, blockMass Mᴴ m := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact normal_blockMass_eq_conjTranspose_blockMass M hM m
    _ ≤ ((n - 1 : ℕ) : ℝ) * strictUpperSq Mᴴ :=
      sum_blockMass_le_natPred_mul_strictUpperSq Mᴴ hn
    _ = ((n - 1 : ℕ) : ℝ) * strictLowerSq M := rfl

lemma frobSq_conjTranspose (M : Matrix (Fin n) (Fin n) ℂ) :
    frobSq Mᴴ = frobSq M := by
  unfold frobSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  simp [Matrix.conjTranspose_apply, Complex.normSq_conj]

lemma strictUpperSq_le_frobSq (M : Matrix (Fin n) (Fin n) ℂ) :
    strictUpperSq M ≤ frobSq M := by
  unfold strictUpperSq strictUpperPart frobSq
  apply Finset.sum_le_sum
  intro i _hi
  apply Finset.sum_le_sum
  intro j _hj
  by_cases hij : i < j
  · simp [hij]
  · simp [hij, Complex.normSq_nonneg]

lemma strictLowerSq_le_frobSq (M : Matrix (Fin n) (Fin n) ℂ) :
    strictLowerSq M ≤ frobSq M := by
  calc
    strictLowerSq M = strictUpperSq Mᴴ := rfl
    _ ≤ frobSq Mᴴ := strictUpperSq_le_frobSq _
    _ = frobSq M := frobSq_conjTranspose M

lemma strictLowerSq_eq_lower_sum (M : Matrix (Fin n) (Fin n) ℂ) :
    strictLowerSq M =
      ∑ i, ∑ j, if j < i then Complex.normSq (M i j) else 0 := by
  unfold strictLowerSq strictUpperSq strictUpperPart frobSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hji : j < i
  · simp [hji, Matrix.conjTranspose_apply, Complex.normSq_conj]
  · simp [hji]

/-- The strict upper and lower supports are disjoint parts of the Frobenius
sum. -/
lemma strictLowerSq_add_strictUpperSq_le_frobSq
    (M : Matrix (Fin n) (Fin n) ℂ) :
    strictLowerSq M + strictUpperSq M ≤ frobSq M := by
  rw [strictLowerSq_eq_lower_sum]
  unfold strictUpperSq strictUpperPart frobSq
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _hj
  rcases lt_trichotomy j i with hji | hEq | hij
  · simp [hji, not_lt.mpr (le_of_lt hji)]
  · subst j
    simp [Complex.normSq_nonneg]
  · simp [hij, not_lt.mpr (le_of_lt hij)]

/-- Below the diagonal of an upper-triangular `T`, the error `T-C` is `-C`,
so the two matrices have the same strict-lower Frobenius mass. -/
lemma strictLowerSq_eq_sub_of_upperTriangular
    (T C : Matrix (Fin n) (Fin n) ℂ)
    (hTtri : ∀ i j, j < i → T i j = 0) :
    strictLowerSq C = strictLowerSq (T - C) := by
  rw [strictLowerSq_eq_lower_sum, strictLowerSq_eq_lower_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hji : j < i
  · rw [if_pos hji, if_pos hji, Matrix.sub_apply, hTtri i j hji,
      zero_sub, Complex.normSq_neg]
  · rw [if_neg hji, if_neg hji]

/-- Scalar Young inequality in the coefficient form used by László's proof. -/
lemma normSq_add_young_nat (r : ℕ) (a b : ℂ) :
    (r : ℝ) * Complex.normSq (a + b) ≤
      ((r + 1 : ℕ) : ℝ) * Complex.normSq a +
        ((r + 1 : ℕ) : ℝ) * (r : ℝ) * Complex.normSq b := by
  have hre : 0 ≤ (a.re - (r : ℝ) * b.re) ^ 2 := sq_nonneg _
  have him : 0 ≤ (a.im - (r : ℝ) * b.im) ^ 2 := sq_nonneg _
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Nat.cast_add,
    Nat.cast_one]
  nlinarith

/-- Entrywise Young inequality summed over the strict-upper support. -/
lemma strictUpperSq_add_young_nat
    (r : ℕ) (C E : Matrix (Fin n) (Fin n) ℂ) :
    (r : ℝ) * strictUpperSq (C + E) ≤
      ((r + 1 : ℕ) : ℝ) * strictUpperSq C +
        ((r + 1 : ℕ) : ℝ) * (r : ℝ) * strictUpperSq E := by
  unfold strictUpperSq strictUpperPart frobSq
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _hj
  by_cases hij : i < j
  · simp only [hij, if_true, Matrix.add_apply]
    exact normSq_add_young_nat r (C i j) (E i j)
  · simp [hij]

/-- **László's universal lower bound, squared in Schur coordinates.**  If `T`
is upper triangular with strict-upper part `N`, then every normal `C` satisfies
`‖N‖_F² ≤ n ‖T-C‖_F²`. -/
theorem laszlo_lower_frobSq_of_upperTriangular
    (T N C : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (hN : ∀ i j, N i j = if j > i then T i j else 0)
    (hC : Cᴴ * C = C * Cᴴ) :
    frobSq N ≤ (n : ℝ) * frobSq (T - C) := by
  by_cases hn1 : n = 1
  · subst n
    have hN0 : N = 0 := by
      ext i j
      rw [hN i j, Matrix.zero_apply]
      have hij : i = j := Subsingleton.elim _ _
      subst j
      simp
    rw [hN0]
    simpa [frobSq] using frobSq_nonneg (T - C)
  · have hn2 : 2 ≤ n := by omega
    let E : Matrix (Fin n) (Fin n) ℂ := T - C
    have hNpart : N = strictUpperPart T := by
      ext i j
      rw [hN i j]
      rfl
    have hNEq : frobSq N = strictUpperSq T := by
      rw [hNpart]
      rfl
    have hTadd : C + E = T := by
      ext i j
      simp [E]
    have hradd : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    have hYoung := strictUpperSq_add_young_nat (n - 1) C E
    rw [hTadd, hradd] at hYoung
    have hnormal := normal_strictUpperSq_le_natPred_mul_strictLowerSq C hn hC
    have hlower : strictLowerSq C = strictLowerSq E := by
      simpa [E] using strictLowerSq_eq_sub_of_upperTriangular T C hTtri
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hr0 : 0 ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hnormalScaled := mul_le_mul_of_nonneg_left hnormal hn0
    rw [hlower] at hnormalScaled
    have htoOffdiag :
        (n : ℝ) * strictUpperSq C +
            (n : ℝ) * ((n - 1 : ℕ) : ℝ) * strictUpperSq E ≤
          (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
            (strictLowerSq E + strictUpperSq E) := by
      calc
        (n : ℝ) * strictUpperSq C +
              (n : ℝ) * ((n - 1 : ℕ) : ℝ) * strictUpperSq E ≤
            (n : ℝ) * (((n - 1 : ℕ) : ℝ) * strictLowerSq E) +
              (n : ℝ) * ((n - 1 : ℕ) : ℝ) * strictUpperSq E :=
          add_le_add hnormalScaled le_rfl
        _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
              (strictLowerSq E + strictUpperSq E) := by ring
    have hoff := strictLowerSq_add_strictUpperSq_le_frobSq E
    have hscale :
        (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
            (strictLowerSq E + strictUpperSq E) ≤
          (n : ℝ) * ((n - 1 : ℕ) : ℝ) * frobSq E := by
      exact mul_le_mul_of_nonneg_left hoff (mul_nonneg hn0 hr0)
    have hscaled :
        ((n - 1 : ℕ) : ℝ) * strictUpperSq T ≤
          (n : ℝ) * ((n - 1 : ℕ) : ℝ) * frobSq E :=
      hYoung.trans (htoOffdiag.trans hscale)
    have hrpos : 0 < ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < n - 1 by omega)
    rw [hNEq]
    have hcancel : strictUpperSq T ≤ (n : ℝ) * frobSq E := by
      refine (mul_le_mul_iff_of_pos_left hrpos).mp ?_
      calc
        ((n - 1 : ℕ) : ℝ) * strictUpperSq T ≤
            (n : ℝ) * ((n - 1 : ℕ) : ℝ) * frobSq E := hscaled
        _ = ((n - 1 : ℕ) : ℝ) * ((n : ℝ) * frobSq E) := by ring
    simpa [E] using hcancel

lemma diagonal_normal (d : Fin n → ℂ) :
    (Matrix.diagonal d)ᴴ * Matrix.diagonal d =
      Matrix.diagonal d * (Matrix.diagonal d)ᴴ := by
  have hstar : (Matrix.diagonal d)ᴴ = Matrix.diagonal (fun i => star (d i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.conjTranspose_apply]
    · have hji : j ≠ i := Ne.symm hij
      simp [Matrix.conjTranspose_apply, hij, hji]
  rw [hstar, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/-- **László's attaining upper witness in Schur coordinates.**  The diagonal
part `D` is normal and is exactly `‖N‖_F` away from `T=D+N`. -/
theorem laszlo_upper_witness_frobSq_of_split
    (T D N : Matrix (Fin n) (Fin n) ℂ)
    (hD : D = Matrix.diagonal (fun i => T i i))
    (hTeq : T = D + N) :
    Dᴴ * D = D * Dᴴ ∧ frobSq (T - D) = frobSq N := by
  constructor
  · rw [hD]
    exact diagonal_normal _
  · rw [hTeq]
    simp

/-- Complete squared nearest-normal package in Schur coordinates: a universal
lower bound for every normal competitor and the concrete diagonal witness. -/
theorem laszlo_nearest_normal_frobSq_of_schur
    (T D N : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (hD : D = Matrix.diagonal (fun i => T i i))
    (hN : ∀ i j, N i j = if j > i then T i j else 0)
    (hTeq : T = D + N) :
    (∀ C : Matrix (Fin n) (Fin n) ℂ,
        Cᴴ * C = C * Cᴴ → frobSq N ≤ (n : ℝ) * frobSq (T - C)) ∧
      Dᴴ * D = D * Dᴴ ∧ frobSq (T - D) = frobSq N := by
  refine ⟨?_, laszlo_upper_witness_frobSq_of_split T D N hD hTeq⟩
  intro C hC
  exact laszlo_lower_frobSq_of_upperTriangular T N C hn hTtri hN hC

lemma unitary_conj_normal
    (U M : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hM : Mᴴ * M = M * Mᴴ) :
    (U * M * Uᴴ)ᴴ * (U * M * Uᴴ) =
      (U * M * Uᴴ) * (U * M * Uᴴ)ᴴ := by
  have hUHU : Uᴴ * U = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff' (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hBH : (U * M * Uᴴ)ᴴ = U * Mᴴ * Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hBH]
  calc
    U * Mᴴ * Uᴴ * (U * M * Uᴴ) =
        U * Mᴴ * (Uᴴ * U) * M * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = U * (Mᴴ * M) * Uᴴ := by rw [hUHU]; simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = U * (M * Mᴴ) * Uᴴ := by rw [hM]
    _ = U * M * (Uᴴ * U) * Mᴴ * Uᴴ := by
      rw [hUHU]
      simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = U * M * Uᴴ * (U * Mᴴ * Uᴴ) := by simp only [Matrix.mul_assoc]

/-- **László's complete squared source endpoint in the original coordinates.**
For a Schur form `Uᴴ A U = T = D+N`, every normal matrix `B` obeys
`‖N‖_F² ≤ n ‖A-B‖_F²`; the explicit normal witness `U D Uᴴ` is exactly
`‖N‖_F` away.  This is the universal-lower/attaining-upper formulation of
`Δ_F(A)/sqrt(n) ≤ ν(A) ≤ Δ_F(A)` without assuming a value for `ν(A)`. -/
theorem laszlo_nearest_normal_frobSq_of_original_schur
    (A U T D N : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hUeq : Uᴴ * A * U = T)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (hD : D = Matrix.diagonal (fun i => T i i))
    (hN : ∀ i j, N i j = if j > i then T i j else 0)
    (hTeq : T = D + N) :
    (∀ B : Matrix (Fin n) (Fin n) ℂ,
        Bᴴ * B = B * Bᴴ → frobSq N ≤ (n : ℝ) * frobSq (A - B)) ∧
      ∃ B : Matrix (Fin n) (Fin n) ℂ,
        Bᴴ * B = B * Bᴴ ∧ frobSq (A - B) = frobSq N := by
  have hdiff : ∀ B : Matrix (Fin n) (Fin n) ℂ,
      T - Uᴴ * B * U = Uᴴ * (A - B) * U := by
    intro B
    rw [← hUeq]
    simp only [Matrix.mul_sub, Matrix.sub_mul]
  constructor
  · intro B hB
    let C : Matrix (Fin n) (Fin n) ℂ := Uᴴ * B * U
    have hC : Cᴴ * C = C * Cᴴ :=
      schurFactor_normal_of_normal B U C hU rfl hB
    have hlower := laszlo_lower_frobSq_of_upperTriangular T N C hn hTtri hN hC
    have htransport : frobSq (T - C) = frobSq (A - B) := by
      rw [show T - C = Uᴴ * (A - B) * U by simpa [C] using hdiff B]
      exact frobSq_unitary_conj (A - B) U hU
    rwa [htransport] at hlower
  · let B : Matrix (Fin n) (Fin n) ℂ := U * D * Uᴴ
    refine ⟨B, ?_, ?_⟩
    · exact unitary_conj_normal U D hU
        (laszlo_upper_witness_frobSq_of_split T D N hD hTeq).1
    · have hUHU : Uᴴ * U = 1 := by
        have h := (Matrix.mem_unitaryGroup_iff' (A := U)).mp hU
        rwa [Matrix.star_eq_conjTranspose] at h
      have hconjB : Uᴴ * B * U = D := by
        simp only [B, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᴴ U (D * (Uᴴ * U)), hUHU, Matrix.one_mul,
          Matrix.mul_one]
      have htransport : frobSq (T - D) = frobSq (A - B) := by
        calc
          frobSq (T - D) = frobSq (T - Uᴴ * B * U) := by rw [hconjB]
          _ = frobSq (Uᴴ * (A - B) * U) := by rw [hdiff B]
          _ = frobSq (A - B) := frobSq_unitary_conj (A - B) U hU
      rw [← htransport]
      exact (laszlo_upper_witness_frobSq_of_split T D N hD hTeq).2

/-- **Higham §18.1 / László, unconditional arbitrary-matrix endpoint.**
Every nonempty complex square matrix has a genuine Schur departure factor `N`
for which every normal competitor is at squared distance at least
`frobSq N / n`, while an explicitly constructed normal competitor has squared
distance exactly `frobSq N`. -/
theorem higham18_laszlo_nearest_normal_frobSq
    (A : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    ∃ (U T D N : Matrix (Fin n) (Fin n) ℂ),
      U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      Uᴴ * A * U = T ∧
      (∀ i j, j < i → T i j = 0) ∧
      D = Matrix.diagonal (fun i => T i i) ∧
      (∀ i j, N i j = if j > i then T i j else 0) ∧
      T = D + N ∧
      (∀ B : Matrix (Fin n) (Fin n) ℂ,
          Bᴴ * B = B * Bᴴ → frobSq N ≤ (n : ℝ) * frobSq (A - B)) ∧
      ∃ B : Matrix (Fin n) (Fin n) ℂ,
        Bᴴ * B = B * Bᴴ ∧ frobSq (A - B) = frobSq N := by
  obtain ⟨U, T, D, N, hU, hUeq, hTtri, hD, hN, hTeq⟩ :=
    schur_triangulation_diag_add_strictUpper A
  refine ⟨U, T, D, N, hU, hUeq, hTtri, hD, hN, hTeq, ?_⟩
  exact laszlo_nearest_normal_frobSq_of_original_schur
    A U T D N hn hU hUeq hTtri hD hN hTeq

end NumStability
