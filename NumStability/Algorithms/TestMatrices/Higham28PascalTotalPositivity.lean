/- Higham Chapter 28: strict total positivity of the Pascal matrix. -/

import NumStability.Algorithms.TestMatrices.Higham28Contracts
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Vandermonde

namespace NumStability

open scoped BigOperators
open Set

noncomputable def compoundMatrix (n k : ℕ) (A : RSqMat n) :
    Matrix (Set.powersetCard (Fin n) k) (Set.powersetCard (Fin n) k) ℝ :=
  LinearMap.toMatrix
    ((Pi.basisFun ℝ (Fin n)).exteriorPower k)
    ((Pi.basisFun ℝ (Fin n)).exteriorPower k)
    (exteriorPower.map k (Matrix.toLin' A))

theorem compoundMatrix_apply (n k : ℕ) (A : RSqMat n)
    (s t : Set.powersetCard (Fin n) k) :
    compoundMatrix n k A s t =
      Matrix.det (fun i j : Fin k =>
        A (Set.powersetCard.ofFinEmbEquiv.symm s i)
          (Set.powersetCard.ofFinEmbEquiv.symm t j)) := by
  simp only [compoundMatrix, LinearMap.toMatrix_apply,
    exteriorPower.basis_apply, exteriorPower.basis_repr_apply]
  rw [exteriorPower.map_apply_ιMulti_family]
  simp only [exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti]
  rw [← Matrix.det_transpose]
  apply congrArg Matrix.det
  ext i j
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Pi.basisFun_apply, Matrix.transpose_apply]

theorem compoundMatrix_mul (n k : ℕ) (A B : RSqMat n) :
    compoundMatrix n k (A * B) = compoundMatrix n k A * compoundMatrix n k B := by
  unfold compoundMatrix
  rw [Matrix.toLin'_mul, exteriorPower.map_comp]
  exact LinearMap.toMatrix_comp
    ((Pi.basisFun ℝ (Fin n)).exteriorPower k)
    ((Pi.basisFun ℝ (Fin n)).exteriorPower k)
    ((Pi.basisFun ℝ (Fin n)).exteriorPower k)
    _ _

/-- Every ordered square minor is nonnegative. -/
def IsTotallyNonnegative {m n : ℕ} (A : RMat m n) : Prop :=
  ∀ (k : ℕ) (r : Fin k → Fin m) (c : Fin k → Fin n),
    StrictMono r → StrictMono c →
      0 ≤ Matrix.det (fun i j => A (r i) (c j))

theorem isTotallyNonnegative_mul {n : ℕ} {A B : RSqMat n}
    (hA : IsTotallyNonnegative A) (hB : IsTotallyNonnegative B) :
    IsTotallyNonnegative (A * B) := by
  intro k r c hr hc
  let sr : Set.powersetCard (Fin n) k :=
    Set.powersetCard.ofFinEmbEquiv
      (OrderEmbedding.ofStrictMono r hr)
  let sc : Set.powersetCard (Fin n) k :=
    Set.powersetCard.ofFinEmbEquiv
      (OrderEmbedding.ofStrictMono c hc)
  have hdet : Matrix.det (fun i j => (A * B) (r i) (c j)) =
      compoundMatrix n k (A * B) sr sc := by
    rw [compoundMatrix_apply]
    congr 1
    funext i j
    simp [sr, sc]
  rw [hdet, compoundMatrix_mul, Matrix.mul_apply]
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg
  · rw [compoundMatrix_apply]
    simpa [sr] using hA k r (Set.powersetCard.ofFinEmbEquiv.symm s)
      hr (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono
  · rw [compoundMatrix_apply]
    simpa [sc] using hB k (Set.powersetCard.ofFinEmbEquiv.symm s) c
      (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono hc

/-- A unit lower-bidiagonal Pascal elimination step.  At stage `q`, rows
`q,q+1,...` add their predecessor. -/
noncomputable def pascalBidiagonalStep (n q : ℕ) : RSqMat n :=
  fun i j =>
    if i = j then 1
    else if j.val + 1 = i.val ∧ q ≤ i.val then 1
    else 0

theorem pascalBidiagonalStep_nonneg (n q : ℕ) (i j : Fin n) :
    0 ≤ pascalBidiagonalStep n q i j := by
  by_cases hij : i = j
  · simp [pascalBidiagonalStep, hij]
  · by_cases hs : j.val + 1 = i.val ∧ q ≤ i.val
    · simp [pascalBidiagonalStep, hij, hs]
    · simp [pascalBidiagonalStep, hij, hs]

theorem pascalBidiagonalStep_band {n q : ℕ} {i j : Fin n}
    (h : pascalBidiagonalStep n q i j ≠ 0) :
    j.val ≤ i.val ∧ i.val ≤ j.val + 1 := by
  simp only [pascalBidiagonalStep] at h
  split at h
  · next hij => subst j; omega
  · split at h
    · next hs => exact ⟨by omega, by omega⟩
    · simp at h

theorem lowerBidiagonal_ordered_minor_det
    {n k : ℕ} (M : RSqMat n)
    (hband : ∀ {i j}, M i j ≠ 0 →
      j.val ≤ i.val ∧ i.val ≤ j.val + 1)
    (r c : Fin k → Fin n) (hr : StrictMono r) (hc : StrictMono c) :
    Matrix.det (fun i j => M (r i) (c j)) =
      ∏ i : Fin k, M (r i) (c i) := by
  rw [Matrix.det_apply']
  classical
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin k))]
  · simp
  · intro σ _ hσ
    have hzero : ∃ j : Fin k, M (r (σ j)) (c j) = 0 := by
      by_contra hnone
      push_neg at hnone
      have hmono : Monotone σ := by
        intro a b hab
        rcases hab.eq_or_lt with rfl | hab
        · exact le_rfl
        have ha := hband (hnone a)
        have hb := hband (hnone b)
        have hcb : (c a).val + 1 ≤ (c b).val := by
          have hc' := hc hab
          exact hc'
        have hrr : (r (σ a)).val ≤ (r (σ b)).val := by omega
        exact hr.le_iff_le.mp hrr
      have hstrict : StrictMono σ :=
        hmono.strictMono_of_injective σ.injective
      have hσone : σ = 1 := by
        ext i
        exact le_antisymm (hstrict.le_id i) (hstrict.id_le i)
      exact hσ hσone
    rcases hzero with ⟨j, hj⟩
    have hp : (∏ i : Fin k, M (r (σ i)) (c i)) = 0 :=
      Finset.prod_eq_zero_iff.mpr ⟨j, Finset.mem_univ j, hj⟩
    rw [hp, mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem pascalBidiagonalStep_isTotallyNonnegative (n q : ℕ) :
    IsTotallyNonnegative (pascalBidiagonalStep n q) := by
  intro k r c hr hc
  rw [lowerBidiagonal_ordered_minor_det
    (pascalBidiagonalStep n q) (fun {_ _} => pascalBidiagonalStep_band) r c hr hc]
  exact Finset.prod_nonneg fun i _ => pascalBidiagonalStep_nonneg n q (r i) (c i)

theorem pascalBidiagonalStep_mul_apply
    {n : ℕ} (q : ℕ) (A : RSqMat n) (i j : Fin n) :
    (pascalBidiagonalStep n q * A) i j =
      A i j +
        if h : 0 < i.val ∧ q ≤ i.val then
          A ⟨i.val - 1, by omega⟩ j
        else 0 := by
  rw [Matrix.mul_apply]
  have hsplit :
      (∑ x : Fin n, pascalBidiagonalStep n q i x * A x j) =
        (∑ x : Fin n, if i = x then A x j else 0) +
          (∑ x : Fin n,
            if x.val + 1 = i.val ∧ q ≤ i.val then A x j else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hix : i = x
    · subst x
      simp [pascalBidiagonalStep]
    · by_cases hs : x.val + 1 = i.val ∧ q ≤ i.val
      · simp [pascalBidiagonalStep, hix, hs]
      · simp [pascalBidiagonalStep, hix, hs]
  rw [hsplit]
  have hdiag : (∑ x : Fin n, if i = x then A x j else 0) = A i j := by
    simp
  rw [hdiag]
  by_cases h : 0 < i.val ∧ q ≤ i.val
  · let im : Fin n := ⟨i.val - 1, by omega⟩
    have him : ∀ x : Fin n, x.val + 1 = i.val ∧ q ≤ i.val ↔ x = im := by
      intro x
      constructor
      · rintro ⟨hx, _⟩
        apply Fin.ext
        simp [im]
        omega
      · rintro rfl
        simp [im, h]
        omega
    simp_rw [him]
    simp [h, im]
  · have hnone : ∀ x : Fin n, ¬(x.val + 1 = i.val ∧ q ≤ i.val) := by
      intro x hx
      apply h
      exact ⟨by omega, hx.2⟩
    simp_rw [if_neg (hnone _)]
    simp [h]

noncomputable def pascalBidiagonalProduct (n : ℕ) : ℕ → RSqMat n
  | 0 => 1
  | q + 1 => pascalBidiagonalStep n (q + 1) * pascalBidiagonalProduct n q

noncomputable def pascalBidiagonalProductEntry (q i j : ℕ) : ℝ :=
  if i ≤ q then (Nat.choose i j : ℝ)
  else if i - q ≤ j then (Nat.choose q (j - (i - q)) : ℝ)
  else 0

theorem pascalBidiagonalProduct_zero_apply
    {n : ℕ} (i j : Fin n) :
    pascalBidiagonalProduct n 0 i j =
      pascalBidiagonalProductEntry 0 i.val j.val := by
  simp only [pascalBidiagonalProduct]
  simp only [pascalBidiagonalProductEntry]
  by_cases hi : i.val = 0
  · have hieq : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [hieq]
    by_cases hj : j.val = 0
    · simp [Matrix.one_apply, Fin.ext_iff, hj]
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hj
      simp [Matrix.one_apply, Fin.ext_iff, hm, Nat.choose_zero_succ]
  · have hipos : 0 < i.val := Nat.pos_of_ne_zero hi
    by_cases hij : i = j
    · subst j
      simp [Matrix.one_apply, hi, Nat.choose_self]
    · have hvne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      rcases lt_trichotomy j.val i.val with hji | hji | hijv
      · simp [Matrix.one_apply, hi, hij, hji, show ¬i.val ≤ j.val by omega]
      · exact (hvne hji.symm).elim
      · have hdiff : 0 < j.val - i.val := Nat.sub_pos_of_lt hijv
        simp [Matrix.one_apply, hi, hij, hijv.le, Nat.choose_eq_zero_of_lt hdiff]

theorem pascalBidiagonalProductEntry_succ (q i j : ℕ) :
    pascalBidiagonalProductEntry q i j +
        (if 0 < i ∧ q + 1 ≤ i then
          pascalBidiagonalProductEntry q (i - 1) j
        else 0) =
      pascalBidiagonalProductEntry (q + 1) i j := by
  by_cases hiq : i ≤ q
  · have hiqs : i ≤ q + 1 := by omega
    have hnot : ¬(0 < i ∧ q + 1 ≤ i) := by omega
    simp [pascalBidiagonalProductEntry, hiq, hiqs, hnot]
  · have hqi : q < i := by omega
    rcases eq_or_lt_of_le (show q + 1 ≤ i by omega) with hi | hi
    · subst i
      have hpos : 0 < q + 1 := by omega
      have hprev : q + 1 - 1 = q := by omega
      by_cases hj : j = 0
      · subst j
        simp [pascalBidiagonalProductEntry, hprev]
      · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
        simp only [pascalBidiagonalProductEntry]
        simp only [show ¬q + 1 ≤ q by omega, if_false,
          show q + 1 - q = 1 by omega,
          show 1 ≤ t + 1 by omega, if_true,
          show t + 1 - 1 = t by omega,
          show 0 < q + 1 ∧ q + 1 ≤ q + 1 by omega,
          show q + 1 - 1 = q by omega,
          show q ≤ q by omega,
          show q + 1 ≤ q + 1 by omega]
        exact_mod_cast (Nat.choose_succ_succ' q t).symm
    · have hpos : 0 < i := by omega
      have hupdate : 0 < i ∧ q + 1 ≤ i := ⟨hpos, by omega⟩
      let d := i - (q + 1)
      have hdpos : 0 < d := by simp [d]; omega
      have hiqsub : i - q = d + 1 := by simp [d]; omega
      have himqsub : i - 1 - q = d := by simp [d]; omega
      have himgt : q < i - 1 := by omega
      have hsuccgt : q + 1 < i := hi
      rcases lt_trichotomy j d with hjd | hjd | hdj
      · have hnotd : ¬d ≤ j := by omega
        have hnotds : ¬d + 1 ≤ j := by omega
        simp [pascalBidiagonalProductEntry, hiq, hupdate,
          show ¬i - 1 ≤ q by omega, show ¬i ≤ q + 1 by omega,
          hiqsub, himqsub, hnotd, hnotds,
          show i - (q + 1) = d by simp [d],
          show ¬i - (q + 1) ≤ j by omega]
      · subst j
        have hnotds : ¬d + 1 ≤ d := by omega
        have hidecomp : i = d + (q + 1) := by simp [d]; omega
        simp [pascalBidiagonalProductEntry, hiq, hupdate,
          show ¬i - 1 ≤ q by omega, show ¬i ≤ q + 1 by omega,
          hiqsub, himqsub, hnotds, hidecomp,
          show i - (q + 1) = d by simp [d]]
        simp [hdpos.ne', show ¬d + (q + 1) ≤ q by omega]
      · obtain ⟨t, ht⟩ : ∃ t, j = d + (t + 1) := by
          refine ⟨j - d - 1, ?_⟩
          omega
        subst j
        have hdle : d ≤ d + (t + 1) := by omega
        have hdsle : d + 1 ≤ d + (t + 1) := by omega
        simp only [pascalBidiagonalProductEntry,
          show ¬i ≤ q by omega, if_false, hiqsub, hdsle, if_true,
          show d + (t + 1) - (d + 1) = t by omega,
          hupdate, show ¬i - 1 ≤ q by omega, himqsub, hdle,
          show d + (t + 1) - d = t + 1 by omega,
          show ¬i ≤ q + 1 by omega,
          show i - (q + 1) = d by simp [d],
          show d ≤ d + (t + 1) by omega]
        exact_mod_cast (Nat.choose_succ_succ' q t).symm

theorem pascalBidiagonalProduct_apply
    {n : ℕ} (q : ℕ) (i j : Fin n) :
    pascalBidiagonalProduct n q i j =
      pascalBidiagonalProductEntry q i.val j.val := by
  induction q generalizing i j with
  | zero => exact pascalBidiagonalProduct_zero_apply i j
  | succ q ih =>
      rw [pascalBidiagonalProduct, pascalBidiagonalStep_mul_apply]
      rw [ih i j]
      split
      · next h =>
        rw [ih]
        have hs := pascalBidiagonalProductEntry_succ q i.val j.val
        rw [if_pos h] at hs
        simpa using hs
      · next h =>
        have hs := pascalBidiagonalProductEntry_succ q i.val j.val
        rw [if_neg h] at hs
        exact hs

theorem pascalBidiagonalProduct_eq_pascalLower (n : ℕ) :
    pascalBidiagonalProduct n (n - 1) = pascalLower n := by
  ext i j
  rw [pascalBidiagonalProduct_apply]
  unfold pascalBidiagonalProductEntry pascalLower
  have hi : i.val ≤ n - 1 := by omega
  simp [hi]

theorem identity_isTotallyNonnegative (n : ℕ) :
    IsTotallyNonnegative (1 : RSqMat n) := by
  intro k r c hr hc
  rw [lowerBidiagonal_ordered_minor_det (1 : RSqMat n)
    (hband := fun {i j} h => by
      have hij : i = j := by
        by_contra hne
        simp [Matrix.one_apply, hne] at h
      subst j
      omega)
    r c hr hc]
  · exact Finset.prod_nonneg fun i _ => by
      simp only [Matrix.one_apply]
      split <;> norm_num

theorem pascalBidiagonalProduct_isTotallyNonnegative (n q : ℕ) :
    IsTotallyNonnegative (pascalBidiagonalProduct n q) := by
  induction q with
  | zero => simpa [pascalBidiagonalProduct] using identity_isTotallyNonnegative n
  | succ q ih =>
      rw [pascalBidiagonalProduct]
      exact isTotallyNonnegative_mul
        (pascalBidiagonalStep_isTotallyNonnegative n (q + 1)) ih

theorem pascalLower_isTotallyNonnegative (n : ℕ) :
    IsTotallyNonnegative (pascalLower n) := by
  rw [← pascalBidiagonalProduct_eq_pascalLower n]
  exact pascalBidiagonalProduct_isTotallyNonnegative n (n - 1)

theorem isTotallyNonnegative_transpose {n : ℕ} {A : RSqMat n}
    (hA : IsTotallyNonnegative A) :
    IsTotallyNonnegative A.transpose := by
  intro k r c hr hc
  have h := hA k c r hc hr
  rw [← Matrix.det_transpose] at h
  exact h

private theorem det_eval_descPochhammer_eq_factorial_mul_choose
    {k : ℕ} (v : Fin k → ℕ) :
    Matrix.det (fun i j : Fin k =>
      (descPochhammer ℝ j).eval (v i : ℝ)) =
      (∏ j : Fin k, (Nat.factorial j : ℝ)) *
        Matrix.det (fun i j : Fin k => (Nat.choose (v i) j : ℝ)) := by
  convert Matrix.det_mul_row
    (fun j : Fin k => (Nat.factorial j : ℝ))
    (fun i j : Fin k => (Nat.choose (v i) j : ℝ))
  · rw [Matrix.of_apply, descPochhammer_eval_eq_descFactorial]
    congr
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose _ _

private theorem det_choose_initial_columns_pos
    {n k : ℕ} (r : Fin k → Fin n) (hr : StrictMono r) :
    0 < Matrix.det (fun i j : Fin k =>
      (Nat.choose (r i).val j.val : ℝ)) := by
  let v : Fin k → ℝ := fun i => (r i).val
  have heval := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    v (fun j : Fin k => descPochhammer ℝ j)
    (fun j => descPochhammer_natDegree ℝ j)
    (fun j => monic_descPochhammer ℝ j)
  have hvand : 0 < Matrix.det (Matrix.vandermonde v) := by
    rw [Matrix.det_vandermonde]
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hrij : (r i).val < (r j).val := hr hij
    dsimp [v]
    exact sub_pos.mpr (by exact_mod_cast hrij)
  have hfac : 0 < ∏ j : Fin k, (Nat.factorial j : ℝ) := by
    positivity
  have hscale := det_eval_descPochhammer_eq_factorial_mul_choose
    (fun i : Fin k => (r i).val)
  have hcombined : Matrix.det (Matrix.vandermonde v) =
      (∏ j : Fin k, (Nat.factorial j : ℝ)) *
        Matrix.det (fun i j : Fin k => (Nat.choose (r i).val j.val : ℝ)) := by
    rw [heval]
    simpa [v, Matrix.of_apply] using hscale
  nlinarith [hcombined]

theorem pascalLower_initial_minor_pos
    {n k : ℕ} (r : Fin k → Fin n) (hr : StrictMono r) :
    0 < Matrix.det (fun i j : Fin k =>
      pascalLower n (r i)
        (Fin.castLE (by
          simpa using Fintype.card_le_of_injective r hr.injective) j)) := by
  simpa [pascalLower] using det_choose_initial_columns_pos r hr

/-- Higham, Section 28.4, p. 520: every square minor of positive order of
the symmetric Pascal matrix is strictly positive. -/
theorem pascalMatrix_isStrictlyTotallyPositive (n : ℕ) :
    IsStrictlyTotallyPositive (pascalMatrix n) := by
  intro k hk r c hr hc
  have hkn : k ≤ n := by
    simpa using Fintype.card_le_of_injective r hr.injective
  let rz : Fin k → Fin n := Fin.castLE hkn
  have hrz : StrictMono rz := Fin.strictMono_castLE hkn
  let sr : Set.powersetCard (Fin n) k :=
    Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.ofStrictMono r hr)
  let sc : Set.powersetCard (Fin n) k :=
    Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.ofStrictMono c hc)
  let sz : Set.powersetCard (Fin n) k :=
    Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.ofStrictMono rz hrz)
  have hdet : Matrix.det (fun i j => pascalMatrix n (r i) (c j)) =
      compoundMatrix n k (pascalMatrix n) sr sc := by
    rw [compoundMatrix_apply]
    congr 1
    funext i j
    simp [sr, sc]
  rw [hdet, pascalMatrix_eq_lower_mul_transpose, compoundMatrix_mul,
    Matrix.mul_apply]
  have hL := pascalLower_isTotallyNonnegative n
  have hLT := isTotallyNonnegative_transpose hL
  apply Finset.sum_pos'
  · intro s _
    apply mul_nonneg
    · rw [compoundMatrix_apply]
      simpa [sr] using hL k r (Set.powersetCard.ofFinEmbEquiv.symm s)
        hr (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono
    · rw [compoundMatrix_apply]
      simpa [sc] using hLT k (Set.powersetCard.ofFinEmbEquiv.symm s) c
        (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono hc
  · refine ⟨sz, Finset.mem_univ _, ?_⟩
    apply mul_pos
    · rw [compoundMatrix_apply]
      simpa [sr, sz, rz] using pascalLower_initial_minor_pos r hr
    · rw [compoundMatrix_apply]
      have hcp := pascalLower_initial_minor_pos c hc
      let M : Matrix (Fin k) (Fin k) ℝ := fun i j =>
        pascalLower n (c i) (rz j)
      have hcpM : 0 < Matrix.det M := by
        simpa [M, rz] using hcp
      have ht : 0 < Matrix.det M.transpose := by
        rw [Matrix.det_transpose]
        exact hcpM
      have hgoal : 0 < Matrix.det (fun i j : Fin k =>
          (pascalLower n).transpose (rz i) (c j)) := by
        simpa only [Matrix.transpose_apply] using ht
      simpa [sc, sz] using hgoal

end NumStability
