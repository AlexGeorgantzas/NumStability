-- Analysis/VectorNorms/Basic.lean
--
-- Foundational complex-vector norm definitions and elementary laws.

import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Basic complex-vector norm infrastructure

Defines `CVec`, abstract complex-vector norm predicates, concrete one-, two-,
infinity-, and `L^p` norms, and their foundational algebraic/order lemmas.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Complex vector indexed by `Fin n`, the source domain for Higham Chapter 6
    vector norms. -/
abbrev CVec (n : ℕ) := Fin n → ℂ

/-- Pointwise vector addition, kept explicit so Chapter 6 abstract norm
    predicates do not depend on notation choices. -/
noncomputable def complexVecAdd {n : ℕ} (x y : CVec n) : CVec n :=
  fun i => x i + y i

/-- Scalar multiplication for source-facing complex vectors. -/
noncomputable def complexVecSMul {n : ℕ} (a : ℂ) (x : CVec n) : CVec n :=
  fun i => a * x i

/-- Componentwise absolute-value vector, embedded back into `C^n`. -/
noncomputable def complexAbsVec {n : ℕ} (x : CVec n) : CVec n :=
  fun i => (‖x i‖ : ℂ)

/-- Componentwise complex conjugation on source-facing finite vectors. -/
noncomputable def complexConjVec {n : ℕ} (x : CVec n) : CVec n :=
  fun i => star (x i)

@[simp]
lemma complexAbsVec_norm_apply {n : ℕ} (x : CVec n) (i : Fin n) :
    ‖complexAbsVec x i‖ = ‖x i‖ := by
  simp [complexAbsVec]

@[simp]
lemma complexAbsVec_idem {n : ℕ} (x : CVec n) :
    complexAbsVec (complexAbsVec x) = complexAbsVec x := by
  ext i
  simp [complexAbsVec]

@[simp]
lemma complexConjVec_involutive {n : ℕ} (x : CVec n) :
    complexConjVec (complexConjVec x) = x := by
  ext i
  simp [complexConjVec]

/-- Componentwise absolute-value order used in Higham, Definition 6.1. -/
def componentwiseAbsLe {n : ℕ} (x y : CVec n) : Prop :=
  ∀ i : Fin n, ‖x i‖ ≤ ‖y i‖

/-- Abstract vector norm axioms for functions `C^n -> R`, matching the three
    axioms listed at the start of Higham, Chapter 6, Section 6.1. -/
structure IsComplexVectorNorm {n : ℕ} (ν : CVec n → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ν x
  eq_zero_iff : ∀ x, ν x = 0 ↔ x = 0
  smul : ∀ (a : ℂ) (x : CVec n), ν (complexVecSMul a x) = ‖a‖ * ν x
  add_le : ∀ x y : CVec n, ν (complexVecAdd x y) ≤ ν x + ν y

/-- Source-facing finite complex `L^p` norm, implemented using Mathlib's
    finite-product `PiLp` norm.  The hypothesis `1 ≤ p` is required only when
    the norm axioms are used. -/
noncomputable def complexVecLpNorm {n : ℕ} (p : ℝ≥0∞) (x : CVec n) : ℝ :=
  ‖WithLp.toLp p x‖

theorem complexVecLpNorm_two_eq_toLp {n : ℕ} (x : CVec n) :
    complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) x =
      ‖WithLp.toLp (2 : ENNReal) x‖ := by
  have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
  rw [complexVecLpNorm, h2]

theorem complexVecLpNorm_two_ofLp_eq {n : ℕ}
    (x : EuclideanSpace ℂ (Fin n)) :
    complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) (WithLp.ofLp x) = ‖x‖ := by
  have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
  rw [complexVecLpNorm, h2, WithLp.toLp_ofLp]

/-- Mathlib's finite-product `L^p` norm satisfies the vector-norm axioms for
    every exponent with `1 ≤ p`, including `p = ∞`. -/
theorem complexVecLpNorm_isComplexVectorNorm {n : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsComplexVectorNorm (complexVecLpNorm (n := n) p) := by
  constructor
  · intro x
    exact norm_nonneg _
  · intro x
    constructor
    · intro hx
      have h : WithLp.toLp p x = 0 := norm_eq_zero.mp hx
      exact WithLp.toLp_injective p h
    · intro hx
      subst hx
      simp [complexVecLpNorm]
  · intro a x
    unfold complexVecLpNorm complexVecSMul
    change ‖WithLp.toLp p (a • x)‖ = ‖a‖ * ‖WithLp.toLp p x‖
    rw [WithLp.toLp_smul]
    exact norm_smul a (WithLp.toLp p x)
  · intro x y
    unfold complexVecLpNorm complexVecAdd
    change ‖WithLp.toLp p (x + y)‖ ≤ ‖WithLp.toLp p x‖ + ‖WithLp.toLp p y‖
    rw [WithLp.toLp_add]
    exact norm_add_le _ _

/-- Every coordinate is bounded by the finite-product `L^p` norm.  This is the
    general basis-vector lower-bound ingredient for matrix p-norm comparisons. -/
lemma complexVecLpNorm_coord_le {n : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (x : CVec n) (j : Fin n) :
    ‖x j‖ ≤ complexVecLpNorm p x := by
  unfold complexVecLpNorm
  exact PiLp.norm_apply_le (WithLp.toLp p x) j

lemma complexVecLpNorm_coord_le_one_of_le_one {n : ℕ} (p : ℝ≥0∞)
    [Fact (1 ≤ p)] {x : CVec n}
    (hx : complexVecLpNorm p x ≤ 1) (j : Fin n) :
    ‖x j‖ ≤ 1 :=
  (complexVecLpNorm_coord_le p x j).trans hx

/-- Finite-product `L^p` norm expanded as a finite real power sum for
    positive finite real exponents. -/
lemma complexVecLpNorm_ofReal_eq_sum_rpow {n : ℕ} {p : ℝ} (hp : 0 < p)
    (x : CVec n) :
    complexVecLpNorm (ENNReal.ofReal p) x =
      (∑ i : Fin n, ‖x i‖ ^ p) ^ p⁻¹ := by
  have hp_nonneg : 0 ≤ p := le_of_lt hp
  unfold complexVecLpNorm
  rw [PiLp.norm_eq_sum]
  · have hp_toReal : (ENNReal.ofReal p).toReal = p :=
      ENNReal.toReal_ofReal hp_nonneg
    simp [hp_toReal, one_div]
  · have hp_toReal : (ENNReal.ofReal p).toReal = p :=
      ENNReal.toReal_ofReal hp_nonneg
    simpa [hp_toReal] using hp

/-- Raising the finite-product `L^p` norm back to `p` recovers the finite
    power sum for positive finite real exponents. -/
lemma complexVecLpNorm_rpow_eq_sum_rpow {n : ℕ} {p : ℝ} (hp : 0 < p)
    (x : CVec n) :
    complexVecLpNorm (ENNReal.ofReal p) x ^ p =
      ∑ i : Fin n, ‖x i‖ ^ p := by
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, ‖x i‖ ^ p :=
    Finset.sum_nonneg (fun i _hi =>
      Real.rpow_nonneg (norm_nonneg (x i)) p)
  rw [complexVecLpNorm_ofReal_eq_sum_rpow hp x]
  exact Real.rpow_inv_rpow hsum_nonneg hp.ne'

/-- The all-ones vector has finite-product `L^p` norm `n^(1/p)`.
    This is the sharpness witness for the finite vector comparison in
    Higham equation (6.4). -/
lemma complexVecLpNorm_const_one_ofReal {n : ℕ} {p : ℝ} (hp : 0 < p) :
    complexVecLpNorm (n := n) (ENNReal.ofReal p) (fun _ : Fin n => (1 : ℂ)) =
      (n : ℝ) ^ p⁻¹ := by
  rw [complexVecLpNorm_ofReal_eq_sum_rpow hp]
  simp [Finset.sum_const, Fintype.card_fin]

/-- The all-ones vector is nonzero when the finite dimension is nonempty. -/
lemma complexVecConstOne_ne_zero {n : ℕ} (hn : 0 < n) :
    (fun _ : Fin n => (1 : ℂ)) ≠ 0 := by
  intro hzero
  let j : Fin n := ⟨0, hn⟩
  have hj := congrFun hzero j
  norm_num at hj

/-- Finite real-exponent `Lp` norms are absolute: replacing each complex
    coordinate by its absolute value does not change the norm. -/
lemma complexVecLpNorm_ofReal_abs_eq {n : ℕ} {p : ℝ} (hp : 0 < p)
    (x : CVec n) :
    complexVecLpNorm (ENNReal.ofReal p) (complexAbsVec x) =
      complexVecLpNorm (ENNReal.ofReal p) x := by
  rw [complexVecLpNorm_ofReal_eq_sum_rpow hp,
    complexVecLpNorm_ofReal_eq_sum_rpow hp]
  apply congrArg (fun r : ℝ => r ^ p⁻¹)
  apply Finset.sum_congr rfl
  intro i _hi
  simp [complexAbsVec]

/-- Finite real-exponent `Lp` norms are invariant under componentwise complex
    conjugation. -/
lemma complexVecLpNorm_ofReal_conj_eq {n : ℕ} {p : ℝ} (hp : 0 < p)
    (x : CVec n) :
    complexVecLpNorm (ENNReal.ofReal p) (complexConjVec x) =
      complexVecLpNorm (ENNReal.ofReal p) x := by
  rw [complexVecLpNorm_ofReal_eq_sum_rpow hp,
    complexVecLpNorm_ofReal_eq_sum_rpow hp]
  apply congrArg (fun r : ℝ => r ^ p⁻¹)
  apply Finset.sum_congr rfl
  intro i _hi
  simp [complexConjVec]

/-- Finite complex Hölder inequality for the source-facing `L^p` family.
    This covers finite conjugate exponents; endpoint cases are handled by
    separate `1`/`∞` lemmas. -/
theorem complexVecLpNorm_holder {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (a x : CVec n) :
    ‖∑ i : Fin n, a i * x i‖ ≤
      complexVecLpNorm (ENNReal.ofReal q) a * complexVecLpNorm (ENNReal.ofReal p) x := by
  have hsum_norm : ‖∑ i : Fin n, a i * x i‖ ≤ ∑ i : Fin n, ‖a i‖ * ‖x i‖ := by
    calc
      ‖∑ i : Fin n, a i * x i‖ ≤ ∑ i : Fin n, ‖a i * x i‖ := norm_sum_le _ _
      _ = ∑ i : Fin n, ‖a i‖ * ‖x i‖ := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact norm_mul (a i) (x i)
  have hholder :
      (∑ i : Fin n, ‖a i‖ * ‖x i‖) ≤
        (∑ i : Fin n, ‖a i‖ ^ q) ^ (1 / q) *
          (∑ i : Fin n, ‖x i‖ ^ p) ^ (1 / p) := by
    simpa using
      (Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
        (f := fun i : Fin n => ‖a i‖) (g := fun i : Fin n => ‖x i‖)
        hpq.symm (by intro i _hi; exact norm_nonneg (a i))
        (by intro i _hi; exact norm_nonneg (x i)))
  have hp_toReal : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal hpq.nonneg
  have hq_toReal : (ENNReal.ofReal q).toReal = q :=
    ENNReal.toReal_ofReal hpq.symm.nonneg
  calc
    ‖∑ i : Fin n, a i * x i‖ ≤ ∑ i : Fin n, ‖a i‖ * ‖x i‖ := hsum_norm
    _ ≤ (∑ i : Fin n, ‖a i‖ ^ q) ^ (1 / q) *
        (∑ i : Fin n, ‖x i‖ ^ p) ^ (1 / p) := hholder
    _ = complexVecLpNorm (ENNReal.ofReal q) a * complexVecLpNorm (ENNReal.ofReal p) x := by
        unfold complexVecLpNorm
        rw [PiLp.norm_eq_sum, PiLp.norm_eq_sum]
        · simp [hp_toReal, hq_toReal]
        · rw [hp_toReal]
          exact hpq.pos
        · rw [hq_toReal]
          exact hpq.symm.pos

/-- Higham, 2nd ed., Chapter 6, Definition 6.1:
    a vector norm is absolute if `‖ |x| ‖ = ‖x‖`. -/
def IsAbsoluteComplexVectorNorm {n : ℕ} (ν : CVec n → ℝ) : Prop :=
  ∀ x : CVec n, ν (complexAbsVec x) = ν x

/-- Higham, 2nd ed., Chapter 6, Definition 6.1:
    a vector norm is monotone if `|x| <= |y|` componentwise implies
    `‖x‖ <= ‖y‖`. -/
def IsMonotoneComplexVectorNorm {n : ℕ} (ν : CVec n → ℝ) : Prop :=
  ∀ x y : CVec n, componentwiseAbsLe x y → ν x ≤ ν y

/-- Change the sign of one coordinate. -/
noncomputable def flipCoord {n : ℕ} (j : Fin n) (x : CVec n) : CVec n :=
  fun i => if i = j then -x i else x i

/-- Scale one coordinate by a real scalar. -/
noncomputable def scaleCoord {n : ℕ} (j : Fin n) (t : ℝ) (x : CVec n) : CVec n :=
  fun i => if i = j then (t : ℂ) * x i else x i

lemma complexAbsVec_flipCoord {n : ℕ} (j : Fin n) (x : CVec n) :
    complexAbsVec (flipCoord j x) = complexAbsVec x := by
  ext i
  by_cases h : i = j
  · simp [complexAbsVec, flipCoord, h]
  · simp [complexAbsVec, flipCoord, h]

lemma absolute_norm_flipCoord_eq {n : ℕ} {ν : CVec n → ℝ}
    (habs : IsAbsoluteComplexVectorNorm ν) (j : Fin n) (x : CVec n) :
    ν (flipCoord j x) = ν x := by
  calc
    ν (flipCoord j x) = ν (complexAbsVec (flipCoord j x)) := (habs (flipCoord j x)).symm
    _ = ν (complexAbsVec x) := by rw [complexAbsVec_flipCoord]
    _ = ν x := habs x

/-- A one-coordinate contraction does not increase an absolute norm. -/
lemma absolute_norm_scaleCoord_le {n : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) (habs : IsAbsoluteComplexVectorNorm ν)
    (j : Fin n) (t : ℝ) (x : CVec n) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ν (scaleCoord j t x) ≤ ν x := by
  let a : ℝ := (1 + t) / 2
  let b : ℝ := (1 - t) / 2
  have ha0 : 0 ≤ a := by
    dsimp [a]
    nlinarith
  have hb0 : 0 ≤ b := by
    dsimp [b]
    nlinarith
  have hab_sum : a + b = 1 := by
    dsimp [a, b]
    ring
  have hflip : ν (flipCoord j x) = ν x := absolute_norm_flipCoord_eq habs j x
  have hrepr :
      scaleCoord j t x =
        complexVecAdd (complexVecSMul (a : ℂ) x)
          (complexVecSMul (b : ℂ) (flipCoord j x)) := by
    ext i
    by_cases h : i = j
    · simp [scaleCoord, complexVecAdd, complexVecSMul, flipCoord, h, a, b]
      ring
    · simp [scaleCoord, complexVecAdd, complexVecSMul, flipCoord, h, a, b]
      ring
  calc
    ν (scaleCoord j t x)
        = ν (complexVecAdd (complexVecSMul (a : ℂ) x)
            (complexVecSMul (b : ℂ) (flipCoord j x))) := by rw [hrepr]
    _ ≤ ν (complexVecSMul (a : ℂ) x) +
          ν (complexVecSMul (b : ℂ) (flipCoord j x)) :=
        hν.add_le _ _
    _ = a * ν x + b * ν (flipCoord j x) := by
        rw [hν.smul, hν.smul, Complex.norm_of_nonneg ha0, Complex.norm_of_nonneg hb0]
    _ = (a + b) * ν x := by
        rw [hflip]
        ring
    _ = ν x := by
        rw [hab_sum]
        ring

/-- Scale the coordinates in a finite set by prescribed real factors. -/
noncomputable def scaleOn {n : ℕ} (s : Finset (Fin n)) (θ : Fin n → ℝ)
    (x : CVec n) : CVec n :=
  fun i => if i ∈ s then (θ i : ℂ) * x i else x i

lemma scaleOn_insert_eq_scaleCoord {n : ℕ} (s : Finset (Fin n)) (a : Fin n)
    (ha : a ∉ s) (θ : Fin n → ℝ) (x : CVec n) :
    scaleOn (insert a s) θ x = scaleCoord a (θ a) (scaleOn s θ x) := by
  ext i
  by_cases hi : i = a
  · subst hi
    simp [scaleOn, scaleCoord, ha]
  · by_cases his : i ∈ s
    · have hins : i ∈ insert a s := by exact Finset.mem_insert.mpr (Or.inr his)
      simp [scaleOn, scaleCoord, hi, his, hins]
    · have hins : i ∉ insert a s := by
        intro hmem
        rcases Finset.mem_insert.mp hmem with hia | hs
        · exact hi hia
        · exact his hs
      simp [scaleOn, scaleCoord, hi, his, hins]

/-- Iterating one-coordinate contractions over a finite set cannot increase an
    absolute norm. -/
lemma absolute_norm_scaleOn_le {n : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) (habs : IsAbsoluteComplexVectorNorm ν)
    (s : Finset (Fin n)) (θ : Fin n → ℝ) (x : CVec n)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθ1 : ∀ i, θ i ≤ 1) :
    ν (scaleOn s θ x) ≤ ν x := by
  induction s using Finset.induction_on with
  | empty =>
      have hscale : scaleOn (∅ : Finset (Fin n)) θ x = x := by
        ext i
        simp [scaleOn]
      rw [hscale]
  | insert a s ha ih =>
      rw [scaleOn_insert_eq_scaleCoord s a ha θ x]
      exact (absolute_norm_scaleCoord_le hν habs a (θ a) (scaleOn s θ x)
        (hθ0 a) (hθ1 a)).trans (ih)

lemma exists_unit_interval_scale_of_abs_le {n : ℕ} (x y : CVec n)
    (hxy : componentwiseAbsLe x y) :
    ∃ θ : Fin n → ℝ,
      (∀ i, 0 ≤ θ i) ∧ (∀ i, θ i ≤ 1) ∧
        complexAbsVec x = scaleOn Finset.univ θ (complexAbsVec y) := by
  let θ : Fin n → ℝ := fun i => if ‖y i‖ = 0 then 0 else ‖x i‖ / ‖y i‖
  refine ⟨θ, ?_, ?_, ?_⟩
  · intro i
    by_cases hy : ‖y i‖ = 0
    · simp [θ, hy]
    · dsimp [θ]
      rw [if_neg hy]
      exact div_nonneg (norm_nonneg (x i)) (norm_nonneg (y i))
  · intro i
    by_cases hy : ‖y i‖ = 0
    · simp [θ, hy]
    · have hypos : 0 < ‖y i‖ := lt_of_le_of_ne (norm_nonneg (y i)) (Ne.symm hy)
      dsimp [θ]
      rw [if_neg hy]
      exact (div_le_one hypos).mpr (hxy i)
  · ext i
    have hreal : ‖x i‖ = θ i * ‖y i‖ := by
      by_cases hy : ‖y i‖ = 0
      · have hx0 : ‖x i‖ = 0 := by
          exact le_antisymm ((hxy i).trans (le_of_eq hy)) (norm_nonneg _)
        simp [θ, hy, hx0]
      · have hyne : ‖y i‖ ≠ 0 := hy
        dsimp [θ]
        rw [if_neg hy]
        field_simp [hyne]
    have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
    simpa [complexAbsVec, scaleOn, Complex.ofReal_mul] using hc

/-- The easy direction of Higham, Theorem 6.2: monotone vector norms are
    absolute. -/
theorem absolute_of_monotone_complexVectorNorm {n : ℕ} {ν : CVec n → ℝ}
    (hmono : IsMonotoneComplexVectorNorm ν) :
    IsAbsoluteComplexVectorNorm ν := by
  intro x
  apply le_antisymm
  · exact hmono (complexAbsVec x) x (by intro i; simp)
  · exact hmono x (complexAbsVec x) (by intro i; simp)

/-- Higham, 2nd ed., Chapter 6, Definition 6.1 / Theorem 6.2
    (Bauer-Stoer-Witzgall): an abstract norm on `C^n` is monotone iff it is
    absolute.  The proof formalizes the coordinate-contraction argument rather
    than importing the cited theorem as a hypothesis. -/
theorem monotone_iff_absolute_complexVectorNorm {n : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) :
    IsMonotoneComplexVectorNorm ν ↔ IsAbsoluteComplexVectorNorm ν := by
  constructor
  · exact absolute_of_monotone_complexVectorNorm
  · intro habs x y hxy
    obtain ⟨θ, hθ0, hθ1, hscale⟩ := exists_unit_interval_scale_of_abs_le x y hxy
    calc
      ν x = ν (complexAbsVec x) := (habs x).symm
      _ = ν (scaleOn Finset.univ θ (complexAbsVec y)) := by rw [hscale]
      _ ≤ ν (complexAbsVec y) := absolute_norm_scaleOn_le hν habs Finset.univ θ
        (complexAbsVec y) hθ0 hθ1
      _ = ν y := habs y

/-- Source-facing theorem name for Higham, 2nd ed., Chapter 6, Theorem 6.2. -/
theorem absolute_norm_iff_monotone_norm {n : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) :
    IsAbsoluteComplexVectorNorm ν ↔ IsMonotoneComplexVectorNorm ν := by
  exact (monotone_iff_absolute_complexVectorNorm hν).symm

/-- Finite real-exponent `Lp` norms are monotone in the componentwise absolute
    value order of Definition 6.1. -/
theorem complexVecLpNorm_ofReal_monotone {n : ℕ} {p : ℝ} (hp : 1 ≤ p) :
    IsMonotoneComplexVectorNorm (complexVecLpNorm (n := n) (ENNReal.ofReal p)) := by
  have hfact : 1 ≤ ENNReal.ofReal p := by
    rw [ENNReal.one_le_ofReal]
    exact hp
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨hfact⟩
  exact (absolute_norm_iff_monotone_norm
    (complexVecLpNorm_isComplexVectorNorm (n := n) (ENNReal.ofReal p))).mp
      (fun x => complexVecLpNorm_ofReal_abs_eq (lt_of_lt_of_le zero_lt_one hp) x)

/-- Embed a real source vector into the complex-vector norm infrastructure. -/
noncomputable def realVecToComplex {n : ℕ} (x : Fin n → ℝ) : CVec n :=
  fun i => (x i : ℂ)

/-- Real-vector specialization of the monotonicity consequence of an absolute
    complex vector norm. -/
lemma realVecToComplex_norm_le_of_abs_le {n : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) (habs : IsAbsoluteComplexVectorNorm ν)
    {x y : Fin n → ℝ} (hy : ∀ i, 0 ≤ y i)
    (hxy : ∀ i, |x i| ≤ y i) :
    ν (realVecToComplex x) ≤ ν (realVecToComplex y) := by
  have hmono : IsMonotoneComplexVectorNorm ν :=
    (monotone_iff_absolute_complexVectorNorm hν).mpr habs
  apply hmono
  intro i
  simpa [realVecToComplex, Real.norm_eq_abs, abs_of_nonneg (hy i)] using hxy i

/-- Homogeneity for a nonnegative real scalar after embedding real vectors into
    `CVec`. -/
lemma realVecToComplex_norm_smul_nonneg {n : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) (a : ℝ) (ha : 0 ≤ a)
    (x : Fin n → ℝ) :
    ν (realVecToComplex (fun i => a * x i)) =
      a * ν (realVecToComplex x) := by
  have h := hν.smul (a : ℂ) (realVecToComplex x)
  calc
    ν (realVecToComplex (fun i => a * x i))
        = ν (complexVecSMul (a : ℂ) (realVecToComplex x)) := by
            congr 1
            ext i
            simp [realVecToComplex, complexVecSMul]
    _ = ‖(a : ℂ)‖ * ν (realVecToComplex x) := h
    _ = a * ν (realVecToComplex x) := by
            rw [Complex.norm_of_nonneg ha]

/-- Negating an embedded real vector does not change any complex vector norm. -/
lemma realVecToComplex_norm_neg {n : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) (x : Fin n → ℝ) :
    ν (realVecToComplex (fun i => -x i)) =
      ν (realVecToComplex x) := by
  have h := hν.smul (-1 : ℂ) (realVecToComplex x)
  calc
    ν (realVecToComplex (fun i => -x i))
        = ν (complexVecSMul (-1 : ℂ) (realVecToComplex x)) := by
            congr 1
            ext i
            simp [realVecToComplex, complexVecSMul]
    _ = ‖(-1 : ℂ)‖ * ν (realVecToComplex x) := h
    _ = ν (realVecToComplex x) := by
            norm_num

/-- Triangle inequality after embedding real vectors into `CVec`. -/
lemma realVecToComplex_norm_add_le {n : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) (x y : Fin n → ℝ) :
    ν (realVecToComplex (fun i => x i + y i)) ≤
      ν (realVecToComplex x) + ν (realVecToComplex y) := by
  have h := hν.add_le (realVecToComplex x) (realVecToComplex y)
  calc
    ν (realVecToComplex (fun i => x i + y i))
        = ν (complexVecAdd (realVecToComplex x) (realVecToComplex y)) := by
            congr 1
            ext i
            simp [realVecToComplex, complexVecAdd]
    _ ≤ ν (realVecToComplex x) + ν (realVecToComplex y) := h

/-- Standard coordinate vector in `C^n`. -/
def standardBasisCVec {n : ℕ} (j : Fin n) : CVec n :=
  fun i => if i = j then 1 else 0

/-- A standard coordinate vector is nonzero. -/
lemma standardBasisCVec_ne_zero {n : ℕ} (j : Fin n) :
    standardBasisCVec j ≠ 0 := by
  intro hzero
  have hj := congrFun hzero j
  simp [standardBasisCVec] at hj

/-- The source-facing standard coordinate vector is Mathlib's `Pi.single`. -/
lemma standardBasisCVec_eq_pi_single {n : ℕ} (j : Fin n) :
    standardBasisCVec j = Pi.single j (1 : ℂ) := by
  ext i
  by_cases hij : i = j
  · subst hij
    simp [standardBasisCVec]
  · simp [standardBasisCVec, hij]

/-- Every standard coordinate vector has finite-product `L^p` norm `1`.  This
    keeps equation (6.12)'s general lower-bound route source-faithful. -/
lemma complexVecLpNorm_standardBasisCVec {n : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (j : Fin n) :
    complexVecLpNorm p (standardBasisCVec j) = 1 := by
  rw [standardBasisCVec_eq_pi_single]
  unfold complexVecLpNorm
  simp

lemma sum_smul_standardBasisCVec {n : ℕ} (x : CVec n) :
    (fun i : Fin n => ∑ j : Fin n, x j * standardBasisCVec j i) = x := by
  ext i
  calc
    (∑ j : Fin n, x j * standardBasisCVec j i) = x i * standardBasisCVec i i := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro j _hj hji
        simp [standardBasisCVec, hji.symm]
      · intro hnot
        simp at hnot
    _ = x i := by
      simp [standardBasisCVec]

/-- Concrete complex vector 1-norm. -/
noncomputable def complexVecOneNorm {n : ℕ} (x : CVec n) : ℝ :=
  ∑ i : Fin n, ‖x i‖

theorem complexVecOneNorm_isComplexVectorNorm {n : ℕ} :
    IsComplexVectorNorm (complexVecOneNorm (n := n)) := by
  constructor
  · intro x
    exact Finset.sum_nonneg (fun i _ => norm_nonneg (x i))
  · intro x
    constructor
    · intro hx
      have hterms :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => norm_nonneg (x i))).mp hx
      ext i
      exact norm_eq_zero.mp (hterms i (Finset.mem_univ i))
    · intro hx
      subst hx
      simp [complexVecOneNorm]
  · intro a x
    unfold complexVecOneNorm complexVecSMul
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_mul]
  · intro x y
    unfold complexVecOneNorm complexVecAdd
    calc
      (∑ i : Fin n, ‖x i + y i‖)
          ≤ ∑ i : Fin n, (‖x i‖ + ‖y i‖) := by
            apply Finset.sum_le_sum
            intro i _
            exact norm_add_le (x i) (y i)
      _ = (∑ i : Fin n, ‖x i‖) + ∑ i : Fin n, ‖y i‖ := by
            rw [Finset.sum_add_distrib]

/-- Real scalar multiplication on `C^n`, used for Higham Problem 6.16 where
    the gauge is a real norm on the underlying real vector space rather than a
    complex vector norm. -/
noncomputable def complexVecRealSMul {n : ℕ} (a : ℝ) (x : CVec n) : CVec n :=
  fun i => (a : ℂ) * x i

/-- Real-vector norm axioms on the underlying real vector space of `C^n`. -/
structure IsRealVectorNormOnCVec {n : ℕ} (ν : CVec n → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ν x
  eq_zero_iff : ∀ x, ν x = 0 ↔ x = 0
  smul : ∀ (a : ℝ) (x : CVec n), ν (complexVecRealSMul a x) = |a| * ν x
  add_le : ∀ x y : CVec n, ν (complexVecAdd x y) ≤ ν x + ν y

/-- The scalar absolute-value gauge on `C`: `|Re z| + |Im z|`. -/
noncomputable def complexRealImagAbs (z : ℂ) : ℝ :=
  |z.re| + |z.im|

lemma complexRealImagAbs_nonneg (z : ℂ) : 0 ≤ complexRealImagAbs z := by
  exact add_nonneg (abs_nonneg z.re) (abs_nonneg z.im)

/-- Nonnegative version of `complexRealImagAbs`, for finite maxima. -/
noncomputable def complexRealImagAbsNN (z : ℂ) : NNReal :=
  ⟨complexRealImagAbs z, complexRealImagAbs_nonneg z⟩

@[simp]
lemma complexRealImagAbsNN_coe (z : ℂ) :
    ((complexRealImagAbsNN z : NNReal) : ℝ) = complexRealImagAbs z := rfl

/-- Higham Problem 6.16's gauge `ν(x) = Σ_i (|Re x_i| + |Im x_i|)`. -/
noncomputable def complexVecRealImagOneNorm {n : ℕ} (x : CVec n) : ℝ :=
  ∑ i : Fin n, complexRealImagAbs (x i)

lemma complexVecRealImagOneNorm_nonneg {n : ℕ} (x : CVec n) :
    0 ≤ complexVecRealImagOneNorm x := by
  unfold complexVecRealImagOneNorm
  exact Finset.sum_nonneg (fun i _hi => complexRealImagAbs_nonneg (x i))

lemma complexVecRealImagOneNorm_eq_zero_iff {n : ℕ} (x : CVec n) :
    complexVecRealImagOneNorm x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    ext i
    have hterm :
        complexRealImagAbs (x i) = 0 := by
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => complexRealImagAbs (x i))
        (fun i _hi => complexRealImagAbs_nonneg (x i))).mp hx
      exact hzero i (Finset.mem_univ i)
    have hterm_sum : |(x i).re| + |(x i).im| = 0 := by
      simpa [complexRealImagAbs] using hterm
    have hre_abs_le : |(x i).re| ≤ 0 := by
      have hle : |(x i).re| ≤ |(x i).re| + |(x i).im| :=
        le_add_of_nonneg_right (abs_nonneg (x i).im)
      exact hle.trans (le_of_eq hterm_sum)
    have him_abs_le : |(x i).im| ≤ 0 := by
      have hle : |(x i).im| ≤ |(x i).re| + |(x i).im| :=
        le_add_of_nonneg_left (abs_nonneg (x i).re)
      exact hle.trans (le_of_eq hterm_sum)
    have hre : (x i).re = 0 :=
      abs_eq_zero.mp (le_antisymm hre_abs_le (abs_nonneg (x i).re))
    have him : (x i).im = 0 :=
      abs_eq_zero.mp (le_antisymm him_abs_le (abs_nonneg (x i).im))
    exact Complex.ext (by simpa using hre) (by simpa using him)
  · intro hx
    subst hx
    simp [complexVecRealImagOneNorm, complexRealImagAbs]

lemma complexVecRealImagOneNorm_real_smul {n : ℕ} (a : ℝ) (x : CVec n) :
    complexVecRealImagOneNorm (complexVecRealSMul a x) =
      |a| * complexVecRealImagOneNorm x := by
  unfold complexVecRealImagOneNorm complexVecRealSMul complexRealImagAbs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp [abs_mul]
  ring

lemma complexRealImagAbs_add_le (z w : ℂ) :
    complexRealImagAbs (z + w) ≤ complexRealImagAbs z + complexRealImagAbs w := by
  unfold complexRealImagAbs
  have hre : |(z + w).re| ≤ |z.re| + |w.re| := by
    simpa using abs_add_le z.re w.re
  have him : |(z + w).im| ≤ |z.im| + |w.im| := by
    simpa using abs_add_le z.im w.im
  linarith

lemma complexRealImagAbs_mul_le (z w : ℂ) :
    complexRealImagAbs (z * w) ≤ complexRealImagAbs z * complexRealImagAbs w := by
  unfold complexRealImagAbs
  have hre :
      |z.re * w.re - z.im * w.im| ≤
        |z.re| * |w.re| + |z.im| * |w.im| := by
    calc
      |z.re * w.re - z.im * w.im|
          = |z.re * w.re + -(z.im * w.im)| := by ring_nf
      _ ≤ |z.re * w.re| + |-(z.im * w.im)| :=
          abs_add_le (z.re * w.re) (-(z.im * w.im))
      _ = |z.re| * |w.re| + |z.im| * |w.im| := by
          rw [abs_mul, abs_neg, abs_mul]
  have him :
      |z.re * w.im + z.im * w.re| ≤
        |z.re| * |w.im| + |z.im| * |w.re| := by
    calc
      |z.re * w.im + z.im * w.re|
          ≤ |z.re * w.im| + |z.im * w.re| :=
            abs_add_le (z.re * w.im) (z.im * w.re)
      _ = |z.re| * |w.im| + |z.im| * |w.re| := by
          rw [abs_mul, abs_mul]
  have h := add_le_add hre him
  simpa [mul_add, add_mul, add_assoc, add_left_comm, add_comm] using h

lemma complexRealImagAbs_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    complexRealImagAbs (s.sum f) ≤
      s.sum (fun i => complexRealImagAbs (f i)) := by
  unfold complexRealImagAbs
  have hre :
      |(s.sum f).re| ≤ s.sum (fun i => |(f i).re|) := by
    have h := norm_sum_le s (fun i => (f i).re)
    simpa [Real.norm_eq_abs] using h
  have him :
      |(s.sum f).im| ≤ s.sum (fun i => |(f i).im|) := by
    have h := norm_sum_le s (fun i => (f i).im)
    simpa [Real.norm_eq_abs] using h
  calc
    |(s.sum f).re| + |(s.sum f).im|
        ≤ s.sum (fun i => |(f i).re|) + s.sum (fun i => |(f i).im|) :=
          add_le_add hre him
    _ = s.sum (fun i => |(f i).re| + |(f i).im|) := by
          rw [Finset.sum_add_distrib]

lemma complexVecRealImagOneNorm_add_le {n : ℕ} (x y : CVec n) :
    complexVecRealImagOneNorm (complexVecAdd x y) ≤
      complexVecRealImagOneNorm x + complexVecRealImagOneNorm y := by
  unfold complexVecRealImagOneNorm complexVecAdd
  calc
    (∑ i : Fin n, complexRealImagAbs (x i + y i))
        ≤ ∑ i : Fin n, (complexRealImagAbs (x i) + complexRealImagAbs (y i)) := by
          exact Finset.sum_le_sum (fun i _hi => complexRealImagAbs_add_le (x i) (y i))
    _ = (∑ i : Fin n, complexRealImagAbs (x i)) +
        (∑ i : Fin n, complexRealImagAbs (y i)) := by
          rw [Finset.sum_add_distrib]

/-- Problem 6.16: `ν` is a norm on the underlying real vector space of `C^n`. -/
theorem complexVecRealImagOneNorm_isRealVectorNormOnCVec {n : ℕ} :
    IsRealVectorNormOnCVec (complexVecRealImagOneNorm (n := n)) := by
  constructor
  · exact complexVecRealImagOneNorm_nonneg
  · exact complexVecRealImagOneNorm_eq_zero_iff
  · exact complexVecRealImagOneNorm_real_smul
  · exact complexVecRealImagOneNorm_add_le

/-- Problem 6.16 subtlety: this real norm is not a complex vector norm. -/
theorem complexVecRealImagOneNorm_not_isComplexVectorNorm :
    ¬ IsComplexVectorNorm (complexVecRealImagOneNorm (n := 1)) := by
  intro hν
  let x : CVec 1 := fun _ => (1 : ℂ)
  have hsmul := hν.smul (1 + Complex.I) x
  have hx : complexVecRealImagOneNorm x = 1 := by
    simp [x, complexVecRealImagOneNorm, complexRealImagAbs]
  have hleft :
      complexVecRealImagOneNorm (complexVecSMul (1 + Complex.I) x) = 2 := by
    norm_num [x, complexVecRealImagOneNorm, complexRealImagAbs, complexVecSMul]
  rw [hleft, hx, mul_one] at hsmul
  have hnormsq : Complex.normSq (1 + Complex.I) = 4 := by
    rw [Complex.normSq_eq_norm_sq, ← hsmul]
    norm_num [sq]
  norm_num [Complex.normSq_apply] at hnormsq

lemma complexVecOneNorm_standardBasisCVec {n : ℕ} (j : Fin n) :
    complexVecOneNorm (standardBasisCVec j) = 1 := by
  unfold complexVecOneNorm standardBasisCVec
  calc
    (∑ i : Fin n, ‖(if i = j then 1 else 0 : ℂ)‖) =
        ∑ i : Fin n, (if i = j then 1 else 0 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hij : i = j
          · simp [hij]
          · simp [hij]
    _ = 1 := by
          simp [Finset.sum_ite_eq', Finset.mem_univ]

lemma complexVecRealImagOneNorm_standardBasisCVec {n : ℕ} (j : Fin n) :
    complexVecRealImagOneNorm (standardBasisCVec j) = 1 := by
  unfold complexVecRealImagOneNorm standardBasisCVec complexRealImagAbs
  calc
    (∑ i : Fin n,
        (|(if i = j then 1 else 0 : ℂ).re| +
          |(if i = j then 1 else 0 : ℂ).im|)) =
        ∑ i : Fin n, (if i = j then 1 else 0 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases hij : i = j
          · simp [hij]
          · simp [hij]
    _ = 1 := by
          simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- The finite support of a source-facing complex vector.  This is the
    cardinality carrier for sparse refinements of the finite `L^p` comparison
    inequalities in Problem 6.14. -/
noncomputable def complexVecSupport {n : ℕ} (x : CVec n) : Finset (Fin n) :=
  (Finset.univ.filter fun i : Fin n => x i ≠ 0)

lemma complexVecOneNorm_eq_sum_support {n : ℕ} (x : CVec n) :
    complexVecOneNorm x = (complexVecSupport x).sum (fun i => ‖x i‖) := by
  classical
  unfold complexVecOneNorm complexVecSupport
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hxi : x i = 0
  · simp [hxi]
  · simp [hxi]

lemma complexVecLpPowerSum_eq_sum_support {n : ℕ} {p : ℝ} (hp : 0 < p)
    (x : CVec n) :
    (∑ i : Fin n, ‖x i‖ ^ p) =
      (complexVecSupport x).sum (fun i => ‖x i‖ ^ p) := by
  classical
  unfold complexVecSupport
  symm
  apply Finset.sum_subset
    (by intro i _hi; exact Finset.mem_univ i)
  intro i _hi hnot
  have hxi : x i = 0 := by
    by_contra hne
    exact hnot (by simp [hne])
  simp [hxi, Real.zero_rpow hp.ne']

/-- Finite vector norm comparison: `||x||_1 <= n^(1 - 1/p) ||x||_p`.
    This is the vector ingredient for the upper bound in Higham equation
    (6.12). -/
theorem complexVecOneNorm_le_card_rpow_mul_complexVecLpNorm {n : ℕ} {p : ℝ}
    (hp : 1 ≤ p) (x : CVec n) :
    complexVecOneNorm x ≤
      (n : ℝ) ^ (1 - p⁻¹) * complexVecLpNorm (ENNReal.ofReal p) x := by
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hLp : complexVecLpNorm (ENNReal.ofReal p) x =
      (∑ i : Fin n, ‖x i‖ ^ p) ^ p⁻¹ := by
    unfold complexVecLpNorm
    rw [PiLp.norm_eq_sum]
    · have hp_toReal : (ENNReal.ofReal p).toReal = p :=
        ENNReal.toReal_ofReal hp_nonneg
      simp [hp_toReal, one_div]
    · have hp_toReal : (ENNReal.ofReal p).toReal = p :=
        ENNReal.toReal_ofReal hp_nonneg
      simpa [hp_toReal] using hp_pos
  have h :=
    Real.inner_le_weight_mul_Lp_of_nonneg (s := Finset.univ) (p := p) hp
      (w := fun _ : Fin n => (1 : ℝ)) (f := fun i : Fin n => ‖x i‖)
      (by intro _; exact zero_le_one)
      (by intro i; exact norm_nonneg (x i))
  simpa [complexVecOneNorm, hLp, Finset.sum_const, one_mul] using h

/-- Sparse finite vector norm comparison:
    `||x||_1 <= μ^(1 - 1/p) ||x||_p` whenever `x` has at most `μ` nonzero
    entries.  This is the vector support ingredient behind the sparse-row
    refinement in Higham Problem 6.14. -/
theorem complexVecOneNorm_le_supportCard_rpow_mul_complexVecLpNorm {n : ℕ}
    {p : ℝ} (hp : 1 ≤ p) (x : CVec n) {μ : ℕ}
    (hμ : (complexVecSupport x).card ≤ μ) :
    complexVecOneNorm x ≤
      (μ : ℝ) ^ (1 - p⁻¹) * complexVecLpNorm (ENNReal.ofReal p) x := by
  classical
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hexp_nonneg : 0 ≤ 1 - p⁻¹ := by
    have hinv_le_one : p⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp
    linarith
  have hLp : complexVecLpNorm (ENNReal.ofReal p) x =
      (∑ i : Fin n, ‖x i‖ ^ p) ^ p⁻¹ := by
    unfold complexVecLpNorm
    rw [PiLp.norm_eq_sum]
    · have hp_toReal : (ENNReal.ofReal p).toReal = p :=
        ENNReal.toReal_ofReal hp_nonneg
      simp [hp_toReal, one_div]
    · have hp_toReal : (ENNReal.ofReal p).toReal = p :=
        ENNReal.toReal_ofReal hp_nonneg
      simpa [hp_toReal] using hp_pos
  let s : Finset (Fin n) := complexVecSupport x
  let S : ℝ := s.sum (fun i => ‖x i‖ ^ p)
  let T : ℝ := ∑ i : Fin n, ‖x i‖ ^ p
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun i _hi =>
      Real.rpow_nonneg (norm_nonneg (x i)) p)
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg (fun i _hi =>
      Real.rpow_nonneg (norm_nonneg (x i)) p)
  have hS_le_T : S ≤ T := by
    dsimp [S, T]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro i _hi; exact Finset.mem_univ i)
      (by
        intro i _hi _hnot
        exact Real.rpow_nonneg (norm_nonneg (x i)) p)
  have hroot_le : S ^ p⁻¹ ≤ T ^ p⁻¹ :=
    Real.rpow_le_rpow hS_nonneg hS_le_T (inv_nonneg.mpr hp_nonneg)
  have hholder :
      s.sum (fun i => ‖x i‖) ≤
        (s.card : ℝ) ^ (1 - p⁻¹) * S ^ p⁻¹ := by
    have h :=
      Real.inner_le_weight_mul_Lp_of_nonneg (s := s) (p := p) hp
        (w := fun _ : Fin n => (1 : ℝ)) (f := fun i : Fin n => ‖x i‖)
        (by intro _; exact zero_le_one)
        (by intro i; exact norm_nonneg (x i))
    simpa [S, Finset.sum_const, nsmul_eq_mul, one_mul] using h
  have hcard_real : (s.card : ℝ) ≤ (μ : ℝ) := by
    exact_mod_cast hμ
  have hcard_factor :
      (s.card : ℝ) ^ (1 - p⁻¹) ≤ (μ : ℝ) ^ (1 - p⁻¹) :=
    Real.rpow_le_rpow (Nat.cast_nonneg s.card) hcard_real hexp_nonneg
  calc
    complexVecOneNorm x = s.sum (fun i => ‖x i‖) := by
      simpa [s] using complexVecOneNorm_eq_sum_support x
    _ ≤ (s.card : ℝ) ^ (1 - p⁻¹) * S ^ p⁻¹ := hholder
    _ ≤ (s.card : ℝ) ^ (1 - p⁻¹) * T ^ p⁻¹ :=
        mul_le_mul_of_nonneg_left hroot_le
          (Real.rpow_nonneg (Nat.cast_nonneg s.card) (1 - p⁻¹))
    _ ≤ (μ : ℝ) ^ (1 - p⁻¹) * T ^ p⁻¹ :=
        mul_le_mul_of_nonneg_right hcard_factor
          (Real.rpow_nonneg hT_nonneg p⁻¹)
    _ = (μ : ℝ) ^ (1 - p⁻¹) *
        complexVecLpNorm (ENNReal.ofReal p) x := by
          rw [hLp]

/-- Finite vector norm comparison: if `1 <= q <= p`, then
    `||x||_q <= n^(1/q - 1/p) ||x||_p`.  This is the general vector
    ingredient behind Higham equation (6.4) and the later matrix comparison
    rows. -/
theorem complexVecLpNorm_le_card_rpow_mul_complexVecLpNorm_of_exponent_le
    {n : ℕ} {p q : ℝ} (hq : 1 ≤ q) (hqp : q ≤ p) (x : CVec n) :
    complexVecLpNorm (ENNReal.ofReal q) x ≤
      (n : ℝ) ^ (q⁻¹ - p⁻¹) * complexVecLpNorm (ENNReal.ofReal p) x := by
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp : 1 ≤ p := hq.trans hqp
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hdiv : 1 ≤ p / q := by
    rw [one_le_div hq_pos]
    exact hqp
  let Sq : ℝ := ∑ i : Fin n, ‖x i‖ ^ q
  let Sp : ℝ := ∑ i : Fin n, ‖x i‖ ^ p
  have hSq_nonneg : 0 ≤ Sq := by
    dsimp [Sq]
    exact Finset.sum_nonneg (fun i _hi =>
      Real.rpow_nonneg (norm_nonneg (x i)) q)
  have hSp_nonneg : 0 ≤ Sp := by
    dsimp [Sp]
    exact Finset.sum_nonneg (fun i _hi =>
      Real.rpow_nonneg (norm_nonneg (x i)) p)
  have hpow_eq :
      ∀ i : Fin n, (‖x i‖ ^ q) ^ (p / q) = ‖x i‖ ^ p := by
    intro i
    rw [← Real.rpow_mul (norm_nonneg (x i)) q (p / q)]
    congr 1
    field_simp [hq_pos.ne']
  have hholder :=
    Real.inner_le_weight_mul_Lp_of_nonneg (s := Finset.univ) (p := p / q) hdiv
      (w := fun _ : Fin n => (1 : ℝ))
      (f := fun i : Fin n => ‖x i‖ ^ q)
      (by intro _; exact zero_le_one)
      (by intro i; exact Real.rpow_nonneg (norm_nonneg (x i)) q)
  have hsum :
      Sq ≤
        (n : ℝ) ^ (1 - (p / q)⁻¹) * Sp ^ (p / q)⁻¹ := by
    have hleft :
        (∑ i : Fin n, (1 : ℝ) * ‖x i‖ ^ q) = Sq := by
      simp [Sq]
    have hcard : (∑ _i : Fin n, (1 : ℝ)) = (n : ℝ) := by
      simp
    have hpow_sum :
        (∑ i : Fin n, (1 : ℝ) * (‖x i‖ ^ q) ^ (p / q)) = Sp := by
      dsimp [Sp]
      apply Finset.sum_congr rfl
      intro i _hi
      simp [hpow_eq i]
    calc
      Sq = ∑ i : Fin n, (1 : ℝ) * ‖x i‖ ^ q := hleft.symm
      _ ≤ (∑ i : Fin n, (1 : ℝ)) ^ (1 - (p / q)⁻¹) *
          (∑ i : Fin n, (1 : ℝ) * (‖x i‖ ^ q) ^ (p / q)) ^ (p / q)⁻¹ :=
            hholder
      _ = (n : ℝ) ^ (1 - (p / q)⁻¹) * Sp ^ (p / q)⁻¹ := by
        rw [hcard, hpow_sum]
  have hroot_le :
      Sq ^ q⁻¹ ≤
        ((n : ℝ) ^ (1 - (p / q)⁻¹) * Sp ^ (p / q)⁻¹) ^ q⁻¹ :=
    Real.rpow_le_rpow hSq_nonneg hsum (inv_nonneg.mpr (le_of_lt hq_pos))
  have hfactor :
      ((n : ℝ) ^ (1 - (p / q)⁻¹) * Sp ^ (p / q)⁻¹) ^ q⁻¹ =
        (n : ℝ) ^ (q⁻¹ - p⁻¹) * Sp ^ p⁻¹ := by
    rw [Real.mul_rpow
      (Real.rpow_nonneg (Nat.cast_nonneg n) (1 - (p / q)⁻¹))
      (Real.rpow_nonneg hSp_nonneg (p / q)⁻¹)]
    rw [← Real.rpow_mul (Nat.cast_nonneg n) (1 - (p / q)⁻¹) q⁻¹]
    rw [← Real.rpow_mul hSp_nonneg (p / q)⁻¹ q⁻¹]
    congr 2 <;> field_simp [hq_pos.ne', hp_pos.ne']
  calc
    complexVecLpNorm (ENNReal.ofReal q) x = Sq ^ q⁻¹ := by
      rw [complexVecLpNorm_ofReal_eq_sum_rpow hq_pos x]
    _ ≤ ((n : ℝ) ^ (1 - (p / q)⁻¹) * Sp ^ (p / q)⁻¹) ^ q⁻¹ := hroot_le
    _ = (n : ℝ) ^ (q⁻¹ - p⁻¹) * Sp ^ p⁻¹ := hfactor
    _ = (n : ℝ) ^ (q⁻¹ - p⁻¹) *
        complexVecLpNorm (ENNReal.ofReal p) x := by
          rw [complexVecLpNorm_ofReal_eq_sum_rpow hp_pos x]

/-- Finite nonnegative power-sum comparison:
    `sum_i f_i^r <= (sum_i f_i)^r` for `1 <= r`. -/
lemma sum_rpow_le_rpow_sum_of_nonneg {ι : Type*} {s : Finset ι}
    {f : ι → ℝ} {r : ℝ} (hr : 1 ≤ r)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    s.sum (fun i => f i ^ r) ≤ (s.sum f) ^ r := by
  classical
  revert hf
  refine Finset.induction_on s ?empty ?insert
  · intro _hf
    simp [Real.rpow_nonneg]
  · intro a s has ih hf
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i := by
      intro i hi
      exact hf i (Finset.mem_insert_of_mem hi)
    have ih' := ih hfs
    have hsum_nonneg : 0 ≤ s.sum f :=
      Finset.sum_nonneg hfs
    calc
      (insert a s).sum (fun i => f i ^ r)
          = f a ^ r + s.sum (fun i => f i ^ r) := by
              rw [Finset.sum_insert has]
      _ ≤ f a ^ r + (s.sum f) ^ r := by
              exact add_le_add (le_refl _) ih'
      _ ≤ (f a + s.sum f) ^ r :=
              Real.add_rpow_le_rpow_add hfa hsum_nonneg hr
      _ = ((insert a s).sum f) ^ r := by
              rw [Finset.sum_insert has]

/-- Weighted Schur/Hölder power estimate:
    `(sum_i w_i f_i)^p <= (sum_i w_i)^(p-1) sum_i w_i f_i^p`
    for nonnegative finite weights and values. -/
lemma weighted_sum_mul_rpow_le_sum_weight_rpow_mul_sum_weight_mul_rpow
    {ι : Type*} {s : Finset ι} {w f : ι → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) :
    (s.sum (fun i => w i * f i)) ^ p ≤
      (s.sum w) ^ (p - 1) *
        (s.sum (fun i => w i * f i ^ p)) := by
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let W : ℝ := s.sum w
  let P : ℝ := s.sum (fun i => w i * f i ^ p)
  let L : ℝ := s.sum (fun i => w i * f i)
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact Finset.sum_nonneg (fun i _hi => hw i)
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact Finset.sum_nonneg (fun i _hi =>
      mul_nonneg (hw i) (Real.rpow_nonneg (hf i) p))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Finset.sum_nonneg (fun i _hi => mul_nonneg (hw i) (hf i))
  have hholder : L ≤ W ^ (1 - p⁻¹) * P ^ p⁻¹ := by
    have h :=
      Real.inner_le_weight_mul_Lp_of_nonneg (s := s) (p := p) hp
        (w := w) (f := f) hw hf
    simpa [L, W, P] using h
  have hpow :
      L ^ p ≤ (W ^ (1 - p⁻¹) * P ^ p⁻¹) ^ p :=
    Real.rpow_le_rpow hL_nonneg hholder hp_nonneg
  have hfactor :
      (W ^ (1 - p⁻¹) * P ^ p⁻¹) ^ p =
        W ^ (p - 1) * P := by
    calc
      (W ^ (1 - p⁻¹) * P ^ p⁻¹) ^ p =
          (W ^ (1 - p⁻¹)) ^ p * (P ^ p⁻¹) ^ p := by
            rw [Real.mul_rpow
              (Real.rpow_nonneg hW_nonneg (1 - p⁻¹))
              (Real.rpow_nonneg hP_nonneg p⁻¹)]
      _ = W ^ ((1 - p⁻¹) * p) * P := by
            rw [← Real.rpow_mul hW_nonneg (1 - p⁻¹) p]
            rw [← Real.rpow_mul hP_nonneg p⁻¹ p]
            have hinv_mul : p⁻¹ * p = 1 := by
              field_simp [hp_pos.ne']
            rw [hinv_mul, Real.rpow_one]
      _ = W ^ (p - 1) * P := by
            have hmul : (1 - p⁻¹) * p = p - 1 := by
              field_simp [hp_pos.ne']
            rw [hmul]
  simpa [L, W, P] using hpow.trans_eq hfactor

/-- Finite vector norm monotonicity: if `1 <= q <= p`, then
    `||x||_p <= ||x||_q`.  Together with
    `complexVecLpNorm_le_card_rpow_mul_complexVecLpNorm_of_exponent_le`, this is
    the vector-level norm equivalence content behind Higham equation (6.4). -/
theorem complexVecLpNorm_le_complexVecLpNorm_of_exponent_le
    {n : ℕ} {p q : ℝ} (hq : 1 ≤ q) (hqp : q ≤ p) (x : CVec n) :
    complexVecLpNorm (ENNReal.ofReal p) x ≤
      complexVecLpNorm (ENNReal.ofReal q) x := by
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp : 1 ≤ p := hq.trans hqp
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  have hdiv : 1 ≤ p / q := by
    rw [one_le_div hq_pos]
    exact hqp
  let Sq : ℝ := ∑ i : Fin n, ‖x i‖ ^ q
  let Sp : ℝ := ∑ i : Fin n, ‖x i‖ ^ p
  have hSq_nonneg : 0 ≤ Sq := by
    dsimp [Sq]
    exact Finset.sum_nonneg (fun i _hi =>
      Real.rpow_nonneg (norm_nonneg (x i)) q)
  have hSp_nonneg : 0 ≤ Sp := by
    dsimp [Sp]
    exact Finset.sum_nonneg (fun i _hi =>
      Real.rpow_nonneg (norm_nonneg (x i)) p)
  have hpow_eq :
      ∀ i : Fin n, (‖x i‖ ^ q) ^ (p / q) = ‖x i‖ ^ p := by
    intro i
    rw [← Real.rpow_mul (norm_nonneg (x i)) q (p / q)]
    congr 1
    field_simp [hq_pos.ne']
  have hsum_power : Sp ≤ Sq ^ (p / q) := by
    have h :=
      sum_rpow_le_rpow_sum_of_nonneg (s := Finset.univ)
        (f := fun i : Fin n => ‖x i‖ ^ q) (r := p / q) hdiv
        (by intro i _hi; exact Real.rpow_nonneg (norm_nonneg (x i)) q)
    dsimp [Sp, Sq]
    simpa [hpow_eq] using h
  have hroot_le :
      Sp ^ p⁻¹ ≤ (Sq ^ (p / q)) ^ p⁻¹ :=
    Real.rpow_le_rpow hSp_nonneg hsum_power (inv_nonneg.mpr hp_nonneg)
  have hfactor : (Sq ^ (p / q)) ^ p⁻¹ = Sq ^ q⁻¹ := by
    rw [← Real.rpow_mul hSq_nonneg (p / q) p⁻¹]
    congr 1
    field_simp [hq_pos.ne', hp_pos.ne']
  calc
    complexVecLpNorm (ENNReal.ofReal p) x = Sp ^ p⁻¹ := by
      rw [complexVecLpNorm_ofReal_eq_sum_rpow hp_pos x]
    _ ≤ (Sq ^ (p / q)) ^ p⁻¹ := hroot_le
    _ = Sq ^ q⁻¹ := hfactor
    _ = complexVecLpNorm (ENNReal.ofReal q) x := by
          rw [complexVecLpNorm_ofReal_eq_sum_rpow hq_pos x]

/-- The source-facing finite `L^p` family specializes to the existing complex
    vector 1-norm at `p = 1`. -/
theorem complexVecLpNorm_one_eq_complexVecOneNorm {n : ℕ} (x : CVec n) :
    complexVecLpNorm 1 x = complexVecOneNorm x := by
  unfold complexVecLpNorm complexVecOneNorm
  rw [PiLp.norm_eq_of_L1]

/-- Concrete complex vector infinity norm, using Mathlib's sup norm on finite
    functions. -/
noncomputable def complexVecInfNorm {n : ℕ} (x : CVec n) : ℝ :=
  ‖x‖

lemma complexVecInfNorm_nonneg {n : ℕ} (x : CVec n) :
    0 ≤ complexVecInfNorm x := by
  unfold complexVecInfNorm
  exact norm_nonneg x

lemma complexVecInfNorm_coord_le {n : ℕ} (x : CVec n) (i : Fin n) :
    ‖x i‖ ≤ complexVecInfNorm x := by
  unfold complexVecInfNorm
  exact norm_le_pi_norm x i

lemma complexVecInfNorm_le_of_coord_le {n : ℕ} (x : CVec n) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i : Fin n, ‖x i‖ ≤ c) :
    complexVecInfNorm x ≤ c := by
  unfold complexVecInfNorm
  rw [pi_norm_le_iff_of_nonneg hc]
  exact h

theorem complexVecInfNorm_isComplexVectorNorm {n : ℕ} :
    IsComplexVectorNorm (complexVecInfNorm (n := n)) := by
  constructor
  · exact complexVecInfNorm_nonneg
  · intro x
    constructor
    · intro hx
      exact norm_eq_zero.mp hx
    · intro hx
      subst hx
      simp [complexVecInfNorm]
  · intro a x
    have hvec : complexVecSMul a x = a • x := by
      ext i
      simp [complexVecSMul]
    simp [complexVecInfNorm, hvec, norm_smul]
  · intro x y
    have hvec : complexVecAdd x y = x + y := by
      ext i
      simp [complexVecAdd]
    simpa [complexVecInfNorm, hvec] using norm_add_le x y

lemma complexVecInfNorm_standardBasisCVec {n : ℕ} (j : Fin n) :
    complexVecInfNorm (standardBasisCVec j) = 1 := by
  apply le_antisymm
  · apply complexVecInfNorm_le_of_coord_le _ zero_le_one
    intro i
    by_cases hij : i = j
    · simp [standardBasisCVec, hij]
    · simp [standardBasisCVec, hij]
  · have h := complexVecInfNorm_coord_le (standardBasisCVec j) j
    simpa [standardBasisCVec] using h

/-- The source-facing finite `L^p` family specializes to the existing complex
    vector infinity norm at `p = ∞`. -/
theorem complexVecLpNorm_infty_eq_complexVecInfNorm {n : ℕ} (x : CVec n) :
    complexVecLpNorm ∞ x = complexVecInfNorm x := by
  unfold complexVecLpNorm complexVecInfNorm
  exact PiLp.norm_toLp x

/-- Endpoint complex Hölder inequality for the source-facing `∞`/`1` norms. -/
theorem complexVecInfNorm_mul_oneNorm_pairing_le {n : ℕ} (a x : CVec n) :
    ‖∑ i : Fin n, a i * x i‖ ≤ complexVecInfNorm a * complexVecOneNorm x := by
  calc
    ‖∑ i : Fin n, a i * x i‖ ≤ ∑ i : Fin n, ‖a i * x i‖ := norm_sum_le _ _
    _ = ∑ i : Fin n, ‖a i‖ * ‖x i‖ := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact norm_mul (a i) (x i)
    _ ≤ ∑ i : Fin n, complexVecInfNorm a * ‖x i‖ := by
          apply Finset.sum_le_sum
          intro i _hi
          exact mul_le_mul_of_nonneg_right
            (complexVecInfNorm_coord_le a i) (norm_nonneg (x i))
    _ = complexVecInfNorm a * complexVecOneNorm x := by
          rw [← Finset.mul_sum]
          rfl

/-- Endpoint complex Holder inequality with the factors in the `1`/`infinity`
    order needed for the `p = infinity`, `q = 1` Riesz-Thorin boundary. -/
theorem complexVecOneNorm_mul_infNorm_pairing_le {n : ℕ} (a x : CVec n) :
    ‖∑ i : Fin n, a i * x i‖ ≤ complexVecOneNorm a * complexVecInfNorm x := by
  have h :=
    complexVecInfNorm_mul_oneNorm_pairing_le (a := x) (x := a)
  have hsum :
      (∑ i : Fin n, x i * a i) = ∑ i : Fin n, a i * x i := by
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  calc
    ‖∑ i : Fin n, a i * x i‖ = ‖∑ i : Fin n, x i * a i‖ := by
      rw [hsum]
    _ ≤ complexVecInfNorm x * complexVecOneNorm a := h
    _ = complexVecOneNorm a * complexVecInfNorm x := by ring

/-- Finite vector norm comparison: `||x||_p <= n^(1/p) ||x||_∞`.
    This is the vector ingredient for the upper bound in Higham equation
    (6.13). -/
theorem complexVecLpNorm_le_card_rpow_mul_complexVecInfNorm {n : ℕ} {p : ℝ}
    (hp : 1 ≤ p) (x : CVec n) :
    complexVecLpNorm (ENNReal.ofReal p) x ≤
      (n : ℝ) ^ p⁻¹ * complexVecInfNorm x := by
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hLp : complexVecLpNorm (ENNReal.ofReal p) x =
      (∑ i : Fin n, ‖x i‖ ^ p) ^ p⁻¹ := by
    unfold complexVecLpNorm
    rw [PiLp.norm_eq_sum]
    · have hp_toReal : (ENNReal.ofReal p).toReal = p :=
        ENNReal.toReal_ofReal hp_nonneg
      simp [hp_toReal, one_div]
    · have hp_toReal : (ENNReal.ofReal p).toReal = p :=
        ENNReal.toReal_ofReal hp_nonneg
      simpa [hp_toReal] using hp_pos
  let M : ℝ := complexVecInfNorm x
  have hM_nonneg : 0 ≤ M := complexVecInfNorm_nonneg x
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, ‖x i‖ ^ p :=
    Finset.sum_nonneg (by
      intro i _hi
      exact Real.rpow_nonneg (norm_nonneg (x i)) p)
  have hsum : ∑ i : Fin n, ‖x i‖ ^ p ≤ (n : ℝ) * M ^ p := by
    calc
      ∑ i : Fin n, ‖x i‖ ^ p ≤ ∑ _i : Fin n, M ^ p := by
        apply Finset.sum_le_sum
        intro i _hi
        exact Real.rpow_le_rpow (norm_nonneg (x i))
          (complexVecInfNorm_coord_le x i) hp_nonneg
      _ = (n : ℝ) * M ^ p := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hpow_le :
      (∑ i : Fin n, ‖x i‖ ^ p) ^ p⁻¹ ≤ ((n : ℝ) * M ^ p) ^ p⁻¹ :=
    Real.rpow_le_rpow hsum_nonneg hsum (inv_nonneg.mpr hp_nonneg)
  have hprod : ((n : ℝ) * M ^ p) ^ p⁻¹ = (n : ℝ) ^ p⁻¹ * M := by
    calc
      ((n : ℝ) * M ^ p) ^ p⁻¹ =
          (n : ℝ) ^ p⁻¹ * (M ^ p) ^ p⁻¹ := by
        rw [Real.mul_rpow (Nat.cast_nonneg n) (Real.rpow_nonneg hM_nonneg p)]
      _ = (n : ℝ) ^ p⁻¹ * M := by
        rw [Real.rpow_rpow_inv hM_nonneg hp_pos.ne']
  calc
    complexVecLpNorm (ENNReal.ofReal p) x
        = (∑ i : Fin n, ‖x i‖ ^ p) ^ p⁻¹ := hLp
    _ ≤ ((n : ℝ) * M ^ p) ^ p⁻¹ := hpow_le
    _ = (n : ℝ) ^ p⁻¹ * complexVecInfNorm x := by
      simpa [M] using hprod

/-- Sparse finite vector norm comparison:
    `||x||_p <= μ^(1/p) ||x||_∞` whenever `x` has at most `μ` nonzero
    entries.  This is the support-count version of the vector estimate used in
    Higham equation (6.13) and the sparse-column side of Problem 6.14. -/
theorem complexVecLpNorm_le_supportCard_rpow_mul_complexVecInfNorm {n : ℕ}
    {p : ℝ} (hp : 1 ≤ p) (x : CVec n) {μ : ℕ}
    (hμ : (complexVecSupport x).card ≤ μ) :
    complexVecLpNorm (ENNReal.ofReal p) x ≤
      (μ : ℝ) ^ p⁻¹ * complexVecInfNorm x := by
  classical
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hLp : complexVecLpNorm (ENNReal.ofReal p) x =
      (∑ i : Fin n, ‖x i‖ ^ p) ^ p⁻¹ := by
    unfold complexVecLpNorm
    rw [PiLp.norm_eq_sum]
    · have hp_toReal : (ENNReal.ofReal p).toReal = p :=
        ENNReal.toReal_ofReal hp_nonneg
      simp [hp_toReal, one_div]
    · have hp_toReal : (ENNReal.ofReal p).toReal = p :=
        ENNReal.toReal_ofReal hp_nonneg
      simpa [hp_toReal] using hp_pos
  let s : Finset (Fin n) := complexVecSupport x
  let M : ℝ := complexVecInfNorm x
  let T : ℝ := ∑ i : Fin n, ‖x i‖ ^ p
  have hM_nonneg : 0 ≤ M := complexVecInfNorm_nonneg x
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg (fun i _hi =>
      Real.rpow_nonneg (norm_nonneg (x i)) p)
  have hcard_real : (s.card : ℝ) ≤ (μ : ℝ) := by
    exact_mod_cast hμ
  have hsum_support :
      s.sum (fun i => ‖x i‖ ^ p) ≤ (s.card : ℝ) * M ^ p := by
    calc
      s.sum (fun i => ‖x i‖ ^ p) ≤ s.sum (fun _i => M ^ p) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact Real.rpow_le_rpow (norm_nonneg (x i))
          (complexVecInfNorm_coord_le x i) hp_nonneg
      _ = (s.card : ℝ) * M ^ p := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hsum : T ≤ (μ : ℝ) * M ^ p := by
    calc
      T = s.sum (fun i => ‖x i‖ ^ p) := by
        simpa [T, s] using complexVecLpPowerSum_eq_sum_support hp_pos x
      _ ≤ (s.card : ℝ) * M ^ p := hsum_support
      _ ≤ (μ : ℝ) * M ^ p :=
        mul_le_mul_of_nonneg_right hcard_real
          (Real.rpow_nonneg hM_nonneg p)
  have hpow_le :
      T ^ p⁻¹ ≤ ((μ : ℝ) * M ^ p) ^ p⁻¹ :=
    Real.rpow_le_rpow hT_nonneg hsum (inv_nonneg.mpr hp_nonneg)
  have hprod : ((μ : ℝ) * M ^ p) ^ p⁻¹ = (μ : ℝ) ^ p⁻¹ * M := by
    calc
      ((μ : ℝ) * M ^ p) ^ p⁻¹ =
          (μ : ℝ) ^ p⁻¹ * (M ^ p) ^ p⁻¹ := by
            rw [Real.mul_rpow (Nat.cast_nonneg μ)
              (Real.rpow_nonneg hM_nonneg p)]
      _ = (μ : ℝ) ^ p⁻¹ * M := by
            rw [Real.rpow_rpow_inv hM_nonneg hp_pos.ne']
  calc
    complexVecLpNorm (ENNReal.ofReal p) x = T ^ p⁻¹ := by
      simpa [T] using hLp
    _ ≤ ((μ : ℝ) * M ^ p) ^ p⁻¹ := hpow_le
    _ = (μ : ℝ) ^ p⁻¹ * complexVecInfNorm x := by
      simpa [M] using hprod

/-- A nontrivial source-facing normed `C^n` has at least one unit vector. -/
lemma exists_unit_complexVectorNorm {n : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) (hn : 0 < n) :
    ∃ u : CVec n, ν u = 1 := by
  let j0 : Fin n := ⟨0, hn⟩
  let e : CVec n := standardBasisCVec j0
  have he_ne : e ≠ 0 := by
    intro he
    have hcoord := congr_fun he j0
    simp [e, standardBasisCVec] at hcoord
  have hνe_ne : ν e ≠ 0 := by
    intro hνe
    exact he_ne ((hν.eq_zero_iff e).mp hνe)
  have hνe_pos : 0 < ν e :=
    lt_of_le_of_ne (hν.nonneg e) (Ne.symm hνe_ne)
  let u : CVec n := complexVecSMul (((ν e)⁻¹ : ℝ) : ℂ) e
  refine ⟨u, ?_⟩
  have hinv_nonneg : 0 ≤ (ν e)⁻¹ := inv_nonneg.mpr (hν.nonneg e)
  dsimp [u]
  rw [hν.smul, Complex.norm_of_nonneg hinv_nonneg]
  field_simp [ne_of_gt hνe_pos]

-- ============================================================
-- Hahn-Banach bridge for abstract Chapter 6 vector norms
-- ============================================================

/-- Wrapper around `C^n` whose built-in norm is a source-facing abstract
    Higham vector norm `ν`.  This lets Mathlib's Hahn-Banach theorem apply
    without replacing the canonical normed-space structure on `Fin n -> C`. -/
structure NormedCVec (n : ℕ) (ν : CVec n → ℝ) where
  val : CVec n


namespace NormedCVec

variable {n : ℕ} {ν : CVec n → ℝ}


/-- The wrapper is linearly equivalent to the underlying vector type. -/
protected def equiv (n : ℕ) (ν : CVec n → ℝ) : NormedCVec n ν ≃ CVec n where
  toFun := NormedCVec.val
  invFun := fun x => ⟨x⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

instance : CoeFun (NormedCVec n ν) (fun _ => Fin n → ℂ) :=
  ⟨NormedCVec.val⟩

@[ext]
lemma ext {x y : NormedCVec n ν} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance : AddCommGroup (NormedCVec n ν) :=
  (NormedCVec.equiv n ν).addCommGroup

noncomputable instance : Module ℂ (NormedCVec n ν) :=
  (NormedCVec.equiv n ν).module ℂ

@[simp] lemma val_zero : (0 : NormedCVec n ν).val = 0 := rfl
@[simp] lemma val_add (x y : NormedCVec n ν) : (x + y).val = x.val + y.val := rfl
@[simp] lemma val_neg (x : NormedCVec n ν) : (-x).val = -x.val := rfl
@[simp] lemma val_sub (x y : NormedCVec n ν) : (x - y).val = x.val - y.val := rfl
@[simp] lemma val_smul (a : ℂ) (x : NormedCVec n ν) : (a • x).val = a • x.val := rfl

instance : Norm (NormedCVec n ν) where
  norm x := ν x.val

lemma norm_eq (x : NormedCVec n ν) : ‖x‖ = ν x.val := rfl

lemma add_val_eq_complexVecAdd (x y : NormedCVec n ν) :
    (x + y).val = complexVecAdd x.val y.val := by
  ext i
  rfl

lemma smul_val_eq_complexVecSMul (a : ℂ) (x : NormedCVec n ν) :
    (a • x).val = complexVecSMul a x.val := by
  ext i
  simp [complexVecSMul]

/-- Core normed-space data generated by an abstract source-facing vector norm. -/
def normedSpaceCore (hν : IsComplexVectorNorm ν) :
    NormedSpace.Core ℂ (NormedCVec n ν) where
  norm_nonneg x := hν.nonneg x.val
  norm_smul a x := by
    change ν (a • x.val) = ‖a‖ * ν x.val
    rw [show (a • x.val) = complexVecSMul a x.val by ext i; rfl]
    exact hν.smul a x.val
  norm_triangle x y := by
    change ν (x.val + y.val) ≤ ν x.val + ν y.val
    rw [show (x.val + y.val) = complexVecAdd x.val y.val by ext i; rfl]
    exact hν.add_le x.val y.val
  norm_eq_zero_iff x := by
    change ν x.val = 0 ↔ x = 0
    constructor
    · intro h
      apply ext
      exact (hν.eq_zero_iff x.val).mp h
    · intro h
      subst h
      exact (hν.eq_zero_iff 0).mpr rfl

noncomputable def normedAddCommGroup (hν : IsComplexVectorNorm ν) :
    NormedAddCommGroup (NormedCVec n ν) :=
  NormedAddCommGroup.ofCore (𝕜 := ℂ) (normedSpaceCore hν)
end NormedCVec


lemma complexVecSupport_mul_left_subset {n : ℕ} (a x : CVec n) :
    complexVecSupport (fun j : Fin n => a j * x j) ⊆ complexVecSupport a := by
  classical
  intro j hj
  have hprod : a j * x j ≠ 0 := (Finset.mem_filter.mp hj).2
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ j, by
      intro ha
      exact hprod (by simp [ha])⟩

lemma complexVecSupport_mul_left_card_le {n : ℕ} (a x : CVec n) :
    (complexVecSupport (fun j : Fin n => a j * x j)).card ≤
      (complexVecSupport a).card :=
  Finset.card_le_card (complexVecSupport_mul_left_subset a x)

/-- Finite triangle inequality for a source-facing complex vector norm. -/
lemma IsComplexVectorNorm.sum_le {n k : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) (v : Fin k → CVec n) :
    ν (fun i : Fin n => ∑ j : Fin k, v j i) ≤ ∑ j : Fin k, ν (v j) := by
  classical
  have hfinite : ∀ s : Finset (Fin k),
      ν (fun i : Fin n => s.sum (fun j => v j i)) ≤ s.sum (fun j => ν (v j)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hzero : ν (0 : CVec n) = 0 := (hν.eq_zero_iff 0).mpr rfl
        change ν (0 : CVec n) ≤ 0
        rw [hzero]
    | insert a s ha ih =>
        have hsplit :
            (fun i : Fin n => (insert a s).sum (fun j => v j i)) =
              complexVecAdd (v a) (fun i : Fin n => s.sum (fun j => v j i)) := by
          ext i
          simp [Finset.sum_insert ha, complexVecAdd]
        calc
          ν (fun i : Fin n => (insert a s).sum (fun j => v j i))
              = ν (complexVecAdd (v a) (fun i : Fin n => s.sum (fun j => v j i))) := by
                rw [hsplit]
          _ ≤ ν (v a) + ν (fun i : Fin n => s.sum (fun j => v j i)) := hν.add_le _ _
          _ ≤ ν (v a) + s.sum (fun j => ν (v j)) := add_le_add (le_refl _) ih
          _ = (insert a s).sum (fun j => ν (v j)) := by rw [Finset.sum_insert ha]
  simpa using hfinite Finset.univ

/-- Componentwise conjugation preserves the concrete source-facing infinity norm. -/
lemma complexVecInfNorm_conj_eq {n : ℕ} (x : CVec n) :
    complexVecInfNorm (complexConjVec x) = complexVecInfNorm x := by
  apply le_antisymm
  · apply complexVecInfNorm_le_of_coord_le _ (complexVecInfNorm_nonneg x)
    intro i
    simpa [complexConjVec, norm_star] using complexVecInfNorm_coord_le x i
  · apply complexVecInfNorm_le_of_coord_le _ (complexVecInfNorm_nonneg (complexConjVec x))
    intro i
    have h := complexVecInfNorm_coord_le (complexConjVec x) i
    simpa [complexConjVec, norm_star] using h

/-- Endpoint dual pairing with conjugated first vector, in the book's
    `x^* y` orientation. -/
lemma complexVecConjInfNorm_mul_oneNorm_pairing_le {n : ℕ}
    (x y : CVec n) :
    ‖∑ i : Fin n, star (x i) * y i‖ ≤
      complexVecInfNorm x * complexVecOneNorm y := by
  have h := complexVecInfNorm_mul_oneNorm_pairing_le (complexConjVec x) y
  simpa [complexConjVec, complexVecInfNorm_conj_eq x] using h

/-- Weighted infinity norm used for the constructive half of Higham
    Problem 6.8.  In triangular coordinates this is
    `max_i |x_i| / r^i`, with `i` represented by `i.val`. -/
noncomputable def complexVecWeightedInfNorm {n : ℕ} (r : ℝ) (x : CVec n) : ℝ :=
  complexVecInfNorm (fun i => (((r ^ i.val : ℝ) : ℂ)⁻¹ * x i))

theorem complexVecWeightedInfNorm_isComplexVectorNorm {n : ℕ} {r : ℝ} (hr : 0 < r) :
    IsComplexVectorNorm (complexVecWeightedInfNorm (n := n) r) := by
  constructor
  · intro x
    exact complexVecInfNorm_nonneg _
  · intro x
    constructor
    · intro hx
      have hzero :
          (fun i : Fin n => (((r ^ i.val : ℝ) : ℂ)⁻¹ * x i)) = 0 := by
        exact (complexVecInfNorm_isComplexVectorNorm.eq_zero_iff _).mp hx
      ext i
      have hi := congr_fun hzero i
      have hpow_pos : 0 < r ^ i.val := pow_pos hr i.val
      have hcoef_ne : (((r ^ i.val : ℝ) : ℂ)⁻¹) ≠ 0 := by
        exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hpow_pos))
      have hmul : (((r ^ i.val : ℝ) : ℂ)⁻¹ * x i) = 0 := by
        simpa using hi
      exact (mul_eq_zero.mp hmul).resolve_left hcoef_ne
    · intro hx
      subst hx
      unfold complexVecWeightedInfNorm
      have hzero :
          (fun i : Fin n => (((r ^ i.val : ℝ) : ℂ)⁻¹ * (0 : CVec n) i)) =
            (0 : CVec n) := by
        ext i
        simp
      rw [hzero]
      exact (complexVecInfNorm_isComplexVectorNorm.eq_zero_iff 0).mpr rfl
  · intro a x
    unfold complexVecWeightedInfNorm
    have hvec :
        (fun i : Fin n => (((r ^ i.val : ℝ) : ℂ)⁻¹ * complexVecSMul a x i)) =
          complexVecSMul a (fun i : Fin n => (((r ^ i.val : ℝ) : ℂ)⁻¹ * x i)) := by
      ext i
      simp [complexVecSMul]
      ring
    rw [hvec]
    exact complexVecInfNorm_isComplexVectorNorm.smul a _
  · intro x y
    unfold complexVecWeightedInfNorm
    have hvec :
        (fun i : Fin n => (((r ^ i.val : ℝ) : ℂ)⁻¹ * complexVecAdd x y i)) =
          complexVecAdd
            (fun i : Fin n => (((r ^ i.val : ℝ) : ℂ)⁻¹ * x i))
            (fun i : Fin n => (((r ^ i.val : ℝ) : ℂ)⁻¹ * y i)) := by
      ext i
      simp [complexVecAdd]
      ring
    rw [hvec]
    exact complexVecInfNorm_isComplexVectorNorm.add_le _ _

lemma complexVecWeightedInfNorm_coord_le {n : ℕ} {r : ℝ} (hr : 0 < r)
    (x : CVec n) (i : Fin n) :
    ‖x i‖ ≤ complexVecWeightedInfNorm r x * r ^ i.val := by
  unfold complexVecWeightedInfNorm
  have hcoord :=
    complexVecInfNorm_coord_le
      (fun i : Fin n => (((r ^ i.val : ℝ) : ℂ)⁻¹ * x i)) i
  have hpow_pos : 0 < r ^ i.val := pow_pos hr i.val
  have hnorm :
      ‖(((r ^ i.val : ℝ) : ℂ)⁻¹ * x i)‖ =
        (r ^ i.val)⁻¹ * ‖x i‖ := by
    rw [norm_mul, norm_inv]
    have hnorm : ‖((r ^ i.val : ℝ) : ℂ)‖ = r ^ i.val :=
      Complex.norm_of_nonneg (le_of_lt hpow_pos)
    rw [hnorm]
  rw [hnorm] at hcoord
  have hmul := mul_le_mul_of_nonneg_right hcoord (le_of_lt hpow_pos)
  have hleft : ((r ^ i.val)⁻¹ * ‖x i‖) * r ^ i.val = ‖x i‖ := by
    field_simp [ne_of_gt hpow_pos]
  rw [hleft] at hmul
  exact hmul

lemma complexVecOneNorm_const_one {n : ℕ} :
    complexVecOneNorm (fun _ : Fin n => (1 : ℂ)) = (n : ℝ) := by
  simp [complexVecOneNorm, Finset.sum_const, Fintype.card_fin]

lemma complexVecNormSqSum_const_one {n : ℕ} :
    (∑ _ : Fin n, ‖(1 : ℂ)‖ ^ 2) = (n : ℝ) := by
  simp [Finset.sum_const, Fintype.card_fin]

lemma complexVecNormSqSum_standardBasisCVec {n : ℕ} (j0 : Fin n) :
    (∑ j : Fin n, ‖standardBasisCVec j0 j‖ ^ 2) = 1 := by
  haveI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by
    rw [ENNReal.one_le_ofReal]
    norm_num⟩
  have h :=
    complexVecLpNorm_rpow_eq_sum_rpow (n := n) (p := (2 : ℝ))
      (by norm_num) (standardBasisCVec j0)
  rw [complexVecLpNorm_standardBasisCVec] at h
  norm_num at h
  simpa using h.symm
end NumStability
