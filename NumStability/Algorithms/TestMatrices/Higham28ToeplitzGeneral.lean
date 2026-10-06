/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28Contracts

/-! # Higham Chapter 28: nonsymmetric tridiagonal Toeplitz spectrum -/

namespace NumStability

noncomputable def toeplitzScaledVector {n : ℕ}
    (q : ℝ) (x : RVec n) : RVec n := fun i => q ^ i.val * x i

theorem tridiagonalToeplitz_mulVec_scaled_similarity {n : ℕ}
    (c d e q s : ℝ) (x : RVec n)
    (heq : e * q = s) (hcq : c = q * s) :
    Matrix.mulVec (tridiagonalToeplitz n c d e) (toeplitzScaledVector q x) =
      toeplitzScaledVector q
        (Matrix.mulVec (tridiagonalToeplitz n s d s) x) := by
  funext i
  rw [tridiagonalToeplitz_mulVec_apply]
  unfold toeplitzScaledVector
  rw [tridiagonalToeplitz_mulVec_apply]
  by_cases hs : i.val + 1 < n
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte]
      rw [pow_succ]
      have hpred : q ^ i.val = q ^ (i.val - 1) * q := by
        conv_lhs => rw [show i.val = (i.val - 1) + 1 by omega]
        rw [pow_succ]
      rw [hpred]
      linear_combination
        (q ^ (i.val - 1) * q * x ⟨i.val + 1, hs⟩) * heq +
        (q ^ (i.val - 1) * x ⟨i.val - 1, by omega⟩) * hcq
    · have hi0 : i.val = 0 := by omega
      simp only [hs, hp, ↓reduceDIte]
      let j : Fin n := ⟨i.val + 1, hs⟩
      change
        d * (q ^ i.val * x i) + e * (q ^ (i.val + 1) * x j) + 0 =
          q ^ i.val * (d * x i + s * x j + 0)
      simp only [hi0, pow_zero, zero_add, pow_one, one_mul]
      linear_combination x j * heq
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte]
      have hpred : q ^ i.val = q ^ (i.val - 1) * q := by
        conv_lhs => rw [show i.val = (i.val - 1) + 1 by omega]
        rw [pow_succ]
      rw [hpred]
      linear_combination
        (q ^ (i.val - 1) * x ⟨i.val - 1, by omega⟩) * hcq
    · simp only [hs, hp, ↓reduceDIte]
      ring

noncomputable def generalToeplitzSineVector {n : ℕ}
    (c e : ℝ) (k : Fin n) : RVec n :=
  toeplitzScaledVector (Real.sqrt c / Real.sqrt e) (toeplitzSineVector n k)

noncomputable def generalToeplitzEigenvalue
    (n : ℕ) (c d e : ℝ) (k : Fin n) : ℝ :=
  d + 2 * Real.sqrt (c * e) *
    Real.cos (((k.val + 1 : ℕ) : ℝ) * Real.pi / (n + 1 : ℕ))

theorem generalToeplitz_sine_eigenpair {n : ℕ}
    (c d e : ℝ) (hc : 0 < c) (he : 0 < e) (k : Fin n) :
    Matrix.mulVec (tridiagonalToeplitz n c d e)
        (generalToeplitzSineVector c e k) =
      generalToeplitzEigenvalue n c d e k •
        generalToeplitzSineVector c e k := by
  let q := Real.sqrt c / Real.sqrt e
  let s := Real.sqrt c * Real.sqrt e
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hse : 0 < Real.sqrt e := Real.sqrt_pos.2 he
  have hcSq : Real.sqrt c * Real.sqrt c = c :=
    Real.mul_self_sqrt (le_of_lt hc)
  have heSq : Real.sqrt e * Real.sqrt e = e :=
    Real.mul_self_sqrt (le_of_lt he)
  have heq : e * q = s := by
    dsimp [q, s]
    field_simp [hse.ne']
    nlinarith
  have hcq : c = q * s := by
    dsimp [q, s]
    field_simp [hse.ne']
    nlinarith
  have hsqrt : Real.sqrt (c * e) = s := by
    dsimp [s]
    rw [Real.sqrt_mul (le_of_lt hc)]
  rw [generalToeplitzSineVector]
  have hsim := tridiagonalToeplitz_mulVec_scaled_similarity
    c d e q s (toeplitzSineVector n k) heq hcq
  rw [hsim]
  have heig := symmetricToeplitz_sine_eigenpair s d k
  rw [heig]
  funext i
  simp only [toeplitzScaledVector, Pi.smul_apply, smul_eq_mul,
    generalToeplitzEigenvalue]
  rw [hsqrt]
  simp [symmetricToeplitzEigenvalue, q]
  ring

/-- The scaled sine vector is nonzero on the positive source domain, so the
preceding equality is a genuine eigenpair. -/
theorem generalToeplitzSineVector_ne_zero {n : ℕ}
    (c e : ℝ) (hc : 0 < c) (he : 0 < e) (k : Fin n) :
    generalToeplitzSineVector c e k ≠ 0 := by
  have hq : Real.sqrt c / Real.sqrt e ≠ 0 :=
    div_ne_zero (ne_of_gt (Real.sqrt_pos.2 hc))
      (ne_of_gt (Real.sqrt_pos.2 he))
  intro hzero
  apply toeplitzSineVector_ne_zero k
  funext i
  have hi := congrFun hzero i
  simp only [generalToeplitzSineVector, toeplitzScaledVector,
    Pi.zero_apply] at hi
  exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero _ hq)

/-! ## The unrestricted complex spectrum printed on p. 522

The real scaled-similarity proof above is useful when `c,e > 0`, but the
source does not impose that restriction.  The following complexification
covers every real `c,d,e`, including `c*e < 0` and the triangular zero cases.
-/

/-- The tridiagonal Toeplitz matrix over `ℂ`.  For real parameters this is
entrywise the complexification of `tridiagonalToeplitz`. -/
noncomputable def complexTridiagonalToeplitz
    (n : ℕ) (c d e : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    if i = j then d
    else if i.val + 1 = j.val then e
    else if j.val + 1 = i.val then c
    else 0

theorem complexTridiagonalToeplitz_ofReal
    (n : ℕ) (c d e : ℝ) :
    complexTridiagonalToeplitz n c d e =
      (tridiagonalToeplitz n c d e).map Complex.ofReal := by
  ext i j
  simp only [complexTridiagonalToeplitz, tridiagonalToeplitz,
    Matrix.map_apply]
  split_ifs <;> simp

/-- Complex Toeplitz multiplication has the same three-term recurrence as
the real matrix. -/
theorem complexTridiagonalToeplitz_mulVec_apply
    {n : ℕ} (c d e : ℂ) (x : Fin n → ℂ) (i : Fin n) :
    Matrix.mulVec (complexTridiagonalToeplitz n c d e) x i =
      d * x i +
        (if h : i.val + 1 < n then e * x ⟨i.val + 1, h⟩ else 0) +
        (if h : 0 < i.val then c * x ⟨i.val - 1, by omega⟩ else 0) := by
  simp only [Matrix.mulVec, dotProduct]
  calc
    (∑ j, complexTridiagonalToeplitz n c d e i j * x j) =
        ∑ j, ((if i = j then d else 0) +
          (if i.val + 1 = j.val then e else 0) +
          (if j.val + 1 = i.val then c else 0)) * x j := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · subst j
        simp [complexTridiagonalToeplitz]
      · by_cases hs : i.val + 1 = j.val
        · have hb : ¬j.val + 1 = i.val := by omega
          simp [complexTridiagonalToeplitz, hij, hs, hb]
        · by_cases hp : j.val + 1 = i.val
          · simp [complexTridiagonalToeplitz, hij, hs, hp]
          · simp [complexTridiagonalToeplitz, hij, hs, hp]
    _ = (∑ j, (if i = j then d else 0) * x j) +
          (∑ j, (if i.val + 1 = j.val then e else 0) * x j) +
          (∑ j, (if j.val + 1 = i.val then c else 0) * x j) := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = d * x i +
        (if h : i.val + 1 < n then e * x ⟨i.val + 1, h⟩ else 0) +
        (if h : 0 < i.val then c * x ⟨i.val - 1, by omega⟩ else 0) := by
      simp only [ite_mul, zero_mul]
      have hdiag : (∑ j : Fin n, if i = j then d * x j else 0) =
          d * x i := by simp
      rw [hdiag]
      by_cases hs : i.val + 1 < n
      · let ip : Fin n := ⟨i.val + 1, hs⟩
        have hsUnique : ∀ j : Fin n, i.val + 1 = j.val ↔ j = ip := by
          intro j
          constructor
          · intro h
            apply Fin.ext
            simpa [ip] using h.symm
          · intro h
            subst j
            simp [ip]
        simp_rw [hsUnique]
        by_cases hp : 0 < i.val
        · let im : Fin n := ⟨i.val - 1, by omega⟩
          have hpUnique : ∀ j : Fin n, j.val + 1 = i.val ↔ j = im := by
            intro j
            constructor
            · intro h
              apply Fin.ext
              simp [im]
              omega
            · intro h
              subst j
              simp [im]
              omega
          simp_rw [hpUnique]
          simp [hs, hp, ip, im]
        · have hpNone : ∀ j : Fin n, ¬j.val + 1 = i.val := by
            intro j h
            omega
          simp_rw [if_neg (hpNone _)]
          simp [hs, hp, ip]
      · have hsNone : ∀ j : Fin n, ¬i.val + 1 = j.val := by
          intro j h
          omega
        simp_rw [if_neg (hsNone _)]
        by_cases hp : 0 < i.val
        · let im : Fin n := ⟨i.val - 1, by omega⟩
          have hpUnique : ∀ j : Fin n, j.val + 1 = i.val ↔ j = im := by
            intro j
            constructor
            · intro h
              apply Fin.ext
              simp [im]
              omega
            · intro h
              subst j
              simp [im]
              omega
          simp_rw [hpUnique]
          simp [hs, hp, im]
        · have hpNone : ∀ j : Fin n, ¬j.val + 1 = i.val := by
            intro j h
            omega
          simp_rw [if_neg (hpNone _)]
          simp [hs, hp]

noncomputable def complexToeplitzScaledVector {n : ℕ}
    (q : ℂ) (x : Fin n → ℂ) : Fin n → ℂ := fun i => q ^ i.val * x i

theorem complexTridiagonalToeplitz_mulVec_scaled_similarity {n : ℕ}
    (c d e q s : ℂ) (x : Fin n → ℂ)
    (heq : e * q = s) (hcq : c = q * s) :
    Matrix.mulVec (complexTridiagonalToeplitz n c d e)
        (complexToeplitzScaledVector q x) =
      complexToeplitzScaledVector q
        (Matrix.mulVec (complexTridiagonalToeplitz n s d s) x) := by
  funext i
  rw [complexTridiagonalToeplitz_mulVec_apply]
  unfold complexToeplitzScaledVector
  rw [complexTridiagonalToeplitz_mulVec_apply]
  by_cases hs : i.val + 1 < n
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte]
      rw [pow_succ]
      have hpred : q ^ i.val = q ^ (i.val - 1) * q := by
        conv_lhs => rw [show i.val = (i.val - 1) + 1 by omega]
        rw [pow_succ]
      rw [hpred]
      linear_combination
        (q ^ (i.val - 1) * q * x ⟨i.val + 1, hs⟩) * heq +
        (q ^ (i.val - 1) * x ⟨i.val - 1, by omega⟩) * hcq
    · have hi0 : i.val = 0 := by omega
      simp only [hs, hp, ↓reduceDIte]
      let j : Fin n := ⟨i.val + 1, hs⟩
      change
        d * (q ^ i.val * x i) + e * (q ^ (i.val + 1) * x j) + 0 =
          q ^ i.val * (d * x i + s * x j + 0)
      simp only [hi0, pow_zero, zero_add, pow_one, one_mul]
      linear_combination x j * heq
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte]
      have hpred : q ^ i.val = q ^ (i.val - 1) * q := by
        conv_lhs => rw [show i.val = (i.val - 1) + 1 by omega]
        rw [pow_succ]
      rw [hpred]
      linear_combination
        (q ^ (i.val - 1) * x ⟨i.val - 1, by omega⟩) * hcq
    · simp only [hs, hp, ↓reduceDIte]
      ring

/-- A concrete complex square root of a real product. -/
noncomputable def realProductComplexSqrt (c e : ℝ) : ℂ :=
  if 0 ≤ c * e then (Real.sqrt (c * e) : ℂ)
  else Complex.I * (Real.sqrt (-(c * e)) : ℂ)

theorem realProductComplexSqrt_sq (c e : ℝ) :
    realProductComplexSqrt c e * realProductComplexSqrt c e =
      ((c * e : ℝ) : ℂ) := by
  by_cases h : 0 ≤ c * e
  · simp only [realProductComplexSqrt, if_pos h, ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt h]
  · have hn : 0 ≤ -(c * e) := le_of_lt (neg_pos.2 (lt_of_not_ge h))
    simp only [realProductComplexSqrt, if_neg h]
    rw [mul_mul_mul_comm, Complex.I_mul_I, neg_one_mul,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hn, Complex.ofReal_neg]
    simp

noncomputable def complexToeplitzSineVector {n : ℕ}
    (q : ℂ) (k : Fin n) : Fin n → ℂ :=
  complexToeplitzScaledVector q (fun i => (toeplitzSineVector n k i : ℂ))

noncomputable def generalToeplitzComplexEigenvalue
    (n : ℕ) (c d e : ℝ) (k : Fin n) : ℂ :=
  (d : ℂ) + 2 * realProductComplexSqrt c e *
    (Real.cos (((k.val + 1 : ℕ) : ℝ) * Real.pi / (n + 1 : ℕ)) : ℂ)

/-- The complexified symmetric Toeplitz matrix has the usual sine eigenpair,
with no sign restriction on its (possibly complex) off-diagonal scalar. -/
theorem complexSymmetricToeplitz_sine_eigenpair {n : ℕ}
    (s d : ℂ) (k : Fin n) :
    Matrix.mulVec (complexTridiagonalToeplitz n s d s)
        (fun i => (toeplitzSineVector n k i : ℂ)) =
      (d + 2 * s *
          (Real.cos (((k.val + 1 : ℕ) : ℝ) * Real.pi /
            (n + 1 : ℕ)) : ℂ)) •
        (fun i => (toeplitzSineVector n k i : ℂ)) := by
  funext i
  rw [complexTridiagonalToeplitz_mulVec_apply]
  have hreal := congrFun
    (symmetricToeplitz_sine_eigenpair (c := (1 : ℝ)) (d := (0 : ℝ)) k) i
  rw [tridiagonalToeplitz_mulVec_apply] at hreal
  have hcast := congrArg Complex.ofReal hreal
  simp only [symmetricToeplitzEigenvalue, zero_mul, zero_add, one_mul,
    Pi.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat] at hcast
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs at hcast ⊢ <;>
    simp only [Complex.ofReal_zero, Complex.ofReal_one,
      add_zero, zero_add] at hcast ⊢ <;>
    ring_nf at hcast ⊢ <;> linear_combination s * hcast

/-- Higham p. 522, unrestricted nontriangular case: for every printed index,
the displayed complex eigenvalue has an explicit sine eigenvector. -/
theorem generalToeplitz_complex_sine_eigenpair_of_super_ne_zero {n : ℕ}
    (c d e : ℝ) (he : e ≠ 0) (k : Fin n) :
    let s := realProductComplexSqrt c e
    let q := s / (e : ℂ)
    Matrix.mulVec (complexTridiagonalToeplitz n c d e)
        (complexToeplitzSineVector q k) =
      generalToeplitzComplexEigenvalue n c d e k •
        complexToeplitzSineVector q k := by
  dsimp only
  let s : ℂ := realProductComplexSqrt c e
  let q : ℂ := s / (e : ℂ)
  have heC : (e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he
  have heq : (e : ℂ) * q = s := by
    dsimp [q]
    field_simp
  have hsquare : s * s = ((c * e : ℝ) : ℂ) := by
    exact realProductComplexSqrt_sq c e
  have hcq : (c : ℂ) = q * s := by
    dsimp [q]
    rw [div_mul_eq_mul_div, hsquare, Complex.ofReal_mul]
    field_simp
  rw [complexToeplitzSineVector]
  rw [complexTridiagonalToeplitz_mulVec_scaled_similarity
    (c := (c : ℂ)) (d := (d : ℂ)) (e := (e : ℂ))
    (q := q) (s := s) _ heq hcq]
  rw [complexSymmetricToeplitz_sine_eigenpair]
  funext i
  simp only [complexToeplitzScaledVector, Pi.smul_apply, smul_eq_mul,
    generalToeplitzComplexEigenvalue, s, q]
  ring

/-- The unrestricted sine vector above is nonzero for every scale, including
`q = 0`: its zeroth component is unchanged by scaling. -/
theorem complexToeplitzSineVector_ne_zero {n : ℕ}
    (q : ℂ) (k : Fin n) :
    complexToeplitzSineVector q k ≠ 0 := by
  let i0 : Fin n := ⟨0, Nat.zero_lt_of_lt k.isLt⟩
  let θ : ℝ := (((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ)
  have hden : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hθpos : 0 < θ := by
    dsimp [θ]
    positivity
  have hratio : ((k.val + 1 : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ k.isLt
  have hθlt : θ < Real.pi := by
    dsimp [θ]
    rw [div_lt_iff₀ hden]
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
  intro hzero
  have hi := congrFun hzero i0
  simp only [complexToeplitzSineVector, complexToeplitzScaledVector,
    Pi.zero_apply] at hi
  have hentry : toeplitzSineVector n k i0 = Real.sin θ := by
    simp [toeplitzSineVector, i0, θ]
  rw [hentry] at hi
  norm_num at hi
  have hi' : (Real.sin θ : ℂ) = 0 := by simpa using hi
  exact (ne_of_gt hsin) (Complex.ofReal_eq_zero.mp hi')

def complexToeplitzLastIndex {n : ℕ} (k : Fin n) : Fin n :=
  ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt k.isLt) Nat.zero_lt_one⟩

def complexToeplitzLastVector {n : ℕ} (k : Fin n) : Fin n → ℂ :=
  Pi.single (complexToeplitzLastIndex k) 1

/-- When the superdiagonal vanishes, the last coordinate vector is an
eigenvector with eigenvalue `d`. -/
theorem complexTridiagonalToeplitz_last_eigenpair {n : ℕ}
    (c d : ℂ) (k : Fin n) :
    Matrix.mulVec (complexTridiagonalToeplitz n c d 0)
        (complexToeplitzLastVector k) =
      d • complexToeplitzLastVector k := by
  rw [complexToeplitzLastVector]
  rw [Matrix.mulVec_single_one]
  funext i
  simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hi : i = complexToeplitzLastIndex k
  · subst i
    simp [complexTridiagonalToeplitz, complexToeplitzLastIndex]
  · have hiLast : i ≠ (⟨n - 1,
        Nat.sub_lt (Nat.zero_lt_of_lt k.isLt) Nat.zero_lt_one⟩ : Fin n) := by
      simpa [complexToeplitzLastIndex] using hi
    have hbottom : n - 1 + 1 ≠ i.val := by omega
    simp [complexTridiagonalToeplitz, complexToeplitzLastIndex,
      hiLast, hbottom]

theorem complexTridiagonalToeplitz_lastVector_ne_zero {n : ℕ}
    (k : Fin n) :
    complexToeplitzLastVector k ≠ 0 := by
  intro h
  have hi := congrFun h (complexToeplitzLastIndex k)
  simp [complexToeplitzLastVector] at hi

/-- One explicit eigenvector used for the unrestricted p. 522 formula. -/
noncomputable def generalToeplitzComplexEigenvector {n : ℕ}
    (c e : ℝ) (k : Fin n) : Fin n → ℂ :=
  if e ≠ 0 then
    let s := realProductComplexSqrt c e
    complexToeplitzSineVector (s / (e : ℂ)) k
  else
    complexToeplitzLastVector k

/-- Higham p. 522, without sign or nonzero restrictions: every member of the
printed list is a genuine eigenvalue of the complexified real Toeplitz matrix,
witnessed by a nonzero vector.  The zero-superdiagonal branch is triangular;
all other cases use the complex scaled-sine similarity. -/
theorem generalToeplitz_unrestricted_complex_eigenpair {n : ℕ}
    (c d e : ℝ) (k : Fin n) :
    generalToeplitzComplexEigenvector c e k ≠ 0 ∧
      Matrix.mulVec (complexTridiagonalToeplitz n c d e)
          (generalToeplitzComplexEigenvector c e k) =
        generalToeplitzComplexEigenvalue n c d e k •
          generalToeplitzComplexEigenvector c e k := by
  by_cases he : e ≠ 0
  · constructor
    · simpa [generalToeplitzComplexEigenvector, he] using
        complexToeplitzSineVector_ne_zero
          (realProductComplexSqrt c e / (e : ℂ)) k
    · simpa [generalToeplitzComplexEigenvector, he] using
        generalToeplitz_complex_sine_eigenpair_of_super_ne_zero c d e he k
  · have he0 : e = 0 := not_ne_iff.mp he
    subst e
    constructor
    · simpa [generalToeplitzComplexEigenvector] using
        complexTridiagonalToeplitz_lastVector_ne_zero k
    · have hlast := complexTridiagonalToeplitz_last_eigenpair
        (c := (c : ℂ)) (d := (d : ℂ)) k
      simpa [generalToeplitzComplexEigenvector,
        generalToeplitzComplexEigenvalue, realProductComplexSqrt] using hlast

/-- Source-facing p. 522 endpoint: the original real matrix, mapped to `ℂ`,
has every member of the displayed `k = 1:n` eigenvalue list. -/
theorem tridiagonalToeplitz_p522_unrestricted_eigenvalue {n : ℕ}
    (c d e : ℝ) (k : Fin n) :
    ∃ v : Fin n → ℂ, v ≠ 0 ∧
      Matrix.mulVec ((tridiagonalToeplitz n c d e).map Complex.ofReal) v =
        generalToeplitzComplexEigenvalue n c d e k • v := by
  have h := generalToeplitz_unrestricted_complex_eigenpair c d e k
  refine ⟨generalToeplitzComplexEigenvector c e k, h.1, ?_⟩
  rw [← complexTridiagonalToeplitz_ofReal]
  exact h.2

end NumStability
