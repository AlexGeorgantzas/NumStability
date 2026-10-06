/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter22.VandermondeSystems
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

namespace NumStability

open scoped BigOperators Matrix.Norms.L2Operator

/-! # Higham Problem 22.7: Chebyshev--Vandermonde conditioning

This file formalizes Higham, *Accuracy and Stability of Numerical
Algorithms*, second edition, Chapter 22, Problem 22.7 (pp. 430--431) and its
Appendix A solution (p. 568).  The matrices below are the actual finite
Chebyshev-evaluation matrices at the printed nodes.  Their discrete
orthogonality is proved from finite trigonometric sums; it is not supplied as
a hypothesis.

The source's parameter `n` gives an `(n+1) x (n+1)` matrix.  The exact
`sqrt 2` assertion at the zeros needs `n >= 1`: at `n = 0` the matrix is
`[1]` and its condition number is one.  The extrema assertion also uses its
natural domain `n >= 1`, because its nodes contain division by `n`.
-/

section TrigonometricSums

/-- Elementary finite telescoping identity used in both discrete cosine
orthogonality proofs. -/
lemma higham22_problem22_7_sum_succ_sub (N : Nat) (f : Nat -> Real) :
    (Finset.range N).sum (fun j => f (j + 1) - f j) = f N - f 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Midpoint-grid cosine sum, before specializing the mesh width. -/
lemma higham22_problem22_7_midpoint_cos_telescope (N : Nat) (a : Real) :
    2 * Real.sin (a / 2) *
        (Finset.range N).sum
          (fun j => Real.cos (((j : Real) + 1 / 2) * a)) =
      Real.sin ((N : Real) * a) := by
  rw [Finset.mul_sum]
  calc
    (Finset.range N).sum
        (fun j => (2 * Real.sin (a / 2)) *
          Real.cos (((j : Real) + 1 / 2) * a)) =
        (Finset.range N).sum
          (fun j => Real.sin (((j : Real) + 1) * a) -
            Real.sin ((j : Real) * a)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hdiff :
          ((((j : Real) + 1) * a - (j : Real) * a) / 2) = a / 2 := by
        ring
      have hsum :
          ((((j : Real) + 1) * a + (j : Real) * a) / 2) =
            ((j : Real) + 1 / 2) * a := by
        ring
      rw [Real.sin_sub_sin, hdiff, hsum]
    _ = Real.sin ((N : Real) * a) - Real.sin 0 := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul] using
        higham22_problem22_7_sum_succ_sub N
          (fun j => Real.sin ((j : Real) * a))
    _ = Real.sin ((N : Real) * a) := by simp

/-- Every nonconstant midpoint-grid cosine mode below the Nyquist frequency
has zero discrete mean. -/
lemma higham22_problem22_7_midpoint_cos_sum_eq_zero
    (N k : Nat) (hN : 0 < N) (hk0 : 0 < k) (hkN : k < 2 * N) :
    (Finset.range N).sum
        (fun j => Real.cos (((j : Real) + 1 / 2) *
          ((k : Real) * Real.pi / (N : Real)))) = 0 := by
  let a : Real := (k : Real) * Real.pi / (N : Real)
  have ha2_pos : 0 < a / 2 := by
    dsimp [a]
    positivity
  have ha2_lt : a / 2 < Real.pi := by
    dsimp [a]
    have hNR : (0 : Real) < (N : Real) := by exact_mod_cast hN
    have hkNR : (k : Real) < 2 * (N : Real) := by exact_mod_cast hkN
    calc
      (k : Real) * Real.pi / (N : Real) / 2 =
          ((k : Real) / (2 * (N : Real))) * Real.pi := by ring
      _ < 1 * Real.pi := by
        gcongr
        exact (div_lt_one (by positivity : (0 : Real) < 2 * (N : Real))).2 hkNR
      _ = Real.pi := one_mul _
  have hsin : Real.sin (a / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi ha2_pos ha2_lt).ne'
  have hNa : Real.sin ((N : Real) * a) = 0 := by
    have hNR : (N : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have heq : (N : Real) * a = (k : Real) * Real.pi := by
      dsimp [a]
      field_simp
    rw [heq]
    exact Real.sin_nat_mul_pi k
  have htel := higham22_problem22_7_midpoint_cos_telescope N a
  rw [hNa] at htel
  have hcoef : 2 * Real.sin (a / 2) ≠ 0 := mul_ne_zero (by norm_num) hsin
  exact (mul_eq_zero.mp htel).resolve_left hcoef

/-- Endpoint half-weights used by the extrema grid (the diagonal `D` in
Appendix A.22.7).  The subtraction form makes the two endpoint corrections
explicit and is valid on the intended domain `n > 0`. -/
noncomputable def higham22Problem22_7EndpointWeight (n j : Nat) : Real :=
  1 - (if j = 0 then 1 / 2 else 0) - (if j = n then 1 / 2 else 0)

lemma higham22_problem22_7_endpointWeight_zero (n : Nat) (hn : 0 < n) :
    higham22Problem22_7EndpointWeight n 0 = 1 / 2 := by
  simp [higham22Problem22_7EndpointWeight, (Nat.ne_of_gt hn).symm]
  norm_num

lemma higham22_problem22_7_endpointWeight_last (n : Nat) (hn : 0 < n) :
    higham22Problem22_7EndpointWeight n n = 1 / 2 := by
  simp [higham22Problem22_7EndpointWeight, Nat.ne_of_gt hn]
  norm_num

lemma higham22_problem22_7_endpointWeight_interior
    (n j : Nat) (hj0 : j ≠ 0) (hjn : j ≠ n) :
    higham22Problem22_7EndpointWeight n j = 1 := by
  simp [higham22Problem22_7EndpointWeight, hj0, hjn]

/-- A weighted range sum is the full sum with half of each endpoint removed. -/
lemma higham22_problem22_7_endpointWeight_sum
    (n : Nat) (hn : 0 < n) (f : Nat -> Real) :
    (Finset.range (n + 1)).sum
        (fun j => higham22Problem22_7EndpointWeight n j * f j) =
      (Finset.range (n + 1)).sum f - (f 0 + f n) / 2 := by
  simp_rw [higham22Problem22_7EndpointWeight, sub_mul, one_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp [hn, Nat.ne_of_gt hn, add_div]
  ring

/-- Trapezoidally weighted cosine sum on `0, a, ..., n*a`, before
specializing `a`. -/
lemma higham22_problem22_7_endpoint_cos_telescope
    (n : Nat) (hn : 0 < n) (a : Real) :
    2 * Real.sin (a / 2) *
        (Finset.range (n + 1)).sum
          (fun j => higham22Problem22_7EndpointWeight n j *
            Real.cos ((j : Real) * a)) =
      Real.sin ((n : Real) * a) * Real.cos (a / 2) := by
  rw [higham22_problem22_7_endpointWeight_sum n hn]
  rw [mul_sub]
  have hfull :
      2 * Real.sin (a / 2) *
          (Finset.range (n + 1)).sum (fun j => Real.cos ((j : Real) * a)) =
        Real.sin (((n : Real) + 1 / 2) * a) + Real.sin (a / 2) := by
    rw [Finset.mul_sum]
    calc
      (Finset.range (n + 1)).sum
          (fun j => (2 * Real.sin (a / 2)) * Real.cos ((j : Real) * a)) =
          (Finset.range (n + 1)).sum
            (fun j => Real.sin ((((j : Real) + 1) - 1 / 2) * a) -
              Real.sin (((j : Real) - 1 / 2) * a)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hdiff :
            (((((j : Real) + 1) - 1 / 2) * a -
              ((j : Real) - 1 / 2) * a) / 2) = a / 2 := by
          ring
        have hsum :
            (((((j : Real) + 1) - 1 / 2) * a +
              ((j : Real) - 1 / 2) * a) / 2) = (j : Real) * a := by
          ring
        rw [Real.sin_sub_sin, hdiff, hsum]
      _ = Real.sin ((((n : Real) + 1) - 1 / 2) * a) -
            Real.sin ((0 - 1 / 2) * a) := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
          higham22_problem22_7_sum_succ_sub (n + 1)
            (fun j => Real.sin (((j : Real) - 1 / 2) * a))
      _ = Real.sin (((n : Real) + 1 / 2) * a) + Real.sin (a / 2) := by
        have hneg :
            Real.sin ((0 - 1 / 2) * a) = -Real.sin (a / 2) := by
          rw [show (0 - 1 / 2) * a = -(a / 2) by ring, Real.sin_neg]
        rw [hneg]
        norm_num [Nat.cast_add, Nat.cast_one]
        congr 1 <;> ring
  rw [hfull]
  have hcorr :
      2 * Real.sin (a / 2) *
          ((Real.cos (((0 : Nat) : Real) * a) +
              Real.cos ((n : Real) * a)) / 2) =
        Real.sin (a / 2) * (1 + Real.cos ((n : Real) * a)) := by
    norm_num
    ring
  rw [hcorr]
  have hadd :
      Real.sin (((n : Real) + 1 / 2) * a) =
        Real.sin ((n : Real) * a) * Real.cos (a / 2) +
          Real.cos ((n : Real) * a) * Real.sin (a / 2) := by
    convert Real.sin_add ((n : Real) * a) (a / 2) using 1 <;> ring
  rw [hadd]
  ring

/-- All nonconstant extrema-grid cosine modes strictly below frequency
`2*n` have zero endpoint-weighted mean. -/
lemma higham22_problem22_7_endpoint_cos_sum_eq_zero
    (n k : Nat) (hn : 0 < n) (hk0 : 0 < k) (hkn : k < 2 * n) :
    (Finset.range (n + 1)).sum
        (fun j => higham22Problem22_7EndpointWeight n j *
          Real.cos ((j : Real) * ((k : Real) * Real.pi / (n : Real)))) = 0 := by
  let a : Real := (k : Real) * Real.pi / (n : Real)
  have ha2_pos : 0 < a / 2 := by
    dsimp [a]
    positivity
  have ha2_lt : a / 2 < Real.pi := by
    dsimp [a]
    have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
    have hkR : (k : Real) < 2 * (n : Real) := by exact_mod_cast hkn
    calc
      (k : Real) * Real.pi / (n : Real) / 2 =
          ((k : Real) / (2 * (n : Real))) * Real.pi := by ring
      _ < 1 * Real.pi := by
        gcongr
        exact (div_lt_one (by positivity : (0 : Real) < 2 * (n : Real))).2 hkR
      _ = Real.pi := one_mul _
  have hsin : Real.sin (a / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi ha2_pos ha2_lt).ne'
  have hna : Real.sin ((n : Real) * a) = 0 := by
    have hnR : (n : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have heq : (n : Real) * a = (k : Real) * Real.pi := by
      dsimp [a]
      field_simp
    rw [heq]
    exact Real.sin_nat_mul_pi k
  have htel := higham22_problem22_7_endpoint_cos_telescope n hn a
  rw [hna, zero_mul] at htel
  have hcoef : 2 * Real.sin (a / 2) ≠ 0 := mul_ne_zero (by norm_num) hsin
  exact (mul_eq_zero.mp htel).resolve_left hcoef

/-- The endpoint weights sum to `n`. -/
lemma higham22_problem22_7_endpointWeight_sum_one (n : Nat) (hn : 0 < n) :
    (Finset.range (n + 1)).sum
        (fun j => higham22Problem22_7EndpointWeight n j) = (n : Real) := by
  simpa using higham22_problem22_7_endpointWeight_sum n hn (fun _ => (1 : Real))

end TrigonometricSums

section Matrices

/-- The actual Chebyshev--Vandermonde-like matrix `T=(T_i(alpha_j))` in
Higham's row-polynomial/column-node orientation. -/
noncomputable def higham22Problem22_7ChebyshevVandermonde {N : Nat}
    (alpha : Fin N -> Real) : Fin N -> Fin N -> Real :=
  fun i j => (Polynomial.Chebyshev.T Real (i.val : Int)).eval (alpha j)

/-- Midpoint angles for the zeros of `T_(n+1)`. -/
noncomputable def higham22Problem22_7ZeroAngle (n : Nat)
    (j : Fin (n + 1)) : Real :=
  ((j.val : Real) + 1 / 2) * Real.pi / (n + 1 : Nat)

/-- The printed zeros `alpha_j=cos((j+1/2)pi/(n+1))`. -/
noncomputable def higham22Problem22_7ZeroNodes (n : Nat) :
    Fin (n + 1) -> Real :=
  fun j => Real.cos (higham22Problem22_7ZeroAngle n j)

/-- The first matrix in Problem 22.7. -/
noncomputable def higham22Problem22_7ZeroMatrix (n : Nat) :
    Fin (n + 1) -> Fin (n + 1) -> Real :=
  higham22Problem22_7ChebyshevVandermonde
    (higham22Problem22_7ZeroNodes n)

/-- On the printed zero nodes, the Chebyshev evaluation entries are the
corresponding DCT-II cosines. -/
theorem higham22_problem22_7_zeroMatrix_apply (n : Nat)
    (i j : Fin (n + 1)) :
    higham22Problem22_7ZeroMatrix n i j =
      Real.cos ((i.val : Real) * higham22Problem22_7ZeroAngle n j) := by
  simp [higham22Problem22_7ZeroMatrix,
    higham22Problem22_7ChebyshevVandermonde,
    higham22Problem22_7ZeroNodes]

/-- The nodes used in the first part really are zeros of `T_(n+1)`. -/
theorem higham22_problem22_7_zeroNodes_are_roots (n : Nat)
    (j : Fin (n + 1)) :
    (Polynomial.Chebyshev.T Real ((n + 1 : Nat) : Int)).eval
        (higham22Problem22_7ZeroNodes n j) = 0 := by
  rw [higham22Problem22_7ZeroNodes, Polynomial.Chebyshev.T_real_cos]
  rw [Real.cos_eq_zero_iff]
  refine ⟨j.val, ?_⟩
  dsimp [higham22Problem22_7ZeroAngle]
  push_cast
  field_simp

/-- Extrema-grid angles `j*pi/n`, on their natural domain `n>0`. -/
noncomputable def higham22Problem22_7ExtremaAngle (n : Nat)
    (j : Fin (n + 1)) : Real :=
  (j.val : Real) * Real.pi / (n : Real)

/-- The extrema nodes of `T_n`. -/
noncomputable def higham22Problem22_7ExtremaNodes (n : Nat) :
    Fin (n + 1) -> Real :=
  fun j => Real.cos (higham22Problem22_7ExtremaAngle n j)

/-- The second matrix in Problem 22.7. -/
noncomputable def higham22Problem22_7ExtremaMatrix (n : Nat) :
    Fin (n + 1) -> Fin (n + 1) -> Real :=
  higham22Problem22_7ChebyshevVandermonde
    (higham22Problem22_7ExtremaNodes n)

/-- On extrema nodes, the Chebyshev evaluation entries are DCT-I cosines. -/
theorem higham22_problem22_7_extremaMatrix_apply (n : Nat)
    (i j : Fin (n + 1)) :
    higham22Problem22_7ExtremaMatrix n i j =
      Real.cos ((i.val : Real) * higham22Problem22_7ExtremaAngle n j) := by
  simp [higham22Problem22_7ExtremaMatrix,
    higham22Problem22_7ChebyshevVandermonde,
    higham22Problem22_7ExtremaNodes]

/-- At the extrema nodes, `T_n(alpha_j)=(-1)^j`. -/
theorem higham22_problem22_7_extremaNodes_are_extrema
    (n : Nat) (hn : 0 < n) (j : Fin (n + 1)) :
    (Polynomial.Chebyshev.T Real (n : Int)).eval
        (higham22Problem22_7ExtremaNodes n j) = (-1 : Real) ^ j.val := by
  rw [higham22Problem22_7ExtremaNodes, Polynomial.Chebyshev.T_real_cos]
  change Real.cos ((n : Real) * higham22Problem22_7ExtremaAngle n j) =
    (-1 : Real) ^ j.val
  have hnR : (n : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have heq : (n : Real) * higham22Problem22_7ExtremaAngle n j =
      (j.val : Real) * Real.pi := by
    dsimp [higham22Problem22_7ExtremaAngle]
    field_simp
  rw [heq]
  exact Real.cos_nat_mul_pi j.val

end Matrices

section ZeroOrthogonality

/-- A nonzero DCT-II mode has zero sum on the actual zero-node grid. -/
lemma higham22_problem22_7_zero_mode_sum
    (n k : Nat) (hk0 : 0 < k) (hk : k < 2 * (n + 1)) :
    ∑ j : Fin (n + 1),
        Real.cos ((k : Real) * higham22Problem22_7ZeroAngle n j) = 0 := by
  change (∑ j : Fin (n + 1),
      Real.cos ((k : Real) *
        (((j.val : Real) + 1 / 2) * Real.pi / (n + 1 : Nat)))) = 0
  rw [Fin.sum_univ_eq_sum_range
    (fun j : Nat => Real.cos ((k : Real) *
      (((j : Real) + 1 / 2) * Real.pi / (n + 1 : Nat)))) (n + 1)]
  convert higham22_problem22_7_midpoint_cos_sum_eq_zero
      (n + 1) k (Nat.zero_lt_succ n) hk0 hk using 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  simp [higham22Problem22_7ZeroAngle]
  ring

/-- Product-to-sum identity over the DCT-II grid. -/
lemma higham22_problem22_7_zero_product_sum_twice
    (n : Nat) (r s : Fin (n + 1)) :
    2 * (∑ j : Fin (n + 1),
        Real.cos ((r.val : Real) * higham22Problem22_7ZeroAngle n j) *
          Real.cos ((s.val : Real) * higham22Problem22_7ZeroAngle n j)) =
      (∑ j : Fin (n + 1),
        Real.cos (((r.val : Real) - (s.val : Real)) *
          higham22Problem22_7ZeroAngle n j)) +
      (∑ j : Fin (n + 1),
        Real.cos (((r.val : Real) + (s.val : Real)) *
          higham22Problem22_7ZeroAngle n j)) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  convert Real.two_mul_cos_mul_cos
      ((r.val : Real) * higham22Problem22_7ZeroAngle n j)
      ((s.val : Real) * higham22Problem22_7ZeroAngle n j) using 1 <;> ring

/-- Appendix A.22.7, first discrete orthogonality identity, entrywise.
The zeroth Chebyshev row has squared norm `n+1`; every other row has
squared norm `(n+1)/2`. -/
theorem higham22_problem22_7_zero_discrete_orthogonality
    (n : Nat) (r s : Fin (n + 1)) :
    ∑ j : Fin (n + 1),
        higham22Problem22_7ZeroMatrix n r j *
          higham22Problem22_7ZeroMatrix n s j =
      if r = s then
        if r.val = 0 then (n + 1 : Real) else (n + 1 : Real) / 2
      else 0 := by
  simp_rw [higham22_problem22_7_zeroMatrix_apply]
  by_cases hrs : r = s
  · subst s
    rw [if_pos rfl]
    by_cases hr0 : r.val = 0
    · rw [if_pos hr0]
      have hr : r = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hr0
      subst r
      simp
    · rw [if_neg hr0]
      have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr0
      have h2r : 2 * r.val < 2 * (n + 1) := by omega
      have hmode := higham22_problem22_7_zero_mode_sum n (2 * r.val)
        (Nat.mul_pos (by norm_num) hrpos) h2r
      have htwice := higham22_problem22_7_zero_product_sum_twice n r r
      have hdiff :
          (∑ j : Fin (n + 1),
            Real.cos (((r.val : Real) - (r.val : Real)) *
              higham22Problem22_7ZeroAngle n j)) = (n + 1 : Real) := by simp
      have hsum :
          (∑ j : Fin (n + 1),
            Real.cos (((r.val : Real) + (r.val : Real)) *
              higham22Problem22_7ZeroAngle n j)) = 0 := by
        convert hmode using 1
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        norm_cast <;> ring
      rw [hdiff, hsum, add_zero] at htwice
      linarith
  · rw [if_neg hrs]
    rcases lt_or_gt_of_ne (fun h => hrs (Fin.ext h)) with hrslt | hrslt
    · have hdpos : 0 < s.val - r.val := Nat.sub_pos_of_lt hrslt
      have hdlt : s.val - r.val < 2 * (n + 1) := by omega
      have hsumpos : 0 < r.val + s.val := by omega
      have hsumlt : r.val + s.val < 2 * (n + 1) := by omega
      have hdiff := higham22_problem22_7_zero_mode_sum n (s.val - r.val)
        hdpos hdlt
      have hsum := higham22_problem22_7_zero_mode_sum n (r.val + s.val)
        hsumpos hsumlt
      have htwice := higham22_problem22_7_zero_product_sum_twice n r s
      have hdiff' :
          (∑ j : Fin (n + 1),
            Real.cos (((r.val : Real) - (s.val : Real)) *
              higham22Problem22_7ZeroAngle n j)) = 0 := by
        rw [← hdiff]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Real.cos_neg]
        congr 1
        rw [Nat.cast_sub (le_of_lt hrslt)]
        ring
      have hsum' :
          (∑ j : Fin (n + 1),
            Real.cos (((r.val : Real) + (s.val : Real)) *
              higham22Problem22_7ZeroAngle n j)) = 0 := by
        convert hsum using 1
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        norm_cast <;> ring
      rw [hdiff', hsum', add_zero] at htwice
      linarith
    · have hdpos : 0 < r.val - s.val := Nat.sub_pos_of_lt hrslt
      have hdlt : r.val - s.val < 2 * (n + 1) := by omega
      have hsumpos : 0 < r.val + s.val := by omega
      have hsumlt : r.val + s.val < 2 * (n + 1) := by omega
      have hdiff := higham22_problem22_7_zero_mode_sum n (r.val - s.val)
        hdpos hdlt
      have hsum := higham22_problem22_7_zero_mode_sum n (r.val + s.val)
        hsumpos hsumlt
      have htwice := higham22_problem22_7_zero_product_sum_twice n r s
      have hdiff' :
          (∑ j : Fin (n + 1),
            Real.cos (((r.val : Real) - (s.val : Real)) *
              higham22Problem22_7ZeroAngle n j)) = 0 := by
        convert hdiff using 1
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        rw [Nat.cast_sub (le_of_lt hrslt)]
      have hsum' :
          (∑ j : Fin (n + 1),
            Real.cos (((r.val : Real) + (s.val : Real)) *
              higham22Problem22_7ZeroAngle n j)) = 0 := by
        convert hsum using 1
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        norm_cast <;> ring
      rw [hdiff', hsum', add_zero] at htwice
      linarith

/-- Diagonal in the first Appendix A.22.7 Gram identity. -/
noncomputable def higham22Problem22_7ZeroGramDiagonal (n : Nat) :
    Fin (n + 1) -> Real :=
  fun i => if i.val = 0 then (n + 1 : Real) else (n + 1 : Real) / 2

/-- Matrix form of `C C^T=(n+1)diag(1,1/2,...,1/2)` for the actual
Chebyshev evaluation matrix at the zeros. -/
theorem higham22_problem22_7_zero_gram
    (n : Nat) :
    matMul (n + 1) (higham22Problem22_7ZeroMatrix n)
        (matTranspose (higham22Problem22_7ZeroMatrix n)) =
      diagMatrix (higham22Problem22_7ZeroGramDiagonal n) := by
  funext i j
  simp only [matMul, matTranspose]
  rw [higham22_problem22_7_zero_discrete_orthogonality]
  by_cases hij : i = j
  · subst j
    simp [diagMatrix, higham22Problem22_7ZeroGramDiagonal]
  · simp [diagMatrix, higham22Problem22_7ZeroGramDiagonal, hij]

end ZeroOrthogonality

section ExtremaOrthogonality

/-- A nonzero DCT-I mode strictly below `2*n` has zero endpoint-weighted
sum. -/
lemma higham22_problem22_7_extrema_mode_sum
    (n k : Nat) (hn : 0 < n) (hk0 : 0 < k) (hk : k < 2 * n) :
    ∑ j : Fin (n + 1),
        higham22Problem22_7EndpointWeight n j.val *
          Real.cos ((k : Real) * higham22Problem22_7ExtremaAngle n j) = 0 := by
  change (∑ j : Fin (n + 1),
      higham22Problem22_7EndpointWeight n j.val *
        Real.cos ((k : Real) *
          ((j.val : Real) * Real.pi / (n : Real)))) = 0
  rw [Fin.sum_univ_eq_sum_range
    (fun j : Nat => higham22Problem22_7EndpointWeight n j *
      Real.cos ((k : Real) *
        ((j : Real) * Real.pi / (n : Real)))) (n + 1)]
  convert higham22_problem22_7_endpoint_cos_sum_eq_zero n k hn hk0 hk using 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  ring

/-- The endpoint mode `2*n` is constant one and therefore has weighted sum
`n`. -/
lemma higham22_problem22_7_extrema_top_mode_sum
    (n : Nat) (hn : 0 < n) :
    ∑ j : Fin (n + 1),
        higham22Problem22_7EndpointWeight n j.val *
          Real.cos (((2 * n : Nat) : Real) *
            higham22Problem22_7ExtremaAngle n j) = (n : Real) := by
  have hnR : (n : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    (∑ j : Fin (n + 1),
        higham22Problem22_7EndpointWeight n j.val *
          Real.cos (((2 * n : Nat) : Real) *
            higham22Problem22_7ExtremaAngle n j)) =
        ∑ j : Fin (n + 1),
          higham22Problem22_7EndpointWeight n j.val := by
      apply Finset.sum_congr rfl
      intro j hj
      have harg : ((2 * n : Nat) : Real) *
          higham22Problem22_7ExtremaAngle n j =
          (j.val : Real) * (2 * Real.pi) := by
        rw [higham22Problem22_7ExtremaAngle]
        push_cast
        field_simp <;> ring
      rw [harg, Real.cos_nat_mul_two_pi, mul_one]
    _ = (Finset.range (n + 1)).sum
          (fun j => higham22Problem22_7EndpointWeight n j) := by
      rw [Fin.sum_univ_eq_sum_range]
    _ = (n : Real) := higham22_problem22_7_endpointWeight_sum_one n hn

/-- Product-to-sum identity for the endpoint-weighted DCT-I grid. -/
lemma higham22_problem22_7_extrema_product_sum_twice
    (n : Nat) (r s : Fin (n + 1)) :
    2 * (∑ j : Fin (n + 1),
        higham22Problem22_7EndpointWeight n j.val *
          (Real.cos ((r.val : Real) * higham22Problem22_7ExtremaAngle n j) *
            Real.cos ((s.val : Real) * higham22Problem22_7ExtremaAngle n j))) =
      (∑ j : Fin (n + 1),
        higham22Problem22_7EndpointWeight n j.val *
          Real.cos (((r.val : Real) - (s.val : Real)) *
            higham22Problem22_7ExtremaAngle n j)) +
      (∑ j : Fin (n + 1),
        higham22Problem22_7EndpointWeight n j.val *
          Real.cos (((r.val : Real) + (s.val : Real)) *
            higham22Problem22_7ExtremaAngle n j)) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    2 * (higham22Problem22_7EndpointWeight n j.val *
        (Real.cos ((r.val : Real) * higham22Problem22_7ExtremaAngle n j) *
          Real.cos ((s.val : Real) * higham22Problem22_7ExtremaAngle n j))) =
        higham22Problem22_7EndpointWeight n j.val *
          (2 * Real.cos ((r.val : Real) * higham22Problem22_7ExtremaAngle n j) *
            Real.cos ((s.val : Real) * higham22Problem22_7ExtremaAngle n j)) := by
      ring
    _ = higham22Problem22_7EndpointWeight n j.val *
          (Real.cos (((r.val : Real) - (s.val : Real)) *
              higham22Problem22_7ExtremaAngle n j) +
            Real.cos (((r.val : Real) + (s.val : Real)) *
              higham22Problem22_7ExtremaAngle n j)) := by
      rw [Real.two_mul_cos_mul_cos]
      congr 2 <;> ring
    _ = higham22Problem22_7EndpointWeight n j.val *
          Real.cos (((r.val : Real) - (s.val : Real)) *
            higham22Problem22_7ExtremaAngle n j) +
        higham22Problem22_7EndpointWeight n j.val *
          Real.cos (((r.val : Real) + (s.val : Real)) *
            higham22Problem22_7ExtremaAngle n j) := by ring

/-- A row index is an endpoint exactly when it is `0` or `n`. -/
def higham22Problem22_7IsEndpoint (n : Nat) (i : Fin (n + 1)) : Prop :=
  i.val = 0 ∨ i.val = n

instance higham22Problem22_7IsEndpoint_decidable (n : Nat)
    (i : Fin (n + 1)) :
    Decidable (higham22Problem22_7IsEndpoint n i) := by
  unfold higham22Problem22_7IsEndpoint
  infer_instance

/-- Appendix A.22.7, second discrete orthogonality identity, entrywise:
`sum_j D_j C_{rj} C_{sj}` is `n` on the two endpoint rows, `n/2` on
interior rows, and zero off diagonal. -/
theorem higham22_problem22_7_extrema_discrete_orthogonality
    (n : Nat) (hn : 0 < n) (r s : Fin (n + 1)) :
    ∑ j : Fin (n + 1),
        higham22Problem22_7EndpointWeight n j.val *
          (higham22Problem22_7ExtremaMatrix n r j *
            higham22Problem22_7ExtremaMatrix n s j) =
      if r = s then
        if higham22Problem22_7IsEndpoint n r then (n : Real) else (n : Real) / 2
      else 0 := by
  simp_rw [higham22_problem22_7_extremaMatrix_apply]
  by_cases hrs : r = s
  · subst s
    rw [if_pos rfl]
    have htwice := higham22_problem22_7_extrema_product_sum_twice n r r
    have hzeroMode :
        (∑ j : Fin (n + 1),
          higham22Problem22_7EndpointWeight n j.val *
            Real.cos (((r.val : Real) - (r.val : Real)) *
              higham22Problem22_7ExtremaAngle n j)) = (n : Real) := by
      simp only [sub_self, zero_mul, Real.cos_zero, mul_one]
      rw [Fin.sum_univ_eq_sum_range]
      exact higham22_problem22_7_endpointWeight_sum_one n hn
    rw [hzeroMode] at htwice
    by_cases hrend : higham22Problem22_7IsEndpoint n r
    · rw [if_pos hrend]
      rcases hrend with hr0 | hrn
      · have hr : r = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hr0
        subst r
        simpa only [Nat.cast_zero, zero_mul, Real.cos_zero, one_mul, mul_one,
          Fin.sum_univ_eq_sum_range] using
          higham22_problem22_7_endpointWeight_sum_one n hn
      · have hsumTop :
            (∑ j : Fin (n + 1),
              higham22Problem22_7EndpointWeight n j.val *
                Real.cos (((r.val : Real) + (r.val : Real)) *
                  higham22Problem22_7ExtremaAngle n j)) = (n : Real) := by
          rw [hrn]
          convert higham22_problem22_7_extrema_top_mode_sum n hn using 1
          apply Finset.sum_congr rfl
          intro j hj
          congr 2
          norm_cast <;> ring
        rw [hsumTop] at htwice
        linarith
    · rw [if_neg hrend]
      have hr0 : 0 < r.val := by
        have : r.val ≠ 0 := fun h => hrend (Or.inl h)
        exact Nat.pos_of_ne_zero this
      have hrn : r.val < n := by
        have hrle : r.val ≤ n := Nat.le_of_lt_succ r.isLt
        exact lt_of_le_of_ne hrle (fun h => hrend (Or.inr h))
      have hmode := higham22_problem22_7_extrema_mode_sum n (2 * r.val) hn
        (Nat.mul_pos (by norm_num) hr0) (by omega)
      have hsumMode :
          (∑ j : Fin (n + 1),
            higham22Problem22_7EndpointWeight n j.val *
              Real.cos (((r.val : Real) + (r.val : Real)) *
                higham22Problem22_7ExtremaAngle n j)) = 0 := by
        convert hmode using 1
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
        norm_cast <;> ring
      rw [hsumMode, add_zero] at htwice
      linarith
  · rw [if_neg hrs]
    rcases lt_or_gt_of_ne (fun h => hrs (Fin.ext h)) with hrslt | hrslt
    · have hdpos : 0 < s.val - r.val := Nat.sub_pos_of_lt hrslt
      have hdlt : s.val - r.val < 2 * n := by omega
      have hsumpos : 0 < r.val + s.val := by omega
      have hsumlt : r.val + s.val < 2 * n := by omega
      have hdiff := higham22_problem22_7_extrema_mode_sum n (s.val - r.val)
        hn hdpos hdlt
      have hsum := higham22_problem22_7_extrema_mode_sum n (r.val + s.val)
        hn hsumpos hsumlt
      have htwice := higham22_problem22_7_extrema_product_sum_twice n r s
      have hdiff' :
          (∑ j : Fin (n + 1),
            higham22Problem22_7EndpointWeight n j.val *
              Real.cos (((r.val : Real) - (s.val : Real)) *
                higham22Problem22_7ExtremaAngle n j)) = 0 := by
        rw [← hdiff]
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        rw [← Real.cos_neg]
        congr 1
        rw [Nat.cast_sub (le_of_lt hrslt)]
        ring
      have hsum' :
          (∑ j : Fin (n + 1),
            higham22Problem22_7EndpointWeight n j.val *
              Real.cos (((r.val : Real) + (s.val : Real)) *
                higham22Problem22_7ExtremaAngle n j)) = 0 := by
        convert hsum using 1
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
        norm_cast <;> ring
      rw [hdiff', hsum', add_zero] at htwice
      linarith
    · have hdpos : 0 < r.val - s.val := Nat.sub_pos_of_lt hrslt
      have hdlt : r.val - s.val < 2 * n := by omega
      have hsumpos : 0 < r.val + s.val := by omega
      have hsumlt : r.val + s.val < 2 * n := by omega
      have hdiff := higham22_problem22_7_extrema_mode_sum n (r.val - s.val)
        hn hdpos hdlt
      have hsum := higham22_problem22_7_extrema_mode_sum n (r.val + s.val)
        hn hsumpos hsumlt
      have htwice := higham22_problem22_7_extrema_product_sum_twice n r s
      have hdiff' :
          (∑ j : Fin (n + 1),
            higham22Problem22_7EndpointWeight n j.val *
              Real.cos (((r.val : Real) - (s.val : Real)) *
                higham22Problem22_7ExtremaAngle n j)) = 0 := by
        convert hdiff using 1
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
        rw [Nat.cast_sub (le_of_lt hrslt)]
      have hsum' :
          (∑ j : Fin (n + 1),
            higham22Problem22_7EndpointWeight n j.val *
              Real.cos (((r.val : Real) + (s.val : Real)) *
                higham22Problem22_7ExtremaAngle n j)) = 0 := by
        convert hsum using 1
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
        norm_cast <;> ring
      rw [hdiff', hsum', add_zero] at htwice
      linarith

/-- The diagonal `D` from Appendix A.22.7. -/
noncomputable def higham22Problem22_7ExtremaD (n : Nat) :
    Fin (n + 1) -> Real :=
  fun i => higham22Problem22_7EndpointWeight n i.val

/-- The diagonal `(n/2)D^{-1}` in the weighted Gram identity. -/
noncomputable def higham22Problem22_7ExtremaGramDiagonal (n : Nat) :
    Fin (n + 1) -> Real :=
  fun i => if higham22Problem22_7IsEndpoint n i then (n : Real) else (n : Real) / 2

/-- Matrix form of Appendix A.22.7's identity
`C D C^T = (n/2) D^{-1}`. -/
theorem higham22_problem22_7_extrema_weighted_gram
    (n : Nat) (hn : 0 < n) :
    matMul (n + 1)
        (matMul (n + 1) (higham22Problem22_7ExtremaMatrix n)
          (diagMatrix (higham22Problem22_7ExtremaD n)))
        (matTranspose (higham22Problem22_7ExtremaMatrix n)) =
      diagMatrix (higham22Problem22_7ExtremaGramDiagonal n) := by
  funext i j
  simp only [matMul, matTranspose, diagMatrix]
  rw [show
      (∑ x : Fin (n + 1),
        (∑ x_1 : Fin (n + 1),
          higham22Problem22_7ExtremaMatrix n i x_1 *
            (if x_1 = x then higham22Problem22_7ExtremaD n x_1 else 0)) *
          higham22Problem22_7ExtremaMatrix n j x) =
        ∑ x : Fin (n + 1),
          higham22Problem22_7ExtremaD n x *
            (higham22Problem22_7ExtremaMatrix n i x *
              higham22Problem22_7ExtremaMatrix n j x) by
      apply Finset.sum_congr rfl
      intro x hx
      rw [show
        (∑ x_1 : Fin (n + 1),
          higham22Problem22_7ExtremaMatrix n i x_1 *
            (if x_1 = x then higham22Problem22_7ExtremaD n x_1 else 0)) =
          higham22Problem22_7ExtremaMatrix n i x *
            higham22Problem22_7ExtremaD n x by simp]
      ring]
  change (∑ x : Fin (n + 1),
      higham22Problem22_7EndpointWeight n x.val *
        (higham22Problem22_7ExtremaMatrix n i x *
          higham22Problem22_7ExtremaMatrix n j x)) = _
  rw [higham22_problem22_7_extrema_discrete_orthogonality n hn]
  by_cases hij : i = j
  · subst j
    simp [higham22Problem22_7ExtremaD, diagMatrix,
      higham22Problem22_7ExtremaGramDiagonal]
  · simp [higham22Problem22_7ExtremaD, diagMatrix,
      higham22Problem22_7ExtremaGramDiagonal, hij]

end ExtremaOrthogonality

section OperatorNormHelpers

/-- Euclidean operator norm is submultiplicative in the repository's
`CMatrix` carrier. -/
lemma higham22_problem22_7_complexMatrixOp2_mul_le {m n p : Nat}
    (A : CMatrix m n) (B : CMatrix n p) :
    complexMatrixOp2 (complexMatrixMul A B) ≤
      complexMatrixOp2 A * complexMatrixOp2 B := by
  rw [complexMatrixOp2_eq_norm_euclideanLin,
    complexMatrixOp2_eq_norm_euclideanLin,
    complexMatrixOp2_eq_norm_euclideanLin]
  have hmaps :
      (complexMatrixEuclideanLin (complexMatrixMul A B)).toContinuousLinearMap =
        (complexMatrixEuclideanLin A).toContinuousLinearMap.comp
          (complexMatrixEuclideanLin B).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    exact complexMatrixEuclideanLin_mul A B x
  rw [hmaps]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- Real matrix product specialization of operator-norm
submultiplicativity. -/
lemma higham22_problem22_7_real_matMul_op2_le {N : Nat}
    (A B : Fin N -> Fin N -> Real) :
    complexMatrixOp2 (realRectToCMatrix (matMul N A B)) ≤
      complexMatrixOp2 (realRectToCMatrix A) *
        complexMatrixOp2 (realRectToCMatrix B) := by
  rw [realRectToCMatrix_matMul]
  exact higham22_problem22_7_complexMatrixOp2_mul_le _ _

/-- Operator norm of a complexified real diagonal matrix is the sup norm of
its diagonal. -/
lemma higham22_problem22_7_real_diag_op2
    {N : Nat} (d : Fin N -> Real) :
    complexMatrixOp2 (realRectToCMatrix (diagMatrix d)) =
      ‖fun i : Fin N => ((d i : Real) : Complex)‖ := by
  rw [complexMatrixOp2]
  rw [← Matrix.l2_opNorm_def]
  have hdiag :
      (realRectToCMatrix (diagMatrix d) : Matrix (Fin N) (Fin N) Complex) =
        Matrix.diagonal (fun i : Fin N => ((d i : Real) : Complex)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [realRectToCMatrix, diagMatrix]
    · simp [realRectToCMatrix, diagMatrix, Matrix.diagonal, hij]
  rw [hdiag, Matrix.l2_opNorm_diagonal]

/-- A pointwise nonnegative diagonal bounded by `c` has operator norm at
most `c`. -/
lemma higham22_problem22_7_real_diag_op2_le
    {N : Nat} (d : Fin N -> Real) (c : Real)
    (hc : 0 ≤ c) (hd0 : ∀ i, 0 ≤ d i) (hd : ∀ i, d i ≤ c) :
    complexMatrixOp2 (realRectToCMatrix (diagMatrix d)) ≤ c := by
  rw [higham22_problem22_7_real_diag_op2]
  apply (pi_norm_le_iff_of_nonneg hc).2
  intro i
  rw [complexNorm_ofReal_of_nonneg (hd0 i)]
  exact hd i

/-- If the preceding diagonal bound is attained at one coordinate, its
operator norm is exactly `c`. -/
lemma higham22_problem22_7_real_diag_op2_eq
    {N : Nat} (d : Fin N -> Real) (c : Real) (i0 : Fin N)
    (hc : 0 ≤ c) (hd0 : ∀ i, 0 ≤ d i) (hd : ∀ i, d i ≤ c)
    (hi0 : d i0 = c) :
    complexMatrixOp2 (realRectToCMatrix (diagMatrix d)) = c := by
  apply le_antisymm
  · exact higham22_problem22_7_real_diag_op2_le d c hc hd0 hd
  · rw [higham22_problem22_7_real_diag_op2]
    calc
      c = ‖(((d i0 : Real) : Complex))‖ := by
        rw [complexNorm_ofReal_of_nonneg (hd0 i0), hi0]
      _ ≤ ‖fun i : Fin N => ((d i : Real) : Complex)‖ :=
        norm_le_pi_norm (fun i : Fin N => ((d i : Real) : Complex)) i0

end OperatorNormHelpers

section ZeroConditionNumber

/-- Inverse diagonal of the first Gram matrix. -/
noncomputable def higham22Problem22_7ZeroGramInvDiagonal (n : Nat) :
    Fin (n + 1) -> Real :=
  fun i => if i.val = 0 then 1 / (n + 1 : Nat) else 2 / (n + 1 : Nat)

lemma higham22_problem22_7_zero_gram_diagonal_mul_inv
    (n : Nat) (i : Fin (n + 1)) :
    higham22Problem22_7ZeroGramDiagonal n i *
        higham22Problem22_7ZeroGramInvDiagonal n i = 1 := by
  by_cases hi : i.val = 0
  · simp [higham22Problem22_7ZeroGramDiagonal,
      higham22Problem22_7ZeroGramInvDiagonal, hi]
    field_simp
  · simp [higham22Problem22_7ZeroGramDiagonal,
      higham22Problem22_7ZeroGramInvDiagonal, hi]
    field_simp

/-- Explicit inverse obtained from `C C^T=G`: `C^{-1}=C^T G^{-1}`. -/
noncomputable def higham22Problem22_7ZeroInverse (n : Nat) :
    Fin (n + 1) -> Fin (n + 1) -> Real :=
  fun i j => higham22Problem22_7ZeroMatrix n j i *
    higham22Problem22_7ZeroGramInvDiagonal n j

/-- The explicit zero-grid inverse is a right inverse of the actual
Chebyshev--Vandermonde matrix. -/
theorem higham22_problem22_7_zero_isRightInverse (n : Nat) :
    IsRightInverse (n + 1) (higham22Problem22_7ZeroMatrix n)
      (higham22Problem22_7ZeroInverse n) := by
  intro i j
  simp only [higham22Problem22_7ZeroInverse]
  rw [show
      (∑ k : Fin (n + 1),
        higham22Problem22_7ZeroMatrix n i k *
          (higham22Problem22_7ZeroMatrix n j k *
            higham22Problem22_7ZeroGramInvDiagonal n j)) =
        (∑ k : Fin (n + 1),
          higham22Problem22_7ZeroMatrix n i k *
            higham22Problem22_7ZeroMatrix n j k) *
          higham22Problem22_7ZeroGramInvDiagonal n j by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring]
  rw [higham22_problem22_7_zero_discrete_orthogonality]
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    exact higham22_problem22_7_zero_gram_diagonal_mul_inv n i
  · simp [hij]

/-- The explicit zero-grid inverse is two-sided. -/
theorem higham22_problem22_7_zero_isInverse (n : Nat) :
    IsInverse (n + 1) (higham22Problem22_7ZeroMatrix n)
      (higham22Problem22_7ZeroInverse n) :=
  ⟨isLeftInverse_of_isRightInverse _ _
      (higham22_problem22_7_zero_isRightInverse n),
    higham22_problem22_7_zero_isRightInverse n⟩

/-- The explicit inverse is the repository's canonical nonsingular inverse. -/
theorem higham22_problem22_7_zero_nonsingInv_eq (n : Nat) :
    nonsingInv (n + 1) (higham22Problem22_7ZeroMatrix n) =
      higham22Problem22_7ZeroInverse n :=
  nonsingInv_eq_of_isRightInverse _ _
    (higham22_problem22_7_zero_isRightInverse n)

/-- Gram identity for the explicit inverse, `C^{-T}C^{-1}=G^{-1}`. -/
theorem higham22_problem22_7_zero_inverse_gram (n : Nat) :
    matMul (n + 1) (matTranspose (higham22Problem22_7ZeroInverse n))
        (higham22Problem22_7ZeroInverse n) =
      diagMatrix (higham22Problem22_7ZeroGramInvDiagonal n) := by
  funext i j
  simp only [matMul, matTranspose, higham22Problem22_7ZeroInverse]
  rw [show
      (∑ x : Fin (n + 1),
        (higham22Problem22_7ZeroMatrix n i x *
          higham22Problem22_7ZeroGramInvDiagonal n i) *
        (higham22Problem22_7ZeroMatrix n j x *
          higham22Problem22_7ZeroGramInvDiagonal n j)) =
        higham22Problem22_7ZeroGramInvDiagonal n i *
          higham22Problem22_7ZeroGramInvDiagonal n j *
          (∑ x : Fin (n + 1),
            higham22Problem22_7ZeroMatrix n i x *
              higham22Problem22_7ZeroMatrix n j x) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring]
  rw [higham22_problem22_7_zero_discrete_orthogonality]
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    rw [diagMatrix]
    simp only [if_pos]
    change higham22Problem22_7ZeroGramInvDiagonal n i *
        higham22Problem22_7ZeroGramInvDiagonal n i *
          higham22Problem22_7ZeroGramDiagonal n i =
      higham22Problem22_7ZeroGramInvDiagonal n i
    have hrecip := higham22_problem22_7_zero_gram_diagonal_mul_inv n i
    calc
      higham22Problem22_7ZeroGramInvDiagonal n i *
          higham22Problem22_7ZeroGramInvDiagonal n i *
            higham22Problem22_7ZeroGramDiagonal n i =
          higham22Problem22_7ZeroGramInvDiagonal n i *
            (higham22Problem22_7ZeroGramDiagonal n i *
              higham22Problem22_7ZeroGramInvDiagonal n i) := by ring
      _ = higham22Problem22_7ZeroGramInvDiagonal n i := by rw [hrecip, mul_one]
  · simp [diagMatrix, hij]

/-- The zero-grid matrix has squared operator norm `n+1`. -/
theorem higham22_problem22_7_zero_op2_sq (n : Nat) :
    complexMatrixOp2 (realRectToCMatrix
        (higham22Problem22_7ZeroMatrix n)) ^ 2 = (n + 1 : Nat) := by
  have hgram :=
    complexMatrixOp2_realRectToCMatrix_mul_transpose_self_eq_sq
      (higham22Problem22_7ZeroMatrix n)
  rw [higham22_problem22_7_zero_gram] at hgram
  have hdiag :
      complexMatrixOp2
          (realRectToCMatrix
            (diagMatrix (higham22Problem22_7ZeroGramDiagonal n))) =
        (n + 1 : Nat) := by
    apply higham22_problem22_7_real_diag_op2_eq _ _
      (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
    · positivity
    · intro i
      by_cases hi : i.val = 0 <;>
        simp [higham22Problem22_7ZeroGramDiagonal, hi] <;> positivity
    · intro i
      by_cases hi : i.val = 0
      · simp [higham22Problem22_7ZeroGramDiagonal, hi]
      · simp [higham22Problem22_7ZeroGramDiagonal, hi]
        have hN : (0 : Real) ≤ (n : Real) + 1 := by positivity
        linarith
    · simp [higham22Problem22_7ZeroGramDiagonal]
  linarith

/-- For `n>=1`, the explicit inverse has squared operator norm
`2/(n+1)`. -/
theorem higham22_problem22_7_zero_inverse_op2_sq
    (n : Nat) (hn : 1 ≤ n) :
    complexMatrixOp2 (realRectToCMatrix
        (higham22Problem22_7ZeroInverse n)) ^ 2 =
      2 / (n + 1 : Nat) := by
  have hgram :=
    complexMatrixOp2_realRectToCMatrix_transpose_mul_self_eq_sq
      (higham22Problem22_7ZeroInverse n)
  rw [higham22_problem22_7_zero_inverse_gram] at hgram
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  have hdiag :
      complexMatrixOp2
          (realRectToCMatrix
            (diagMatrix (higham22Problem22_7ZeroGramInvDiagonal n))) =
        2 / (n + 1 : Nat) := by
    apply higham22_problem22_7_real_diag_op2_eq _ _ i1
    · positivity
    · intro i
      by_cases hi : i.val = 0 <;>
        simp [higham22Problem22_7ZeroGramInvDiagonal, hi] <;> positivity
    · intro i
      by_cases hi : i.val = 0
      · simp [higham22Problem22_7ZeroGramInvDiagonal, hi]
        have hinv : 0 ≤ ((n : Real) + 1)⁻¹ := by positivity
        rw [div_eq_mul_inv]
        nlinarith
      · simp [higham22Problem22_7ZeroGramInvDiagonal, hi]
    · simp [i1, higham22Problem22_7ZeroGramInvDiagonal]
  linarith

/-- Source-facing spectral condition number formed with a proved inverse. -/
noncomputable def higham22Problem22_7Condition2 {N : Nat}
    (A Ainv : Fin N -> Fin N -> Real) : Real :=
  complexMatrixOp2 (realRectToCMatrix A) *
    complexMatrixOp2 (realRectToCMatrix Ainv)

/-- Higham Problem 22.7(1), with the source's actual nodes and canonical
inverse: `kappa_2(T)=sqrt 2` for zeros of `T_(n+1)`, on the honest nontrivial
domain `n>=1`. -/
theorem higham22_problem22_7_zeros_kappa2_eq_sqrt_two
    (n : Nat) (hn : 1 ≤ n) :
    higham22Problem22_7Condition2
        (higham22Problem22_7ZeroMatrix n)
        (nonsingInv (n + 1) (higham22Problem22_7ZeroMatrix n)) =
      Real.sqrt 2 := by
  rw [higham22Problem22_7Condition2,
    higham22_problem22_7_zero_nonsingInv_eq]
  apply (sq_eq_sq₀
    (mul_nonneg (complexMatrixOp2_nonneg _) (complexMatrixOp2_nonneg _))
    (Real.sqrt_nonneg _)).mp
  rw [mul_pow, higham22_problem22_7_zero_op2_sq,
    higham22_problem22_7_zero_inverse_op2_sq n hn,
    Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hN : ((n + 1 : Nat) : Real) ≠ 0 := by positivity
  field_simp

end ZeroConditionNumber

section ExtremaConditionNumber

/-- Square-root endpoint scaling `D^(1/2)`. -/
noncomputable def higham22Problem22_7ExtremaSqrtD (n : Nat) :
    Fin (n + 1) -> Real :=
  fun i => if higham22Problem22_7IsEndpoint n i then
    1 / Real.sqrt 2 else 1

/-- Reciprocal square-root endpoint scaling `D^(-1/2)`. -/
noncomputable def higham22Problem22_7ExtremaInvSqrtD (n : Nat) :
    Fin (n + 1) -> Real :=
  fun i => if higham22Problem22_7IsEndpoint n i then
    Real.sqrt 2 else 1

lemma higham22_problem22_7_extrema_sqrt_mul_invSqrt
    (n : Nat) (i : Fin (n + 1)) :
    higham22Problem22_7ExtremaSqrtD n i *
        higham22Problem22_7ExtremaInvSqrtD n i = 1 := by
  by_cases hi : higham22Problem22_7IsEndpoint n i
  · simp [higham22Problem22_7ExtremaSqrtD,
      higham22Problem22_7ExtremaInvSqrtD, hi,
      Real.sqrt_ne_zero'.mpr (by norm_num : (0 : Real) < 2)]
  · simp [higham22Problem22_7ExtremaSqrtD,
      higham22Problem22_7ExtremaInvSqrtD, hi]

lemma higham22_problem22_7_extrema_sqrtD_sq
    (n : Nat) (hn : 0 < n) (i : Fin (n + 1)) :
    higham22Problem22_7ExtremaSqrtD n i ^ 2 =
      higham22Problem22_7ExtremaD n i := by
  by_cases hi : higham22Problem22_7IsEndpoint n i
  · have hsqrt : Real.sqrt 2 ^ 2 = (2 : Real) :=
      Real.sq_sqrt (by norm_num)
    rcases hi with hi0 | hin
    · simp [higham22Problem22_7ExtremaSqrtD, higham22Problem22_7ExtremaD,
        higham22Problem22_7IsEndpoint, hi0,
        higham22_problem22_7_endpointWeight_zero n hn, hsqrt]
    · simp [higham22Problem22_7ExtremaSqrtD, higham22Problem22_7ExtremaD,
        higham22Problem22_7IsEndpoint, hin,
        higham22_problem22_7_endpointWeight_last n hn, hsqrt]
  · have hi0 : i.val ≠ 0 := fun h => hi (Or.inl h)
    have hin : i.val ≠ n := fun h => hi (Or.inr h)
    simp [higham22Problem22_7ExtremaSqrtD, higham22Problem22_7ExtremaD,
      hi, higham22_problem22_7_endpointWeight_interior n i.val hi0 hin]

/-- The scaled matrix `B=C D^(1/2)` from Appendix A.22.7. -/
noncomputable def higham22Problem22_7ExtremaB (n : Nat) :
    Fin (n + 1) -> Fin (n + 1) -> Real :=
  fun i j => higham22Problem22_7ExtremaMatrix n i j *
    higham22Problem22_7ExtremaSqrtD n j

/-- `B B^T=(n/2)D^{-1}` for the actual scaled Chebyshev matrix. -/
theorem higham22_problem22_7_extrema_B_gram
    (n : Nat) (hn : 0 < n) :
    matMul (n + 1) (higham22Problem22_7ExtremaB n)
        (matTranspose (higham22Problem22_7ExtremaB n)) =
      diagMatrix (higham22Problem22_7ExtremaGramDiagonal n) := by
  funext i j
  simp only [matMul, matTranspose, higham22Problem22_7ExtremaB]
  rw [show
      (∑ x : Fin (n + 1),
        (higham22Problem22_7ExtremaMatrix n i x *
          higham22Problem22_7ExtremaSqrtD n x) *
        (higham22Problem22_7ExtremaMatrix n j x *
          higham22Problem22_7ExtremaSqrtD n x)) =
        ∑ x : Fin (n + 1),
          higham22Problem22_7ExtremaD n x *
            (higham22Problem22_7ExtremaMatrix n i x *
              higham22Problem22_7ExtremaMatrix n j x) by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← higham22_problem22_7_extrema_sqrtD_sq n hn x]
      ring]
  change (∑ x : Fin (n + 1),
      higham22Problem22_7EndpointWeight n x.val *
        (higham22Problem22_7ExtremaMatrix n i x *
          higham22Problem22_7ExtremaMatrix n j x)) = _
  rw [higham22_problem22_7_extrema_discrete_orthogonality n hn]
  by_cases hij : i = j
  · subst j
    simp [diagMatrix, higham22Problem22_7ExtremaGramDiagonal]
  · simp [diagMatrix, higham22Problem22_7ExtremaGramDiagonal, hij]

/-- Inverse of the scaled Gram diagonal. -/
noncomputable def higham22Problem22_7ExtremaGramInvDiagonal (n : Nat) :
    Fin (n + 1) -> Real :=
  fun i => if higham22Problem22_7IsEndpoint n i then
    1 / (n : Real) else 2 / (n : Real)

lemma higham22_problem22_7_extrema_gram_diagonal_mul_inv
    (n : Nat) (hn : 0 < n) (i : Fin (n + 1)) :
    higham22Problem22_7ExtremaGramDiagonal n i *
        higham22Problem22_7ExtremaGramInvDiagonal n i = 1 := by
  have hnR : (n : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  by_cases hi : higham22Problem22_7IsEndpoint n i
  · simp [higham22Problem22_7ExtremaGramDiagonal,
      higham22Problem22_7ExtremaGramInvDiagonal, hi, hnR]
  · simp [higham22Problem22_7ExtremaGramDiagonal,
      higham22Problem22_7ExtremaGramInvDiagonal, hi, hnR]

/-- Explicit inverse of `B`, namely `B^T ((n/2)D^{-1})^{-1}`. -/
noncomputable def higham22Problem22_7ExtremaBInverse (n : Nat) :
    Fin (n + 1) -> Fin (n + 1) -> Real :=
  fun i j => higham22Problem22_7ExtremaB n j i *
    higham22Problem22_7ExtremaGramInvDiagonal n j

theorem higham22_problem22_7_extrema_B_isRightInverse
    (n : Nat) (hn : 0 < n) :
    IsRightInverse (n + 1) (higham22Problem22_7ExtremaB n)
      (higham22Problem22_7ExtremaBInverse n) := by
  intro i j
  simp only [higham22Problem22_7ExtremaBInverse]
  rw [show
      (∑ k : Fin (n + 1),
        higham22Problem22_7ExtremaB n i k *
          (higham22Problem22_7ExtremaB n j k *
            higham22Problem22_7ExtremaGramInvDiagonal n j)) =
        (∑ k : Fin (n + 1),
          higham22Problem22_7ExtremaB n i k *
            higham22Problem22_7ExtremaB n j k) *
          higham22Problem22_7ExtremaGramInvDiagonal n j by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring]
  have hentry := congrFun
    (congrFun (higham22_problem22_7_extrema_B_gram n hn) i) j
  simp only [matMul, matTranspose] at hentry
  rw [hentry]
  by_cases hij : i = j
  · subst j
    simp only [diagMatrix, if_pos]
    exact higham22_problem22_7_extrema_gram_diagonal_mul_inv n hn i
  · simp [diagMatrix, hij]

/-- The source matrix inverse `C^{-1}=D^(1/2) B^{-1}`. -/
noncomputable def higham22Problem22_7ExtremaInverse (n : Nat) :
    Fin (n + 1) -> Fin (n + 1) -> Real :=
  fun i j => higham22Problem22_7ExtremaSqrtD n i *
    higham22Problem22_7ExtremaBInverse n i j

/-- The constructed inverse is a right inverse of the actual extrema-grid
Chebyshev--Vandermonde matrix. -/
theorem higham22_problem22_7_extrema_isRightInverse
    (n : Nat) (hn : 0 < n) :
    IsRightInverse (n + 1) (higham22Problem22_7ExtremaMatrix n)
      (higham22Problem22_7ExtremaInverse n) := by
  intro i j
  simp only [higham22Problem22_7ExtremaInverse]
  rw [show
      (∑ k : Fin (n + 1),
        higham22Problem22_7ExtremaMatrix n i k *
          (higham22Problem22_7ExtremaSqrtD n k *
            higham22Problem22_7ExtremaBInverse n k j)) =
        ∑ k : Fin (n + 1),
          higham22Problem22_7ExtremaB n i k *
            higham22Problem22_7ExtremaBInverse n k j by
      apply Finset.sum_congr rfl
      intro k hk
      simp [higham22Problem22_7ExtremaB]
      ring]
  exact higham22_problem22_7_extrema_B_isRightInverse n hn i j

/-- The extrema-grid inverse is two-sided. -/
theorem higham22_problem22_7_extrema_isInverse
    (n : Nat) (hn : 0 < n) :
    IsInverse (n + 1) (higham22Problem22_7ExtremaMatrix n)
      (higham22Problem22_7ExtremaInverse n) :=
  ⟨isLeftInverse_of_isRightInverse _ _
      (higham22_problem22_7_extrema_isRightInverse n hn),
    higham22_problem22_7_extrema_isRightInverse n hn⟩

/-- Canonical-inverse identification for the extrema grid. -/
theorem higham22_problem22_7_extrema_nonsingInv_eq
    (n : Nat) (hn : 0 < n) :
    nonsingInv (n + 1) (higham22Problem22_7ExtremaMatrix n) =
      higham22Problem22_7ExtremaInverse n :=
  nonsingInv_eq_of_isRightInverse _ _
    (higham22_problem22_7_extrema_isRightInverse n hn)

/-- Gram matrix of `B^{-1}`. -/
theorem higham22_problem22_7_extrema_B_inverse_gram
    (n : Nat) (hn : 0 < n) :
    matMul (n + 1) (matTranspose (higham22Problem22_7ExtremaBInverse n))
        (higham22Problem22_7ExtremaBInverse n) =
      diagMatrix (higham22Problem22_7ExtremaGramInvDiagonal n) := by
  funext i j
  simp only [matMul, matTranspose, higham22Problem22_7ExtremaBInverse]
  rw [show
      (∑ x : Fin (n + 1),
        (higham22Problem22_7ExtremaB n i x *
          higham22Problem22_7ExtremaGramInvDiagonal n i) *
        (higham22Problem22_7ExtremaB n j x *
          higham22Problem22_7ExtremaGramInvDiagonal n j)) =
        higham22Problem22_7ExtremaGramInvDiagonal n i *
          higham22Problem22_7ExtremaGramInvDiagonal n j *
          (∑ x : Fin (n + 1),
            higham22Problem22_7ExtremaB n i x *
              higham22Problem22_7ExtremaB n j x) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring]
  have hentry := congrFun
    (congrFun (higham22_problem22_7_extrema_B_gram n hn) i) j
  simp only [matMul, matTranspose] at hentry
  rw [hentry]
  by_cases hij : i = j
  · subst j
    simp only [diagMatrix, if_pos]
    change higham22Problem22_7ExtremaGramInvDiagonal n i *
        higham22Problem22_7ExtremaGramInvDiagonal n i *
          higham22Problem22_7ExtremaGramDiagonal n i =
      higham22Problem22_7ExtremaGramInvDiagonal n i
    have hrecip :=
      higham22_problem22_7_extrema_gram_diagonal_mul_inv n hn i
    calc
      higham22Problem22_7ExtremaGramInvDiagonal n i *
          higham22Problem22_7ExtremaGramInvDiagonal n i *
            higham22Problem22_7ExtremaGramDiagonal n i =
          higham22Problem22_7ExtremaGramInvDiagonal n i *
            (higham22Problem22_7ExtremaGramDiagonal n i *
              higham22Problem22_7ExtremaGramInvDiagonal n i) := by ring
      _ = higham22Problem22_7ExtremaGramInvDiagonal n i := by
        rw [hrecip, mul_one]
  · simp [diagMatrix, hij]

/-- The scaled matrix `B` has squared operator norm `n`. -/
theorem higham22_problem22_7_extrema_B_op2_sq
    (n : Nat) (hn : 0 < n) :
    complexMatrixOp2 (realRectToCMatrix
        (higham22Problem22_7ExtremaB n)) ^ 2 = (n : Real) := by
  have hgram :=
    complexMatrixOp2_realRectToCMatrix_mul_transpose_self_eq_sq
      (higham22Problem22_7ExtremaB n)
  rw [higham22_problem22_7_extrema_B_gram n hn] at hgram
  have hdiag :
      complexMatrixOp2
          (realRectToCMatrix
            (diagMatrix (higham22Problem22_7ExtremaGramDiagonal n))) =
        (n : Real) := by
    apply higham22_problem22_7_real_diag_op2_eq _ _
      (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
    · positivity
    · intro i
      by_cases hi : higham22Problem22_7IsEndpoint n i <;>
        simp [higham22Problem22_7ExtremaGramDiagonal, hi] <;> positivity
    · intro i
      by_cases hi : higham22Problem22_7IsEndpoint n i
      · simp [higham22Problem22_7ExtremaGramDiagonal, hi]
      · simp [higham22Problem22_7ExtremaGramDiagonal, hi]
    · simp [higham22Problem22_7ExtremaGramDiagonal,
        higham22Problem22_7IsEndpoint]
  linarith

/-- The scaled inverse has squared operator norm at most `2/n`.  For `n=1`
this is deliberately an upper bound (there is no interior row), which is all
the source's final `kappa_2(C)<=2` proof needs. -/
theorem higham22_problem22_7_extrema_B_inverse_op2_sq_le
    (n : Nat) (hn : 0 < n) :
    complexMatrixOp2 (realRectToCMatrix
        (higham22Problem22_7ExtremaBInverse n)) ^ 2 ≤
      2 / (n : Real) := by
  have hgram :=
    complexMatrixOp2_realRectToCMatrix_transpose_mul_self_eq_sq
      (higham22Problem22_7ExtremaBInverse n)
  rw [higham22_problem22_7_extrema_B_inverse_gram n hn] at hgram
  rw [← hgram]
  apply higham22_problem22_7_real_diag_op2_le
  · positivity
  · intro i
    by_cases hi : higham22Problem22_7IsEndpoint n i <;>
      simp [higham22Problem22_7ExtremaGramInvDiagonal, hi] <;> positivity
  · intro i
    by_cases hi : higham22Problem22_7IsEndpoint n i
    · simp [higham22Problem22_7ExtremaGramInvDiagonal, hi]
      have hinv : 0 ≤ ((n : Real))⁻¹ := by positivity
      rw [div_eq_mul_inv]
      nlinarith
    · simp [higham22Problem22_7ExtremaGramInvDiagonal, hi]

/-- `C=B D^(-1/2)` entrywise. -/
theorem higham22_problem22_7_extrema_factor_C
    (n : Nat) :
    higham22Problem22_7ExtremaMatrix n =
      matMul (n + 1) (higham22Problem22_7ExtremaB n)
        (diagMatrix (higham22Problem22_7ExtremaInvSqrtD n)) := by
  funext i j
  rw [matMul_diagMatrix_right]
  unfold higham22Problem22_7ExtremaB
  rw [mul_assoc, higham22_problem22_7_extrema_sqrt_mul_invSqrt]
  ring

/-- `C^{-1}=D^(1/2)B^{-1}` entrywise. -/
theorem higham22_problem22_7_extrema_factor_inverse
    (n : Nat) :
    higham22Problem22_7ExtremaInverse n =
      matMul (n + 1) (diagMatrix (higham22Problem22_7ExtremaSqrtD n))
        (higham22Problem22_7ExtremaBInverse n) := by
  funext i j
  rw [matMul_diagMatrix_left]
  rfl

lemma higham22_problem22_7_extrema_sqrtD_op2_le_one
    (n : Nat) :
    complexMatrixOp2 (realRectToCMatrix
        (diagMatrix (higham22Problem22_7ExtremaSqrtD n))) ≤ 1 := by
  apply higham22_problem22_7_real_diag_op2_le
  · norm_num
  · intro i
    simp [higham22Problem22_7ExtremaSqrtD]
    split_ifs <;> positivity
  · intro i
    simp [higham22Problem22_7ExtremaSqrtD]
    split_ifs
    · have hsqrt : (1 : Real) ≤ Real.sqrt 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2),
          Real.sqrt_nonneg 2]
      have hinv := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hsqrt
      norm_num at hinv
      exact hinv
    · exact le_rfl

lemma higham22_problem22_7_extrema_invSqrtD_op2_eq_sqrt_two
    (n : Nat) :
    complexMatrixOp2 (realRectToCMatrix
        (diagMatrix (higham22Problem22_7ExtremaInvSqrtD n))) =
      Real.sqrt 2 := by
  apply higham22_problem22_7_real_diag_op2_eq _ _
    (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  · positivity
  · intro i
    simp [higham22Problem22_7ExtremaInvSqrtD]
    split_ifs <;> positivity
  · intro i
    simp [higham22Problem22_7ExtremaInvSqrtD]
    split_ifs
    · exact le_rfl
    · nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2),
        Real.sqrt_nonneg 2]
  · simp [higham22Problem22_7ExtremaInvSqrtD,
      higham22Problem22_7IsEndpoint]

/-- Higham Problem 22.7(2), with actual extrema nodes and the canonical
inverse: `kappa_2(T)<=2` for every `n>=1`. -/
theorem higham22_problem22_7_extrema_kappa2_le_two
    (n : Nat) (hn : 0 < n) :
    higham22Problem22_7Condition2
        (higham22Problem22_7ExtremaMatrix n)
        (nonsingInv (n + 1) (higham22Problem22_7ExtremaMatrix n)) ≤ 2 := by
  rw [higham22Problem22_7Condition2,
    higham22_problem22_7_extrema_nonsingInv_eq n hn]
  let bnorm := complexMatrixOp2
    (realRectToCMatrix (higham22Problem22_7ExtremaB n))
  let binvnorm := complexMatrixOp2
    (realRectToCMatrix (higham22Problem22_7ExtremaBInverse n))
  have hb_sq : bnorm ^ 2 = (n : Real) := by
    exact higham22_problem22_7_extrema_B_op2_sq n hn
  have hbinv_sq : binvnorm ^ 2 ≤ 2 / (n : Real) := by
    exact higham22_problem22_7_extrema_B_inverse_op2_sq_le n hn
  have hb0 : 0 ≤ bnorm := complexMatrixOp2_nonneg _
  have hbinv0 : 0 ≤ binvnorm := complexMatrixOp2_nonneg _
  have hpair : bnorm * binvnorm ≤ Real.sqrt 2 := by
    apply (sq_le_sq₀ (mul_nonneg hb0 hbinv0) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, hb_sq, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
    have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
    calc
      (n : Real) * binvnorm ^ 2 ≤ (n : Real) * (2 / (n : Real)) :=
        mul_le_mul_of_nonneg_left hbinv_sq hnR.le
      _ = 2 := by field_simp
  have hC :
      complexMatrixOp2
          (realRectToCMatrix (higham22Problem22_7ExtremaMatrix n)) ≤
        bnorm * Real.sqrt 2 := by
    rw [higham22_problem22_7_extrema_factor_C]
    calc
      complexMatrixOp2
          (realRectToCMatrix
            (matMul (n + 1) (higham22Problem22_7ExtremaB n)
              (diagMatrix (higham22Problem22_7ExtremaInvSqrtD n)))) ≤
          bnorm * complexMatrixOp2
            (realRectToCMatrix
              (diagMatrix (higham22Problem22_7ExtremaInvSqrtD n))) :=
        higham22_problem22_7_real_matMul_op2_le _ _
      _ = bnorm * Real.sqrt 2 := by
        rw [higham22_problem22_7_extrema_invSqrtD_op2_eq_sqrt_two]
  have hCinv :
      complexMatrixOp2
          (realRectToCMatrix (higham22Problem22_7ExtremaInverse n)) ≤
        binvnorm := by
    rw [higham22_problem22_7_extrema_factor_inverse]
    calc
      complexMatrixOp2
          (realRectToCMatrix
            (matMul (n + 1)
              (diagMatrix (higham22Problem22_7ExtremaSqrtD n))
              (higham22Problem22_7ExtremaBInverse n))) ≤
          complexMatrixOp2
              (realRectToCMatrix
                (diagMatrix (higham22Problem22_7ExtremaSqrtD n))) *
            binvnorm := higham22_problem22_7_real_matMul_op2_le _ _
      _ ≤ 1 * binvnorm :=
        mul_le_mul_of_nonneg_right
          (higham22_problem22_7_extrema_sqrtD_op2_le_one n) hbinv0
      _ = binvnorm := one_mul _
  calc
    complexMatrixOp2
        (realRectToCMatrix (higham22Problem22_7ExtremaMatrix n)) *
      complexMatrixOp2
        (realRectToCMatrix (higham22Problem22_7ExtremaInverse n)) ≤
        (bnorm * Real.sqrt 2) * binvnorm :=
      mul_le_mul hC hCinv (complexMatrixOp2_nonneg _)
        (mul_nonneg hb0 (Real.sqrt_nonneg _))
    _ = Real.sqrt 2 * (bnorm * binvnorm) := by ring
    _ ≤ Real.sqrt 2 * Real.sqrt 2 :=
      mul_le_mul_of_nonneg_left hpair (Real.sqrt_nonneg _)
    _ = 2 := Real.mul_self_sqrt (by norm_num)

end ExtremaConditionNumber

end NumStability
