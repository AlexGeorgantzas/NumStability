import NumStability.Algorithms.LeastSquares.Higham20AlternativeBound
import NumStability.Algorithms.LeastSquares.Higham20Theorem20_3

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# Higham, Chapter 20: residual quality after the QR solve

This file records the two exact identities printed immediately after
Theorem 20.3.  In particular, the second identity concerns the residual for
the *original* data, `b - A xhat`; it is not merely the difference between
the exact and perturbed residuals.
-/

/-- The residual of a supplied vector for the original least-squares data. -/
noncomputable def higham20ConventionalResidual {m n : Nat}
    (A : Fin m → Fin n → Real) (b : Fin m → Real)
    (xhat : Fin n → Real) : Fin m → Real :=
  fun i => b i - rectMatMulVec A xhat i

/-- Higham, 2nd ed., p. 385, the two exact residual-difference identities
following Theorem 20.3.

Here `r = b - A x` is the exact least-squares residual, while `rhat` is the
exact residual for the perturbed data `(A + DeltaA, b + Deltab)` at `xhat`.
The first equality is the top block of (20.6).  Eliminating `rhat` from that
equality gives the second, source-facing equality for `b - A xhat`.
-/
theorem higham20_postQR_residual_difference_identities
    {m n : Nat}
    (A : Fin m → Fin n → Real)
    (Aplus : Fin n → Fin m → Real)
    (gramInv : Fin n → Fin n → Real)
    (DeltaA : Fin m → Fin n → Real)
    (b Deltab r rhat : Fin m → Real)
    (x xhat : Fin n → Real)
    (hAplus : ∀ j i, Aplus j i = ∑ k : Fin n, gramInv j k * A i k)
    (hGramInv : IsInverse n (rectLSGram A) gramInv)
    (hGramInv_symm : ∀ j k : Fin n, gramInv j k = gramInv k j)
    (hExact : LSAugmentedSystem A b (0 : Fin n → Real) r x)
    (hPert :
      LSAugmentedSystem (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) (0 : Fin n → Real) rhat xhat) :
    (∀ i : Fin m,
      rhat i - r i =
        (Deltab i - rectMatMulVec DeltaA xhat i) -
          rectMatMulVec A
            (rectMatMulVec Aplus
              (fun k => Deltab k - rectMatMulVec DeltaA xhat k)) i -
          ∑ j : Fin n, Aplus j i *
            (∑ k : Fin m, DeltaA k j * rhat k)) ∧
    (∀ i : Fin m,
      higham20ConventionalResidual A b xhat i - r i =
        -rectMatMulVec A
            (rectMatMulVec Aplus
              (fun k => Deltab k - rectMatMulVec DeltaA xhat k)) i -
          ∑ j : Fin n, Aplus j i *
            (∑ k : Fin m, DeltaA k j * rhat k)) := by
  have hdiff :=
    lsAugmentedEq20_6_action_eq_differences_of_perturbed_systems
      A Aplus gramInv DeltaA b Deltab r rhat x xhat
      hAplus hGramInv hGramInv_symm hExact hPert
  have hfirst : ∀ i : Fin m,
      rhat i - r i =
        (Deltab i - rectMatMulVec DeltaA xhat i) -
          rectMatMulVec A
            (rectMatMulVec Aplus
              (fun k => Deltab k - rectMatMulVec DeltaA xhat k)) i -
          ∑ j : Fin n, Aplus j i *
            (∑ k : Fin m, DeltaA k j * rhat k) := by
    intro i
    have hi := hdiff.1 i
    unfold lsAugmentedInverseActionTop lsEq20_6RhsTop
      lsEq20_6RhsBottom at hi
    simpa only [mul_neg, Finset.sum_neg_distrib] using hi.symm
  refine ⟨hfirst, ?_⟩
  intro i
  have hpert_i := hPert.1 i
  have hresidual :
      higham20ConventionalResidual A b xhat i =
        rhat i - (Deltab i - rectMatMulVec DeltaA xhat i) := by
    unfold higham20ConventionalResidual rectMatMulVec at ⊢ hpert_i
    simp_rw [add_mul] at hpert_i
    rw [Finset.sum_add_distrib] at hpert_i
    linarith
  rw [hresidual]
  linarith [hfirst i]

/-- The first-order absolute majorant in the post-Theorem-20.3 residual
estimate:

`|AA^+| (f + E|x|) + |A^+|^T E^T |r|`.
-/
noncomputable def higham20PostQRResidualFirstOrderMajorant {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real)
    (E : Fin m → Fin n → Real) (f r : Fin m → Real)
    (x : Fin n → Real) : Fin m → Real :=
  fun i =>
    rectMatMulVec (absMatrixRect (rectMatMul A Aplus))
        (lsComponentwiseDataMajorant E f x) i +
      ∑ j : Fin n, |Aplus j i| * lsComponentwiseTransposeMajorant E r j

/-- The first-order majorant embedded in the combined residual/solution
space.  The lower block is zero because the target is only the conventional
residual. -/
noncomputable def higham20PostQRResidualFirstOrderVector {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real)
    (E : Fin m → Fin n → Real) (f r : Fin m → Real)
    (x : Fin n → Real) : Fin (m + n) → Real :=
  Fin.append (higham20PostQRResidualFirstOrderMajorant A Aplus E f r x)
    (fun _ : Fin n => 0)

/-- The exact nonnegative matrix multiplying
`[|rhat-r|; |xhat-x|]` in the quadratic residual correction.

Its upper-left block is `|A^+|^T E^T`, its upper-right block is
`|AA^+| E`, and its lower block is zero. -/
noncomputable def higham20PostQRResidualCorrectionMatrix {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real)
    (E : Fin m → Fin n → Real) :
    Fin (m + n) → Fin (m + n) → Real :=
  Fin.append
    (fun i : Fin m =>
      Fin.append
        (fun k : Fin m => ∑ j : Fin n, |Aplus j i| * E k j)
        (fun l : Fin n =>
          ∑ k : Fin m, |rectMatMul A Aplus i k| * E k l))
    (fun _ : Fin n => fun _ : Fin (m + n) => 0)

/-- The conventional residual error embedded in the combined space. -/
noncomputable def higham20PostQRConventionalResidualError {m n : Nat}
    (A : Fin m → Fin n → Real) (b r : Fin m → Real)
    (xhat : Fin n → Real) : Fin (m + n) → Real :=
  Fin.append (fun i => higham20ConventionalResidual A b xhat i - r i)
    (fun _ : Fin n => 0)

theorem higham20PostQRResidualCorrectionMatrix_nonneg {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real)
    {E : Fin m → Fin n → Real} (hE : ∀ i j, 0 ≤ E i j) :
    ∀ i j, 0 ≤ higham20PostQRResidualCorrectionMatrix A Aplus E i j := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro ii j
    refine Fin.addCases ?_ ?_ j <;> intro jj
    · simp only [higham20PostQRResidualCorrectionMatrix, Fin.append_left]
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg (Aplus k ii)) (hE jj k))
    · simp only [higham20PostQRResidualCorrectionMatrix, Fin.append_left,
        Fin.append_right]
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg (rectMatMul A Aplus ii k)) (hE k jj))
  · intro ii j
    simp [higham20PostQRResidualCorrectionMatrix]

theorem higham20PostQRResidualFirstOrderVector_nonneg {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real)
    {E : Fin m → Fin n → Real} {f r : Fin m → Real}
    (x : Fin n → Real) (hE : ∀ i j, 0 ≤ E i j)
    (hf : ∀ i, 0 ≤ f i) :
    ∀ k, 0 ≤ higham20PostQRResidualFirstOrderVector A Aplus E f r x k := by
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp only [higham20PostQRResidualFirstOrderVector, Fin.append_left,
      higham20PostQRResidualFirstOrderMajorant]
    apply add_nonneg
    · unfold rectMatMulVec absMatrixRect
      exact Finset.sum_nonneg (fun t _ => mul_nonneg
        (abs_nonneg (rectMatMul A Aplus i t)) (by
          unfold lsComponentwiseDataMajorant rectMatMulVec absVec
          exact add_nonneg (hf t) (Finset.sum_nonneg (fun j _ =>
            mul_nonneg (hE t j) (abs_nonneg (x j))))))
    · exact Finset.sum_nonneg (fun j _ => mul_nonneg
        (abs_nonneg (Aplus j i)) (by
          unfold lsComponentwiseTransposeMajorant
          exact Finset.sum_nonneg (fun t _ =>
            mul_nonneg (hE t j) (abs_nonneg (r t)))))
  · intro j
    simp [higham20PostQRResidualFirstOrderVector]

/-- Higham's post-Theorem-20.3 residual estimate with its `O(eps^2)`
replaced by a proved finite rational remainder.

The leading vector is exactly
`[|AA^+|(f+E|x|)+|A^+|^T E^T|r|; 0]`.  The remainder is quadratic in
`eps`; its coefficient uses genuine subordinate bounds for the two explicit
nonnegative matrices that propagate the already-proved componentwise
fixed-point estimate.  No displacement or residual-error conclusion is an
assumption.
-/
theorem higham20_postQR_residual_quality_finite
    {m n : Nat}
    (nu : CVec (m + n) → Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A : Fin m → Fin n → Real)
    (DeltaA E : Fin m → Fin n → Real)
    (Deltab f b : Fin m → Real)
    (r rhat : Fin m → Real) (x xhat : Fin n → Real)
    (eps q p : Real)
    (hA : Function.Injective (rectMatMulVec A))
    (hExact : LSAugmentedSystem A b (0 : Fin n → Real) r x)
    (hPert :
      LSAugmentedSystem (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) (0 : Fin n → Real) rhat xhat)
    (hcomp : LSComponentwisePerturbation DeltaA E Deltab f eps)
    (hq : MixedSubordinateMatrixBound nu nu
      (realRectToCMatrix
        (higham20AlternativeCouplingMatrix A (lsAplusOfGramNonsingInv A)
          (lsGramNonsingInv A) E)) q)
    (hp : MixedSubordinateMatrixBound nu nu
      (realRectToCMatrix
        (higham20PostQRResidualCorrectionMatrix A
          (lsAplusOfGramNonsingInv A) E)) p)
    (hp_nonneg : 0 ≤ p) (hsmall : eps * q < 1) :
    nu (realVecToComplex
        (higham20PostQRConventionalResidualError A b r xhat)) ≤
      eps * nu (realVecToComplex
        (higham20PostQRResidualFirstOrderVector A
          (lsAplusOfGramNonsingInv A) E f r x)) +
      eps ^ 2 * p *
        nu (realVecToComplex
          (higham20AlternativeSourceResponse A
            (lsAplusOfGramNonsingInv A) (lsGramNonsingInv A) E f r x)) /
        (1 - eps * q) := by
  let Aplus := lsAplusOfGramNonsingInv A
  let gramInv := lsGramNonsingInv A
  let C := higham20PostQRResidualCorrectionMatrix A Aplus E
  let lead := higham20PostQRResidualFirstOrderVector A Aplus E f r x
  let source := higham20AlternativeSourceResponse A Aplus gramInv E f r x
  let z : Fin (m + n) → Real :=
    Fin.append (fun i => rhat i - r i) (fun j => xhat j - x j)
  let w := higham20PostQRConventionalResidualError A b r xhat
  rcases hcomp with ⟨heps, hE, hf, hDeltaA, hDeltab⟩
  have hid :=
    higham20_postQR_residual_difference_identities
      A Aplus gramInv DeltaA b Deltab r rhat x xhat
      (by intro j i; rfl)
      (lsGramNonsingInv_isInverse_of_det_ne_zero A
        (rectLSGram_det_ne_zero_of_rectMatMulVec_injective A hA))
      (by intro j k; exact lsGramNonsingInv_symmetric A j k)
      hExact hPert
  have hx_abs (j : Fin n) : |xhat j| ≤ |x j| + |xhat j - x j| := by
    calc
      |xhat j| = |x j + (xhat j - x j)| := by ring_nf
      _ ≤ |x j| + |xhat j - x j| := abs_add_le _ _
  have hr_abs (i : Fin m) : |rhat i| ≤ |r i| + |rhat i - r i| := by
    calc
      |rhat i| = |r i + (rhat i - r i)| := by ring_nf
      _ ≤ |r i| + |rhat i - r i| := abs_add_le _ _
  have hpoint_top (i : Fin m) :
      |higham20ConventionalResidual A b xhat i - r i| ≤
        eps * (higham20PostQRResidualFirstOrderMajorant A Aplus E f r x i +
          rectMatMulVec C (fun k => |z k|) (Fin.castAdd n i)) := by
    have hexact := hid.2 i
    have habs0 :
        |higham20ConventionalResidual A b xhat i - r i| ≤
          |rectMatMulVec A
              (rectMatMulVec Aplus
                (fun k => Deltab k - rectMatMulVec DeltaA xhat k)) i| +
          |∑ j : Fin n, Aplus j i *
            (∑ k : Fin m, DeltaA k j * rhat k)| := by
      rw [hexact]
      simpa [abs_neg] using abs_add_le
        (-rectMatMulVec A
          (rectMatMulVec Aplus
            (fun k => Deltab k - rectMatMulVec DeltaA xhat k)) i)
        (-∑ j : Fin n, Aplus j i *
          (∑ k : Fin m, DeltaA k j * rhat k))
    have hdata (k : Fin m) :
        |Deltab k - rectMatMulVec DeltaA xhat k| ≤
          eps * (f k + ∑ j : Fin n, E k j * |xhat j|) := by
      calc
        |Deltab k - rectMatMulVec DeltaA xhat k|
            ≤ |Deltab k| + |rectMatMulVec DeltaA xhat k| := by
              simpa [sub_eq_add_neg, abs_neg] using
                abs_add_le (Deltab k) (-(rectMatMulVec DeltaA xhat k))
        _ ≤ eps * f k + ∑ j : Fin n, |DeltaA k j| * |xhat j| := by
              exact add_le_add (hDeltab k) (abs_rectMatMulVec_le DeltaA xhat k)
        _ ≤ eps * f k + ∑ j : Fin n, (eps * E k j) * |xhat j| := by
              apply add_le_add_right
              apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul_of_nonneg_right (hDeltaA k j) (abs_nonneg _)
        _ = eps * (f k + ∑ j : Fin n, E k j * |xhat j|) := by
              have hs :
                  (∑ j : Fin n, (eps * E k j) * |xhat j|) =
                    eps * ∑ j : Fin n, E k j * |xhat j| := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
              rw [hs]
              ring
    have hleft :
        |rectMatMulVec A
          (rectMatMulVec Aplus
            (fun k => Deltab k - rectMatMulVec DeltaA xhat k)) i| ≤
          eps * rectMatMulVec (absMatrixRect (rectMatMul A Aplus))
            (fun k => f k + ∑ j : Fin n, E k j * |xhat j|) i := by
      calc
        |rectMatMulVec A
          (rectMatMulVec Aplus
            (fun k => Deltab k - rectMatMulVec DeltaA xhat k)) i|
            = |rectMatMulVec (rectMatMul A Aplus)
                (fun k => Deltab k - rectMatMulVec DeltaA xhat k) i| := by
                  rw [rectMatMulVec_rectMatMul]
        _ ≤ ∑ k : Fin m, |rectMatMul A Aplus i k| *
              |Deltab k - rectMatMulVec DeltaA xhat k| :=
                abs_rectMatMulVec_le _ _ i
        _ ≤ ∑ k : Fin m, |rectMatMul A Aplus i k| *
              (eps * (f k + ∑ j : Fin n, E k j * |xhat j|)) := by
                apply Finset.sum_le_sum
                intro k _
                exact mul_le_mul_of_nonneg_left (hdata k) (abs_nonneg _)
        _ = eps * rectMatMulVec (absMatrixRect (rectMatMul A Aplus))
              (fun k => f k + ∑ j : Fin n, E k j * |xhat j|) i := by
                unfold rectMatMulVec absMatrixRect
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _
                ring
    have hright :
        |∑ j : Fin n, Aplus j i *
          (∑ k : Fin m, DeltaA k j * rhat k)| ≤
          eps * ∑ j : Fin n, |Aplus j i| *
            (∑ k : Fin m, E k j * |rhat k|) := by
      calc
        |∑ j : Fin n, Aplus j i *
          (∑ k : Fin m, DeltaA k j * rhat k)|
            ≤ ∑ j : Fin n, |Aplus j i| *
              |∑ k : Fin m, DeltaA k j * rhat k| := by
                calc
                  _ ≤ ∑ j : Fin n,
                      |Aplus j i * (∑ k : Fin m, DeltaA k j * rhat k)| :=
                        Finset.abs_sum_le_sum_abs _ _
                  _ = _ := by
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [abs_mul]
        _ ≤ ∑ j : Fin n, |Aplus j i| *
              (∑ k : Fin m, |DeltaA k j| * |rhat k|) := by
                apply Finset.sum_le_sum
                intro j _
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                calc
                  |∑ k : Fin m, DeltaA k j * rhat k|
                      ≤ ∑ k : Fin m, |DeltaA k j * rhat k| :=
                        Finset.abs_sum_le_sum_abs _ _
                  _ = _ := by
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [abs_mul]
        _ ≤ ∑ j : Fin n, |Aplus j i| *
              (∑ k : Fin m, (eps * E k j) * |rhat k|) := by
                apply Finset.sum_le_sum
                intro j _
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                apply Finset.sum_le_sum
                intro k _
                exact mul_le_mul_of_nonneg_right (hDeltaA k j) (abs_nonneg _)
        _ = eps * ∑ j : Fin n, |Aplus j i| *
              (∑ k : Fin m, E k j * |rhat k|) := by
                have hinner (j : Fin n) :
                    (∑ k : Fin m, (eps * E k j) * |rhat k|) =
                      eps * ∑ k : Fin m, E k j * |rhat k| := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro k _
                  ring
                simp_rw [hinner]
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
    have hraw := habs0.trans (add_le_add hleft hright)
    have hsplit_left :
        rectMatMulVec (absMatrixRect (rectMatMul A Aplus))
            (fun k => f k + ∑ j : Fin n, E k j * |xhat j|) i ≤
          rectMatMulVec (absMatrixRect (rectMatMul A Aplus))
              (lsComponentwiseDataMajorant E f x) i +
            ∑ l : Fin n,
              (∑ k : Fin m, |rectMatMul A Aplus i k| * E k l) *
                |xhat l - x l| := by
      unfold rectMatMulVec absMatrixRect lsComponentwiseDataMajorant absVec
      calc
        ∑ k : Fin m, |rectMatMul A Aplus i k| *
            (f k + ∑ j : Fin n, E k j * |xhat j|)
            ≤ ∑ k : Fin m, |rectMatMul A Aplus i k| *
              (f k + ∑ j : Fin n, E k j *
                (|x j| + |xhat j - x j|)) := by
                  apply Finset.sum_le_sum
                  intro k _
                  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                  apply add_le_add_right
                  apply Finset.sum_le_sum
                  intro j _
                  exact mul_le_mul_of_nonneg_left (hx_abs j) (hE k j)
        _ = (∑ k : Fin m, |rectMatMul A Aplus i k| *
              (f k + ∑ j : Fin n, E k j * |x j|)) +
            ∑ l : Fin n,
              (∑ k : Fin m, |rectMatMul A Aplus i k| * E k l) *
                |xhat l - x l| := by
                  have hswap :
                      (∑ k : Fin m, |rectMatMul A Aplus i k| *
                        (∑ l : Fin n, E k l * |xhat l - x l|)) =
                        ∑ l : Fin n,
                          (∑ k : Fin m,
                            |rectMatMul A Aplus i k| * E k l) *
                              |xhat l - x l| := by
                    simp_rw [Finset.mul_sum]
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro l _
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro k _
                    ring
                  simp_rw [mul_add]
                  simp_rw [Finset.sum_add_distrib]
                  simp_rw [mul_add]
                  simp_rw [Finset.sum_add_distrib]
                  rw [hswap]
                  ring
    have hsplit_right :
        ∑ j : Fin n, |Aplus j i| *
            (∑ k : Fin m, E k j * |rhat k|) ≤
          ∑ j : Fin n, |Aplus j i| *
              lsComponentwiseTransposeMajorant E r j +
            ∑ k : Fin m, (∑ j : Fin n, |Aplus j i| * E k j) *
              |rhat k - r k| := by
      unfold lsComponentwiseTransposeMajorant
      calc
        ∑ j : Fin n, |Aplus j i| *
            (∑ k : Fin m, E k j * |rhat k|)
            ≤ ∑ j : Fin n, |Aplus j i| *
              (∑ k : Fin m, E k j * (|r k| + |rhat k - r k|)) := by
                apply Finset.sum_le_sum
                intro j _
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                apply Finset.sum_le_sum
                intro k _
                exact mul_le_mul_of_nonneg_left (hr_abs k) (hE k j)
        _ = ∑ j : Fin n, |Aplus j i| *
              (∑ k : Fin m, E k j * |r k|) +
            ∑ k : Fin m, (∑ j : Fin n, |Aplus j i| * E k j) *
              |rhat k - r k| := by
                have hswap :
                    (∑ j : Fin n, |Aplus j i| *
                      (∑ k : Fin m, E k j * |rhat k - r k|)) =
                      ∑ k : Fin m,
                        (∑ j : Fin n, |Aplus j i| * E k j) *
                          |rhat k - r k| := by
                  simp_rw [Finset.mul_sum]
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro k _
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
                simp_rw [mul_add]
                simp_rw [Finset.sum_add_distrib]
                simp_rw [mul_add]
                simp_rw [Finset.sum_add_distrib]
                rw [hswap]
    calc
      |higham20ConventionalResidual A b xhat i - r i|
          ≤ eps *
            (rectMatMulVec (absMatrixRect (rectMatMul A Aplus))
                (fun k => f k + ∑ j : Fin n, E k j * |xhat j|) i +
              ∑ j : Fin n, |Aplus j i| *
                (∑ k : Fin m, E k j * |rhat k|)) := by
              simpa [mul_add] using hraw
      _ ≤ eps *
            ((rectMatMulVec (absMatrixRect (rectMatMul A Aplus))
                (lsComponentwiseDataMajorant E f x) i +
              ∑ j : Fin n, |Aplus j i| *
                lsComponentwiseTransposeMajorant E r j) +
              ((∑ k : Fin m, (∑ j : Fin n, |Aplus j i| * E k j) *
                  |rhat k - r k|) +
                ∑ l : Fin n,
                  (∑ k : Fin m, |rectMatMul A Aplus i k| * E k l) *
                    |xhat l - x l|)) := by
              apply mul_le_mul_of_nonneg_left _ heps
              linarith [hsplit_left, hsplit_right]
      _ = eps * (higham20PostQRResidualFirstOrderMajorant A Aplus E f r x i +
            rectMatMulVec C (fun k => |z k|) (Fin.castAdd n i)) := by
              simp [higham20PostQRResidualFirstOrderMajorant, C,
                higham20PostQRResidualCorrectionMatrix, z, rectMatMulVec,
                Fin.sum_univ_add]
  have hpoint : ∀ k, |w k| ≤
      eps * (lead k + rectMatMulVec C (fun j => |z j|) k) := by
    intro k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simpa [w, lead, Aplus, higham20PostQRConventionalResidualError,
        higham20PostQRResidualFirstOrderVector, Fin.append_left] using
          hpoint_top i
    · intro j
      have hCzero : rectMatMulVec C (fun k => |z k|) (Fin.natAdd m j) = 0 := by
        simp [C, higham20PostQRResidualCorrectionMatrix, rectMatMulVec]
      simp [w, lead, higham20PostQRConventionalResidualError,
        higham20PostQRResidualFirstOrderVector, hCzero]
  have hlead_nonneg : ∀ k, 0 ≤ lead k := by
    exact higham20PostQRResidualFirstOrderVector_nonneg A Aplus x hE hf
  have hC_nonneg : ∀ i j, 0 ≤ C i j := by
    exact higham20PostQRResidualCorrectionMatrix_nonneg A Aplus hE
  have hCz_nonneg : ∀ i, 0 ≤ rectMatMulVec C (fun j => |z j|) i := by
    intro i
    unfold rectMatMulVec
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hC_nonneg i j) (abs_nonneg _))
  have hmajor_nonneg : ∀ i,
      0 ≤ eps * (lead i + rectMatMulVec C (fun j => |z j|) i) := by
    intro i
    exact mul_nonneg heps (add_nonneg (hlead_nonneg i) (hCz_nonneg i))
  have hmono :
      nu (realVecToComplex w) ≤
        nu (realVecToComplex
          (fun i => eps * (lead i + rectMatMulVec C (fun j => |z j|) i))) :=
    realVecToComplex_norm_le_of_abs_le hnu habs hmajor_nonneg hpoint
  have hscale :
      nu (realVecToComplex
          (fun i => eps * (lead i + rectMatMulVec C (fun j => |z j|) i))) =
        eps * nu (realVecToComplex
          (fun i => lead i + rectMatMulVec C (fun j => |z j|) i)) :=
    realVecToComplex_norm_smul_nonneg hnu eps heps _
  have htri :
      nu (realVecToComplex
          (fun i => lead i + rectMatMulVec C (fun j => |z j|) i)) ≤
        nu (realVecToComplex lead) +
          nu (realVecToComplex (rectMatMulVec C (fun j => |z j|))) :=
    realVecToComplex_norm_add_le hnu lead (rectMatMulVec C (fun j => |z j|))
  have hmap :
      complexMatrixVecMul (realRectToCMatrix C)
          (realVecToComplex (fun j => |z j|)) =
        realVecToComplex (rectMatMulVec C (fun j => |z j|)) := by
    ext i
    simp [complexMatrixVecMul, realRectToCMatrix, realVecToComplex,
      rectMatMulVec]
  have habsz :
      nu (realVecToComplex (fun j => |z j|)) = nu (realVecToComplex z) := by
    have hv : complexAbsVec (realVecToComplex z) =
        realVecToComplex (fun j => |z j|) := by
      ext i
      simp [complexAbsVec, realVecToComplex, Real.norm_eq_abs]
    exact (congrArg nu hv).symm.trans (habs (realVecToComplex z))
  have hCbound :
      nu (realVecToComplex (rectMatMulVec C (fun j => |z j|))) ≤
        p * nu (realVecToComplex z) := by
    have hh := hp (realVecToComplex (fun j => |z j|))
    rw [hmap, habsz] at hh
    exact hh
  have hrawNorm :
      nu (realVecToComplex w) ≤
        eps * (nu (realVecToComplex lead) + p * nu (realVecToComplex z)) := by
    calc
      nu (realVecToComplex w)
          ≤ nu (realVecToComplex
            (fun i => eps * (lead i + rectMatMulVec C (fun j => |z j|) i))) :=
              hmono
      _ = eps * nu (realVecToComplex
            (fun i => lead i + rectMatMulVec C (fun j => |z j|) i)) := hscale
      _ ≤ eps * (nu (realVecToComplex lead) +
            nu (realVecToComplex (rectMatMulVec C (fun j => |z j|)))) :=
              mul_le_mul_of_nonneg_left htri heps
      _ ≤ eps * (nu (realVecToComplex lead) + p * nu (realVecToComplex z)) :=
              mul_le_mul_of_nonneg_left (add_le_add_right hCbound _) heps
  have hdisp :=
    higham20_alternative_theorem20_2_combined_bound
      nu hnu habs A DeltaA E Deltab f b r rhat x xhat eps q
      hA hExact hPert ⟨heps, hE, hf, hDeltaA, hDeltab⟩ hq hsmall
  have hden : 0 < 1 - eps * q := by linarith
  have hepsp : 0 ≤ eps * p := mul_nonneg heps hp_nonneg
  have hreplace :
      eps * p * nu (realVecToComplex z) ≤
        eps * p * ((eps * nu (realVecToComplex source)) / (1 - eps * q)) :=
    mul_le_mul_of_nonneg_left (by simpa [z, source, Aplus, gramInv] using hdisp) hepsp
  calc
    nu (realVecToComplex w)
        ≤ eps * (nu (realVecToComplex lead) + p * nu (realVecToComplex z)) :=
          hrawNorm
    _ = eps * nu (realVecToComplex lead) +
          eps * p * nu (realVecToComplex z) := by ring
    _ ≤ eps * nu (realVecToComplex lead) +
          eps * p * ((eps * nu (realVecToComplex source)) / (1 - eps * q)) :=
            add_le_add_right hreplace _
    _ = eps * nu (realVecToComplex lead) +
          eps ^ 2 * p * nu (realVecToComplex source) / (1 - eps * q) := by
            ring
    _ = _ := by
      simp [lead, source, Aplus, gramInv]

/-- A row-repeated column-2-norm majorant for a QR matrix perturbation.  It
is pointwise no larger than the source's `e e^T |A|` majorant. -/
noncomputable def higham20QRColumnNormMajorant {m n : Nat}
    (A : Fin m → Fin n → Real) : Fin m → Fin n → Real :=
  fun _ j => vecNorm2 (fun i : Fin m => A i j)

/-- A row-repeated 2-norm majorant for the QR right-hand-side perturbation. -/
noncomputable def higham20QRRhsNormMajorant {m : Nat}
    (b : Fin m → Real) : Fin m → Real :=
  fun _ => vecNorm2 b

/-- Columnwise and RHS 2-norm bounds imply the componentwise perturbation
model needed by the finite residual-quality theorem. -/
theorem higham20_qr_norm_bounds_to_componentwise
    {m n : Nat} (A DeltaA : Fin m → Fin n → Real)
    (b Deltab : Fin m → Real) (eps : Real)
    (heps : 0 ≤ eps)
    (hA : ∀ j : Fin n,
      vecNorm2 (fun i : Fin m => DeltaA i j) ≤
        eps * vecNorm2 (fun i : Fin m => A i j))
    (hb : vecNorm2 Deltab ≤ eps * vecNorm2 b) :
    LSComponentwisePerturbation DeltaA (higham20QRColumnNormMajorant A)
      Deltab (higham20QRRhsNormMajorant b) eps := by
  refine ⟨heps, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact vecNorm2_nonneg _
  · intro i
    exact vecNorm2_nonneg _
  · intro i j
    exact (abs_coord_le_vecNorm2 (fun k : Fin m => DeltaA k j) i).trans (hA j)
  · intro i
    exact (abs_coord_le_vecNorm2 Deltab i).trans hb

/-- Euclidean norm is bounded by the sum of coordinate absolute values. -/
theorem higham20_vecNorm2_le_sum_abs {d : Nat} (v : Fin d → Real) :
    vecNorm2 v ≤ ∑ i : Fin d, |v i| := by
  have hsq : vecNorm2 v ^ 2 ≤ (∑ i : Fin d, |v i|) ^ 2 := by
    rw [vecNorm2_sq]
    exact vecNorm2Sq_le_sum_abs_sq v
  have hv : 0 ≤ vecNorm2 v := vecNorm2_nonneg v
  have hs : 0 ≤ ∑ i : Fin d, |v i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg (v i))
  nlinarith

/-- The literal `e e^T |A|` majorant used in the source residual analysis. -/
noncomputable def higham20QRSourceDenseMatrixMajorant {m n : Nat}
    (A : Fin m → Fin n → Real) : Fin m → Fin n → Real :=
  fun _ j => ∑ i : Fin m, |A i j|

/-- The literal `e e^T |b|` majorant used in the source residual analysis. -/
noncomputable def higham20QRSourceDenseRhsMajorant {m : Nat}
    (b : Fin m → Real) : Fin m → Real :=
  fun _ => ∑ i : Fin m, |b i|

/-- The first vector in the literal Euclidean leading coefficient on p. 385:
`e eᵀ (|b| + |A| |x|)`. -/
noncomputable def higham20QRSourceDenseDataVector {m n : Nat}
    (A : Fin m → Fin n → Real) (b : Fin m → Real)
    (x : Fin n → Real) : Fin m → Real :=
  fun _ => ∑ i : Fin m, (|b i| + ∑ j : Fin n, |A i j| * |x j|)

/-- The second vector in the literal Euclidean leading coefficient on p. 385:
`|A⁺|ᵀ |Aᵀ| e eᵀ |r|`. -/
noncomputable def higham20QRSourceDenseAdjointResidualVector {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real)
    (r : Fin m → Real) : Fin m → Real :=
  fun i => ∑ j : Fin n, |Aplus j i| *
    ((∑ k : Fin m, |A k j|) * (∑ l : Fin m, |r l|))

/-- The dense componentwise data majorant unfolds exactly to
`e eᵀ (|b| + |A| |x|)`. -/
theorem higham20QRSourceDense_data_majorant_eq
    {m n : Nat} (A : Fin m → Fin n → Real) (b : Fin m → Real)
    (x : Fin n → Real) :
    lsComponentwiseDataMajorant (higham20QRSourceDenseMatrixMajorant A)
        (higham20QRSourceDenseRhsMajorant b) x =
      higham20QRSourceDenseDataVector A b x := by
  funext i
  unfold lsComponentwiseDataMajorant higham20QRSourceDenseMatrixMajorant
    higham20QRSourceDenseRhsMajorant higham20QRSourceDenseDataVector
    rectMatMulVec absVec
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    ∑ j : Fin n, (∑ k : Fin m, |A k j|) * |x j| =
        ∑ j : Fin n, ∑ k : Fin m, |A k j| * |x j| := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
    _ = ∑ k : Fin m, ∑ j : Fin n, |A k j| * |x j| := Finset.sum_comm

/-- The dense transpose majorant unfolds exactly to
`|A⁺|ᵀ |Aᵀ| e eᵀ |r|`. -/
theorem higham20QRSourceDense_adjoint_residual_majorant_eq
    {m n : Nat} (A : Fin m → Fin n → Real)
    (Aplus : Fin n → Fin m → Real) (r : Fin m → Real) :
    (fun i => ∑ j : Fin n, |Aplus j i| *
      lsComponentwiseTransposeMajorant
        (higham20QRSourceDenseMatrixMajorant A) r j) =
      higham20QRSourceDenseAdjointResidualVector A Aplus r := by
  funext i
  unfold lsComponentwiseTransposeMajorant higham20QRSourceDenseMatrixMajorant
    higham20QRSourceDenseAdjointResidualVector
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [Finset.mul_sum]

/-- The repository's complex `L²` norm agrees with `vecNorm2` on embedded
real vectors. -/
theorem higham20_complexVecLpNorm_two_realVecToComplex_eq_vecNorm2
    {d : Nat} (v : Fin d → Real) :
    complexVecLpNorm (ENNReal.ofReal (2 : Real)) (realVecToComplex v) =
      vecNorm2 v := by
  calc
    complexVecLpNorm (ENNReal.ofReal (2 : Real)) (realVecToComplex v) =
        norm (WithLp.toLp (2 : ENNReal) (realVecToComplex v)) :=
      complexVecLpNorm_two_eq_toLp (realVecToComplex v)
    _ = norm (realVecToEuclidean v) := by rfl
    _ = vecNorm2 v := realVecToEuclidean_norm v

/-- Theorem 20.3's norm bounds imply the exact dense componentwise model
`|DeltaA| <= eps e e^T |A|`,
`|Deltab| <= eps e e^T |b|` used on printed page 385. -/
theorem higham20_qr_norm_bounds_to_source_dense_componentwise
    {m n : Nat} (A DeltaA : Fin m → Fin n → Real)
    (b Deltab : Fin m → Real) (eps : Real)
    (heps : 0 ≤ eps)
    (hA : ∀ j : Fin n,
      vecNorm2 (fun i : Fin m => DeltaA i j) ≤
        eps * vecNorm2 (fun i : Fin m => A i j))
    (hb : vecNorm2 Deltab ≤ eps * vecNorm2 b) :
    LSComponentwisePerturbation DeltaA (higham20QRSourceDenseMatrixMajorant A)
      Deltab (higham20QRSourceDenseRhsMajorant b) eps := by
  refine ⟨heps, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact Finset.sum_nonneg (fun k _ => abs_nonneg (A k j))
  · intro i
    exact Finset.sum_nonneg (fun k _ => abs_nonneg (b k))
  · intro i j
    calc
      |DeltaA i j| ≤ vecNorm2 (fun k : Fin m => DeltaA k j) :=
        abs_coord_le_vecNorm2 (fun k : Fin m => DeltaA k j) i
      _ ≤ eps * vecNorm2 (fun k : Fin m => A k j) := hA j
      _ ≤ eps * (∑ k : Fin m, |A k j|) :=
        mul_le_mul_of_nonneg_left (higham20_vecNorm2_le_sum_abs _) heps
  · intro i
    calc
      |Deltab i| ≤ vecNorm2 Deltab := abs_coord_le_vecNorm2 _ i
      _ ≤ eps * vecNorm2 b := hb
      _ ≤ eps * (∑ k : Fin m, |b k|) :=
        mul_le_mul_of_nonneg_left (higham20_vecNorm2_le_sum_abs _) heps

/-- The sharp Euclidean specialization of the post-Theorem-20.3 estimate.

Unlike the absolute-norm endpoint above, the leading data term uses that
`A A⁺` is an orthogonal projector in the Euclidean norm.  Consequently its
coefficient is `||f + E|x||₂`, not the generally larger
`|||A A⁺|(f + E|x|)||₂`.  The second leading vector is exactly
`|A⁺|ᵀ Eᵀ |r|`.  The displayed remainder is a proved rational
`eps²` term obtained from the same genuine subordinate bounds `p` and `q` as
the combined fixed-point theorem. -/
theorem higham20_postQR_residual_quality_euclidean_sharp_finite
    {m n : Nat}
    (A : Fin m → Fin n → Real)
    (DeltaA E : Fin m → Fin n → Real)
    (Deltab f b : Fin m → Real)
    (r rhat : Fin m → Real) (x xhat : Fin n → Real)
    (eps q p : Real)
    (hA : Function.Injective (rectMatMulVec A))
    (hExact : LSAugmentedSystem A b (0 : Fin n → Real) r x)
    (hPert :
      LSAugmentedSystem (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) (0 : Fin n → Real) rhat xhat)
    (hcomp : LSComponentwisePerturbation DeltaA E Deltab f eps)
    (hq : MixedSubordinateMatrixBound
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (realRectToCMatrix
        (higham20AlternativeCouplingMatrix A (lsAplusOfGramNonsingInv A)
          (lsGramNonsingInv A) E)) q)
    (hp : MixedSubordinateMatrixBound
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (realRectToCMatrix
        (higham20PostQRResidualCorrectionMatrix A
          (lsAplusOfGramNonsingInv A) E)) p)
    (hp_nonneg : 0 ≤ p) (hsmall : eps * q < 1) :
    vecNorm2 (fun i => higham20ConventionalResidual A b xhat i - r i) ≤
      eps *
        (vecNorm2 (lsComponentwiseDataMajorant E f x) +
          vecNorm2 (fun i => ∑ j : Fin n, |lsAplusOfGramNonsingInv A j i| *
            lsComponentwiseTransposeMajorant E r j)) +
      eps ^ 2 * p *
        vecNorm2 (higham20AlternativeSourceResponse A
          (lsAplusOfGramNonsingInv A) (lsGramNonsingInv A) E f r x) /
        (1 - eps * q) := by
  let Aplus := lsAplusOfGramNonsingInv A
  let gramInv := lsGramNonsingInv A
  let P := rectMatMul A Aplus
  let C := higham20PostQRResidualCorrectionMatrix A Aplus E
  let data := lsComponentwiseDataMajorant E f x
  let adj : Fin m → Real := fun i =>
    ∑ j : Fin n, |Aplus j i| * lsComponentwiseTransposeMajorant E r j
  let source := higham20AlternativeSourceResponse A Aplus gramInv E f r x
  let dx : Fin n → Real := fun j => xhat j - x j
  let dr : Fin m → Real := fun i => rhat i - r i
  let z : Fin (m + n) → Real := Fin.append dr dx
  let d0 : Fin m → Real := fun i =>
    Deltab i - rectMatMulVec DeltaA x i
  let d1 : Fin m → Real := rectMatMulVec DeltaA dx
  let u0 : Fin m → Real := rectMatMulVec P d0
  let u1 : Fin m → Real := rectMatMulVec P d1
  let v0 : Fin m → Real := fun i =>
    ∑ j : Fin n, Aplus j i * (∑ k : Fin m, DeltaA k j * r k)
  let v1 : Fin m → Real := fun i =>
    ∑ j : Fin n, Aplus j i * (∑ k : Fin m, DeltaA k j * dr k)
  let lead : Fin m → Real := fun i => -u0 i - v0 i
  let corr : Fin m → Real := fun i => u1 i - v1 i
  let w : Fin m → Real := fun i =>
    higham20ConventionalResidual A b xhat i - r i
  rcases hcomp with ⟨heps, hE, hf, hDeltaA, hDeltab⟩
  have htwo : 1 ≤ ENNReal.ofReal (2 : Real) := by norm_num
  letI : Fact (1 ≤ ENNReal.ofReal (2 : Real)) := ⟨htwo⟩
  have hnu : IsComplexVectorNorm
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real))) :=
    complexVecLpNorm_isComplexVectorNorm _
  have habs : IsAbsoluteComplexVectorNorm
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real))) := by
    intro y
    exact complexVecLpNorm_ofReal_abs_eq (by norm_num) y
  have hid :=
    higham20_postQR_residual_difference_identities
      A Aplus gramInv DeltaA b Deltab r rhat x xhat
      (by intro j i; rfl)
      (lsGramNonsingInv_isInverse_of_det_ne_zero A
        (rectLSGram_det_ne_zero_of_rectMatMulVec_injective A hA))
      (by intro j k; exact lsGramNonsingInv_symmetric A j k)
      hExact hPert
  have hDAxhat (i : Fin m) :
      rectMatMulVec DeltaA xhat i =
        rectMatMulVec DeltaA x i + rectMatMulVec DeltaA dx i := by
    unfold rectMatMulVec dx
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hPsplit (i : Fin m) :
      rectMatMulVec P
          (fun k => Deltab k - rectMatMulVec DeltaA xhat k) i =
        u0 i - u1 i := by
    unfold u0 u1 d0 d1
    simp_rw [hDAxhat]
    unfold rectMatMulVec
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hVsplit (i : Fin m) :
      (∑ j : Fin n, Aplus j i *
          (∑ k : Fin m, DeltaA k j * rhat k)) = v0 i + v1 i := by
    unfold v0 v1 dr
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hw : w = fun i => lead i + corr i := by
    funext i
    have hi := hid.2 i
    unfold w lead corr
    rw [hi, ← rectMatMulVec_rectMatMul A Aplus, hPsplit, hVsplit]
    ring
  have hleftSym :=
    lsAplusOfGramNonsingInv_left_inverse_and_projection_symmetric A hA
  have hPcontract : rectOpNorm2Le P 1 := by
    apply theorem7_5_rect_left_inverse_symmetric_range_projection_op2Le_one
      A Aplus
    · intro i j
      have hij := congrFun (congrFun hleftSym.1 i) j
      simpa [rectMatMul, idMatrix] using hij
    · exact hleftSym.2
  have hd0point (i : Fin m) : |d0 i| ≤ eps * data i := by
    unfold d0 data lsComponentwiseDataMajorant rectMatMulVec absVec
    calc
      |Deltab i - ∑ j : Fin n, DeltaA i j * x j| ≤
          |Deltab i| + |∑ j : Fin n, DeltaA i j * x j| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add_le (Deltab i) (-∑ j : Fin n, DeltaA i j * x j)
      _ ≤ eps * f i + ∑ j : Fin n, |DeltaA i j| * |x j| :=
        add_le_add (hDeltab i) (by
          calc
            |∑ j : Fin n, DeltaA i j * x j| ≤
                ∑ j : Fin n, |DeltaA i j * x j| :=
              Finset.abs_sum_le_sum_abs _ _
            _ = ∑ j : Fin n, |DeltaA i j| * |x j| := by
              apply Finset.sum_congr rfl
              intro j _
              rw [abs_mul])
      _ ≤ eps * f i + ∑ j : Fin n, (eps * E i j) * |x j| := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hDeltaA i j) (abs_nonneg _)
      _ = eps * (f i + ∑ j : Fin n, E i j * |x j|) := by
        have hs : (∑ j : Fin n, (eps * E i j) * |x j|) =
            eps * ∑ j : Fin n, E i j * |x j| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hs]
        ring
  have hd0 : vecNorm2 d0 ≤ eps * vecNorm2 data := by
    calc
      vecNorm2 d0 ≤ vecNorm2 (fun i => eps * data i) :=
        vecNorm2_le_of_abs_le d0 _ hd0point
      _ = eps * vecNorm2 data := by
        rw [vecNorm2_smul, abs_of_nonneg heps]
  have hu0 : vecNorm2 u0 ≤ eps * vecNorm2 data := by
    have hpu : vecNorm2 u0 ≤ vecNorm2 d0 := by
      simpa [u0] using hPcontract d0
    exact hpu.trans hd0
  have hv0point (i : Fin m) : |v0 i| ≤ eps * adj i := by
    unfold v0 adj lsComponentwiseTransposeMajorant
    calc
      |∑ j : Fin n, Aplus j i *
          (∑ k : Fin m, DeltaA k j * r k)| ≤
          ∑ j : Fin n, |Aplus j i| *
            |∑ k : Fin m, DeltaA k j * r k| := by
        calc
          _ ≤ ∑ j : Fin n,
              |Aplus j i * (∑ k : Fin m, DeltaA k j * r k)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_mul]
      _ ≤ ∑ j : Fin n, |Aplus j i| *
          (∑ k : Fin m, |DeltaA k j| * |r k|) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc
          |∑ k : Fin m, DeltaA k j * r k| ≤
              ∑ k : Fin m, |DeltaA k j * r k| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro k _
            rw [abs_mul]
      _ ≤ ∑ j : Fin n, |Aplus j i| *
          (∑ k : Fin m, (eps * E k j) * |r k|) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hDeltaA k j) (abs_nonneg _)
      _ = eps * ∑ j : Fin n, |Aplus j i| *
          (∑ k : Fin m, E k j * |r k|) := by
        simp_rw [show ∀ j : Fin n,
            (∑ k : Fin m, (eps * E k j) * |r k|) =
              eps * ∑ k : Fin m, E k j * |r k| by
          intro j
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hv0 : vecNorm2 v0 ≤ eps * vecNorm2 adj := by
    calc
      vecNorm2 v0 ≤ vecNorm2 (fun i => eps * adj i) :=
        vecNorm2_le_of_abs_le v0 _ hv0point
      _ = eps * vecNorm2 adj := by
        rw [vecNorm2_smul, abs_of_nonneg heps]
  have hlead : vecNorm2 lead ≤
      eps * (vecNorm2 data + vecNorm2 adj) := by
    calc
      vecNorm2 lead ≤ vecNorm2 (fun i => -u0 i) +
          vecNorm2 (fun i => -v0 i) := by
        simpa [lead] using vecNorm2_add_le (fun i => -u0 i) (fun i => -v0 i)
      _ = vecNorm2 u0 + vecNorm2 v0 := by rw [vecNorm2_neg, vecNorm2_neg]
      _ ≤ eps * vecNorm2 data + eps * vecNorm2 adj := add_le_add hu0 hv0
      _ = eps * (vecNorm2 data + vecNorm2 adj) := by ring
  have hd1point (k : Fin m) : |d1 k| ≤
      eps * ∑ l : Fin n, E k l * |dx l| := by
    unfold d1 rectMatMulVec
    calc
      |∑ l : Fin n, DeltaA k l * dx l| ≤
          ∑ l : Fin n, |DeltaA k l * dx l| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l : Fin n, |DeltaA k l| * |dx l| := by
        apply Finset.sum_congr rfl
        intro l _
        rw [abs_mul]
      _ ≤ ∑ l : Fin n, (eps * E k l) * |dx l| := by
        apply Finset.sum_le_sum
        intro l _
        exact mul_le_mul_of_nonneg_right (hDeltaA k l) (abs_nonneg _)
      _ = eps * ∑ l : Fin n, E k l * |dx l| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
  have hu1point (i : Fin m) : |u1 i| ≤
      eps * ∑ l : Fin n,
        (∑ k : Fin m, |P i k| * E k l) * |dx l| := by
    unfold u1 rectMatMulVec
    calc
      |∑ k : Fin m, P i k * d1 k| ≤
          ∑ k : Fin m, |P i k| * |d1 k| := by
        calc
          _ ≤ ∑ k : Fin m, |P i k * d1 k| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro k _
            rw [abs_mul]
      _ ≤ ∑ k : Fin m, |P i k| *
          (eps * ∑ l : Fin n, E k l * |dx l|) := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hd1point k) (abs_nonneg _)
      _ = eps * ∑ l : Fin n,
          (∑ k : Fin m, |P i k| * E k l) * |dx l| := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.sum_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hv1point (i : Fin m) : |v1 i| ≤
      eps * ∑ k : Fin m,
        (∑ j : Fin n, |Aplus j i| * E k j) * |dr k| := by
    unfold v1
    calc
      |∑ j : Fin n, Aplus j i *
          (∑ k : Fin m, DeltaA k j * dr k)| ≤
          ∑ j : Fin n, |Aplus j i| *
            (∑ k : Fin m, |DeltaA k j| * |dr k|) := by
        calc
          _ ≤ ∑ j : Fin n,
              |Aplus j i * (∑ k : Fin m, DeltaA k j * dr k)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j : Fin n, |Aplus j i| *
              |∑ k : Fin m, DeltaA k j * dr k| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_mul]
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            calc
              |∑ k : Fin m, DeltaA k j * dr k| ≤
                  ∑ k : Fin m, |DeltaA k j * dr k| :=
                Finset.abs_sum_le_sum_abs _ _
              _ = _ := by
                apply Finset.sum_congr rfl
                intro k _
                rw [abs_mul]
      _ ≤ ∑ j : Fin n, |Aplus j i| *
          (∑ k : Fin m, (eps * E k j) * |dr k|) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hDeltaA k j) (abs_nonneg _)
      _ = eps * ∑ k : Fin m,
          (∑ j : Fin n, |Aplus j i| * E k j) * |dr k| := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hcorrpoint (i : Fin m) : |corr i| ≤
      eps * rectMatMulVec C (fun k => |z k|) (Fin.castAdd n i) := by
    calc
      |corr i| ≤ |u1 i| + |v1 i| := by
        simpa [corr, sub_eq_add_neg, abs_neg] using abs_add_le (u1 i) (-v1 i)
      _ ≤ eps * (
          (∑ l : Fin n, (∑ k : Fin m, |P i k| * E k l) * |dx l|) +
          (∑ k : Fin m, (∑ j : Fin n, |Aplus j i| * E k j) * |dr k|)) := by
        linarith [hu1point i, hv1point i]
      _ = eps * rectMatMulVec C (fun k => |z k|) (Fin.castAdd n i) := by
        apply congrArg (fun t : Real => eps * t)
        simp [C, P, higham20PostQRResidualCorrectionMatrix, rectMatMulVec,
          z, dr, dx, Fin.sum_univ_add]
        ring
  have hcorr : vecNorm2 corr ≤
      eps * p * vecNorm2 z := by
    let Cz := rectMatMulVec C (fun k => |z k|)
    have htop : vecNorm2 corr ≤
        vecNorm2 (fun i : Fin m => eps * Cz (Fin.castAdd n i)) :=
      vecNorm2_le_of_abs_le corr _ (by
        intro i
        simpa [Cz] using hcorrpoint i)
    have htop_scale :
        vecNorm2 (fun i : Fin m => eps * Cz (Fin.castAdd n i)) =
          eps * vecNorm2 (fun i : Fin m => Cz (Fin.castAdd n i)) := by
      rw [vecNorm2_smul, abs_of_nonneg heps]
    have htop_full : vecNorm2 (fun i : Fin m => Cz (Fin.castAdd n i)) ≤
        vecNorm2 Cz := lsVecNorm2_left_le_of_sum_coords Cz
    have hmap :
        complexMatrixVecMul (realRectToCMatrix C)
            (realVecToComplex (fun k => |z k|)) =
          realVecToComplex Cz := by
      ext i
      simp [Cz, complexMatrixVecMul, realRectToCMatrix, realVecToComplex,
        rectMatMulVec]
    have hCbound : vecNorm2 Cz ≤ p * vecNorm2 z := by
      have hh := hp (realVecToComplex (fun k => |z k|))
      rw [hmap, higham20_complexVecLpNorm_two_realVecToComplex_eq_vecNorm2,
        higham20_complexVecLpNorm_two_realVecToComplex_eq_vecNorm2,
        vecNorm2_abs] at hh
      exact hh
    calc
      vecNorm2 corr ≤ vecNorm2 (fun i : Fin m => eps * Cz (Fin.castAdd n i)) :=
        htop
      _ = eps * vecNorm2 (fun i : Fin m => Cz (Fin.castAdd n i)) := htop_scale
      _ ≤ eps * vecNorm2 Cz := mul_le_mul_of_nonneg_left htop_full heps
      _ ≤ eps * (p * vecNorm2 z) :=
        mul_le_mul_of_nonneg_left hCbound heps
      _ = eps * p * vecNorm2 z := by ring
  have hraw : vecNorm2 w ≤
      eps * (vecNorm2 data + vecNorm2 adj) + eps * p * vecNorm2 z := by
    calc
      vecNorm2 w = vecNorm2 (fun i => lead i + corr i) := by rw [hw]
      _ ≤ vecNorm2 lead + vecNorm2 corr := vecNorm2_add_le lead corr
      _ ≤ eps * (vecNorm2 data + vecNorm2 adj) + eps * p * vecNorm2 z :=
        add_le_add hlead hcorr
  have hdisp :=
    higham20_alternative_theorem20_2_combined_bound
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      hnu habs A DeltaA E Deltab f b r rhat x xhat eps q
      hA hExact hPert ⟨heps, hE, hf, hDeltaA, hDeltab⟩ hq hsmall
  have hdisp2 : vecNorm2 z ≤
      (eps * vecNorm2 source) / (1 - eps * q) := by
    rw [higham20_complexVecLpNorm_two_realVecToComplex_eq_vecNorm2,
      higham20_complexVecLpNorm_two_realVecToComplex_eq_vecNorm2] at hdisp
    simpa [z, dr, dx, source, Aplus, gramInv] using hdisp
  have hden : 0 < 1 - eps * q := by linarith
  have hepsp : 0 ≤ eps * p := mul_nonneg heps hp_nonneg
  have hreplace : eps * p * vecNorm2 z ≤
      eps * p * ((eps * vecNorm2 source) / (1 - eps * q)) :=
    mul_le_mul_of_nonneg_left hdisp2 hepsp
  calc
    vecNorm2 (fun i => higham20ConventionalResidual A b xhat i - r i) =
        vecNorm2 w := rfl
    _ ≤ eps * (vecNorm2 data + vecNorm2 adj) + eps * p * vecNorm2 z := hraw
    _ ≤ eps * (vecNorm2 data + vecNorm2 adj) +
        eps * p * ((eps * vecNorm2 source) / (1 - eps * q)) :=
      add_le_add_right hreplace _
    _ = eps * (vecNorm2 data + vecNorm2 adj) +
        eps ^ 2 * p * vecNorm2 source / (1 - eps * q) := by ring
    _ = _ := by simp [data, adj, source, Aplus, gramInv]

/-- Page 385 with the two leading vectors written literally as
`e eᵀ (|b| + |A||x|)` and `|A⁺|ᵀ |Aᵀ| e eᵀ |r|`.
The hidden `O(eps²)` in the book is the explicit final rational term. -/
theorem higham20_postQR_residual_quality_source_euclidean_sharp_finite
    {m n : Nat}
    (A DeltaA : Fin m → Fin n → Real)
    (Deltab b r rhat : Fin m → Real) (x xhat : Fin n → Real)
    (eps q p : Real)
    (hA : Function.Injective (rectMatMulVec A))
    (hExact : LSAugmentedSystem A b (0 : Fin n → Real) r x)
    (hPert :
      LSAugmentedSystem (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) (0 : Fin n → Real) rhat xhat)
    (hcomp : LSComponentwisePerturbation DeltaA
      (higham20QRSourceDenseMatrixMajorant A) Deltab
      (higham20QRSourceDenseRhsMajorant b) eps)
    (hq : MixedSubordinateMatrixBound
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (realRectToCMatrix
        (higham20AlternativeCouplingMatrix A (lsAplusOfGramNonsingInv A)
          (lsGramNonsingInv A) (higham20QRSourceDenseMatrixMajorant A))) q)
    (hp : MixedSubordinateMatrixBound
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (realRectToCMatrix
        (higham20PostQRResidualCorrectionMatrix A
          (lsAplusOfGramNonsingInv A)
          (higham20QRSourceDenseMatrixMajorant A))) p)
    (hp_nonneg : 0 ≤ p) (hsmall : eps * q < 1) :
    vecNorm2 (fun i => higham20ConventionalResidual A b xhat i - r i) ≤
      eps *
        (vecNorm2 (higham20QRSourceDenseDataVector A b x) +
          vecNorm2 (higham20QRSourceDenseAdjointResidualVector A
            (lsAplusOfGramNonsingInv A) r)) +
      eps ^ 2 * p *
        vecNorm2 (higham20AlternativeSourceResponse A
          (lsAplusOfGramNonsingInv A) (lsGramNonsingInv A)
          (higham20QRSourceDenseMatrixMajorant A)
          (higham20QRSourceDenseRhsMajorant b) r x) /
        (1 - eps * q) := by
  have h := higham20_postQR_residual_quality_euclidean_sharp_finite
    A DeltaA (higham20QRSourceDenseMatrixMajorant A) Deltab
    (higham20QRSourceDenseRhsMajorant b) b r rhat x xhat eps q p
    hA hExact hPert hcomp hq hp hp_nonneg hsmall
  rw [higham20QRSourceDense_data_majorant_eq,
    higham20QRSourceDense_adjoint_residual_majorant_eq] at h
  exact h

namespace Theorem20_3

theorem gamma_tilde_mn_nonneg
    (fp : FPModel) (m n : Nat) (hvalid : gammaValid fp (gammaIndex m n)) :
    0 ≤ gamma_tilde_mn fp m n := by
  have hvalid_rhs :
      gammaValid fp (householderQRRhsPanelGammaClosedGrowthIndex m n) :=
    gammaValid_mono fp (by simp [gammaIndex]) hvalid
  have hrhs : 0 ≤ rhsCoeff fp m n := by
    unfold rhsCoeff
    exact mul_nonneg (Real.sqrt_nonneg _)
      (gamma_nonneg fp hvalid_rhs)
  exact hrhs.trans (le_max_right (matrixCoeff fp m n) (rhsCoeff fp m n))

/-- The actual Householder-QR/rounded-back-substitution output satisfies the
finite post-QR residual estimate.  This composes Theorem 20.3's constructed
perturbations with `higham20_postQR_residual_quality_finite`, so the
quadratic remainder is attached to the literal computed vector rather than
to an abstract perturbation certificate.
-/
theorem householder_qr_fl_backSub_residual_quality_finite
    {m n : Nat} (fp : FPModel)
    (nu : CVec (m + n) → Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A : Fin m → Fin n → Real) (b : Fin m → Real)
    (x : Fin n → Real) (q p : Real)
    (hn : 0 < n) (hmn : n ≤ m)
    (hvalid : gammaValid fp (gammaIndex m n))
    (hdiag : ∀ i : Fin n, computedR fp A hmn i i ≠ 0)
    (hA : Function.Injective (rectMatMulVec A))
    (hx : IsLeastSquaresMinimizer A b x)
    (hq : MixedSubordinateMatrixBound nu nu
      (realRectToCMatrix
        (higham20AlternativeCouplingMatrix A (lsAplusOfGramNonsingInv A)
          (lsGramNonsingInv A) (higham20QRSourceDenseMatrixMajorant A))) q)
    (hp : MixedSubordinateMatrixBound nu nu
      (realRectToCMatrix
        (higham20PostQRResidualCorrectionMatrix A
          (lsAplusOfGramNonsingInv A) (higham20QRSourceDenseMatrixMajorant A))) p)
    (hp_nonneg : 0 ≤ p)
    (hsmall : gamma_tilde_mn fp m n * q < 1) :
    ∃ (DeltaA : Fin m → Fin n → Real) (Deltab : Fin m → Real),
      (∀ j : Fin n,
        vecNorm2 (fun i : Fin m => DeltaA i j) ≤
          gamma_tilde_mn fp m n * vecNorm2 (fun i : Fin m => A i j)) ∧
      vecNorm2 Deltab ≤ gamma_tilde_mn fp m n * vecNorm2 b ∧
      IsLeastSquaresMinimizer
        (fun i j => A i j + DeltaA i j) (fun i => b i + Deltab i)
        (computedX fp A b hmn) ∧
      nu (realVecToComplex
          (higham20PostQRConventionalResidualError A b
            (lsResidualHigham A b x) (computedX fp A b hmn))) ≤
        gamma_tilde_mn fp m n *
          nu (realVecToComplex
            (higham20PostQRResidualFirstOrderVector A
              (lsAplusOfGramNonsingInv A) (higham20QRSourceDenseMatrixMajorant A)
              (higham20QRSourceDenseRhsMajorant b) (lsResidualHigham A b x) x)) +
        (gamma_tilde_mn fp m n) ^ 2 * p *
          nu (realVecToComplex
            (higham20AlternativeSourceResponse A
              (lsAplusOfGramNonsingInv A) (lsGramNonsingInv A)
              (higham20QRSourceDenseMatrixMajorant A) (higham20QRSourceDenseRhsMajorant b)
              (lsResidualHigham A b x) x)) /
          (1 - gamma_tilde_mn fp m n * q) := by
  rcases householder_qr_fl_backSub_backward_error
      fp A b hn hmn hvalid hdiag with
    ⟨DeltaA, Deltab, hDeltaA, hDeltab, hmin⟩
  have heps : 0 ≤ gamma_tilde_mn fp m n :=
    gamma_tilde_mn_nonneg fp m n hvalid
  have hcomp :=
    higham20_qr_norm_bounds_to_source_dense_componentwise
      A DeltaA b Deltab (gamma_tilde_mn fp m n)
      heps hDeltaA hDeltab
  have hExact :
      LSAugmentedSystem A b (0 : Fin n → Real)
        (lsResidualHigham A b x) x :=
    (LSAugmentedSystem.iff_rectLSNormalEquations_zero_rhs A b x).2
      (IsLeastSquaresMinimizer.rectLSNormalEquations hx)
  let xhat : Fin n → Real := computedX fp A b hmn
  let rhat : Fin m → Real :=
    lsResidualHigham (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i) xhat
  have hmin' :
      IsLeastSquaresMinimizer
        (fun i j => A i j + DeltaA i j) (fun i => b i + Deltab i) xhat := by
    simpa [xhat, computedX] using hmin
  have hPert :
      LSAugmentedSystem (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) (0 : Fin n → Real) rhat xhat := by
    simpa [rhat] using
      (LSPerturbedAugmentedSystem.of_isLeastSquaresMinimizer
        A DeltaA b Deltab xhat hmin')
  have hbound :=
    higham20_postQR_residual_quality_finite
      nu hnu habs A DeltaA (higham20QRSourceDenseMatrixMajorant A)
      Deltab (higham20QRSourceDenseRhsMajorant b) b
      (lsResidualHigham A b x) rhat x xhat
      (gamma_tilde_mn fp m n) q p hA hExact hPert hcomp hq hp hp_nonneg hsmall
  refine ⟨DeltaA, Deltab, hDeltaA, hDeltab, hmin', ?_⟩
  simpa [xhat] using hbound

/-- The literal output `computedX` of Theorem 20.3 satisfies the sharp
Euclidean p. 385 coefficient.  The two displayed `vecNorm2` terms are exactly
`||e eᵀ(|b|+|A||x|)||₂` and
`|||A⁺|ᵀ|Aᵀ|e eᵀ|r|||₂`; the final rational expression is a
proved replacement for `O(gamma_tilde_mn²)`. -/
theorem householder_qr_fl_backSub_residual_quality_euclidean_sharp_finite
    {m n : Nat} (fp : FPModel)
    (A : Fin m → Fin n → Real) (b : Fin m → Real)
    (x : Fin n → Real) (q p : Real)
    (hn : 0 < n) (hmn : n ≤ m)
    (hvalid : gammaValid fp (gammaIndex m n))
    (hdiag : ∀ i : Fin n, computedR fp A hmn i i ≠ 0)
    (hA : Function.Injective (rectMatMulVec A))
    (hx : IsLeastSquaresMinimizer A b x)
    (hq : MixedSubordinateMatrixBound
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (realRectToCMatrix
        (higham20AlternativeCouplingMatrix A (lsAplusOfGramNonsingInv A)
          (lsGramNonsingInv A) (higham20QRSourceDenseMatrixMajorant A))) q)
    (hp : MixedSubordinateMatrixBound
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (realRectToCMatrix
        (higham20PostQRResidualCorrectionMatrix A
          (lsAplusOfGramNonsingInv A) (higham20QRSourceDenseMatrixMajorant A))) p)
    (hp_nonneg : 0 ≤ p)
    (hsmall : gamma_tilde_mn fp m n * q < 1) :
    ∃ (DeltaA : Fin m → Fin n → Real) (Deltab : Fin m → Real),
      (∀ j : Fin n,
        vecNorm2 (fun i : Fin m => DeltaA i j) ≤
          gamma_tilde_mn fp m n * vecNorm2 (fun i : Fin m => A i j)) ∧
      vecNorm2 Deltab ≤ gamma_tilde_mn fp m n * vecNorm2 b ∧
      IsLeastSquaresMinimizer
        (fun i j => A i j + DeltaA i j) (fun i => b i + Deltab i)
        (computedX fp A b hmn) ∧
      vecNorm2 (fun i =>
          higham20ConventionalResidual A b (computedX fp A b hmn) i -
            lsResidualHigham A b x i) ≤
        gamma_tilde_mn fp m n *
          (vecNorm2 (higham20QRSourceDenseDataVector A b x) +
            vecNorm2 (higham20QRSourceDenseAdjointResidualVector A
              (lsAplusOfGramNonsingInv A) (lsResidualHigham A b x))) +
        (gamma_tilde_mn fp m n) ^ 2 * p *
          vecNorm2 (higham20AlternativeSourceResponse A
            (lsAplusOfGramNonsingInv A) (lsGramNonsingInv A)
            (higham20QRSourceDenseMatrixMajorant A)
            (higham20QRSourceDenseRhsMajorant b)
            (lsResidualHigham A b x) x) /
          (1 - gamma_tilde_mn fp m n * q) := by
  rcases householder_qr_fl_backSub_backward_error
      fp A b hn hmn hvalid hdiag with
    ⟨DeltaA, Deltab, hDeltaA, hDeltab, hmin⟩
  have heps : 0 ≤ gamma_tilde_mn fp m n :=
    gamma_tilde_mn_nonneg fp m n hvalid
  have hcomp :=
    higham20_qr_norm_bounds_to_source_dense_componentwise
      A DeltaA b Deltab (gamma_tilde_mn fp m n)
      heps hDeltaA hDeltab
  have hExact :
      LSAugmentedSystem A b (0 : Fin n → Real)
        (lsResidualHigham A b x) x :=
    (LSAugmentedSystem.iff_rectLSNormalEquations_zero_rhs A b x).2
      (IsLeastSquaresMinimizer.rectLSNormalEquations hx)
  let xhat : Fin n → Real := computedX fp A b hmn
  let rhat : Fin m → Real :=
    lsResidualHigham (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i) xhat
  have hmin' :
      IsLeastSquaresMinimizer
        (fun i j => A i j + DeltaA i j) (fun i => b i + Deltab i) xhat := by
    simpa [xhat, computedX] using hmin
  have hPert :
      LSAugmentedSystem (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) (0 : Fin n → Real) rhat xhat := by
    simpa [rhat] using
      (LSPerturbedAugmentedSystem.of_isLeastSquaresMinimizer
        A DeltaA b Deltab xhat hmin')
  have hbound :=
    higham20_postQR_residual_quality_source_euclidean_sharp_finite
      A DeltaA Deltab b (lsResidualHigham A b x) rhat x xhat
      (gamma_tilde_mn fp m n) q p hA hExact hPert hcomp hq hp hp_nonneg hsmall
  refine ⟨DeltaA, Deltab, hDeltaA, hDeltab, hmin', ?_⟩
  simpa [xhat] using hbound

/-- The corresponding p. 385 bound for the norm of the conventional residual
itself, obtained by adding the exact least-squares residual norm. -/
theorem householder_qr_fl_backSub_conventional_residual_euclidean_sharp_finite
    {m n : Nat} (fp : FPModel)
    (A : Fin m → Fin n → Real) (b : Fin m → Real)
    (x : Fin n → Real) (q p : Real)
    (hn : 0 < n) (hmn : n ≤ m)
    (hvalid : gammaValid fp (gammaIndex m n))
    (hdiag : ∀ i : Fin n, computedR fp A hmn i i ≠ 0)
    (hA : Function.Injective (rectMatMulVec A))
    (hx : IsLeastSquaresMinimizer A b x)
    (hq : MixedSubordinateMatrixBound
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (realRectToCMatrix
        (higham20AlternativeCouplingMatrix A (lsAplusOfGramNonsingInv A)
          (lsGramNonsingInv A) (higham20QRSourceDenseMatrixMajorant A))) q)
    (hp : MixedSubordinateMatrixBound
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (complexVecLpNorm (n := m + n) (ENNReal.ofReal (2 : Real)))
      (realRectToCMatrix
        (higham20PostQRResidualCorrectionMatrix A
          (lsAplusOfGramNonsingInv A) (higham20QRSourceDenseMatrixMajorant A))) p)
    (hp_nonneg : 0 ≤ p)
    (hsmall : gamma_tilde_mn fp m n * q < 1) :
    vecNorm2 (higham20ConventionalResidual A b (computedX fp A b hmn)) ≤
      vecNorm2 (lsResidualHigham A b x) +
        gamma_tilde_mn fp m n *
          (vecNorm2 (higham20QRSourceDenseDataVector A b x) +
            vecNorm2 (higham20QRSourceDenseAdjointResidualVector A
              (lsAplusOfGramNonsingInv A) (lsResidualHigham A b x))) +
        (gamma_tilde_mn fp m n) ^ 2 * p *
          vecNorm2 (higham20AlternativeSourceResponse A
            (lsAplusOfGramNonsingInv A) (lsGramNonsingInv A)
            (higham20QRSourceDenseMatrixMajorant A)
            (higham20QRSourceDenseRhsMajorant b)
            (lsResidualHigham A b x) x) /
          (1 - gamma_tilde_mn fp m n * q) := by
  rcases householder_qr_fl_backSub_residual_quality_euclidean_sharp_finite
      fp A b x q p hn hmn hvalid hdiag hA hx hq hp hp_nonneg hsmall with
    ⟨DeltaA, Deltab, hDeltaA, hDeltab, hmin, hdiff⟩
  let r0 := lsResidualHigham A b x
  let rcomp := higham20ConventionalResidual A b (computedX fp A b hmn)
  have hdecomp : rcomp = fun i => r0 i + (rcomp i - r0 i) := by
    funext i
    ring
  calc
    vecNorm2 (higham20ConventionalResidual A b (computedX fp A b hmn)) =
        vecNorm2 rcomp := rfl
    _ = vecNorm2 (fun i => r0 i + (rcomp i - r0 i)) :=
      congrArg vecNorm2 hdecomp
    _ ≤ vecNorm2 r0 + vecNorm2 (fun i => rcomp i - r0 i) :=
      vecNorm2_add_le r0 (fun i => rcomp i - r0 i)
    _ ≤ vecNorm2 r0 +
        (gamma_tilde_mn fp m n *
          (vecNorm2 (higham20QRSourceDenseDataVector A b x) +
            vecNorm2 (higham20QRSourceDenseAdjointResidualVector A
              (lsAplusOfGramNonsingInv A) r0)) +
        (gamma_tilde_mn fp m n) ^ 2 * p *
          vecNorm2 (higham20AlternativeSourceResponse A
            (lsAplusOfGramNonsingInv A) (lsGramNonsingInv A)
            (higham20QRSourceDenseMatrixMajorant A)
            (higham20QRSourceDenseRhsMajorant b) r0 x) /
          (1 - gamma_tilde_mn fp m n * q)) := by
      have hh := add_le_add_left hdiff (vecNorm2 r0)
      simpa [r0, rcomp] using hh
    _ = _ := by
      simp only [r0]
      ring

end Theorem20_3

end NumStability
