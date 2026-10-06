-- Higham20Refinement.lean
--
-- Executed one-step augmented-system iterative refinement for Higham,
-- 2nd ed., Chapter 20, equation (20.16).

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LeastSquares.Higham20Equations

namespace NumStability

open scoped BigOperators

/-- The exact componentwise defect majorant obtained by moving the two
Theorem 20.4 matrix perturbations and the two right-hand-side perturbations
back to the unperturbed augmented system. -/
noncomputable def higham20Eq20_4CorrectionMajorant {m n : ℕ}
    (E1 E2 : Fin m → Fin n → ℝ)
    (Deltaf : Fin m → ℝ) (Deltag : Fin n → ℝ)
    (rhat : Fin m → ℝ) (x : Fin n → ℝ) : Fin (m + n) → ℝ :=
  Fin.append
    (fun i => |Deltaf i| + ∑ j : Fin n, |E1 i j| * |x j|)
    (fun j => |Deltag j| + ∑ i : Fin m, |E2 i j| * |rhat i|)

theorem LSAsymmetricAugmentedSystem.unperturbed_defect_abs_le
    {m n : ℕ}
    (A E1 E2 : Fin m → Fin n → ℝ)
    (f Deltaf : Fin m → ℝ) (g Deltag : Fin n → ℝ)
    (rhat : Fin m → ℝ) (x : Fin n → ℝ)
    (h : LSAsymmetricAugmentedSystem
      (fun i j => A i j + E1 i j)
      (fun i j => A i j + E2 i j)
      (fun i => f i + Deltaf i) (fun j => g j + Deltag j) rhat x) :
    ∀ p : Fin (m + n),
      |Fin.append f g p - ∑ q : Fin (m + n),
          higham20Eq20_16Matrix A p q * Fin.append rhat x q| ≤
        higham20Eq20_4CorrectionMajorant E1 E2 Deltaf Deltag rhat x p := by
  intro p
  refine Fin.addCases (motive := fun p : Fin (m + n) =>
    |Fin.append f g p - ∑ q : Fin (m + n),
        higham20Eq20_16Matrix A p q * Fin.append rhat x q| ≤
      higham20Eq20_4CorrectionMajorant E1 E2 Deltaf Deltag rhat x p) ?_ ?_ p
  · intro i
    have hsys := h.1 i
    change rhat i + ∑ j : Fin n, (A i j + E1 i j) * x j =
      f i + Deltaf i at hsys
    simp only [add_mul, Finset.sum_add_distrib] at hsys
    have heq :
        f i - (rhat i + rectMatMulVec A x i) =
          rectMatMulVec E1 x i - Deltaf i := by
      unfold rectMatMulVec
      linarith
    simp only [Fin.append_left]
    change |f i - rectMatMulVec (higham20Eq20_16Matrix A)
      (Fin.append rhat x) (Fin.castAdd n i)| ≤ _
    rw [higham20Eq20_16Matrix_eq_lsScaledAugmentedMatrix_one A,
      congrFun (lsScaledAugmentedMatrix_mulVec (m := m) (n := n) 1 A rhat x)
        (Fin.castAdd n i), Fin.append_left]
    simp only [one_mul]
    rw [heq]
    unfold higham20Eq20_4CorrectionMajorant rectMatMulVec
    rw [Fin.append_left]
    calc
      |∑ j : Fin n, E1 i j * x j - Deltaf i| ≤
          |∑ j : Fin n, E1 i j * x j| + |Deltaf i| := by
            simpa [sub_eq_add_neg] using
              abs_add_le (∑ j : Fin n, E1 i j * x j) (-Deltaf i)
      _ ≤ (∑ j : Fin n, |E1 i j| * |x j|) + |Deltaf i| := by
            exact add_le_add
              (by
                simpa [abs_mul] using
                  (Finset.abs_sum_le_sum_abs (s := Finset.univ)
                    (f := fun j : Fin n => E1 i j * x j))) le_rfl
      _ = |Deltaf i| + ∑ j : Fin n, |E1 i j| * |x j| := by ring
  · intro j
    have hsys := h.2 j
    change (∑ i : Fin m, (A i j + E2 i j) * rhat i) =
      g j + Deltag j at hsys
    simp only [add_mul, Finset.sum_add_distrib] at hsys
    have heq :
        g j - ∑ i : Fin m, A i j * rhat i =
          (∑ i : Fin m, E2 i j * rhat i) - Deltag j := by
      linarith
    simp only [Fin.append_right]
    change |g j - rectMatMulVec (higham20Eq20_16Matrix A)
      (Fin.append rhat x) (Fin.natAdd m j)| ≤ _
    rw [higham20Eq20_16Matrix_eq_lsScaledAugmentedMatrix_one A,
      congrFun (lsScaledAugmentedMatrix_mulVec (m := m) (n := n) 1 A rhat x)
        (Fin.natAdd m j), Fin.append_right, heq]
    unfold higham20Eq20_4CorrectionMajorant
    rw [Fin.append_right]
    calc
      |∑ i : Fin m, E2 i j * rhat i - Deltag j| ≤
          |∑ i : Fin m, E2 i j * rhat i| + |Deltag j| := by
            simpa [sub_eq_add_neg] using
              abs_add_le (∑ i : Fin m, E2 i j * rhat i) (-Deltag j)
      _ ≤ (∑ i : Fin m, |E2 i j| * |rhat i|) + |Deltag j| := by
            exact add_le_add
              (by
                simpa [abs_mul] using
                  (Finset.abs_sum_le_sum_abs (s := Finset.univ)
                    (f := fun i : Fin m => E2 i j * rhat i))) le_rfl
      _ = |Deltag j| + ∑ i : Fin m, |E2 i j| * |rhat i| := by ring

/-- The exact finite one-step residual inequality with an arbitrary proved
correction-solver majorant.  The conventional residual and the rounded update
are the actual floating-point kernels, so this theorem contains no residual-
formation or update contract. -/
theorem higham20_eq20_16_actual_residual_update_of_solver_majorant
    (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ)
    (z d rhs : Fin (m + n) → ℝ)
    (solverMajorant : Fin (m + n) → ℝ)
    (hdim : gammaValid fp (m + n + 1))
    (hsolve : ∀ p : Fin (m + n),
      |higham20Eq20_16ComputedResidual fp A z rhs p -
          ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q * d q| ≤
        solverMajorant p) :
    ∀ p : Fin (m + n),
      |rhs p - ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q *
          higham20Eq20_16RoundedUpdate fp z d q| ≤
        solverMajorant p +
          gamma fp (m + n + 1) *
            (|rhs p| + ∑ q : Fin (m + n),
              |higham20Eq20_16Matrix A p q| * |z q|) +
          fp.u * ∑ q : Fin (m + n),
            |higham20Eq20_16Matrix A p q| * (|z q| + |d q|) := by
  intro p
  have hdim0 : gammaValid fp (m + n) :=
    gammaValid_mono fp (by omega) hdim
  have hbase := higham12_14_residual_bound (m + n)
    (higham20Eq20_16Matrix A) z d rhs
    (fun q => rhs q - ∑ t : Fin (m + n),
      higham20Eq20_16Matrix A q t * z t)
    (higham20Eq20_16ComputedResidual fp A z rhs)
    (higham20Eq20_16UpdateError fp z d)
    (higham20Eq20_16RoundedUpdate fp z d)
    (fun _ => rfl) (higham20Eq20_16RoundedUpdate_eq fp z d) p
  have hres := higham12_9_conventional_residual_error fp (m + n)
    (higham20Eq20_16Matrix A) z rhs hdim0 hdim p
  have hup := higham20Eq20_16UpdateError_abs_le fp z d
  calc
    |rhs p - ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q *
        higham20Eq20_16RoundedUpdate fp z d q| ≤
        |higham20Eq20_16ComputedResidual fp A z rhs p -
          ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q * d q| +
        |higham20Eq20_16ComputedResidual fp A z rhs p -
          (rhs p - ∑ q : Fin (m + n),
            higham20Eq20_16Matrix A p q * z q)| +
        ∑ q : Fin (m + n), |higham20Eq20_16Matrix A p q| *
          |higham20Eq20_16UpdateError fp z d q| := hbase
    _ ≤ solverMajorant p +
          gamma fp (m + n + 1) *
            (|rhs p| + ∑ q : Fin (m + n),
              |higham20Eq20_16Matrix A p q| * |z q|) +
          fp.u * ∑ q : Fin (m + n),
            |higham20Eq20_16Matrix A p q| * (|z q| + |d q|) := by
      refine add_le_add (add_le_add (hsolve p) hres) ?_
      calc
        (∑ q : Fin (m + n), |higham20Eq20_16Matrix A p q| *
            |higham20Eq20_16UpdateError fp z d q|) ≤
            ∑ q : Fin (m + n), |higham20Eq20_16Matrix A p q| *
              (fp.u * (|z q| + |d q|)) := by
                exact Finset.sum_le_sum (fun q _ =>
                  mul_le_mul_of_nonneg_left (hup q) (abs_nonneg _))
        _ = fp.u * ∑ q : Fin (m + n),
              |higham20Eq20_16Matrix A p q| * (|z q| + |d q|) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro q _
                ring

/-- Every vector on the augmented index set is exactly the append of its two
canonical source blocks. -/
theorem higham20Eq20_16_append_split {m n : ℕ}
    (v : Fin (m + n) → ℝ) :
    Fin.append (fun i : Fin m => v (Fin.castAdd n i))
      (fun j : Fin n => v (Fin.natAdd m j)) = v := by
  ext p
  refine Fin.addCases (motive := fun p : Fin (m + n) =>
    Fin.append (fun i : Fin m => v (Fin.castAdd n i))
      (fun j : Fin n => v (Fin.natAdd m j)) p = v p) ?_ ?_ p
  · intro i
    simp only [Fin.append_left]
  · intro j
    simp only [Fin.append_right]

/-- Equation (20.16) after an asymmetric perturbed augmented-system
certificate for the computed correction.  This discharges the last abstract
solver-defect premise: moving the certificate's perturbations to the right-
hand side gives the explicit `higham20Eq20_4CorrectionMajorant`. -/
theorem higham20_eq20_16_of_asymmetric_perturbed_correction
    (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ)
    (z rhs : Fin (m + n) → ℝ)
    (E1 E2 : Fin m → Fin n → ℝ)
    (Deltaf : Fin m → ℝ) (Deltag : Fin n → ℝ)
    (rhat : Fin m → ℝ) (x : Fin n → ℝ)
    (hdim : gammaValid fp (m + n + 1))
    (hsys : LSAsymmetricAugmentedSystem
      (fun i j => A i j + E1 i j)
      (fun i j => A i j + E2 i j)
      (fun i => higham20Eq20_16ComputedResidual fp A z rhs
          (Fin.castAdd n i) + Deltaf i)
      (fun j => higham20Eq20_16ComputedResidual fp A z rhs
          (Fin.natAdd m j) + Deltag j)
      rhat x) :
    ∀ p : Fin (m + n),
      |rhs p - ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q *
          higham20Eq20_16RoundedUpdate fp z (Fin.append rhat x) q| ≤
        higham20Eq20_4CorrectionMajorant E1 E2 Deltaf Deltag rhat x p +
          gamma fp (m + n + 1) *
            (|rhs p| + ∑ q : Fin (m + n),
              |higham20Eq20_16Matrix A p q| * |z q|) +
          fp.u * ∑ q : Fin (m + n),
            |higham20Eq20_16Matrix A p q| *
              (|z q| + |Fin.append rhat x q|) := by
  apply higham20_eq20_16_actual_residual_update_of_solver_majorant
    fp m n A z (Fin.append rhat x) rhs
      (higham20Eq20_4CorrectionMajorant E1 E2 Deltaf Deltag rhat x) hdim
  intro p
  have hdef := LSAsymmetricAugmentedSystem.unperturbed_defect_abs_le
    A E1 E2
    (fun i : Fin m => higham20Eq20_16ComputedResidual fp A z rhs
      (Fin.castAdd n i)) Deltaf
    (fun j : Fin n => higham20Eq20_16ComputedResidual fp A z rhs
      (Fin.natAdd m j)) Deltag rhat x hsys p
  rw [higham20Eq20_16_append_split
    (higham20Eq20_16ComputedResidual fp A z rhs)] at hdef
  exact hdef

/-! ## Concrete Theorem 20.4 correction solve -/

noncomputable def higham20Eq20_4Q {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ) :
    Fin (n + k) → Fin (n + k) → ℝ :=
  fl_householderQRPanel_Q fp (n + k) n A

noncomputable def higham20Eq20_4R {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => fl_householderQRPanel_R fp (n + k) n A (Fin.castAdd k i) j

noncomputable def higham20Eq20_4TransformedRhs {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ) (f : Fin (n + k) → ℝ) :
    Fin (n + k) → ℝ :=
  fl_householderQRPanel_rhs fp (n + k) n A f

noncomputable def higham20Eq20_4ForwardBlock {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ) (g : Fin n → ℝ) :
    Fin n → ℝ :=
  fl_forwardSub fp n (matTranspose (higham20Eq20_4R fp A)) g

/-- The actual solution block returned by the Householder-QR augmented solve
of Theorem 20.4. -/
noncomputable def higham20Eq20_4CorrectionSolution {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ)
    (f : Fin (n + k) → ℝ) (g : Fin n → ℝ) : Fin n → ℝ :=
  fl_backSub fp n (higham20Eq20_4R fp A)
    (fun i : Fin n =>
      higham20Eq20_4TransformedRhs fp A f (Fin.castAdd k i) -
        higham20Eq20_4ForwardBlock fp A g i)

/-- The actual residual block returned by the Householder-QR augmented solve
of Theorem 20.4. -/
noncomputable def higham20Eq20_4CorrectionResidual {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ)
    (f : Fin (n + k) → ℝ) (g : Fin n → ℝ) : Fin (n + k) → ℝ :=
  matMulVec (n + k) (higham20Eq20_4Q fp A)
    (Fin.append (higham20Eq20_4ForwardBlock fp A g)
      (fun i : Fin k =>
        higham20Eq20_4TransformedRhs fp A f (Fin.natAdd n i)))

/-- All small perturbations supplied by the concrete source-facing Theorem
20.4 QR solve.  Keeping the normalized weight matrices and triangular-solve
perturbations in the certificate makes the solver term in (20.16) auditable;
it is not an unconstrained residual-defect hypothesis. -/
structure Higham20Eq20_4CorrectionCertificate {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ)
    (f : Fin (n + k) → ℝ) (g : Fin n → ℝ) where
  DeltaA : Fin (n + k) → Fin n → ℝ
  G : Fin (n + k) → Fin (n + k) → ℝ
  Deltaf : Fin (n + k) → ℝ
  Deltag : Fin n → ℝ
  H1 : Fin (n + k) → Fin (n + k) → ℝ
  H2 : Fin (n + k) → Fin (n + k) → ℝ
  H3 : Fin (n + k) → Fin (n + k) → ℝ
  DeltaR1 : Fin n → Fin n → ℝ
  DeltaR2 : Fin n → Fin n → ℝ
  deltaA_frob : frobNorm DeltaA ≤
    lsTheorem20_4ConcreteGammaTildeSqrtResidual fp (n + k) n * frobNorm A
  G_nonneg : ∀ i j, 0 ≤ G i j
  G_frob : frobNorm G = 1
  deltaA_componentwise : ∀ i j, |DeltaA i j| ≤
    (((n + k : ℕ) : ℝ) * (n : ℝ) *
      lsTheorem20_4ConcreteGammaTildeSqrtResidual fp (n + k) n) *
        matMulRect (n + k) (n + k) n G (fun a b => |A a b|) i j
  deltaf_componentwise : ∀ i, |Deltaf i| ≤
    (Real.sqrt ((n + k : ℕ) : ℝ) * (n : ℝ) *
      lsTheorem20_4ConcreteGammaTildeSqrtResidual fp (n + k) n) *
        lsTheorem20_4DeltafMajorant H1 H2 f
          (higham20Eq20_4CorrectionResidual fp A f g) i
  deltag_componentwise : ∀ j, |Deltag j| ≤
    (Real.sqrt ((n + k : ℕ) : ℝ) * (n : ℝ) *
      lsTheorem20_4ConcreteGammaTildeSqrtResidual fp (n + k) n) *
        lsTheorem20_4DeltagMajorant A H3
          (higham20Eq20_4CorrectionResidual fp A f g) j
  H1_nonneg : ∀ i j, 0 ≤ H1 i j
  H2_nonneg : ∀ i j, 0 ≤ H2 i j
  H3_nonneg : ∀ i j, 0 ≤ H3 i j
  H1_frob : frobNorm H1 = 1
  H2_frob : frobNorm H2 = 1
  H3_frob : frobNorm H3 = 1
  deltaR1_componentwise : ∀ i j,
    |DeltaR1 i j| ≤ gamma fp n * |higham20Eq20_4R fp A i j|
  deltaR2_componentwise : ∀ i j,
    |DeltaR2 i j| ≤ gamma fp n * |higham20Eq20_4R fp A i j|
  system : LSAsymmetricAugmentedSystem
    (fun i j => A i j + DeltaA i j +
      matMulRectLeft (higham20Eq20_4Q fp A) (lsQRTallBlock DeltaR1) i j)
    (fun i j => A i j + DeltaA i j +
      matMulRectLeft (higham20Eq20_4Q fp A) (lsQRTallBlock DeltaR2) i j)
    (fun i => f i + Deltaf i) (fun j => g j + Deltag j)
    (higham20Eq20_4CorrectionResidual fp A f g)
    (higham20Eq20_4CorrectionSolution fp A f g)

/-- The source-facing Theorem 20.4 endpoint repackaged as a correction-solve
certificate for equation (20.16). -/
theorem Higham20Eq20_4CorrectionCertificate.exists_of_source_domain
    {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ)
    (f : Fin (n + k) → ℝ) (g : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex (n + k)))
    (hdomain : lsTheorem20_4FullRankComputedQRDomain fp A) :
    Nonempty (Higham20Eq20_4CorrectionCertificate fp A f g) := by
  rcases
      LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_householderQRPanel_theorem20_4_source_fullRank_computed_nonbreakdown
        fp A f g hn hvalid hdomain with
    ⟨DeltaA, G, Deltaf, Deltag, H1, H2, H3, DeltaR1, DeltaR2,
      hDeltaA, hGnonneg, hGfrob, hDeltaAcomp, hDeltaf, hDeltag,
      hH1nonneg, hH2nonneg, hH3nonneg, hH1frob, hH2frob, hH3frob,
      hDeltaR1, hDeltaR2, hsys⟩
  refine ⟨⟨DeltaA, G, Deltaf, Deltag, H1, H2, H3, DeltaR1, DeltaR2,
    ?_, hGnonneg, hGfrob, ?_, ?_, ?_, hH1nonneg, hH2nonneg, hH3nonneg,
    hH1frob, hH2frob, hH3frob, ?_, ?_, ?_⟩⟩
  · simpa [higham20Eq20_4Q, higham20Eq20_4R,
      higham20Eq20_4TransformedRhs, higham20Eq20_4ForwardBlock,
      higham20Eq20_4CorrectionSolution, higham20Eq20_4CorrectionResidual] using
      hDeltaA
  · simpa [higham20Eq20_4Q, higham20Eq20_4R,
      higham20Eq20_4TransformedRhs, higham20Eq20_4ForwardBlock,
      higham20Eq20_4CorrectionSolution, higham20Eq20_4CorrectionResidual] using
      hDeltaAcomp
  · simpa [higham20Eq20_4Q, higham20Eq20_4R,
      higham20Eq20_4TransformedRhs, higham20Eq20_4ForwardBlock,
      higham20Eq20_4CorrectionSolution, higham20Eq20_4CorrectionResidual] using
      hDeltaf
  · simpa [higham20Eq20_4Q, higham20Eq20_4R,
      higham20Eq20_4TransformedRhs, higham20Eq20_4ForwardBlock,
      higham20Eq20_4CorrectionSolution, higham20Eq20_4CorrectionResidual] using
      hDeltag
  · simpa [higham20Eq20_4R] using hDeltaR1
  · simpa [higham20Eq20_4R] using hDeltaR2
  · simpa [higham20Eq20_4Q, higham20Eq20_4R,
      higham20Eq20_4TransformedRhs, higham20Eq20_4ForwardBlock,
      higham20Eq20_4CorrectionSolution, higham20Eq20_4CorrectionResidual] using
      hsys

noncomputable def higham20Eq20_16TopComputedResidual {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ)
    (z rhs : Fin ((n + k) + n) → ℝ) : Fin (n + k) → ℝ :=
  fun i => higham20Eq20_16ComputedResidual fp A z rhs (Fin.castAdd n i)

noncomputable def higham20Eq20_16BottomComputedResidual {n k : ℕ}
    (fp : FPModel) (A : Fin (n + k) → Fin n → ℝ)
    (z rhs : Fin ((n + k) + n) → ℝ) : Fin n → ℝ :=
  fun j => higham20Eq20_16ComputedResidual fp A z rhs (Fin.natAdd (n + k) j)

noncomputable def higham20Eq20_16QRCorrection {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ)
    (z rhs : Fin ((n + k) + n) → ℝ) : Fin ((n + k) + n) → ℝ :=
  Fin.append
    (higham20Eq20_4CorrectionResidual fp A
      (higham20Eq20_16TopComputedResidual fp A z rhs)
      (higham20Eq20_16BottomComputedResidual fp A z rhs))
    (higham20Eq20_4CorrectionSolution fp A
      (higham20Eq20_16TopComputedResidual fp A z rhs)
      (higham20Eq20_16BottomComputedResidual fp A z rhs))

/-- Fully concrete finite form of equation (20.16).

The correction right-hand side is formed by the actual conventional residual
kernel, its two blocks are solved by the actual Householder-QR forward- and back-
substitution path of Theorem 20.4, and the correction is applied by the actual
rounded addition kernel.  The existential certificate contains only the
implementation-derived perturbations together with their explicit normalized
gamma bounds; the displayed post-refinement inequality has no primitive
residual, update, or solver-defect premise. -/
theorem higham20_eq20_16_actual_householderQR_one_refinement_finite
    {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ)
    (z rhs : Fin ((n + k) + n) → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex (n + k)))
    (hdomain : lsTheorem20_4FullRankComputedQRDomain fp A)
    (hdim : gammaValid fp ((n + k) + n + 1)) :
    ∃ cert : Higham20Eq20_4CorrectionCertificate fp A
        (higham20Eq20_16TopComputedResidual fp A z rhs)
        (higham20Eq20_16BottomComputedResidual fp A z rhs),
      ∀ p : Fin ((n + k) + n),
        |rhs p - ∑ q : Fin ((n + k) + n),
            higham20Eq20_16Matrix A p q *
              higham20Eq20_16RoundedUpdate fp z
                (higham20Eq20_16QRCorrection fp A z rhs) q| ≤
          higham20Eq20_4CorrectionMajorant
            (fun i j => cert.DeltaA i j +
              matMulRectLeft (higham20Eq20_4Q fp A)
                (lsQRTallBlock cert.DeltaR1) i j)
            (fun i j => cert.DeltaA i j +
              matMulRectLeft (higham20Eq20_4Q fp A)
                (lsQRTallBlock cert.DeltaR2) i j)
            cert.Deltaf cert.Deltag
            (higham20Eq20_4CorrectionResidual fp A
              (higham20Eq20_16TopComputedResidual fp A z rhs)
              (higham20Eq20_16BottomComputedResidual fp A z rhs))
            (higham20Eq20_4CorrectionSolution fp A
              (higham20Eq20_16TopComputedResidual fp A z rhs)
              (higham20Eq20_16BottomComputedResidual fp A z rhs)) p +
          gamma fp ((n + k) + n + 1) *
            (|rhs p| + ∑ q : Fin ((n + k) + n),
              |higham20Eq20_16Matrix A p q| * |z q|) +
          fp.u * ∑ q : Fin ((n + k) + n),
            |higham20Eq20_16Matrix A p q| *
              (|z q| + |higham20Eq20_16QRCorrection fp A z rhs q|) := by
  rcases Higham20Eq20_4CorrectionCertificate.exists_of_source_domain
      fp A (higham20Eq20_16TopComputedResidual fp A z rhs)
        (higham20Eq20_16BottomComputedResidual fp A z rhs)
      hn hvalid hdomain with ⟨cert⟩
  refine ⟨cert, ?_⟩
  have hsys : LSAsymmetricAugmentedSystem
      (fun i j => A i j +
        (cert.DeltaA i j + matMulRectLeft (higham20Eq20_4Q fp A)
          (lsQRTallBlock cert.DeltaR1) i j))
      (fun i j => A i j +
        (cert.DeltaA i j + matMulRectLeft (higham20Eq20_4Q fp A)
          (lsQRTallBlock cert.DeltaR2) i j))
      (fun i => higham20Eq20_16TopComputedResidual fp A z rhs i +
        cert.Deltaf i)
      (fun j => higham20Eq20_16BottomComputedResidual fp A z rhs j +
        cert.Deltag j)
      (higham20Eq20_4CorrectionResidual fp A
        (higham20Eq20_16TopComputedResidual fp A z rhs)
        (higham20Eq20_16BottomComputedResidual fp A z rhs))
      (higham20Eq20_4CorrectionSolution fp A
        (higham20Eq20_16TopComputedResidual fp A z rhs)
        (higham20Eq20_16BottomComputedResidual fp A z rhs)) := by
    simpa only [add_assoc] using cert.system
  simpa only [higham20Eq20_16TopComputedResidual,
      higham20Eq20_16BottomComputedResidual,
      higham20Eq20_16QRCorrection] using
    higham20_eq20_16_of_asymmetric_perturbed_correction
      fp (n + k) n A z rhs
      (fun i j => cert.DeltaA i j +
        matMulRectLeft (higham20Eq20_4Q fp A)
          (lsQRTallBlock cert.DeltaR1) i j)
      (fun i j => cert.DeltaA i j +
        matMulRectLeft (higham20Eq20_4Q fp A)
          (lsQRTallBlock cert.DeltaR2) i j)
      cert.Deltaf cert.Deltag
      (higham20Eq20_4CorrectionResidual fp A
        (higham20Eq20_16TopComputedResidual fp A z rhs)
        (higham20Eq20_16BottomComputedResidual fp A z rhs))
      (higham20Eq20_4CorrectionSolution fp A
        (higham20Eq20_16TopComputedResidual fp A z rhs)
        (higham20Eq20_16BottomComputedResidual fp A z rhs))
      hdim hsys

end NumStability
