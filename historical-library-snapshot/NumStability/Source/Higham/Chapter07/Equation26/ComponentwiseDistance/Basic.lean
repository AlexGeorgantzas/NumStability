import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem10Bauer.Part02
import NumStability.Source.Higham.Chapter09.DoolittleClosure
import NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivot

/-!
# Chapter07 Equation26 ComponentwiseDistance Basic

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapters1To9SourceClosure` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators
open scoped Topology
open scoped Matrix.Norms.Operator

namespace NumStability

/-- The nonnegative matrix `|A⁻¹|E` controlling componentwise distance to
singularity in equation (7.26). -/
noncomputable def higham7_26_distanceMajorant
    (n : ℕ) (Ainv E : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n (absMatrix n Ainv) E

/-- Real value of the complexified algebraic spectral radius used in (7.26). -/
noncomputable def higham7_26_spectralRadius
    {n : ℕ} (M : Fin n → Fin n → ℝ) : ℝ :=
  (spectralRadius ℂ
    (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix M)).toReal

/-- A feasible componentwise singularity radius.  The nonzero right-kernel
vector is equivalent to singularity but is retained explicitly because it is
the useful source witness for both halves of (7.26). -/
def Higham7_26FeasibleSingularRadius
    {n : ℕ} (A E : Fin n → Fin n → ℝ) (ε : ℝ) : Prop :=
  0 ≤ ε ∧
    ∃ ΔA : Fin n → Fin n → ℝ, ∃ x : Fin n → ℝ,
      x ≠ 0 ∧
        (∀ i j : Fin n, |ΔA i j| ≤ ε * E i j) ∧
        matMulVec n (fun i j => A i j + ΔA i j) x = 0

/-- `d` is the componentwise distance `d_E(A)` when it is the least feasible
singularity radius.  This mirrors the source's `min` definition. -/
def IsHigham7_26ComponentwiseDistance
    {n : ℕ} (A E : Fin n → Fin n → ℝ) (d : ℝ) : Prop :=
  IsLeast { ε : ℝ | Higham7_26FeasibleSingularRadius A E ε } d

lemma higham7_26_distanceMajorant_nonneg
    (n : ℕ) (Ainv E : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j) :
    ∀ i j : Fin n, 0 ≤ higham7_26_distanceMajorant n Ainv E i j :=
  ch7_matMul_nonneg n (absMatrix n Ainv) E
    (by intro i j; exact abs_nonneg _) hE

/-- The algebraic spectral radius used in (7.26) is finite. -/
lemma higham7_26_spectralRadius_ne_top
    {n : ℕ} (hn : 0 < n) (M : Fin n → Fin n → ℝ) :
    spectralRadius ℂ
        (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix M) ≠ ⊤ := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let C : Matrix (Fin n) (Fin n) ℂ := realRectToCMatrix M
  letI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) :=
    FiniteDimensional.complete ℂ _
  have hcomplete : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstance
  have hbound :=
    @spectrum.spectralRadius_le_nnnorm ℂ
      (Matrix (Fin n) (Fin n) ℂ) inferInstance inferInstance inferInstance
      hcomplete inferInstance C
  change spectralRadius ℂ C ≠ ⊤
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top hbound

/-- Every actual singular perturbation obeys the reciprocal-spectral-radius
lower bound in (7.26). -/
theorem higham7_26_feasibleRadius_ge_reciprocal_spectralRadius
    {n : ℕ} (hn : 0 < n)
    (A Ainv E : Fin n → Fin n → ℝ) (ε : ℝ)
    (hInv : IsInverse n A Ainv)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hε : Higham7_26FeasibleSingularRadius A E ε) :
    1 / higham7_26_spectralRadius
          (higham7_26_distanceMajorant n Ainv E) ≤ ε := by
  rcases hε with ⟨hεnonneg, ΔA, x, hxne, hΔ, hker⟩
  let M : Fin n → Fin n → ℝ :=
    higham7_26_distanceMajorant n Ainv E
  let v : Fin n → ℝ := fun i => |x i|
  have hAx : ∀ i : Fin n,
      matMulVec n A x i = -matMulVec n ΔA x i := by
    intro i
    have hi := congrFun hker i
    have hadd : matMulVec n (fun i j => A i j + ΔA i j) x i =
        matMulVec n A x i + matMulVec n ΔA x i := by
      unfold matMulVec
      simp [add_mul, Finset.sum_add_distrib]
    rw [hadd] at hi
    simpa using eq_neg_of_add_eq_zero_left hi
  have hleft : matMulVec n Ainv (matMulVec n A x) = x := by
    simpa [matMulVec, rectMatMulVec] using
      rectMatMulVec_left_inverse_of_IsLeftInverse hInv.1 x
  have hxrepr : ∀ i : Fin n,
      x i = -matMulVec n Ainv (matMulVec n ΔA x) i := by
    intro i
    calc
      x i = matMulVec n Ainv (matMulVec n A x) i :=
        congrFun hleft.symm i
      _ = matMulVec n Ainv (fun k => -matMulVec n ΔA x k) i := by
        congr 1
        funext k
        exact hAx k
      _ = -matMulVec n Ainv (matMulVec n ΔA x) i := by
        unfold matMulVec
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hΔx : ∀ k : Fin n,
      |matMulVec n ΔA x k| ≤
        ε * ∑ j : Fin n, E k j * |x j| := by
    intro k
    calc
      |matMulVec n ΔA x k| ≤ ∑ j : Fin n, |ΔA k j| * |x j| :=
        abs_matMulVec_le n ΔA x k
      _ ≤ ∑ j : Fin n, (ε * E k j) * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hΔ k j) (abs_nonneg _)
      _ = ε * ∑ j : Fin n, E k j * |x j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hsub : ∀ i : Fin n,
      v i ≤ ε * matMulVec n M v i := by
    intro i
    calc
      v i = |matMulVec n Ainv (matMulVec n ΔA x) i| := by
        dsimp [v]
        rw [hxrepr i, abs_neg]
      _ ≤ ∑ k : Fin n, |Ainv i k| * |matMulVec n ΔA x k| :=
        abs_matMulVec_le n Ainv (matMulVec n ΔA x) i
      _ ≤ ∑ k : Fin n,
          |Ainv i k| * (ε * ∑ j : Fin n, E k j * |x j|) := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hΔx k) (abs_nonneg _)
      _ = ε * matMulVec n (absMatrix n Ainv) (matMulVec n E v) i := by
        simp only [matMulVec]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        dsimp [v, absMatrix]
        ring
      _ = ε * matMulVec n M v i := by
        rw [← matMulVec_matMul n (absMatrix n Ainv) E v i]
        rfl
  have hvne : v ≠ 0 := by
    intro hv
    apply hxne
    funext i
    have hi := congrFun hv i
    dsimp [v] at hi
    exact abs_eq_zero.mp hi
  have hεpos : 0 < ε := by
    apply lt_of_le_of_ne hεnonneg
    intro hzero
    have hεzero : ε = 0 := hzero.symm
    apply hvne
    funext i
    have hi := hsub i
    rw [hεzero, zero_mul] at hi
    exact le_antisymm hi (abs_nonneg _)
  have hscaled : ∀ i : Fin n,
      (1 / ε) * v i ≤ matMulVec n M v i := by
    intro i
    rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ hεpos).2
    simpa [mul_comm] using hsub i
  have hspectral :
      ENNReal.ofReal (1 / ε) ≤
        spectralRadius ℂ
          (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix M) :=
    ch7_matrix_spectralRadius_ge_of_nonzero_nonneg_right_subeigenvector
      hn M (1 / ε) v
      (by simpa [M] using higham7_26_distanceMajorant_nonneg n Ainv E hE)
      (one_div_nonneg.mpr hεnonneg)
      (by intro i; exact abs_nonneg _) hvne hscaled
  have hspectralReal :
      1 / ε ≤ higham7_26_spectralRadius M := by
    have h := (ENNReal.toReal_le_toReal
      (by simp) (higham7_26_spectralRadius_ne_top hn M)).2 hspectral
    change 1 / ε ≤
      (spectralRadius ℂ
        (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix M)).toReal
    rw [← ENNReal.toReal_ofReal (one_div_nonneg.mpr hεnonneg)]
    exact h
  have hρpos : 0 < higham7_26_spectralRadius M :=
    lt_of_lt_of_le (one_div_pos.mpr hεpos) hspectralReal
  change 1 / higham7_26_spectralRadius M ≤ ε
  apply (div_le_iff₀ hρpos).2
  calc
    1 = ε * (1 / ε) := by field_simp
    _ ≤ ε * higham7_26_spectralRadius M :=
      mul_le_mul_of_nonneg_left hspectralReal (le_of_lt hεpos)
    _ = ε * higham7_26_spectralRadius M := rfl

/-- Lower-bound half of source equation (7.26) for the actual minimum
componentwise singularity radius. -/
theorem higham7_26_componentwiseDistance_ge_reciprocal_spectralRadius
    {n : ℕ} (hn : 0 < n)
    (A Ainv E : Fin n → Fin n → ℝ) (d : ℝ)
    (hInv : IsInverse n A Ainv)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hd : IsHigham7_26ComponentwiseDistance A E d) :
    1 / higham7_26_spectralRadius
          (higham7_26_distanceMajorant n Ainv E) ≤ d :=
  higham7_26_feasibleRadius_ge_reciprocal_spectralRadius
    hn A Ainv E d hInv hE hd.1

/-- The universal factor in Rump's upper estimate in equation (7.26). -/
noncomputable def higham7_26_rumpFactor (n : ℕ) : ℝ :=
  (3 + 2 * Real.sqrt 2) * (n : ℝ)

/-- The linear-algebra output of the hard Rump cycle/sign-real-spectral-radius
argument behind the upper half of (7.26).  Unlike a singular-perturbation or
distance-bound premise, this exposes the signed perturbation matrix and its
ordinary real eigenpair.  Rump's Theorems 3.2 and 4.4 construct precisely this
certificate (after absorbing the row signature into a column signature). -/
structure Higham7_26RumpEigenpairCertificate
    {n : ℕ} (Ainv E : Fin n → Fin n → ℝ) where
  F : Fin n → Fin n → ℝ
  x : Fin n → ℝ
  lam : ℝ
  x_ne : x ≠ 0
  lam_pos : 0 < lam
  F_bound : ∀ i j : Fin n, |F i j| ≤ E i j
  eigenpair :
    matMulVec n Ainv (matMulVec n F x) = fun i => lam * x i
  spectral_fraction_le_lam :
    higham7_26_spectralRadius
        (higham7_26_distanceMajorant n Ainv E) /
          higham7_26_rumpFactor n ≤ lam

/-- A Rump signed-eigenpair certificate produces an actual singular
componentwise perturbation of radius `1 / λ`. -/
theorem higham7_26_feasibleRadius_of_rumpEigenpairCertificate
    {n : ℕ} (A Ainv E : Fin n → Fin n → ℝ)
    (hInv : IsInverse n A Ainv)
    (c : Higham7_26RumpEigenpairCertificate Ainv E) :
    Higham7_26FeasibleSingularRadius A E (1 / c.lam) := by
  let ΔA : Fin n → Fin n → ℝ := fun i j => -(1 / c.lam) * c.F i j
  refine ⟨one_div_nonneg.mpr (le_of_lt c.lam_pos), ΔA, c.x, c.x_ne, ?_, ?_⟩
  · intro i j
    dsimp [ΔA]
    calc
      |-(1 / c.lam) * c.F i j| = (1 / c.lam) * |c.F i j| := by
        rw [abs_mul, abs_neg, abs_of_nonneg
          (one_div_nonneg.mpr (le_of_lt c.lam_pos))]
      _ ≤ (1 / c.lam) * E i j :=
        mul_le_mul_of_nonneg_left (c.F_bound i j)
          (one_div_nonneg.mpr (le_of_lt c.lam_pos))
  · have hright : ∀ y : Fin n → ℝ,
        matMulVec n A (matMulVec n Ainv y) = y := by
      intro y
      simpa [matMulVec, rectMatMulVec] using
        rectMatMulVec_left_inverse_of_IsLeftInverse
          (show IsLeftInverse n Ainv A from hInv.2) y
    have hFx : ∀ i : Fin n,
        matMulVec n c.F c.x i = c.lam * matMulVec n A c.x i := by
      intro i
      calc
        matMulVec n c.F c.x i =
            matMulVec n A (matMulVec n Ainv (matMulVec n c.F c.x)) i :=
          congrFun (hright (matMulVec n c.F c.x)).symm i
        _ = matMulVec n A (fun j => c.lam * c.x j) i := by
          rw [c.eigenpair]
        _ = c.lam * matMulVec n A c.x i := by
          unfold matMulVec
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    funext i
    calc
      matMulVec n (fun i j => A i j + ΔA i j) c.x i =
          matMulVec n A c.x i + matMulVec n ΔA c.x i := by
        unfold matMulVec
        simp [add_mul, Finset.sum_add_distrib]
      _ = matMulVec n A c.x i +
          (-(1 / c.lam) * matMulVec n c.F c.x i) := by
        congr 1
        unfold matMulVec
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [ΔA]
        ring
      _ = 0 := by
        rw [hFx i]
        field_simp [ne_of_gt c.lam_pos]
        ring

/-- Upper half of source equation (7.26), reduced to Rump's genuine signed
eigenpair output rather than to a target-equivalent distance premise. -/
theorem higham7_26_componentwiseDistance_le_rumpBound_of_eigenpairCertificate
    {n : ℕ} (hn : 0 < n)
    (A Ainv E : Fin n → Fin n → ℝ) (d : ℝ)
    (hInv : IsInverse n A Ainv)
    (hd : IsHigham7_26ComponentwiseDistance A E d)
    (hρ : 0 < higham7_26_spectralRadius
      (higham7_26_distanceMajorant n Ainv E))
    (c : Higham7_26RumpEigenpairCertificate Ainv E) :
    d ≤ higham7_26_rumpFactor n /
      higham7_26_spectralRadius
        (higham7_26_distanceMajorant n Ainv E) := by
  have hK : 0 < higham7_26_rumpFactor n := by
    dsimp [higham7_26_rumpFactor]
    positivity
  have hfeasible :=
    higham7_26_feasibleRadius_of_rumpEigenpairCertificate A Ainv E hInv c
  have hdle : d ≤ 1 / c.lam := hd.2 hfeasible
  refine hdle.trans ?_
  apply (div_le_div_iff₀ c.lam_pos hρ).2
  have hscaled := (div_le_iff₀ hK).1 c.spectral_fraction_le_lam
  nlinarith

/-- Source-shaped two-sided equation (7.26) once Rump's cycle theorem has
supplied its signed eigenpair certificate. -/
theorem higham7_26_source_distance_sandwich_of_rumpEigenpairCertificate
    {n : ℕ} (hn : 0 < n)
    (A Ainv E : Fin n → Fin n → ℝ) (d : ℝ)
    (hInv : IsInverse n A Ainv)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hd : IsHigham7_26ComponentwiseDistance A E d)
    (hρ : 0 < higham7_26_spectralRadius
      (higham7_26_distanceMajorant n Ainv E))
    (c : Higham7_26RumpEigenpairCertificate Ainv E) :
    1 / higham7_26_spectralRadius
          (higham7_26_distanceMajorant n Ainv E) ≤ d ∧
      d ≤ higham7_26_rumpFactor n /
        higham7_26_spectralRadius
          (higham7_26_distanceMajorant n Ainv E) :=
  ⟨higham7_26_componentwiseDistance_ge_reciprocal_spectralRadius
      hn A Ainv E d hInv hE hd,
    higham7_26_componentwiseDistance_le_rumpBound_of_eigenpairCertificate
      hn A Ainv E d hInv hd hρ c⟩

end NumStability
