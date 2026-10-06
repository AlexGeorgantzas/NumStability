-- Algorithms/LinearSystems/QR/HouseholderApply.lean
--
-- Concrete rounded application of a Householder reflector to a vector.
--
-- The operation modeled here is y = b - beta * v * (v^T b), implemented with
-- the local rounded dot-product, multiplication, and subtraction operations.
-- The full Lemma 18.2 backward-error bridge to `HouseholderAppError` is a later
-- theorem; this file supplies the concrete kernel and unroll lemma.

import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LinearSystems.QR.HouseholderSpec

/-!
# HouseholderApply

Canonical source-neutral Householder API.  The historical QR path remains an import-only wrapper.
-/


namespace NumStability

open scoped BigOperators

-- ============================================================
-- §18.3  Concrete Householder application kernel
-- ============================================================

/-- Exact application identity for `P = I - beta * v * v^T`.

    This is the exact algebraic target for the rounded kernel below. -/
theorem householder_matMulVec_eq (n : ℕ) (v : Fin n → ℝ) (beta : ℝ)
    (b : Fin n → ℝ) :
    matMulVec n (householder n v beta) b =
      fun i => b i - beta * v i * (∑ j : Fin n, v j * b j) := by
  ext i
  unfold matMulVec householder idMatrix
  have hid : ∑ j : Fin n, (if i = j then 1 else 0) * b j = b i := by
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  have houter :
      ∑ j : Fin n, beta * v i * v j * b j =
        beta * v i * (∑ j : Fin n, v j * b j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  trans
    (∑ j : Fin n, (if i = j then 1 else 0) * b j) -
      ∑ j : Fin n, beta * v i * v j * b j
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [hid, houter]

/-- Rounded application of `I - beta * v * v^T` to vector `b`.

    Operation order:
    1. `t = fl_dotProduct v b`;
    2. `w = fl_mul beta t`;
    3. `y_i = fl_sub b_i (fl_mul w v_i)`.

    This is the concrete algorithmic object needed before proving the
    `HouseholderAppError` contract from Higham Lemma 18.2.  That bridge also
    needs the source hypothesis that the computed Householder vector satisfies
    Higham's equation (18.3), so it is intentionally not claimed in this file
    yet. -/
noncomputable def fl_householderApply (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (beta : ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  let t := fl_dotProduct fp n v b
  let w := fp.fl_mul beta t
  fun i => fp.fl_sub (b i) (fp.fl_mul w (v i))

/-- Matrix represented by the primitive rounding errors in one rounded
    Householder application.

    This is not an arbitrary post-hoc perturbation.  Each entry is determined
    by the same dot-product, scalar-multiplication, componentwise
    multiplication, and subtraction error variables that occur in
    `fl_householderApply_unroll`. -/
noncomputable def householderApplyRoundedMatrix (n : ℕ)
    (v : Fin n → ℝ) (beta : ℝ)
    (η : Fin n → ℝ) (δw : ℝ)
    (δmul δsub : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    idMatrix n i j * (1 + δsub i) -
      (beta * (1 + δw)) * v i * (1 + δmul i) *
        v j * (1 + η j) * (1 + δsub i)

/-- Concrete perturbation matrix represented by the primitive rounding errors
    in one Householder application, relative to an exact target matrix `P`.

    The next Higham Lemma 18.2 step is precisely to bound this matrix in
    Frobenius norm when `P = I - v vᵀ`, the input vector satisfies
    `HouseholderVectorError`, and the displayed rounding variables satisfy the
    primitive `FPModel` bounds. -/
noncomputable def householderApplyDeltaMatrix (n : ℕ)
    (P : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (beta : ℝ)
    (η : Fin n → ℝ) (δw : ℝ)
    (δmul δsub : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => householderApplyRoundedMatrix n v beta η δw δmul δsub i j - P i j

/-- Unroll the concrete Householder-vector application into primitive rounding
    errors from the dot product, one scalar multiplication, one per-component
    multiplication, and one per-component subtraction. -/
theorem fl_householderApply_unroll (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (beta : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∃ (η : Fin n → ℝ) (δw : ℝ) (δmul δsub : Fin n → ℝ),
      (∀ j : Fin n, |η j| ≤ gamma fp n) ∧
      |δw| ≤ fp.u ∧
      (∀ i : Fin n, |δmul i| ≤ fp.u) ∧
      (∀ i : Fin n, |δsub i| ≤ fp.u) ∧
      ∀ i : Fin n,
        fl_householderApply fp n v beta b i =
          (b i -
            (((beta * (∑ j : Fin n, v j * b j * (1 + η j))) * (1 + δw)) *
              v i * (1 + δmul i))) *
            (1 + δsub i) := by
  let t := fl_dotProduct fp n v b
  let w := fp.fl_mul beta t
  obtain ⟨η, hη, hdot⟩ := dotProduct_backward_error fp n v b hn
  obtain ⟨δw, hδw, hw⟩ := fp.model_mul beta t
  have hmul : ∀ i : Fin n, ∃ δ : ℝ,
      |δ| ≤ fp.u ∧ fp.fl_mul w (v i) = (w * v i) * (1 + δ) := by
    intro i
    exact fp.model_mul w (v i)
  let δmul : Fin n → ℝ := fun i => Classical.choose (hmul i)
  have hδmul : ∀ i : Fin n, |δmul i| ≤ fp.u := fun i =>
    (Classical.choose_spec (hmul i)).1
  have hmul_eq : ∀ i : Fin n,
      fp.fl_mul w (v i) = (w * v i) * (1 + δmul i) := fun i =>
    (Classical.choose_spec (hmul i)).2
  have hsub : ∀ i : Fin n, ∃ δ : ℝ,
      |δ| ≤ fp.u ∧
        fp.fl_sub (b i) (fp.fl_mul w (v i)) =
          (b i - fp.fl_mul w (v i)) * (1 + δ) := by
    intro i
    exact fp.model_sub (b i) (fp.fl_mul w (v i))
  let δsub : Fin n → ℝ := fun i => Classical.choose (hsub i)
  have hδsub : ∀ i : Fin n, |δsub i| ≤ fp.u := fun i =>
    (Classical.choose_spec (hsub i)).1
  have hsub_eq : ∀ i : Fin n,
      fp.fl_sub (b i) (fp.fl_mul w (v i)) =
        (b i - fp.fl_mul w (v i)) * (1 + δsub i) := fun i =>
    (Classical.choose_spec (hsub i)).2
  refine ⟨η, δw, δmul, δsub, hη, hδw, hδmul, hδsub, ?_⟩
  intro i
  have happ :
      fl_householderApply fp n v beta b i =
        fp.fl_sub (b i) (fp.fl_mul w (v i)) := by
    rfl
  rw [happ, hsub_eq i, hmul_eq i]
  rw [show w = beta * t * (1 + δw) from hw,
      show t = ∑ j : Fin n, v j * b j * (1 + η j) from hdot]

/-- Matrix-form unroll for the concrete rounded Householder application.

    The rounded output is exactly the product of `b` by the matrix
    `householderApplyRoundedMatrix` built from the primitive rounding errors.
    This is the algebraic bridge needed before proving the Lemma 18.2
    Frobenius-norm perturbation bound. -/
theorem fl_householderApply_matrix_unroll (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (beta : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∃ (η : Fin n → ℝ) (δw : ℝ) (δmul δsub : Fin n → ℝ),
      (∀ j : Fin n, |η j| ≤ gamma fp n) ∧
      |δw| ≤ fp.u ∧
      (∀ i : Fin n, |δmul i| ≤ fp.u) ∧
      (∀ i : Fin n, |δsub i| ≤ fp.u) ∧
      fl_householderApply fp n v beta b =
        matMulVec n
          (householderApplyRoundedMatrix n v beta η δw δmul δsub) b := by
  obtain ⟨η, δw, δmul, δsub, hη, hδw, hδmul, hδsub, hunroll⟩ :=
    fl_householderApply_unroll fp n v beta b hn
  refine ⟨η, δw, δmul, δsub, hη, hδw, hδmul, hδsub, ?_⟩
  ext i
  rw [hunroll i]
  unfold matMulVec householderApplyRoundedMatrix
  have hfirst :
      (∑ j : Fin n, idMatrix n i j * (1 + δsub i) * b j) =
        b i * (1 + δsub i) := by
    unfold idMatrix
    simp [Finset.sum_ite_eq, Finset.mem_univ]
    ring
  have hsecond :
      (∑ j : Fin n,
          ((beta * (1 + δw)) * v i * (1 + δmul i) *
            v j * (1 + η j) * (1 + δsub i)) * b j) =
        (((beta * (∑ j : Fin n, v j * b j * (1 + η j))) *
          (1 + δw)) * v i * (1 + δmul i)) * (1 + δsub i) := by
    calc
      (∑ j : Fin n,
          ((beta * (1 + δw)) * v i * (1 + δmul i) *
            v j * (1 + η j) * (1 + δsub i)) * b j)
          =
            (beta * (1 + δw) * v i * (1 + δmul i) * (1 + δsub i)) *
              (∑ j : Fin n, v j * b j * (1 + η j)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
      _ =
        (((beta * (∑ j : Fin n, v j * b j * (1 + η j))) *
          (1 + δw)) * v i * (1 + δmul i)) * (1 + δsub i) := by
            ring
  have hmatrix :
      (∑ j : Fin n,
          (idMatrix n i j * (1 + δsub i) -
            beta * (1 + δw) * v i * (1 + δmul i) *
              v j * (1 + η j) * (1 + δsub i)) * b j) =
        b i * (1 + δsub i) -
          (((beta * (∑ j : Fin n, v j * b j * (1 + η j))) *
            (1 + δw)) * v i * (1 + δmul i)) * (1 + δsub i) := by
    calc
      (∑ j : Fin n,
          (idMatrix n i j * (1 + δsub i) -
            beta * (1 + δw) * v i * (1 + δmul i) *
              v j * (1 + η j) * (1 + δsub i)) * b j)
          =
            (∑ j : Fin n, idMatrix n i j * (1 + δsub i) * b j) -
              (∑ j : Fin n,
                ((beta * (1 + δw)) * v i * (1 + δmul i) *
                  v j * (1 + η j) * (1 + δsub i)) * b j) := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro j _
                ring
      _ =
          b i * (1 + δsub i) -
            (((beta * (∑ j : Fin n, v j * b j * (1 + η j))) *
              (1 + δw)) * v i * (1 + δmul i)) * (1 + δsub i) := by
            rw [hfirst, hsecond]
  rw [hmatrix]
  ring

/-- Exact factorization of the concrete application perturbation matrix in
    Higham's normalized Householder form `P = I - v vᵀ`.

    This turns the additive vector perturbation model from equation (18.3) into
    relative factors and exposes the product of all vector, dot-product,
    multiplication, and subtraction errors.  The Frobenius bound for the
    normalized case is proved later in this file. -/
theorem householderApplyDeltaMatrix_normalized_factorization (n : ℕ)
    (v v_hat : Fin n → ℝ) (eps : ℝ)
    (η : Fin n → ℝ) (δw : ℝ) (δmul δsub : Fin n → ℝ)
    (hvec : HouseholderVectorError n v v_hat eps) (heps : 0 ≤ eps) :
    ∃ alpha : Fin n → ℝ,
      (∀ i : Fin n, |alpha i| ≤ eps) ∧
      ∀ i j : Fin n,
        householderApplyDeltaMatrix n (householder n v 1) v_hat 1
            η δw δmul δsub i j =
          idMatrix n i j * δsub i -
            v i * v j *
              (((1 + alpha i) * (1 + alpha j) * (1 + δw) *
                (1 + δmul i) * (1 + η j) * (1 + δsub i)) - 1) := by
  obtain ⟨alpha, hα, hvhat⟩ :=
    householderVectorError_relative_factors hvec heps
  refine ⟨alpha, hα, ?_⟩
  intro i j
  simp [householderApplyDeltaMatrix, householderApplyRoundedMatrix,
    householder, hvhat i, hvhat j]
  ring

/-- Product-gamma bridge for the error factors in one normalized Householder
    application.

    The factors are, in order: the two vector-construction perturbations, the
    scalar multiplication for `w`, the component multiplication, the dot-product
    perturbation, and the final subtraction perturbation. -/
theorem householderApply_error_factor_gamma (fp : FPModel) (a n : ℕ)
    (αi αj η δw δmul δsub : ℝ)
    (hαi : |αi| ≤ gamma fp a)
    (hαj : |αj| ≤ gamma fp a)
    (hη : |η| ≤ gamma fp n)
    (hδw : |δw| ≤ fp.u)
    (hδmul : |δmul| ≤ fp.u)
    (hδsub : |δsub| ≤ fp.u)
    (hvalid : gammaValid fp (2 * a + n + 3)) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp (2 * a + n + 3) ∧
      (1 + αi) * (1 + αj) * (1 + δw) * (1 + δmul) *
          (1 + η) * (1 + δsub) =
        1 + θ := by
  have hvalid_aa : gammaValid fp (a + a) :=
    gammaValid_mono fp (by omega) hvalid
  obtain ⟨θ1, hθ1, hprod1⟩ :=
    gamma_mul fp a a αi αj hαi hαj hvalid_aa
  have hδw_gamma : |δw| ≤ gamma fp 1 :=
    le_trans hδw (u_le_gamma fp (by norm_num)
      (gammaValid_mono fp (by omega) hvalid))
  have hδmul_gamma : |δmul| ≤ gamma fp 1 :=
    le_trans hδmul (u_le_gamma fp (by norm_num)
      (gammaValid_mono fp (by omega) hvalid))
  have hδsub_gamma : |δsub| ≤ gamma fp 1 :=
    le_trans hδsub (u_le_gamma fp (by norm_num)
      (gammaValid_mono fp (by omega) hvalid))
  have hvalid_2 : gammaValid fp ((a + a) + 1) :=
    gammaValid_mono fp (by omega) hvalid
  obtain ⟨θ2, hθ2, hprod2⟩ :=
    gamma_mul fp (a + a) 1 θ1 δw hθ1 hδw_gamma hvalid_2
  have hvalid_3 : gammaValid fp (((a + a) + 1) + 1) :=
    gammaValid_mono fp (by omega) hvalid
  obtain ⟨θ3, hθ3, hprod3⟩ :=
    gamma_mul fp ((a + a) + 1) 1 θ2 δmul hθ2 hδmul_gamma hvalid_3
  have hvalid_4 : gammaValid fp ((((a + a) + 1) + 1) + n) :=
    gammaValid_mono fp (by omega) hvalid
  obtain ⟨θ4, hθ4, hprod4⟩ :=
    gamma_mul fp (((a + a) + 1) + 1) n θ3 η hθ3 hη hvalid_4
  have hvalid_5 : gammaValid fp (((((a + a) + 1) + 1) + n) + 1) :=
    gammaValid_mono fp (by omega) hvalid
  obtain ⟨θ5, hθ5, hprod5⟩ :=
    gamma_mul fp ((((a + a) + 1) + 1) + n) 1 θ4 δsub
      hθ4 hδsub_gamma hvalid_5
  refine ⟨θ5, ?_, ?_⟩
  · simpa [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hθ5
  · calc
      (1 + αi) * (1 + αj) * (1 + δw) * (1 + δmul) *
          (1 + η) * (1 + δsub)
          =
            (((((1 + αi) * (1 + αj)) * (1 + δw)) *
              (1 + δmul)) * (1 + η)) * (1 + δsub) := by
                ring
      _ = ((((1 + θ1) * (1 + δw)) * (1 + δmul)) *
            (1 + η)) * (1 + δsub) := by rw [hprod1]
      _ = (((1 + θ2) * (1 + δmul)) * (1 + η)) *
            (1 + δsub) := by rw [hprod2]
      _ = ((1 + θ3) * (1 + η)) * (1 + δsub) := by rw [hprod3]
      _ = (1 + θ4) * (1 + δsub) := by rw [hprod4]
      _ = 1 + θ5 := hprod5

/-- Entrywise gamma form for the normalized Householder application delta.

    If the computed Householder vector satisfies equation (18.3) with
    `eps ≤ gamma fp a`, then every entry of the concrete perturbation matrix
    has the algebraic form
    `δ_ij δsub_i - v_i v_j θ_ij`, where `|θ_ij|` is bounded by the gamma count
    for the two vector factors, the dot product, and the three scalar rounded
    operations. -/
theorem householderApplyDeltaMatrix_normalized_entry_gamma
    (fp : FPModel) (a n : ℕ)
    (v v_hat : Fin n → ℝ) (eps : ℝ)
    (η : Fin n → ℝ) (δw : ℝ) (δmul δsub : Fin n → ℝ)
    (hvec : HouseholderVectorError n v v_hat eps)
    (heps_nonneg : 0 ≤ eps)
    (heps_bound : eps ≤ gamma fp a)
    (hη : ∀ j : Fin n, |η j| ≤ gamma fp n)
    (hδw : |δw| ≤ fp.u)
    (hδmul : ∀ i : Fin n, |δmul i| ≤ fp.u)
    (hδsub : ∀ i : Fin n, |δsub i| ≤ fp.u)
    (hvalid : gammaValid fp (2 * a + n + 3)) :
    ∀ i j : Fin n,
      ∃ θ : ℝ,
        |θ| ≤ gamma fp (2 * a + n + 3) ∧
        householderApplyDeltaMatrix n (householder n v 1) v_hat 1
            η δw δmul δsub i j =
          idMatrix n i j * δsub i - v i * v j * θ := by
  obtain ⟨alpha, hα, hfact⟩ :=
    householderApplyDeltaMatrix_normalized_factorization n v v_hat eps
      η δw δmul δsub hvec heps_nonneg
  intro i j
  have hαi : |alpha i| ≤ gamma fp a := le_trans (hα i) heps_bound
  have hαj : |alpha j| ≤ gamma fp a := le_trans (hα j) heps_bound
  obtain ⟨θ, hθ, hprod⟩ :=
    householderApply_error_factor_gamma fp a n (alpha i) (alpha j)
      (η j) δw (δmul i) (δsub i)
      hαi hαj (hη j) hδw (hδmul i) (hδsub i) hvalid
  refine ⟨θ, hθ, ?_⟩
  rw [hfact i j, hprod]
  ring

/-- Componentwise form of the implementation-backed normalized Householder
    application error.

    This keeps the two terms that appear in Higham's equation (19.40)
    separate: the final subtraction contributes `u * |b_i|`, while all
    errors in constructing and applying the normalized reflector contribute
    a rank-one term

    `gamma(2a+n+3) * |v_i| * sum_j |v_j| |b_j|`.

    Unlike `fl_householderApply_normalized_appError`, this result is
    componentwise and therefore does not introduce a Frobenius-norm or
    `sqrt n` loss. -/
theorem fl_householderApply_normalized_entrywise_error
    (fp : FPModel) (a n : ℕ)
    (v v_hat : Fin n → ℝ) (eps : ℝ) (b : Fin n → ℝ)
    (hvec : HouseholderVectorError n v v_hat eps)
    (heps_nonneg : 0 ≤ eps)
    (heps_bound : eps ≤ gamma fp a)
    (hvalid : gammaValid fp (2 * a + n + 3))
    (i : Fin n) :
    |fl_householderApply fp n v_hat 1 b i -
        matMulVec n (householder n v 1) b i| ≤
      fp.u * |b i| +
        gamma fp (2 * a + n + 3) * |v i| *
          (∑ j : Fin n, |v j| * |b j|) := by
  classical
  have hn : gammaValid fp n :=
    gammaValid_mono fp (by omega) hvalid
  obtain ⟨η, δw, δmul, δsub, hη, hδw, hδmul, hδsub, hmatrix⟩ :=
    fl_householderApply_matrix_unroll fp n v_hat 1 b hn
  have hentry :=
    householderApplyDeltaMatrix_normalized_entry_gamma fp a n
      v v_hat eps η δw δmul δsub hvec heps_nonneg heps_bound
      hη hδw hδmul hδsub hvalid
  let θ : Fin n → ℝ := fun j => Classical.choose (hentry i j)
  have hθ : ∀ j : Fin n, |θ j| ≤ gamma fp (2 * a + n + 3) := by
    intro j
    exact (Classical.choose_spec (hentry i j)).1
  have hdelta : ∀ j : Fin n,
      householderApplyDeltaMatrix n (householder n v 1) v_hat 1
          η δw δmul δsub i j =
        idMatrix n i j * δsub i - v i * v j * θ j := by
    intro j
    exact (Classical.choose_spec (hentry i j)).2
  have hdiff :
      fl_householderApply fp n v_hat 1 b i -
          matMulVec n (householder n v 1) b i =
        ∑ j : Fin n,
          (idMatrix n i j * δsub i - v i * v j * θ j) * b j := by
    calc
      fl_householderApply fp n v_hat 1 b i -
          matMulVec n (householder n v 1) b i =
        matMulVec n
            (householderApplyRoundedMatrix n v_hat 1 η δw δmul δsub) b i -
          matMulVec n (householder n v 1) b i := by
            rw [congr_fun hmatrix i]
      _ = ∑ j : Fin n,
          householderApplyDeltaMatrix n (householder n v 1) v_hat 1
            η δw δmul δsub i j * b j := by
            unfold matMulVec householderApplyDeltaMatrix
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ j : Fin n,
          (idMatrix n i j * δsub i - v i * v j * θ j) * b j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hdelta j]
  have hdiag :
      (∑ j : Fin n, |idMatrix n i j * δsub i * b j|) ≤
        fp.u * |b i| := by
    calc
      (∑ j : Fin n, |idMatrix n i j * δsub i * b j|) =
          |δsub i| * |b i| := by
            unfold idMatrix
            rw [Finset.sum_eq_single i]
            · simp [abs_mul]
            · intro j _ hji
              simp [Ne.symm hji]
            · simp
      _ ≤ fp.u * |b i| :=
        mul_le_mul_of_nonneg_right (hδsub i) (abs_nonneg (b i))
  have houter :
      (∑ j : Fin n, |v i * v j * θ j * b j|) ≤
        gamma fp (2 * a + n + 3) * |v i| *
          (∑ j : Fin n, |v j| * |b j|) := by
    calc
      (∑ j : Fin n, |v i * v j * θ j * b j|) ≤
          ∑ j : Fin n,
            (gamma fp (2 * a + n + 3) * |v i|) *
              (|v j| * |b j|) := by
            apply Finset.sum_le_sum
            intro j _
            calc
              |v i * v j * θ j * b j| =
                  |θ j| * (|v i| * (|v j| * |b j|)) := by
                    simp only [abs_mul]
                    ring
              _ ≤ gamma fp (2 * a + n + 3) *
                    (|v i| * (|v j| * |b j|)) :=
                  mul_le_mul_of_nonneg_right (hθ j) (by positivity)
              _ = (gamma fp (2 * a + n + 3) * |v i|) *
                    (|v j| * |b j|) := by ring
      _ = gamma fp (2 * a + n + 3) * |v i| *
          (∑ j : Fin n, |v j| * |b j|) := by
            rw [Finset.mul_sum]
  rw [hdiff]
  calc
    |∑ j : Fin n,
        (idMatrix n i j * δsub i - v i * v j * θ j) * b j| ≤
        ∑ j : Fin n,
          |(idMatrix n i j * δsub i - v i * v j * θ j) * b j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n,
        (|idMatrix n i j * δsub i * b j| +
          |v i * v j * θ j * b j|) := by
          apply Finset.sum_le_sum
          intro j _
          rw [sub_mul]
          exact abs_sub _ _
    _ = (∑ j : Fin n, |idMatrix n i j * δsub i * b j|) +
        ∑ j : Fin n, |v i * v j * θ j * b j| :=
      Finset.sum_add_distrib
    _ ≤ fp.u * |b i| +
        gamma fp (2 * a + n + 3) * |v i| *
          (∑ j : Fin n, |v j| * |b j|) :=
      add_le_add hdiag houter

/-- Frobenius bound for the diagonal matrix produced by the final componentwise
    subtraction roundoff in a Householder application. -/
theorem householderApply_sub_error_frob_bound (fp : FPModel) (n : ℕ)
    (δsub : Fin n → ℝ)
    (hδsub : ∀ i : Fin n, |δsub i| ≤ fp.u) :
    frobNorm (fun i j => idMatrix n i j * δsub i) ≤
      Real.sqrt ((n : ℝ) * fp.u ^ 2) := by
  let B : Fin n → Fin n → ℝ := fun i j => if i = j then fp.u else 0
  have hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j := by
    intro i j
    by_cases hij : i = j
    · simp [B, hij, fp.u_nonneg]
    · simp [B, hij]
  have hentry :
      ∀ i j : Fin n, |idMatrix n i j * δsub i| ≤ B i j := by
    intro i j
    by_cases hij : i = j
    · simpa [B, idMatrix, hij] using hδsub i
    · simp [B, idMatrix, hij]
  have hBnorm : frobNorm B = Real.sqrt ((n : ℝ) * fp.u ^ 2) := by
    rw [frobNorm_eq_sqrt_frobNormSq]
    congr 1
    unfold frobNormSq
    calc
      (∑ i : Fin n, ∑ j : Fin n, (B i j) ^ 2)
          = ∑ i : Fin n, fp.u ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            simp [B, Finset.sum_ite_eq, Finset.mem_univ]
      _ = (n : ℝ) * fp.u ^ 2 := by
            simp
  calc
    frobNorm (fun i j => idMatrix n i j * δsub i)
        ≤ frobNorm B :=
          frobNorm_le_of_entry_abs_le
            (fun i j => idMatrix n i j * δsub i) B hB_nonneg hentry
    _ = Real.sqrt ((n : ℝ) * fp.u ^ 2) := hBnorm

/-- Frobenius bound for the outer-product part of the normalized Householder
    application perturbation.  The normalization `∑ |v_i|² = 2` gives
    `‖v vᵀ‖_F = 2`, so entrywise gamma factors contribute at most `2γ`. -/
theorem householderApply_outer_gamma_frob_bound (fp : FPModel) (n k : ℕ)
    (v : Fin n → ℝ) (θ : Fin n → Fin n → ℝ)
    (hvnorm : (∑ i : Fin n, |v i| ^ 2) = 2)
    (hθ : ∀ i j : Fin n, |θ i j| ≤ gamma fp k)
    (hvalid : gammaValid fp k) :
    frobNorm (fun i j => -v i * v j * θ i j) ≤
      2 * gamma fp k := by
  let γ : ℝ := gamma fp k
  have hγ : 0 ≤ γ := gamma_nonneg fp hvalid
  have hvnorm_sq : (∑ i : Fin n, v i ^ 2) = 2 := by
    calc
      (∑ i : Fin n, v i ^ 2)
          = ∑ i : Fin n, |v i| ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [sq_abs]
      _ = 2 := hvnorm
  let B : Fin n → Fin n → ℝ := fun i j => γ * |v i| * |v j|
  have hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j := by
    intro i j
    exact mul_nonneg
      (mul_nonneg hγ (abs_nonneg (v i)))
      (abs_nonneg (v j))
  have hentry :
      ∀ i j : Fin n, |-v i * v j * θ i j| ≤ B i j := by
    intro i j
    have hp : 0 ≤ |v i| * |v j| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      |-v i * v j * θ i j|
          = |v i| * |v j| * |θ i j| := by
            rw [abs_mul, abs_mul, abs_neg]
      _ ≤ |v i| * |v j| * γ :=
            mul_le_mul_of_nonneg_left (hθ i j) hp
      _ = B i j := by
            simp [B, γ]
            ring
  have hBsq : frobNormSq B = (2 * γ) ^ 2 := by
    unfold frobNormSq
    calc
      (∑ i : Fin n, ∑ j : Fin n, (B i j) ^ 2)
          = ∑ i : Fin n,
              (γ ^ 2 * v i ^ 2 * (∑ j : Fin n, v j ^ 2)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            have hsq_i : |v i| ^ 2 = v i ^ 2 := sq_abs (v i)
            have hsq_j : |v j| ^ 2 = v j ^ 2 := sq_abs (v j)
            simp [B]
            calc
              (γ * |v i| * |v j|) ^ 2 =
                  γ ^ 2 * |v i| ^ 2 * |v j| ^ 2 := by ring
              _ = γ ^ 2 * v i ^ 2 * v j ^ 2 := by
                  rw [hsq_i, hsq_j]
      _ = ∑ i : Fin n, (γ ^ 2 * v i ^ 2 * 2) := by
            rw [hvnorm_sq]
      _ = 2 * (∑ i : Fin n, γ ^ 2 * v i ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 2 * (γ ^ 2 * (∑ i : Fin n, |v i| ^ 2)) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [sq_abs]
      _ = (2 * γ) ^ 2 := by
            rw [hvnorm]
            ring
  have hBnorm : frobNorm B = 2 * γ := by
    rw [frobNorm_eq_sqrt_frobNormSq, hBsq]
    rw [Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (mul_nonneg (by norm_num) hγ)
  calc
    frobNorm (fun i j => -v i * v j * θ i j)
        ≤ frobNorm B :=
          frobNorm_le_of_entry_abs_le
            (fun i j => -v i * v j * θ i j) B hB_nonneg hentry
    _ = 2 * gamma fp k := by
          simpa [γ] using hBnorm

/-- Concrete Frobenius bound for the normalized Householder application
    perturbation matrix.

    This is the normwise part of the Lemma 18.2 bridge, with the bound kept in
    a transparent raw form:
    the final subtraction contributes `sqrt(n*u^2)`, and the normalized
    rank-one part contributes `2*gamma(2a+n+3)`.  A later cleanup can collapse
    this expression into a single generic `γ_cm` constant if needed. -/
theorem householderApplyDeltaMatrix_normalized_frob_bound
    (fp : FPModel) (a n : ℕ)
    (v v_hat : Fin n → ℝ) (eps : ℝ)
    (η : Fin n → ℝ) (δw : ℝ) (δmul δsub : Fin n → ℝ)
    (hvec : HouseholderVectorError n v v_hat eps)
    (heps_nonneg : 0 ≤ eps)
    (heps_bound : eps ≤ gamma fp a)
    (hη : ∀ j : Fin n, |η j| ≤ gamma fp n)
    (hδw : |δw| ≤ fp.u)
    (hδmul : ∀ i : Fin n, |δmul i| ≤ fp.u)
    (hδsub : ∀ i : Fin n, |δsub i| ≤ fp.u)
    (hvalid : gammaValid fp (2 * a + n + 3)) :
    frobNorm
      (householderApplyDeltaMatrix n (householder n v 1) v_hat 1
        η δw δmul δsub) ≤
      Real.sqrt ((n : ℝ) * fp.u ^ 2) +
        2 * gamma fp (2 * a + n + 3) := by
  let k : ℕ := 2 * a + n + 3
  have hentry :=
    householderApplyDeltaMatrix_normalized_entry_gamma fp a n v v_hat eps
      η δw δmul δsub hvec heps_nonneg heps_bound hη hδw hδmul hδsub
      hvalid
  let θ : Fin n → Fin n → ℝ := fun i j => Classical.choose (hentry i j)
  have hθ : ∀ i j : Fin n, |θ i j| ≤ gamma fp k := by
    intro i j
    have hspec := Classical.choose_spec (hentry i j)
    simpa [θ, k] using hspec.1
  let D : Fin n → Fin n → ℝ := fun i j => idMatrix n i j * δsub i
  let E : Fin n → Fin n → ℝ := fun i j => -v i * v j * θ i j
  have hdecomp :
      householderApplyDeltaMatrix n (householder n v 1) v_hat 1
          η δw δmul δsub =
        fun i j => D i j + E i j := by
    ext i j
    have hspec := Classical.choose_spec (hentry i j)
    rw [hspec.2]
    simp [D, E, θ]
    ring
  calc
    frobNorm
        (householderApplyDeltaMatrix n (householder n v 1) v_hat 1
          η δw δmul δsub)
        = frobNorm (fun i j => D i j + E i j) := by
          rw [hdecomp]
    _ ≤ frobNorm D + frobNorm E :=
          frobNorm_add_le D E
    _ ≤ Real.sqrt ((n : ℝ) * fp.u ^ 2) +
          2 * gamma fp (2 * a + n + 3) := by
          have hD :
              frobNorm D ≤ Real.sqrt ((n : ℝ) * fp.u ^ 2) := by
            simpa [D] using
              householderApply_sub_error_frob_bound fp n δsub hδsub
          have hE :
              frobNorm E ≤ 2 * gamma fp (2 * a + n + 3) := by
            simpa [E, k] using
              householderApply_outer_gamma_frob_bound fp n k v θ
                (householderVectorError_sum_abs_sq hvec) hθ hvalid
          exact add_le_add hD hE

/-- If the concrete perturbation matrix extracted from the rounded
    Householder-application kernel has the required Frobenius bound, then the
    rounded kernel satisfies the `HouseholderAppError` contract.

    This theorem is intentionally a packaging bridge for callers that already
    have the needed perturbation-matrix bound.  The concrete normalized bound is
    proved later in this file and consumed by
    `fl_householderApply_normalized_appError`. -/
theorem fl_householderApply_appError_of_matrix_bound (fp : FPModel) (n : ℕ)
    (P : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (beta : ℝ)
    (b : Fin n → ℝ) (c : ℝ)
    (hn : gammaValid fp n) (horth : IsOrthogonal n P)
    (hbound :
      ∀ (η : Fin n → ℝ) (δw : ℝ) (δmul δsub : Fin n → ℝ),
        (∀ j : Fin n, |η j| ≤ gamma fp n) →
        |δw| ≤ fp.u →
        (∀ i : Fin n, |δmul i| ≤ fp.u) →
        (∀ i : Fin n, |δsub i| ≤ fp.u) →
        frobNorm
          (householderApplyDeltaMatrix n P v beta η δw δmul δsub) ≤ c) :
    HouseholderAppError n P b (fl_householderApply fp n v beta b) c := by
  obtain ⟨η, δw, δmul, δsub, hη, hδw, hδmul, hδsub, hmatrix⟩ :=
    fl_householderApply_matrix_unroll fp n v beta b hn
  refine ⟨horth, ?_⟩
  refine ⟨householderApplyDeltaMatrix n P v beta η δw δmul δsub,
    hbound η δw δmul δsub hη hδw hδmul hδsub, ?_⟩
  intro i
  calc
    fl_householderApply fp n v beta b i =
        matMulVec n (householderApplyRoundedMatrix n v beta η δw δmul δsub) b i := by
          exact congr_fun hmatrix i
    _ = matMulVec n
          (fun a j =>
            P a j + householderApplyDeltaMatrix n P v beta η δw δmul δsub a j) b i := by
          unfold matMulVec householderApplyDeltaMatrix
          apply Finset.sum_congr rfl
          intro j _
          ring

/-- Implementation-backed normalized Householder application error theorem.

    This is the concrete one-reflector bridge corresponding to Higham Lemma
    18.2 in normalized form `P = I - v vᵀ`: if the computed vector satisfies
    equation (18.3), then the concrete rounded application
    `fl_householderApply fp n v_hat 1 b` satisfies `HouseholderAppError`.

    The bound is deliberately left as a transparent raw expression.  Higham's
    text writes this as a generic `γ_cm`; proving a single-gamma presentation is
    a later constants-cleanup step, not a missing algorithmic bridge. -/
theorem fl_householderApply_normalized_appError
    (fp : FPModel) (a n : ℕ)
    (v v_hat : Fin n → ℝ) (eps : ℝ) (b : Fin n → ℝ)
    (hvec : HouseholderVectorError n v v_hat eps)
    (heps_nonneg : 0 ≤ eps)
    (heps_bound : eps ≤ gamma fp a)
    (hvalid : gammaValid fp (2 * a + n + 3)) :
    HouseholderAppError n (householder n v 1) b
      (fl_householderApply fp n v_hat 1 b)
      (Real.sqrt ((n : ℝ) * fp.u ^ 2) +
        2 * gamma fp (2 * a + n + 3)) := by
  have hn : gammaValid fp n :=
    gammaValid_mono fp (by omega) hvalid
  have horth : IsOrthogonal n (householder n v 1) :=
    householder_orthogonal n v 1 (by simpa using hvec.norm_sq)
  apply fl_householderApply_appError_of_matrix_bound fp n
    (householder n v 1) v_hat 1 b
    (Real.sqrt ((n : ℝ) * fp.u ^ 2) +
      2 * gamma fp (2 * a + n + 3)) hn horth
  intro η δw δmul δsub hη hδw hδmul hδsub
  exact householderApplyDeltaMatrix_normalized_frob_bound fp a n
    v v_hat eps η δw δmul δsub hvec heps_nonneg heps_bound
    hη hδw hδmul hδsub hvalid

end NumStability
