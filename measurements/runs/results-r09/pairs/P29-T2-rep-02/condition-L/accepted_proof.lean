import HighamBench.P29Definitions
import NumStability.Algorithms.LinearSystems.Triangular.Combined

namespace HighamBench

open scoped BigOperators

noncomputable def p29AsFPModel (fp : P29FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := fp.fl_div
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := fp.model_div
  model_sqrt := by
    intro x hx
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · simp

private theorem p29ForwardSubSteps_eq (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p29ForwardSubSteps fp n L b k hk x =
        NumStability.fl_forwardSub_steps (p29AsFPModel fp) n L b k hk x := by
  intro k
  induction k with
  | zero =>
      intro hk x
      rfl
  | succ k ih =>
      intro hk x
      simp only [p29ForwardSubSteps, NumStability.fl_forwardSub_steps]
      apply ih

private theorem p29BackSubSteps_eq (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p29BackSubSteps fp n U b k hk x =
        NumStability.fl_backSub_steps (p29AsFPModel fp) n U b k hk x := by
  intro k
  induction k with
  | zero =>
      intro hk x
      rfl
  | succ k ih =>
      intro hk x
      simp only [p29BackSubSteps, NumStability.fl_backSub_steps]
      apply ih

private theorem p29ForwardSub_eq (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) :
    p29ForwardSub fp n L b =
      NumStability.fl_forwardSub (p29AsFPModel fp) n L b := by
  unfold p29ForwardSub NumStability.fl_forwardSub
  exact p29ForwardSubSteps_eq fp n L b n (le_refl n) (fun _ => 0)

private theorem p29BackSub_eq (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) :
    p29BackSub fp n U b =
      NumStability.fl_backSub (p29AsFPModel fp) n U b := by
  unfold p29BackSub NumStability.fl_backSub
  exact p29BackSubSteps_eq fp n U b n (le_refl n) (fun _ => 0)

private theorem p29EntryNorm_nonneg {m n : ℕ} (A : P29Matrix m n) :
    0 ≤ p29EntryNorm A := by
  unfold p29EntryNorm
  positivity

private theorem p29EntryNorm_coord_le {m n : ℕ} (A : P29Matrix m n)
    (i : Fin m) (j : Fin n) : |A i j| ≤ p29EntryNorm A := by
  unfold p29EntryNorm
  calc
    |A i j| ≤ ∑ j' : Fin n, |A i j'| := by
      exact Finset.single_le_sum
        (fun j' (_ : j' ∈ (Finset.univ : Finset (Fin n))) => abs_nonneg (A i j'))
        (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin m, ∑ j' : Fin n, |A i' j'| := by
      exact Finset.single_le_sum
        (fun i' (_ : i' ∈ (Finset.univ : Finset (Fin m))) =>
          Finset.sum_nonneg (fun j' _ => abs_nonneg (A i' j')))
        (Finset.mem_univ i)

private theorem p29EntryNorm_add_le {m n : ℕ} (A B : P29Matrix m n) :
    p29EntryNorm (A + B) ≤ p29EntryNorm A + p29EntryNorm B := by
  unfold p29EntryNorm
  calc
    ∑ i : Fin m, ∑ j : Fin n, |(A + B) i j| ≤
        ∑ i : Fin m, ∑ j : Fin n, (|A i j| + |B i j|) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact abs_add_le _ _
    _ = (∑ i : Fin m, ∑ j : Fin n, |A i j|) +
        ∑ i : Fin m, ∑ j : Fin n, |B i j| := by
      simp_rw [Finset.sum_add_distrib]

private theorem p29EntryNorm_of_componentwise {m n : ℕ}
    (A B : P29Matrix m n) (c : ℝ) (h : ∀ i j, |A i j| ≤ c * |B i j|) :
    p29EntryNorm A ≤ c * p29EntryNorm B := by
  unfold p29EntryNorm
  calc
    ∑ i : Fin m, ∑ j : Fin n, |A i j| ≤
        ∑ i : Fin m, ∑ j : Fin n, c * |B i j| := by
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h i j))
    _ = c * (∑ i : Fin m, ∑ j : Fin n, |B i j|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

private theorem p29EntryNorm_matMul_le (n : ℕ) (A B : P29Matrix n n) :
    p29EntryNorm (p29MatMul A B) ≤
      (n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B := by
  unfold p29EntryNorm p29MatMul
  calc
    ∑ i : Fin n, ∑ j : Fin n, |∑ k : Fin n, A i k * B k j| ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, |A i k * B k j| := by
      exact Finset.sum_le_sum (fun i _ =>
        Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (p29EntryNorm A * p29EntryNorm B) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul (p29EntryNorm_coord_le A i k)
        (p29EntryNorm_coord_le B k j) (abs_nonneg _) (p29EntryNorm_nonneg A)
    _ = (n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B := by
      simp
      ring

private theorem p29EntryNorm_three_mul_le (n : ℕ) (A B C : P29Matrix n n) :
    p29EntryNorm (p29MatMul (p29MatMul A B) C) ≤
      (n : ℝ) ^ 6 * p29EntryNorm A * p29EntryNorm B * p29EntryNorm C := by
  calc
    p29EntryNorm (p29MatMul (p29MatMul A B) C) ≤
        (n : ℝ) ^ 3 * p29EntryNorm (p29MatMul A B) * p29EntryNorm C :=
      p29EntryNorm_matMul_le n (p29MatMul A B) C
    _ ≤ (n : ℝ) ^ 3 *
        ((n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B) * p29EntryNorm C := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (p29EntryNorm_matMul_le n A B) (by positivity))
        (p29EntryNorm_nonneg C)
    _ = (n : ℝ) ^ 6 * p29EntryNorm A * p29EntryNorm B * p29EntryNorm C := by
      ring

private theorem p29MatMul_add_left {m n p : ℕ}
    (A B : P29Matrix m n) (C : P29Matrix n p) :
    p29MatMul (A + B) C = p29MatMul A C + p29MatMul B C := by
  funext i j
  unfold p29MatMul
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]

private theorem p29MatMul_add_right {m n p : ℕ}
    (A : P29Matrix m n) (B C : P29Matrix n p) :
    p29MatMul A (B + C) = p29MatMul A B + p29MatMul A C := by
  funext i j
  unfold p29MatMul
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

private theorem p29CombinedBackwardError_expansion {n : ℕ}
    (L D dL dD dU : P29Matrix n n) :
    p29CombinedBackwardError L D dL dD dU =
      p29MatMul (p29MatMul dL (D + dD)) (p29Transpose L + dU) +
      p29MatMul (p29MatMul L dD) (p29Transpose L + dU) +
      p29MatMul (p29MatMul L D) dU := by
  unfold p29CombinedBackwardError p29PerturbedLDLT p29LDLT
  simp only [p29MatMul_add_left, p29MatMul_add_right]
  abel

private theorem p29CombinedBackwardError_norm_le (n : ℕ)
    (L D dL dD dU : P29Matrix n n) (gamma eta : ℝ)
    (hgamma : 0 ≤ gamma) (heta : 0 ≤ eta)
    (hdL : ∀ i j, |dL i j| ≤ gamma * |L i j|)
    (hdD : p29EntryNorm dD ≤ eta * p29EntryNorm D)
    (hdU : ∀ i j, |dU i j| ≤ gamma * |p29Transpose L i j|) :
    p29EntryNorm (p29CombinedBackwardError L D dL dD dU) ≤
      (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        p29EntryNorm (p29Transpose L) *
        (gamma * (1 + eta) * (1 + gamma) +
          eta * (1 + gamma) + gamma) := by
  have hdLnorm : p29EntryNorm dL ≤ gamma * p29EntryNorm L :=
    p29EntryNorm_of_componentwise dL L gamma hdL
  have hdUnorm : p29EntryNorm dU ≤
      gamma * p29EntryNorm (p29Transpose L) :=
    p29EntryNorm_of_componentwise dU (p29Transpose L) gamma hdU
  have hDadd : p29EntryNorm (D + dD) ≤
      (1 + eta) * p29EntryNorm D := by
    calc
      p29EntryNorm (D + dD) ≤ p29EntryNorm D + p29EntryNorm dD :=
        p29EntryNorm_add_le D dD
      _ ≤ p29EntryNorm D + eta * p29EntryNorm D := by linarith
      _ = (1 + eta) * p29EntryNorm D := by ring
  have hUadd : p29EntryNorm (p29Transpose L + dU) ≤
      (1 + gamma) * p29EntryNorm (p29Transpose L) := by
    calc
      p29EntryNorm (p29Transpose L + dU) ≤
          p29EntryNorm (p29Transpose L) + p29EntryNorm dU :=
        p29EntryNorm_add_le (p29Transpose L) dU
      _ ≤ p29EntryNorm (p29Transpose L) +
          gamma * p29EntryNorm (p29Transpose L) := by linarith
      _ = (1 + gamma) * p29EntryNorm (p29Transpose L) := by ring
  have hL0 : 0 ≤ p29EntryNorm L := p29EntryNorm_nonneg L
  have hD0 : 0 ≤ p29EntryNorm D := p29EntryNorm_nonneg D
  have hT0 : 0 ≤ p29EntryNorm (p29Transpose L) :=
    p29EntryNorm_nonneg (p29Transpose L)
  have hDadd0 : 0 ≤ p29EntryNorm (D + dD) := p29EntryNorm_nonneg (D + dD)
  have hUadd0 : 0 ≤ p29EntryNorm (p29Transpose L + dU) :=
    p29EntryNorm_nonneg (p29Transpose L + dU)
  let X := p29MatMul (p29MatMul dL (D + dD)) (p29Transpose L + dU)
  let Y := p29MatMul (p29MatMul L dD) (p29Transpose L + dU)
  let Z := p29MatMul (p29MatMul L D) dU
  have hX : p29EntryNorm X ≤
      (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        p29EntryNorm (p29Transpose L) *
        (gamma * (1 + eta) * (1 + gamma)) := by
    calc
      p29EntryNorm X ≤ (n : ℝ) ^ 6 * p29EntryNorm dL *
          p29EntryNorm (D + dD) * p29EntryNorm (p29Transpose L + dU) := by
        exact p29EntryNorm_three_mul_le n dL (D + dD) (p29Transpose L + dU)
      _ ≤ (n : ℝ) ^ 6 * (gamma * p29EntryNorm L) *
          ((1 + eta) * p29EntryNorm D) *
          ((1 + gamma) * p29EntryNorm (p29Transpose L)) := by
        gcongr
        all_goals positivity
      _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          p29EntryNorm (p29Transpose L) *
          (gamma * (1 + eta) * (1 + gamma)) := by ring
  have hY : p29EntryNorm Y ≤
      (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        p29EntryNorm (p29Transpose L) * (eta * (1 + gamma)) := by
    calc
      p29EntryNorm Y ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
          p29EntryNorm dD * p29EntryNorm (p29Transpose L + dU) := by
        exact p29EntryNorm_three_mul_le n L dD (p29Transpose L + dU)
      _ ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
          (eta * p29EntryNorm D) *
          ((1 + gamma) * p29EntryNorm (p29Transpose L)) := by
        gcongr
        all_goals positivity
      _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          p29EntryNorm (p29Transpose L) * (eta * (1 + gamma)) := by ring
  have hZ : p29EntryNorm Z ≤
      (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        p29EntryNorm (p29Transpose L) * gamma := by
    calc
      p29EntryNorm Z ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
          p29EntryNorm D * p29EntryNorm dU := by
        exact p29EntryNorm_three_mul_le n L D dU
      _ ≤ (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          (gamma * p29EntryNorm (p29Transpose L)) := by
        gcongr
        all_goals positivity
      _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          p29EntryNorm (p29Transpose L) * gamma := by ring
  calc
    p29EntryNorm (p29CombinedBackwardError L D dL dD dU) =
        p29EntryNorm (X + Y + Z) := by
      rw [p29CombinedBackwardError_expansion]
    _ ≤ p29EntryNorm X + p29EntryNorm Y + p29EntryNorm Z := by
      exact le_trans (p29EntryNorm_add_le (X + Y) Z)
        (add_le_add (p29EntryNorm_add_le X Y) (le_refl _))
    _ ≤
        ((n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
            p29EntryNorm (p29Transpose L) *
            (gamma * (1 + eta) * (1 + gamma))) +
          ((n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
            p29EntryNorm (p29Transpose L) * (eta * (1 + gamma))) +
          ((n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
            p29EntryNorm (p29Transpose L) * gamma) := by linarith
    _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        p29EntryNorm (p29Transpose L) *
        (gamma * (1 + eta) * (1 + gamma) +
          eta * (1 + gamma) + gamma) := by ring

private theorem p29_three_factor_solve {n : ℕ}
    (P Q R : P29Matrix n n) (x z y b : Fin n → ℝ)
    (hR : ∀ i, ∑ j : Fin n, R i j * x j = z i)
    (hQ : ∀ i, ∑ j : Fin n, Q i j * z j = y i)
    (hP : ∀ i, ∑ j : Fin n, P i j * y j = b i) :
    ∀ i, ∑ j : Fin n, p29MatMul (p29MatMul P Q) R i j * x j = b i := by
  have hR' : Matrix.mulVec R x = z := funext hR
  have hQ' : Matrix.mulVec Q z = y := funext hQ
  have hP' : Matrix.mulVec P y = b := funext hP
  intro i
  change Matrix.mulVec ((P * Q) * R) x i = b i
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hR', hQ', hP']

/-- P29-T2: the normwise backward-stability conclusion for the `LDLᵀ`
solution phase in Appendix B. -/
theorem p29_t2_ldlt_solve_backward_stability
    (fp : P29FPModel) (n : ℕ) (A L D E0 : P29Matrix n n)
    (b z : Fin n → ℝ) (eta factorEta : ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P29GammaValid fp.u n)
    (heta : 0 ≤ eta)
    (hfactor : p29LDLT L D = A + E0)
    (hE0 : p29EntryNorm E0 ≤ factorEta * p29EntryNorm A)
    (hDsolve : P29BlockSolveStable n D
      (p29ForwardSub fp n L b) z eta) :
    ∃ (ΔL ΔD ΔU F : P29Matrix n n),
      (∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|) ∧
      p29EntryNorm ΔD ≤ eta * p29EntryNorm D ∧
      (∀ i j, |ΔU i j| ≤
        p29Gamma fp.u n * |p29Transpose L i j|) ∧
      F = p29TotalBackwardError E0 L D ΔL ΔD ΔU ∧
      (∀ i, ∑ j : Fin n,
        (A i j + F i j) *
          p29BackSub fp n (p29Transpose L) z j = b i) ∧
      p29EntryNorm F ≤
        p29TotalBackwardBound fp n eta factorEta A L D := by
  -- PROOF_START P29-T2-H001
  let fp' : NumStability.FPModel := p29AsFPModel fp
  have hvalid' : NumStability.gammaValid fp' n := by
    simpa [fp', p29AsFPModel, NumStability.gammaValid, P29GammaValid] using hvalid
  have hgamma : 0 ≤ p29Gamma fp.u n := by
    have hv : (n : ℝ) * fp.u < 1 := hvalid
    unfold p29Gamma
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg n) fp.u_nonneg)
      (le_of_lt (sub_pos.mpr hv))
  obtain ⟨dL, hdL', hforward'⟩ :=
    NumStability.forwardSub_backward_error fp' n L b hdiag hlower hvalid'
  have hdL : ∀ i j, |dL i j| ≤ p29Gamma fp.u n * |L i j| := by
    simpa [fp', p29AsFPModel, NumStability.gamma, p29Gamma] using hdL'
  have hforward : ∀ i, ∑ j : Fin n,
      (L i j + dL i j) * p29ForwardSub fp n L b j = b i := by
    dsimp [fp'] at hforward'
    rw [p29ForwardSub_eq fp n L b]
    exact hforward'
  obtain ⟨dD, hdD, hmiddle⟩ := hDsolve
  have htdiag : ∀ i, p29Transpose L i i ≠ 0 := by
    intro i
    exact hdiag i
  have htupper : ∀ i j : Fin n, j.val < i.val → p29Transpose L i j = 0 := by
    intro i j hij
    exact hlower j i hij
  obtain ⟨dU, hdU', hback'⟩ :=
    NumStability.backSub_backward_error fp' n (p29Transpose L) z
      htdiag htupper hvalid'
  have hdU : ∀ i j, |dU i j| ≤
      p29Gamma fp.u n * |p29Transpose L i j| := by
    simpa [fp', p29AsFPModel, NumStability.gamma, p29Gamma] using hdU'
  have hback : ∀ i, ∑ j : Fin n,
      (p29Transpose L i j + dU i j) *
        p29BackSub fp n (p29Transpose L) z j = z i := by
    dsimp [fp'] at hback'
    rw [p29BackSub_eq fp n (p29Transpose L) z]
    exact hback'
  let F := p29TotalBackwardError E0 L D dL dD dU
  refine ⟨dL, dD, dU, F, hdL, hdD, hdU, rfl, ?_, ?_⟩
  · have hchain := p29_three_factor_solve
        ((fun i j => L i j + dL i j) : P29Matrix n n)
        ((fun i j => D i j + dD i j) : P29Matrix n n)
        ((fun i j => p29Transpose L i j + dU i j) : P29Matrix n n)
        (p29BackSub fp n (p29Transpose L) z) z
        (p29ForwardSub fp n L b) b
        (by simpa only [Matrix.add_apply] using hback)
        (by simpa only [Matrix.add_apply] using hmiddle)
        (by simpa only [Matrix.add_apply] using hforward)
    have hAF : A + F = p29PerturbedLDLT L D dL dD dU := by
      dsimp [F]
      unfold p29TotalBackwardError p29CombinedBackwardError
      rw [hfactor]
      abel
    intro i
    change ∑ j : Fin n, (A + F) i j *
      p29BackSub fp n (p29Transpose L) z j = b i
    rw [hAF]
    exact hchain i
  · have hcombined := p29CombinedBackwardError_norm_le n L D dL dD dU
        (p29Gamma fp.u n) eta hgamma heta hdL hdD hdU
    dsimp [F]
    unfold p29TotalBackwardBound p29SolveBackwardFactor
    exact le_trans (p29EntryNorm_add_le E0
      (p29CombinedBackwardError L D dL dD dU))
      (add_le_add hE0 hcombined)

end HighamBench
