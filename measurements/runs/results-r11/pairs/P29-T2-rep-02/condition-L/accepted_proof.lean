import HighamBench.P29Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution

namespace HighamBench

open scoped BigOperators

private noncomputable def p29AsFPModel (fp : P29FPModel) :
    NumStability.FPModel where
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
    · ring

private lemma p29_as_gamma (fp : P29FPModel) (n : ℕ) :
    NumStability.gamma (p29AsFPModel fp) n = p29Gamma fp.u n := by
  rfl

private lemma p29_as_valid (fp : P29FPModel) (n : ℕ)
    (h : P29GammaValid fp.u n) :
    NumStability.gammaValid (p29AsFPModel fp) n := by
  exact h

private lemma p29_as_forward_steps (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ) :
    NumStability.fl_forwardSub_steps (p29AsFPModel fp) n L b k hk x =
      p29ForwardSubSteps fp n L b k hk x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      unfold NumStability.fl_forwardSub_steps p29ForwardSubSteps
      apply ih

private lemma p29_as_forward (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) :
    NumStability.fl_forwardSub (p29AsFPModel fp) n L b =
      p29ForwardSub fp n L b := by
  exact p29_as_forward_steps fp n L b n (le_refl n) (fun _ => 0)

private lemma p29_as_back_steps (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ) :
    NumStability.fl_backSub_steps (p29AsFPModel fp) n U b k hk x =
      p29BackSubSteps fp n U b k hk x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      unfold NumStability.fl_backSub_steps p29BackSubSteps
      apply ih

private lemma p29_as_back (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) :
    NumStability.fl_backSub (p29AsFPModel fp) n U b =
      p29BackSub fp n U b := by
  exact p29_as_back_steps fp n U b n (le_refl n) (fun _ => 0)

private lemma p29EntryNorm_nonneg {m n : ℕ} (A : P29Matrix m n) :
    0 ≤ p29EntryNorm A := by
  unfold p29EntryNorm
  positivity

private lemma p29_abs_entry_le_norm {m n : ℕ} (A : P29Matrix m n)
    (i : Fin m) (j : Fin n) :
    |A i j| ≤ p29EntryNorm A := by
  unfold p29EntryNorm
  have hj : |A i j| ≤ ∑ k : Fin n, |A i k| := by
    exact Finset.single_le_sum (fun k _ => abs_nonneg (A i k)) (Finset.mem_univ j)
  exact hj.trans <|
    Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg (A k l)))
      (Finset.mem_univ i)

private lemma p29EntryNorm_add_le {m n : ℕ} (A B : P29Matrix m n) :
    p29EntryNorm (A + B) ≤ p29EntryNorm A + p29EntryNorm B := by
  unfold p29EntryNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  exact abs_add_le (A i j) (B i j)

private lemma p29EntryNorm_of_pointwise {m n : ℕ} {c : ℝ}
    (hc : 0 ≤ c) (A B : P29Matrix m n)
    (h : ∀ i j, |A i j| ≤ c * |B i j|) :
    p29EntryNorm A ≤ c * p29EntryNorm B := by
  unfold p29EntryNorm
  calc
    ∑ i : Fin m, ∑ j : Fin n, |A i j| ≤
        ∑ i : Fin m, ∑ j : Fin n, c * |B i j| := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact h i j
    _ = c * (∑ i : Fin m, ∑ j : Fin n, |B i j|) := by
          simp only [Finset.mul_sum]

private lemma p29EntryNorm_matMul_le (n : ℕ) (A B : P29Matrix n n) :
    p29EntryNorm (p29MatMul A B) ≤
      (n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B := by
  have hentry : ∀ i j : Fin n,
      |p29MatMul A B i j| ≤
        (n : ℝ) * (p29EntryNorm A * p29EntryNorm B) := by
    intro i j
    unfold p29MatMul
    calc
      |∑ k : Fin n, A i k * B k j| ≤
          ∑ k : Fin n, |A i k * B k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, p29EntryNorm A * p29EntryNorm B := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        exact mul_le_mul
          (p29_abs_entry_le_norm A i k)
          (p29_abs_entry_le_norm B k j)
          (abs_nonneg _) (p29EntryNorm_nonneg A)
      _ = (n : ℝ) * (p29EntryNorm A * p29EntryNorm B) := by simp
  unfold p29EntryNorm
  calc
    ∑ i : Fin n, ∑ j : Fin n, |p29MatMul A B i j| ≤
        ∑ _i : Fin n, ∑ _j : Fin n,
          (n : ℝ) * (p29EntryNorm A * p29EntryNorm B) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hentry i j
    _ = (n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B := by
      simp
      ring

private lemma p29EntryNorm_triple_le (n : ℕ)
    (A B C : P29Matrix n n) :
    p29EntryNorm (p29MatMul (p29MatMul A B) C) ≤
      (n : ℝ) ^ 6 * p29EntryNorm A * p29EntryNorm B * p29EntryNorm C := by
  calc
    p29EntryNorm (p29MatMul (p29MatMul A B) C) ≤
        (n : ℝ) ^ 3 * p29EntryNorm (p29MatMul A B) * p29EntryNorm C :=
      p29EntryNorm_matMul_le n (p29MatMul A B) C
    _ ≤ (n : ℝ) ^ 3 *
        ((n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B) *
          p29EntryNorm C := by
      apply mul_le_mul_of_nonneg_right _ (p29EntryNorm_nonneg C)
      apply mul_le_mul_of_nonneg_left
        (p29EntryNorm_matMul_le n A B)
      positivity
    _ = (n : ℝ) ^ 6 * p29EntryNorm A * p29EntryNorm B *
        p29EntryNorm C := by ring_nf

private lemma p29MatMul_add_left {n : ℕ} (A B C : P29Matrix n n) :
    p29MatMul (A + B) C = p29MatMul A C + p29MatMul B C := by
  ext i j
  simp [p29MatMul, add_mul, Finset.sum_add_distrib]

private lemma p29MatMul_add_right {n : ℕ} (A B C : P29Matrix n n) :
    p29MatMul A (B + C) = p29MatMul A B + p29MatMul A C := by
  ext i j
  simp [p29MatMul, mul_add, Finset.sum_add_distrib]

private lemma p29CombinedBackwardError_expand {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) :
    p29CombinedBackwardError L D ΔL ΔD ΔU =
      p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L D) ΔU := by
  unfold p29CombinedBackwardError p29PerturbedLDLT p29LDLT
  simp only [p29MatMul_add_left, p29MatMul_add_right]
  ext i j
  simp
  ring

private lemma p29MatMul_mulVec {n : ℕ} (A B : P29Matrix n n)
    (x : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin n, p29MatMul A B i j * x j =
      ∑ k : Fin n, A i k * (∑ j : Fin n, B k j * x j) := by
  unfold p29MatMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma p29CombinedBackwardError_norm_le {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) (g eta : ℝ)
    (hg : 0 ≤ g) (heta : 0 ≤ eta)
    (hL : ∀ i j, |ΔL i j| ≤ g * |L i j|)
    (hD : p29EntryNorm ΔD ≤ eta * p29EntryNorm D)
    (hU : ∀ i j, |ΔU i j| ≤ g * |p29Transpose L i j|) :
    p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
      (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        p29EntryNorm (p29Transpose L) *
        (g * (1 + eta) * (1 + g) + eta * (1 + g) + g) := by
  have hΔL : p29EntryNorm ΔL ≤ g * p29EntryNorm L :=
    p29EntryNorm_of_pointwise hg ΔL L hL
  have hΔU : p29EntryNorm ΔU ≤
      g * p29EntryNorm (p29Transpose L) :=
    p29EntryNorm_of_pointwise hg ΔU (p29Transpose L) hU
  have hDplus : p29EntryNorm (D + ΔD) ≤
      (1 + eta) * p29EntryNorm D := by
    calc
      p29EntryNorm (D + ΔD) ≤
          p29EntryNorm D + p29EntryNorm ΔD := p29EntryNorm_add_le D ΔD
      _ ≤ p29EntryNorm D + eta * p29EntryNorm D :=
        add_le_add_right hD _
      _ = (1 + eta) * p29EntryNorm D := by ring
  have hUplus : p29EntryNorm (p29Transpose L + ΔU) ≤
      (1 + g) * p29EntryNorm (p29Transpose L) := by
    calc
      p29EntryNorm (p29Transpose L + ΔU) ≤
          p29EntryNorm (p29Transpose L) + p29EntryNorm ΔU :=
        p29EntryNorm_add_le (p29Transpose L) ΔU
      _ ≤ p29EntryNorm (p29Transpose L) +
          g * p29EntryNorm (p29Transpose L) := add_le_add_right hΔU _
      _ = (1 + g) * p29EntryNorm (p29Transpose L) := by ring
  have hn6 : 0 ≤ (n : ℝ) ^ 6 := by positivity
  have hNL : 0 ≤ p29EntryNorm L := p29EntryNorm_nonneg L
  have hND : 0 ≤ p29EntryNorm D := p29EntryNorm_nonneg D
  have hNT : 0 ≤ p29EntryNorm (p29Transpose L) :=
    p29EntryNorm_nonneg (p29Transpose L)
  have hDp : 0 ≤ p29EntryNorm (D + ΔD) := p29EntryNorm_nonneg (D + ΔD)
  have hUp : 0 ≤ p29EntryNorm (p29Transpose L + ΔU) :=
    p29EntryNorm_nonneg (p29Transpose L + ΔU)
  have h1e : 0 ≤ 1 + eta := by linarith
  have h1g : 0 ≤ 1 + g := by linarith
  let X := p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU)
  let Y := p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU)
  let Z := p29MatMul (p29MatMul L D) ΔU
  have hX : p29EntryNorm X ≤
      (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        p29EntryNorm (p29Transpose L) * (g * (1 + eta) * (1 + g)) := by
    calc
      p29EntryNorm X ≤ (n : ℝ) ^ 6 * p29EntryNorm ΔL *
          p29EntryNorm (D + ΔD) * p29EntryNorm (p29Transpose L + ΔU) :=
        p29EntryNorm_triple_le n ΔL (D + ΔD) (p29Transpose L + ΔU)
      _ ≤ (n : ℝ) ^ 6 * (g * p29EntryNorm L) *
          p29EntryNorm (D + ΔD) * p29EntryNorm (p29Transpose L + ΔU) := by
        apply mul_le_mul_of_nonneg_right _ hUp
        apply mul_le_mul_of_nonneg_right _ hDp
        exact mul_le_mul_of_nonneg_left hΔL hn6
      _ ≤ (n : ℝ) ^ 6 * (g * p29EntryNorm L) *
          ((1 + eta) * p29EntryNorm D) *
          p29EntryNorm (p29Transpose L + ΔU) := by
        apply mul_le_mul_of_nonneg_right _ hUp
        exact mul_le_mul_of_nonneg_left hDplus
          (mul_nonneg hn6 (mul_nonneg hg hNL))
      _ ≤ (n : ℝ) ^ 6 * (g * p29EntryNorm L) *
          ((1 + eta) * p29EntryNorm D) *
          ((1 + g) * p29EntryNorm (p29Transpose L)) := by
        exact mul_le_mul_of_nonneg_left hUplus
          (mul_nonneg
            (mul_nonneg hn6 (mul_nonneg hg hNL))
            (mul_nonneg h1e hND))
      _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          p29EntryNorm (p29Transpose L) * (g * (1 + eta) * (1 + g)) := by
        ring
  have hY : p29EntryNorm Y ≤
      (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        p29EntryNorm (p29Transpose L) * (eta * (1 + g)) := by
    calc
      p29EntryNorm Y ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
          p29EntryNorm ΔD * p29EntryNorm (p29Transpose L + ΔU) :=
        p29EntryNorm_triple_le n L ΔD (p29Transpose L + ΔU)
      _ ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
          (eta * p29EntryNorm D) * p29EntryNorm (p29Transpose L + ΔU) := by
        apply mul_le_mul_of_nonneg_right _ hUp
        exact mul_le_mul_of_nonneg_left hD (mul_nonneg hn6 hNL)
      _ ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
          (eta * p29EntryNorm D) *
          ((1 + g) * p29EntryNorm (p29Transpose L)) := by
        exact mul_le_mul_of_nonneg_left hUplus
          (mul_nonneg (mul_nonneg hn6 hNL) (mul_nonneg heta hND))
      _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          p29EntryNorm (p29Transpose L) * (eta * (1 + g)) := by ring
  have hZ : p29EntryNorm Z ≤
      (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        p29EntryNorm (p29Transpose L) * g := by
    calc
      p29EntryNorm Z ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
          p29EntryNorm D * p29EntryNorm ΔU :=
        p29EntryNorm_triple_le n L D ΔU
      _ ≤ (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          (g * p29EntryNorm (p29Transpose L)) := by
        exact mul_le_mul_of_nonneg_left hΔU
          (mul_nonneg (mul_nonneg hn6 hNL) hND)
      _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          p29EntryNorm (p29Transpose L) * g := by ring
  rw [p29CombinedBackwardError_expand]
  change p29EntryNorm (X + Y + Z) ≤ _
  calc
    p29EntryNorm (X + Y + Z) ≤ p29EntryNorm (X + Y) + p29EntryNorm Z :=
      p29EntryNorm_add_le (X + Y) Z
    _ ≤ (p29EntryNorm X + p29EntryNorm Y) + p29EntryNorm Z := by
      gcongr
      exact p29EntryNorm_add_le X Y
    _ ≤
        ((n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          p29EntryNorm (p29Transpose L) * (g * (1 + eta) * (1 + g)) +
         (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          p29EntryNorm (p29Transpose L) * (eta * (1 + g))) +
         (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          p29EntryNorm (p29Transpose L) * g := by
      exact add_le_add (add_le_add hX hY) hZ
    _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        p29EntryNorm (p29Transpose L) *
        (g * (1 + eta) * (1 + g) + eta * (1 + g) + g) := by ring

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
  have hmodelValid : NumStability.gammaValid (p29AsFPModel fp) n :=
    p29_as_valid fp n hvalid
  obtain ⟨(ΔL : P29Matrix n n), hΔLbound, hΔLeq⟩ :=
    NumStability.forwardSub_backward_error (p29AsFPModel fp) n L b
      hdiag hlower hmodelValid
  rw [p29_as_gamma] at hΔLbound
  rw [p29_as_forward] at hΔLeq
  have hTdiag : ∀ i, p29Transpose L i i ≠ 0 := by
    intro i
    exact hdiag i
  have hTupper : ∀ i j : Fin n, j.val < i.val →
      p29Transpose L i j = 0 := by
    intro i j hij
    exact hlower j i hij
  obtain ⟨(ΔU : P29Matrix n n), hΔUbound, hΔUeq⟩ :=
    NumStability.backSub_backward_error (p29AsFPModel fp) n
      (p29Transpose L) z hTdiag hTupper hmodelValid
  rw [p29_as_gamma] at hΔUbound
  rw [p29_as_back] at hΔUeq
  obtain ⟨(ΔD : P29Matrix n n), hΔDbound, hΔDeq⟩ := hDsolve
  let F := p29TotalBackwardError E0 L D ΔL ΔD ΔU
  refine ⟨ΔL, ΔD, ΔU, F, hΔLbound, hΔDbound, hΔUbound, rfl, ?_, ?_⟩
  · have hAF : A + F = p29PerturbedLDLT L D ΔL ΔD ΔU := by
      dsimp [F]
      unfold p29TotalBackwardError p29CombinedBackwardError
      rw [hfactor]
      abel
    intro i
    change ∑ j : Fin n, (A + F) i j *
      p29BackSub fp n (p29Transpose L) z j = b i
    rw [hAF]
    calc
      ∑ j : Fin n, p29PerturbedLDLT L D ΔL ΔD ΔU i j *
          p29BackSub fp n (p29Transpose L) z j =
          ∑ k : Fin n, p29MatMul (L + ΔL) (D + ΔD) i k *
            (∑ j : Fin n, (p29Transpose L + ΔU) k j *
              p29BackSub fp n (p29Transpose L) z j) := by
        exact p29MatMul_mulVec
          (p29MatMul (L + ΔL) (D + ΔD))
          (p29Transpose L + ΔU)
          (p29BackSub fp n (p29Transpose L) z) i
      _ = ∑ k : Fin n, p29MatMul (L + ΔL) (D + ΔD) i k * z k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [show (∑ j : Fin n, (p29Transpose L + ΔU) k j *
            p29BackSub fp n (p29Transpose L) z j) = z k by
          simpa using hΔUeq k]
      _ = ∑ k : Fin n, (L + ΔL) i k *
          (∑ j : Fin n, (D + ΔD) k j * z j) :=
        p29MatMul_mulVec (L + ΔL) (D + ΔD) z i
      _ = ∑ k : Fin n, (L + ΔL) i k * p29ForwardSub fp n L b k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [show (∑ j : Fin n, (D + ΔD) k j * z j) =
            p29ForwardSub fp n L b k by simpa using hΔDeq k]
      _ = b i := by simpa using hΔLeq i
  · have hgamma : 0 ≤ p29Gamma fp.u n := by
      rw [← p29_as_gamma]
      exact NumStability.gamma_nonneg (p29AsFPModel fp) hmodelValid
    have hcombined :
        p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
          p29SolveBackwardFactor fp n eta L D := by
      simpa [p29SolveBackwardFactor] using
        (p29CombinedBackwardError_norm_le L D ΔL ΔD ΔU
          (p29Gamma fp.u n) eta hgamma heta
          hΔLbound hΔDbound hΔUbound)
    dsimp [F]
    unfold p29TotalBackwardError p29TotalBackwardBound
    calc
      p29EntryNorm (E0 + p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
          p29EntryNorm E0 +
            p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) :=
        p29EntryNorm_add_le E0 (p29CombinedBackwardError L D ΔL ΔD ΔU)
      _ ≤ factorEta * p29EntryNorm A + p29SolveBackwardFactor fp n eta L D :=
        add_le_add hE0 hcombined

end HighamBench
