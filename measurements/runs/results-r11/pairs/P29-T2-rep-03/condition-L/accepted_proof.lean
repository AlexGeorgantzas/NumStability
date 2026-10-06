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
    · ring

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
      rw [p29ForwardSubSteps, NumStability.fl_forwardSub_steps]
      exact ih (Nat.le_of_succ_le hk) _

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
      rw [p29BackSubSteps, NumStability.fl_backSub_steps]
      exact ih (Nat.le_of_succ_le hk) _

private theorem p29ForwardSub_eq (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) :
    p29ForwardSub fp n L b =
      NumStability.fl_forwardSub (p29AsFPModel fp) n L b := by
  exact p29ForwardSubSteps_eq fp n L b n (le_refl n) (fun _ => 0)

private theorem p29BackSub_eq (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) :
    p29BackSub fp n U b =
      NumStability.fl_backSub (p29AsFPModel fp) n U b := by
  exact p29BackSubSteps_eq fp n U b n (le_refl n) (fun _ => 0)

private theorem p29EntryNorm_nonneg {m n : ℕ} (A : P29Matrix m n) :
    0 ≤ p29EntryNorm A := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

private theorem p29AbsEntry_le_norm {m n : ℕ} (A : P29Matrix m n)
    (i : Fin m) (j : Fin n) : |A i j| ≤ p29EntryNorm A := by
  have hj : |A i j| ≤ ∑ k : Fin n, |A i k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (A i k)) (Finset.mem_univ j)
  have hi : (∑ k : Fin n, |A i k|) ≤
      ∑ r : Fin m, ∑ k : Fin n, |A r k| :=
    Finset.single_le_sum
      (fun r _ => Finset.sum_nonneg (fun k _ => abs_nonneg (A r k)))
      (Finset.mem_univ i)
  exact hj.trans hi

private theorem p29EntryNorm_add_le {m n : ℕ} (A B : P29Matrix m n) :
    p29EntryNorm (A + B) ≤ p29EntryNorm A + p29EntryNorm B := by
  unfold p29EntryNorm
  calc
    (∑ i : Fin m, ∑ j : Fin n, |(A + B) i j|) ≤
        ∑ i : Fin m, ∑ j : Fin n, (|A i j| + |B i j|) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          simpa using abs_add_le (A i j) (B i j)
    _ = (∑ i : Fin m, ∑ j : Fin n, |A i j|) +
        ∑ i : Fin m, ∑ j : Fin n, |B i j| := by
          simp_rw [Finset.sum_add_distrib]

private theorem p29EntryNorm_le_of_entrywise {m n : ℕ}
    (A B : P29Matrix m n) (c : ℝ)
    (h : ∀ i j, |A i j| ≤ c * |B i j|) :
    p29EntryNorm A ≤ c * p29EntryNorm B := by
  unfold p29EntryNorm
  calc
    (∑ i : Fin m, ∑ j : Fin n, |A i j|) ≤
        ∑ i : Fin m, ∑ j : Fin n, c * |B i j| := by
          apply Finset.sum_le_sum
          intro i _
          exact Finset.sum_le_sum (fun j _ => h i j)
    _ = c * ∑ i : Fin m, ∑ j : Fin n, |B i j| := by
          simp_rw [Finset.mul_sum]

private theorem p29EntryNorm_matMul_le (n : ℕ) (A B : P29Matrix n n) :
    p29EntryNorm (p29MatMul A B) ≤
      (n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B := by
  unfold p29EntryNorm p29MatMul
  calc
    (∑ i : Fin n, ∑ j : Fin n, |∑ k : Fin n, A i k * B k j|) ≤
        ∑ i : Fin n, ∑ j : Fin n,
          ∑ _k : Fin n, p29EntryNorm A * p29EntryNorm B := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        |∑ k : Fin n, A i k * B k j| ≤
            ∑ k : Fin n, |A i k * B k j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin n, p29EntryNorm A * p29EntryNorm B := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          exact mul_le_mul (p29AbsEntry_le_norm A i k)
            (p29AbsEntry_le_norm B k j) (abs_nonneg _) (p29EntryNorm_nonneg A)
    _ = (n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

private theorem p29EntryNorm_tripleMul_le (n : ℕ)
    (A B C : P29Matrix n n) :
    p29EntryNorm (p29MatMul (p29MatMul A B) C) ≤
      (n : ℝ) ^ 6 * p29EntryNorm A * p29EntryNorm B * p29EntryNorm C := by
  have hn3 : 0 ≤ (n : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg n) _
  calc
    p29EntryNorm (p29MatMul (p29MatMul A B) C) ≤
        (n : ℝ) ^ 3 * p29EntryNorm (p29MatMul A B) * p29EntryNorm C :=
      p29EntryNorm_matMul_le n (p29MatMul A B) C
    _ ≤ (n : ℝ) ^ 3 *
        ((n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B) *
          p29EntryNorm C := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (p29EntryNorm_matMul_le n A B) hn3)
        (p29EntryNorm_nonneg C)
    _ = (n : ℝ) ^ 6 * p29EntryNorm A * p29EntryNorm B *
          p29EntryNorm C := by ring

private theorem p29MatMul_add_left {n : ℕ} (A B C : P29Matrix n n) :
    p29MatMul (A + B) C = p29MatMul A C + p29MatMul B C := by
  ext i j
  simp [p29MatMul, add_mul, Finset.sum_add_distrib]

private theorem p29MatMul_add_right {n : ℕ} (A B C : P29Matrix n n) :
    p29MatMul A (B + C) = p29MatMul A B + p29MatMul A C := by
  ext i j
  simp [p29MatMul, mul_add, Finset.sum_add_distrib]

private theorem p29CombinedBackwardError_expand {n : ℕ}
    (L D dL dD dU : P29Matrix n n) :
    p29CombinedBackwardError L D dL dD dU =
      p29MatMul (p29MatMul dL D) (p29Transpose L) +
      p29MatMul (p29MatMul L dD) (p29Transpose L) +
      p29MatMul (p29MatMul L D) dU +
      p29MatMul (p29MatMul dL dD) (p29Transpose L) +
      p29MatMul (p29MatMul dL D) dU +
      p29MatMul (p29MatMul L dD) dU +
      p29MatMul (p29MatMul dL dD) dU := by
  unfold p29CombinedBackwardError p29PerturbedLDLT p29LDLT
  simp only [p29MatMul_add_left, p29MatMul_add_right]
  abel

private theorem p29EntryNorm_sum_seven_le {n : ℕ}
    (A B C D E F G : P29Matrix n n) :
    p29EntryNorm (A + B + C + D + E + F + G) ≤
      p29EntryNorm A + p29EntryNorm B + p29EntryNorm C +
        p29EntryNorm D + p29EntryNorm E + p29EntryNorm F + p29EntryNorm G := by
  calc
    p29EntryNorm (A + B + C + D + E + F + G) ≤
        p29EntryNorm (A + B + C + D + E + F) + p29EntryNorm G :=
      p29EntryNorm_add_le _ _
    _ ≤ (p29EntryNorm (A + B + C + D + E) + p29EntryNorm F) +
        p29EntryNorm G := by
      gcongr
      exact p29EntryNorm_add_le _ _
    _ ≤ ((p29EntryNorm (A + B + C + D) + p29EntryNorm E) +
        p29EntryNorm F) + p29EntryNorm G := by
      gcongr
      exact p29EntryNorm_add_le _ _
    _ ≤ (((p29EntryNorm (A + B + C) + p29EntryNorm D) +
        p29EntryNorm E) + p29EntryNorm F) + p29EntryNorm G := by
      gcongr
      exact p29EntryNorm_add_le _ _
    _ ≤ ((((p29EntryNorm (A + B) + p29EntryNorm C) +
        p29EntryNorm D) + p29EntryNorm E) + p29EntryNorm F) +
          p29EntryNorm G := by
      gcongr
      exact p29EntryNorm_add_le _ _
    _ ≤ (((((p29EntryNorm A + p29EntryNorm B) + p29EntryNorm C) +
        p29EntryNorm D) + p29EntryNorm E) + p29EntryNorm F) +
          p29EntryNorm G := by
      gcongr
      exact p29EntryNorm_add_le _ _

private theorem p29EntryNorm_tripleMul_le_of_bounds (n : ℕ)
    (A B C A₀ B₀ C₀ : P29Matrix n n) (a b c : ℝ)
    (ha : p29EntryNorm A ≤ a * p29EntryNorm A₀)
    (hb : p29EntryNorm B ≤ b * p29EntryNorm B₀)
    (hc : p29EntryNorm C ≤ c * p29EntryNorm C₀)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) :
    p29EntryNorm (p29MatMul (p29MatMul A B) C) ≤
      (n : ℝ) ^ 6 * p29EntryNorm A₀ * p29EntryNorm B₀ *
        p29EntryNorm C₀ * (a * b * c) := by
  have hn6 : 0 ≤ (n : ℝ) ^ 6 := pow_nonneg (Nat.cast_nonneg n) _
  have hA₀ : 0 ≤ p29EntryNorm A₀ := p29EntryNorm_nonneg A₀
  have hB₀ : 0 ≤ p29EntryNorm B₀ := p29EntryNorm_nonneg B₀
  have hC₀ : 0 ≤ p29EntryNorm C₀ := p29EntryNorm_nonneg C₀
  calc
    p29EntryNorm (p29MatMul (p29MatMul A B) C) ≤
        (n : ℝ) ^ 6 * p29EntryNorm A * p29EntryNorm B *
          p29EntryNorm C := p29EntryNorm_tripleMul_le n A B C
    _ ≤ (n : ℝ) ^ 6 * (a * p29EntryNorm A₀) *
        p29EntryNorm B * p29EntryNorm C := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ha hn6) (p29EntryNorm_nonneg B))
        (p29EntryNorm_nonneg C)
    _ ≤ (n : ℝ) ^ 6 * (a * p29EntryNorm A₀) *
        (b * p29EntryNorm B₀) * p29EntryNorm C := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb
          (mul_nonneg hn6 (mul_nonneg ha0 hA₀)))
        (p29EntryNorm_nonneg C)
    _ ≤ (n : ℝ) ^ 6 * (a * p29EntryNorm A₀) *
        (b * p29EntryNorm B₀) * (c * p29EntryNorm C₀) := by
      exact mul_le_mul_of_nonneg_left hc
        (mul_nonneg
          (mul_nonneg hn6 (mul_nonneg ha0 hA₀))
          (mul_nonneg hb0 hB₀))
    _ = (n : ℝ) ^ 6 * p29EntryNorm A₀ * p29EntryNorm B₀ *
        p29EntryNorm C₀ * (a * b * c) := by ring

private theorem p29CombinedBackwardError_norm_le {n : ℕ}
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
  let U := p29Transpose L
  let K := (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D * p29EntryNorm U
  have hdLn : p29EntryNorm dL ≤ gamma * p29EntryNorm L :=
    p29EntryNorm_le_of_entrywise dL L gamma hdL
  have hdUn : p29EntryNorm dU ≤ gamma * p29EntryNorm U := by
    exact p29EntryNorm_le_of_entrywise dU U gamma hdU
  have hLrefl : p29EntryNorm L ≤ 1 * p29EntryNorm L := by simp
  have hDrefl : p29EntryNorm D ≤ 1 * p29EntryNorm D := by simp
  have hUrefl : p29EntryNorm U ≤ 1 * p29EntryNorm U := by simp
  let T₁ := p29MatMul (p29MatMul dL D) U
  let T₂ := p29MatMul (p29MatMul L dD) U
  let T₃ := p29MatMul (p29MatMul L D) dU
  let T₄ := p29MatMul (p29MatMul dL dD) U
  let T₅ := p29MatMul (p29MatMul dL D) dU
  let T₆ := p29MatMul (p29MatMul L dD) dU
  let T₇ := p29MatMul (p29MatMul dL dD) dU
  have hT₁ : p29EntryNorm T₁ ≤ K * gamma := by
    simpa [T₁, K] using p29EntryNorm_tripleMul_le_of_bounds n
      dL D U L D U gamma 1 1 hdLn hDrefl hUrefl hgamma (by positivity) (by positivity)
  have hT₂ : p29EntryNorm T₂ ≤ K * eta := by
    simpa [T₂, K] using p29EntryNorm_tripleMul_le_of_bounds n
      L dD U L D U 1 eta 1 hLrefl hdD hUrefl (by positivity) heta (by positivity)
  have hT₃ : p29EntryNorm T₃ ≤ K * gamma := by
    simpa [T₃, K] using p29EntryNorm_tripleMul_le_of_bounds n
      L D dU L D U 1 1 gamma hLrefl hDrefl hdUn (by positivity) (by positivity) hgamma
  have hT₄ : p29EntryNorm T₄ ≤ K * (gamma * eta) := by
    simpa [T₄, K] using p29EntryNorm_tripleMul_le_of_bounds n
      dL dD U L D U gamma eta 1 hdLn hdD hUrefl hgamma heta (by positivity)
  have hT₅ : p29EntryNorm T₅ ≤ K * (gamma * gamma) := by
    simpa [T₅, K] using p29EntryNorm_tripleMul_le_of_bounds n
      dL D dU L D U gamma 1 gamma hdLn hDrefl hdUn hgamma (by positivity) hgamma
  have hT₆ : p29EntryNorm T₆ ≤ K * (eta * gamma) := by
    simpa [T₆, K] using p29EntryNorm_tripleMul_le_of_bounds n
      L dD dU L D U 1 eta gamma hLrefl hdD hdUn (by positivity) heta hgamma
  have hT₇ : p29EntryNorm T₇ ≤ K * (gamma * eta * gamma) := by
    simpa [T₇, K] using p29EntryNorm_tripleMul_le_of_bounds n
      dL dD dU L D U gamma eta gamma hdLn hdD hdUn hgamma heta hgamma
  calc
    p29EntryNorm (p29CombinedBackwardError L D dL dD dU) =
        p29EntryNorm (T₁ + T₂ + T₃ + T₄ + T₅ + T₆ + T₇) := by
      rw [p29CombinedBackwardError_expand]
    _ ≤ p29EntryNorm T₁ + p29EntryNorm T₂ + p29EntryNorm T₃ +
          p29EntryNorm T₄ + p29EntryNorm T₅ + p29EntryNorm T₆ +
            p29EntryNorm T₇ := p29EntryNorm_sum_seven_le _ _ _ _ _ _ _
    _ ≤ K * gamma + K * eta + K * gamma + K * (gamma * eta) +
          K * (gamma * gamma) + K * (eta * gamma) +
            K * (gamma * eta * gamma) := by gcongr
    _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        p29EntryNorm (p29Transpose L) *
          (gamma * (1 + eta) * (1 + gamma) +
            eta * (1 + gamma) + gamma) := by
      dsimp [K, U]
      ring

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
  let fp' := p29AsFPModel fp
  have hvalid' : NumStability.gammaValid fp' n := by
    simpa [fp', p29AsFPModel, NumStability.gammaValid, P29GammaValid] using hvalid
  have hgamma : 0 ≤ p29Gamma fp.u n := by
    simpa [fp', p29AsFPModel, NumStability.gamma, p29Gamma] using
      (NumStability.gamma_nonneg fp' hvalid')
  obtain ⟨ΔL, hΔL', hforward'⟩ :=
    NumStability.forwardSub_backward_error fp' n L b hdiag hlower hvalid'
  have hΔL : ∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j| := by
    simpa [fp', p29AsFPModel, NumStability.gamma, p29Gamma] using hΔL'
  have hforward : ∀ i, ∑ j : Fin n,
      (L i j + ΔL i j) * p29ForwardSub fp n L b j = b i := by
    rw [p29ForwardSub_eq fp n L b]
    exact hforward'
  have hUdiag : ∀ i, p29Transpose L i i ≠ 0 := by
    intro i
    simpa [p29Transpose] using hdiag i
  have hUupper : ∀ i j : Fin n, j.val < i.val → p29Transpose L i j = 0 := by
    intro i j hij
    simpa [p29Transpose] using hlower j i hij
  obtain ⟨ΔU, hΔU', hback'⟩ :=
    NumStability.backSub_backward_error fp' n (p29Transpose L) z
      hUdiag hUupper hvalid'
  have hΔU : ∀ i j, |ΔU i j| ≤
      p29Gamma fp.u n * |p29Transpose L i j| := by
    simpa [fp', p29AsFPModel, NumStability.gamma, p29Gamma] using hΔU'
  have hback : ∀ i, ∑ j : Fin n,
      (p29Transpose L i j + ΔU i j) *
        p29BackSub fp n (p29Transpose L) z j = z i := by
    rw [p29BackSub_eq fp n (p29Transpose L) z]
    exact hback'
  obtain ⟨ΔD, hΔD, hmiddle⟩ := hDsolve
  let x := p29BackSub fp n (p29Transpose L) z
  have hchain : ∀ i, ∑ j : Fin n,
      p29PerturbedLDLT L D ΔL ΔD ΔU i j * x j = b i := by
    intro i
    calc
      (∑ j : Fin n, p29PerturbedLDLT L D ΔL ΔD ΔU i j * x j) =
          ∑ j : Fin n,
            (∑ q : Fin n, ∑ p : Fin n,
              (L i p + ΔL i p) * (D p q + ΔD p q) *
                (p29Transpose L q j + ΔU q j)) * x j := by
        simp only [p29PerturbedLDLT, p29MatMul, Matrix.add_apply]
        simp_rw [Finset.sum_mul]
      _ = ∑ p : Fin n, (L i p + ΔL i p) *
            (∑ q : Fin n, (D p q + ΔD p q) *
              (∑ j : Fin n,
                (p29Transpose L q j + ΔU q j) * x j)) := by
        let f : Fin n → Fin n → Fin n → ℝ := fun p q j =>
          (L i p + ΔL i p) * (D p q + ΔD p q) *
            (p29Transpose L q j + ΔU q j) * x j
        have hreorder :
            (∑ j : Fin n, ∑ q : Fin n, ∑ p : Fin n, f p q j) =
              ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, f p q j := by
          calc
            (∑ j : Fin n, ∑ q : Fin n, ∑ p : Fin n, f p q j) =
                ∑ q : Fin n, ∑ j : Fin n, ∑ p : Fin n, f p q j :=
              Finset.sum_comm
            _ = ∑ q : Fin n, ∑ p : Fin n, ∑ j : Fin n, f p q j := by
              apply Finset.sum_congr rfl
              intro q _
              exact Finset.sum_comm
            _ = ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, f p q j :=
              Finset.sum_comm
        simpa [f, Finset.sum_mul, Finset.mul_sum, mul_assoc] using hreorder
      _ = ∑ p : Fin n, (L i p + ΔL i p) *
            (∑ q : Fin n, (D p q + ΔD p q) * z q) := by
        apply Finset.sum_congr rfl
        intro p _
        congr 1
        apply Finset.sum_congr rfl
        intro q _
        rw [show (∑ j : Fin n,
          (p29Transpose L q j + ΔU q j) * x j) = z q by
            simpa [x] using hback q]
      _ = ∑ p : Fin n, (L i p + ΔL i p) *
            p29ForwardSub fp n L b p := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hmiddle p]
      _ = b i := hforward i
  let F := p29TotalBackwardError E0 L D ΔL ΔD ΔU
  refine ⟨ΔL, ΔD, ΔU, F, hΔL, hΔD, hΔU, rfl, ?_, ?_⟩
  · intro i
    calc
      (∑ j : Fin n, (A i j + F i j) * x j) =
          ∑ j : Fin n, p29PerturbedLDLT L D ΔL ΔD ΔU i j * x j := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        have hf := congrFun (congrFun hfactor i) j
        dsimp [F, p29TotalBackwardError, p29CombinedBackwardError] at ⊢
        simp only [Matrix.add_apply, Matrix.sub_apply] at hf ⊢
        rw [hf]
        ring
      _ = b i := hchain i
  · have hcombined := p29CombinedBackwardError_norm_le
        L D ΔL ΔD ΔU (p29Gamma fp.u n) eta hgamma heta hΔL hΔD hΔU
    calc
      p29EntryNorm F ≤ p29EntryNorm E0 +
          p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) := by
        dsimp [F, p29TotalBackwardError]
        exact p29EntryNorm_add_le _ _
      _ ≤ factorEta * p29EntryNorm A +
          ((n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
            p29EntryNorm (p29Transpose L) *
              (p29Gamma fp.u n * (1 + eta) * (1 + p29Gamma fp.u n) +
                eta * (1 + p29Gamma fp.u n) + p29Gamma fp.u n)) :=
        add_le_add hE0 hcombined
      _ = p29TotalBackwardBound fp n eta factorEta A L D := rfl

end HighamBench
