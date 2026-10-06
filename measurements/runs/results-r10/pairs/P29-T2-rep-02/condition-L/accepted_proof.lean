import HighamBench.P29Definitions
import NumStability.Algorithms.LinearSystems.Triangular

namespace HighamBench

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
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg

private lemma p29_forwardSubSteps_eq
    (fp : P29FPModel) (n : ℕ) (L : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p29ForwardSubSteps fp n L b k hk x =
        NumStability.fl_forwardSub_steps (p29AsFPModel fp) n L b k hk x := by
  intro k
  induction k with
  | zero => intro hk x; rfl
  | succ k ih =>
      intro hk x
      simp only [p29ForwardSubSteps, NumStability.fl_forwardSub_steps]
      apply ih

private lemma p29_backSubSteps_eq
    (fp : P29FPModel) (n : ℕ) (U : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p29BackSubSteps fp n U b k hk x =
        NumStability.fl_backSub_steps (p29AsFPModel fp) n U b k hk x := by
  intro k
  induction k with
  | zero => intro hk x; rfl
  | succ k ih =>
      intro hk x
      simp only [p29BackSubSteps, NumStability.fl_backSub_steps]
      apply ih

private lemma p29_forwardSub_backward_error
    (fp : P29FPModel) (n : ℕ) (L : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P29GammaValid fp.u n) :
    ∃ ΔL : P29Matrix n n,
      (∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|) ∧
      ∀ i, ∑ j : Fin n,
        (L i j + ΔL i j) * p29ForwardSub fp n L b j = b i := by
  let fp' := p29AsFPModel fp
  have hv : NumStability.gammaValid fp' n := by
    simpa [NumStability.gammaValid, fp', p29AsFPModel] using hvalid
  obtain ⟨ΔL, hΔL, heq⟩ :=
    NumStability.forwardSub_backward_error fp' n L b hdiag hlower hv
  refine ⟨ΔL, ?_, ?_⟩
  · simpa [p29Gamma, NumStability.gamma, fp', p29AsFPModel] using hΔL
  · simpa only [p29ForwardSub, NumStability.fl_forwardSub,
      p29_forwardSubSteps_eq, fp'] using heq

private lemma p29_backSub_backward_error
    (fp : P29FPModel) (n : ℕ) (U : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P29GammaValid fp.u n) :
    ∃ ΔU : P29Matrix n n,
      (∀ i j, |ΔU i j| ≤ p29Gamma fp.u n * |U i j|) ∧
      ∀ i, ∑ j : Fin n,
        (U i j + ΔU i j) * p29BackSub fp n U b j = b i := by
  let fp' := p29AsFPModel fp
  have hv : NumStability.gammaValid fp' n := by
    simpa [NumStability.gammaValid, fp', p29AsFPModel] using hvalid
  obtain ⟨ΔU, hΔU, heq⟩ :=
    NumStability.backSub_backward_error fp' n U b hdiag hupper hv
  refine ⟨ΔU, ?_, ?_⟩
  · simpa [p29Gamma, NumStability.gamma, fp', p29AsFPModel] using hΔU
  · simpa only [p29BackSub, NumStability.fl_backSub,
      p29_backSubSteps_eq, fp'] using heq

private lemma p29EntryNorm_nonneg {m n : ℕ} (X : P29Matrix m n) :
    0 ≤ p29EntryNorm X := by
  unfold p29EntryNorm
  positivity

private lemma p29EntryNorm_add_le {m n : ℕ} (X Y : P29Matrix m n) :
    p29EntryNorm (X + Y) ≤ p29EntryNorm X + p29EntryNorm Y := by
  unfold p29EntryNorm
  simp only [Matrix.add_apply]
  calc
    (∑ i : Fin m, ∑ j : Fin n, |X i j + Y i j|) ≤
        ∑ i : Fin m, ∑ j : Fin n, (|X i j| + |Y i j|) := by
          gcongr with i j
          exact abs_add_le _ _
    _ = (∑ i : Fin m, ∑ j : Fin n, |X i j|) +
        ∑ i : Fin m, ∑ j : Fin n, |Y i j| := by
          simp_rw [Finset.sum_add_distrib]

private lemma p29EntryNorm_le_of_entry {m n : ℕ}
    (X Y : P29Matrix m n) (c : ℝ)
    (h : ∀ i j, |X i j| ≤ c * |Y i j|) :
    p29EntryNorm X ≤ c * p29EntryNorm Y := by
  unfold p29EntryNorm
  calc
    (∑ i : Fin m, ∑ j : Fin n, |X i j|) ≤
        ∑ i : Fin m, ∑ j : Fin n, c * |Y i j| := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact h i j
    _ = c * ∑ i : Fin m, ∑ j : Fin n, |Y i j| := by
          simp_rw [Finset.mul_sum]

private lemma p29Entry_abs_le_norm {m n : ℕ}
    (X : P29Matrix m n) (i : Fin m) (j : Fin n) :
    |X i j| ≤ p29EntryNorm X := by
  unfold p29EntryNorm
  calc
    |X i j| ≤ ∑ j' : Fin n, |X i j'| := by
      exact Finset.single_le_sum
        (f := fun j' : Fin n => |X i j'|) (s := Finset.univ)
        (fun j' _ => abs_nonneg (X i j')) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin m, ∑ j' : Fin n, |X i' j'| := by
      exact Finset.single_le_sum
        (f := fun i' : Fin m => ∑ j' : Fin n, |X i' j'|)
        (s := Finset.univ)
        (fun i' _ => Finset.sum_nonneg (fun j' _ => abs_nonneg (X i' j')))
        (Finset.mem_univ i)

private lemma p29EntryNorm_matMul_le (n : ℕ)
    (X Y : P29Matrix n n) :
    p29EntryNorm (p29MatMul X Y) ≤
      (n : ℝ) ^ 3 * p29EntryNorm X * p29EntryNorm Y := by
  have hterm : ∀ i j k : Fin n,
      |X i k * Y k j| ≤ p29EntryNorm X * p29EntryNorm Y := by
    intro i j k
    rw [abs_mul]
    exact mul_le_mul (p29Entry_abs_le_norm X i k)
      (p29Entry_abs_le_norm Y k j) (abs_nonneg _) (p29EntryNorm_nonneg X)
  unfold p29EntryNorm p29MatMul
  calc
    (∑ i : Fin n, ∑ j : Fin n, |∑ k : Fin n, X i k * Y k j|) ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, |X i k * Y k j| := by
          gcongr with i j
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ∑ _k : Fin n,
        p29EntryNorm X * p29EntryNorm Y := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          apply Finset.sum_le_sum
          intro k hk
          exact hterm i j k
    _ = (n : ℝ) ^ 3 * p29EntryNorm X * p29EntryNorm Y := by
          simp [Finset.card_fin]
          ring

private lemma p29EntryNorm_tripleMul_le (n : ℕ)
    (X Y Z : P29Matrix n n) :
    p29EntryNorm (p29MatMul (p29MatMul X Y) Z) ≤
      (n : ℝ) ^ 6 * p29EntryNorm X * p29EntryNorm Y * p29EntryNorm Z := by
  calc
    p29EntryNorm (p29MatMul (p29MatMul X Y) Z) ≤
        (n : ℝ) ^ 3 * p29EntryNorm (p29MatMul X Y) * p29EntryNorm Z :=
      p29EntryNorm_matMul_le n _ _
    _ ≤ (n : ℝ) ^ 3 *
        ((n : ℝ) ^ 3 * p29EntryNorm X * p29EntryNorm Y) *
          p29EntryNorm Z := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (p29EntryNorm_matMul_le n X Y) (by positivity))
        (p29EntryNorm_nonneg Z)
    _ = (n : ℝ) ^ 6 * p29EntryNorm X * p29EntryNorm Y *
        p29EntryNorm Z := by ring

private lemma p29CombinedBackwardError_eq {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) :
    p29CombinedBackwardError L D ΔL ΔD ΔU =
      p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L D) ΔU := by
  have hadd_left : ∀ (X Y Z : P29Matrix n n),
      p29MatMul (X + Y) Z = p29MatMul X Z + p29MatMul Y Z := by
    intro X Y Z
    ext i j
    simp [p29MatMul, add_mul, Finset.sum_add_distrib]
  have hadd_right : ∀ (X Y Z : P29Matrix n n),
      p29MatMul X (Y + Z) = p29MatMul X Y + p29MatMul X Z := by
    intro X Y Z
    ext i j
    simp [p29MatMul, mul_add, Finset.sum_add_distrib]
  simp only [p29CombinedBackwardError, p29PerturbedLDLT, p29LDLT,
    hadd_left, hadd_right]
  abel

private lemma p29MatMul_mulVec {n : ℕ}
    (X Y : P29Matrix n n) (v : Fin n → ℝ) (i : Fin n) :
    (∑ j : Fin n, p29MatMul X Y i j * v j) =
      ∑ k : Fin n, X i k * (∑ j : Fin n, Y k j * v j) := by
  unfold p29MatMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma p29Gamma_nonneg (fp : P29FPModel) (n : ℕ)
    (hvalid : P29GammaValid fp.u n) :
    0 ≤ p29Gamma fp.u n := by
  unfold p29Gamma P29GammaValid at *
  exact div_nonneg
    (mul_nonneg (Nat.cast_nonneg n) fp.u_nonneg)
    (le_of_lt (sub_pos.mpr hvalid))

private lemma p29CombinedBackwardError_norm_le
    (fp : P29FPModel) (n : ℕ) (eta : ℝ)
    (L D ΔL ΔD ΔU : P29Matrix n n)
    (hvalid : P29GammaValid fp.u n) (heta : 0 ≤ eta)
    (hΔL : ∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|)
    (hΔD : p29EntryNorm ΔD ≤ eta * p29EntryNorm D)
    (hΔU : ∀ i j, |ΔU i j| ≤
      p29Gamma fp.u n * |p29Transpose L i j|) :
    p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p29SolveBackwardFactor fp n eta L D := by
  let g := p29Gamma fp.u n
  let N := (n : ℝ) ^ 6
  have hg : 0 ≤ g := p29Gamma_nonneg fp n hvalid
  have hN : 0 ≤ N := by positivity
  have hNL : 0 ≤ p29EntryNorm L := p29EntryNorm_nonneg L
  have hND : 0 ≤ p29EntryNorm D := p29EntryNorm_nonneg D
  have hNT : 0 ≤ p29EntryNorm (p29Transpose L) :=
    p29EntryNorm_nonneg (p29Transpose L)
  have hNDadd : 0 ≤ p29EntryNorm (D + ΔD) := p29EntryNorm_nonneg _
  have hNUadd : 0 ≤ p29EntryNorm (p29Transpose L + ΔU) :=
    p29EntryNorm_nonneg _
  have hΔLn : p29EntryNorm ΔL ≤ g * p29EntryNorm L := by
    exact p29EntryNorm_le_of_entry ΔL L g hΔL
  have hΔUn : p29EntryNorm ΔU ≤
      g * p29EntryNorm (p29Transpose L) := by
    exact p29EntryNorm_le_of_entry ΔU (p29Transpose L) g hΔU
  have hLadd : p29EntryNorm (L + ΔL) ≤
      (1 + g) * p29EntryNorm L := by
    calc
      p29EntryNorm (L + ΔL) ≤
          p29EntryNorm L + p29EntryNorm ΔL := p29EntryNorm_add_le L ΔL
      _ ≤ p29EntryNorm L + g * p29EntryNorm L := by linarith
      _ = (1 + g) * p29EntryNorm L := by ring
  have hDadd : p29EntryNorm (D + ΔD) ≤
      (1 + eta) * p29EntryNorm D := by
    calc
      p29EntryNorm (D + ΔD) ≤
          p29EntryNorm D + p29EntryNorm ΔD := p29EntryNorm_add_le D ΔD
      _ ≤ p29EntryNorm D + eta * p29EntryNorm D := by linarith
      _ = (1 + eta) * p29EntryNorm D := by ring
  have hUadd : p29EntryNorm (p29Transpose L + ΔU) ≤
      (1 + g) * p29EntryNorm (p29Transpose L) := by
    calc
      p29EntryNorm (p29Transpose L + ΔU) ≤
          p29EntryNorm (p29Transpose L) + p29EntryNorm ΔU :=
        p29EntryNorm_add_le _ _
      _ ≤ p29EntryNorm (p29Transpose L) +
          g * p29EntryNorm (p29Transpose L) := by linarith
      _ = (1 + g) * p29EntryNorm (p29Transpose L) := by ring
  let T1 := p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU)
  let T2 := p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU)
  let T3 := p29MatMul (p29MatMul L D) ΔU
  have hT1 : p29EntryNorm T1 ≤
      N * (g * p29EntryNorm L) * ((1 + eta) * p29EntryNorm D) *
        ((1 + g) * p29EntryNorm (p29Transpose L)) := by
    calc
      p29EntryNorm T1 ≤ N * p29EntryNorm ΔL * p29EntryNorm (D + ΔD) *
          p29EntryNorm (p29Transpose L + ΔU) := by
        exact p29EntryNorm_tripleMul_le n _ _ _
      _ ≤ N * (g * p29EntryNorm L) * ((1 + eta) * p29EntryNorm D) *
          ((1 + g) * p29EntryNorm (p29Transpose L)) := by
        gcongr
  have hT2 : p29EntryNorm T2 ≤
      N * p29EntryNorm L * (eta * p29EntryNorm D) *
        ((1 + g) * p29EntryNorm (p29Transpose L)) := by
    calc
      p29EntryNorm T2 ≤ N * p29EntryNorm L * p29EntryNorm ΔD *
          p29EntryNorm (p29Transpose L + ΔU) := by
        exact p29EntryNorm_tripleMul_le n _ _ _
      _ ≤ N * p29EntryNorm L * (eta * p29EntryNorm D) *
          ((1 + g) * p29EntryNorm (p29Transpose L)) := by
        gcongr
  have hT3 : p29EntryNorm T3 ≤
      N * p29EntryNorm L * p29EntryNorm D *
        (g * p29EntryNorm (p29Transpose L)) := by
    calc
      p29EntryNorm T3 ≤ N * p29EntryNorm L * p29EntryNorm D *
          p29EntryNorm ΔU := by
        exact p29EntryNorm_tripleMul_le n _ _ _
      _ ≤ N * p29EntryNorm L * p29EntryNorm D *
          (g * p29EntryNorm (p29Transpose L)) := by
        gcongr
  rw [p29CombinedBackwardError_eq]
  change p29EntryNorm (T1 + T2 + T3) ≤ _
  calc
    p29EntryNorm (T1 + T2 + T3) ≤
        p29EntryNorm (T1 + T2) + p29EntryNorm T3 := p29EntryNorm_add_le _ _
    _ ≤ (p29EntryNorm T1 + p29EntryNorm T2) + p29EntryNorm T3 := by
      gcongr
      exact p29EntryNorm_add_le _ _
    _ ≤
        (N * (g * p29EntryNorm L) * ((1 + eta) * p29EntryNorm D) *
          ((1 + g) * p29EntryNorm (p29Transpose L)) +
        N * p29EntryNorm L * (eta * p29EntryNorm D) *
          ((1 + g) * p29EntryNorm (p29Transpose L))) +
        N * p29EntryNorm L * p29EntryNorm D *
          (g * p29EntryNorm (p29Transpose L)) := by linarith
    _ = p29SolveBackwardFactor fp n eta L D := by
      unfold p29SolveBackwardFactor
      dsimp [N, g]
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
  obtain ⟨ΔL, hΔL, hforward⟩ :=
    p29_forwardSub_backward_error fp n L b hdiag hlower hvalid
  obtain ⟨ΔD, hΔD, hblock⟩ := hDsolve
  have hdiagT : ∀ i, p29Transpose L i i ≠ 0 := by
    intro i
    exact hdiag i
  have hupperT : ∀ i j : Fin n, j.val < i.val →
      p29Transpose L i j = 0 := by
    intro i j hji
    exact hlower j i hji
  obtain ⟨ΔU, hΔU, hback⟩ :=
    p29_backSub_backward_error fp n (p29Transpose L) z
      hdiagT hupperT hvalid
  let F := p29TotalBackwardError E0 L D ΔL ΔD ΔU
  refine ⟨ΔL, ΔD, ΔU, F, hΔL, hΔD, hΔU, rfl, ?_, ?_⟩
  · have hperturbed : ∀ i, ∑ j : Fin n,
        p29PerturbedLDLT L D ΔL ΔD ΔU i j *
          p29BackSub fp n (p29Transpose L) z j = b i := by
      intro i
      change (∑ j : Fin n,
        p29MatMul (p29MatMul (L + ΔL) (D + ΔD))
          (p29Transpose L + ΔU) i j *
            p29BackSub fp n (p29Transpose L) z j) = b i
      rw [p29MatMul_mulVec]
      simp only [Matrix.add_apply]
      simp_rw [hback]
      rw [p29MatMul_mulVec]
      simp only [Matrix.add_apply]
      simp_rw [hblock]
      exact hforward i
    have hAF : A + F = p29PerturbedLDLT L D ΔL ΔD ΔU := by
      ext i j
      have hf := congrFun (congrFun hfactor i) j
      simp only [Matrix.add_apply] at hf
      simp only [F, p29TotalBackwardError, p29CombinedBackwardError,
        Matrix.add_apply, Matrix.sub_apply]
      rw [hf]
      ring
    intro i
    calc
      (∑ j : Fin n, (A i j + F i j) *
          p29BackSub fp n (p29Transpose L) z j) =
          ∑ j : Fin n, p29PerturbedLDLT L D ΔL ΔD ΔU i j *
            p29BackSub fp n (p29Transpose L) z j := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [show A i j + F i j =
                p29PerturbedLDLT L D ΔL ΔD ΔU i j from
                  congrFun (congrFun hAF i) j]
      _ = b i := hperturbed i
  · calc
      p29EntryNorm F = p29EntryNorm
          (E0 + p29CombinedBackwardError L D ΔL ΔD ΔU) := rfl
      _ ≤ p29EntryNorm E0 +
          p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) :=
        p29EntryNorm_add_le _ _
      _ ≤ factorEta * p29EntryNorm A +
          p29SolveBackwardFactor fp n eta L D := by
        exact add_le_add hE0
          (p29CombinedBackwardError_norm_le fp n eta L D ΔL ΔD ΔU
            hvalid heta hΔL hΔD hΔU)
      _ = p29TotalBackwardBound fp n eta factorEta A L D := rfl

end HighamBench
