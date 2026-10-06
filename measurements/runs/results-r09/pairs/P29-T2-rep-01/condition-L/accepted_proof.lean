import HighamBench.P29Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution

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

lemma p29AsFPModel_gamma (fp : P29FPModel) (n : ℕ) :
    NumStability.gamma (p29AsFPModel fp) n = p29Gamma fp.u n := by
  rfl

lemma p29AsFPModel_forwardSub (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) :
    NumStability.fl_forwardSub (p29AsFPModel fp) n L b =
      p29ForwardSub fp n L b := by
  have hsteps : ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      NumStability.fl_forwardSub_steps (p29AsFPModel fp) n L b k hk x =
        p29ForwardSubSteps fp n L b k hk x := by
    intro k
    induction k with
    | zero => intro hk x; rfl
    | succ k ih =>
        intro hk x
        simp only [NumStability.fl_forwardSub_steps, p29ForwardSubSteps]
        apply ih
  exact hsteps n (le_refl n) (fun _ => 0)

lemma p29AsFPModel_backSub (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) :
    NumStability.fl_backSub (p29AsFPModel fp) n U b =
      p29BackSub fp n U b := by
  have hsteps : ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      NumStability.fl_backSub_steps (p29AsFPModel fp) n U b k hk x =
        p29BackSubSteps fp n U b k hk x := by
    intro k
    induction k with
    | zero => intro hk x; rfl
    | succ k ih =>
        intro hk x
        simp only [NumStability.fl_backSub_steps, p29BackSubSteps]
        apply ih
  exact hsteps n (le_refl n) (fun _ => 0)

lemma p29EntryNorm_nonneg {m n : ℕ} (A : P29Matrix m n) :
    0 ≤ p29EntryNorm A := by
  unfold p29EntryNorm
  positivity

lemma p29EntryNorm_add_le {m n : ℕ} (A B : P29Matrix m n) :
    p29EntryNorm (A + B) ≤ p29EntryNorm A + p29EntryNorm B := by
  simp only [p29EntryNorm, Matrix.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  exact abs_add_le (A i j) (B i j)

lemma p29EntryNorm_sub_le {m n : ℕ} (A B : P29Matrix m n) :
    p29EntryNorm (A - B) ≤ p29EntryNorm A + p29EntryNorm B := by
  simpa [sub_eq_add_neg, p29EntryNorm] using p29EntryNorm_add_le A (-B)

lemma p29EntryNorm_mono {m n : ℕ} {A B : P29Matrix m n}
    (h : ∀ i j, |A i j| ≤ |B i j|) :
    p29EntryNorm A ≤ p29EntryNorm B := by
  unfold p29EntryNorm
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  exact h i j

lemma p29EntryNorm_componentwise {m n : ℕ} {A B : P29Matrix m n}
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, |A i j| ≤ c * |B i j|) :
    p29EntryNorm A ≤ c * p29EntryNorm B := by
  unfold p29EntryNorm
  calc
    ∑ i : Fin m, ∑ j : Fin n, |A i j|
        ≤ ∑ i : Fin m, ∑ j : Fin n, c * |B i j| := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact h i j
    _ = c * ∑ i : Fin m, ∑ j : Fin n, |B i j| := by
          simp only [Finset.mul_sum]

lemma p29EntryNorm_transpose {m n : ℕ} (A : P29Matrix m n) :
    p29EntryNorm (p29Transpose A) = p29EntryNorm A := by
  unfold p29EntryNorm p29Transpose
  rw [Finset.sum_comm]

lemma p29_abs_entry_le_norm {m n : ℕ} (A : P29Matrix m n)
    (i : Fin m) (j : Fin n) : |A i j| ≤ p29EntryNorm A := by
  unfold p29EntryNorm
  calc
    |A i j| ≤ (∑ j' ∈ Finset.univ.erase j, |A i j'|) + |A i j| := by
      have hs : 0 ≤ ∑ j' ∈ Finset.univ.erase j, |A i j'| := by
        exact Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    _ = ∑ j' : Fin n, |A i j'| := by
      exact Finset.sum_erase_add Finset.univ (fun j' => |A i j'|)
        (Finset.mem_univ j)
    _ ≤ (∑ i' ∈ Finset.univ.erase i, ∑ j' : Fin n, |A i' j'|) +
          ∑ j' : Fin n, |A i j'| := by
      have hs : 0 ≤ ∑ i' ∈ Finset.univ.erase i,
          ∑ j' : Fin n, |A i' j'| := by
        exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          abs_nonneg _
      linarith
    _ = ∑ i' : Fin m, ∑ j' : Fin n, |A i' j'| := by
      exact Finset.sum_erase_add Finset.univ
        (fun i' => ∑ j' : Fin n, |A i' j'|) (Finset.mem_univ i)

lemma p29EntryNorm_matMul_le (n : ℕ) (A B : P29Matrix n n) :
    p29EntryNorm (p29MatMul A B) ≤
      (n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B := by
  have hpoint : ∀ i j, |p29MatMul A B i j| ≤
      (n : ℝ) * (p29EntryNorm A * p29EntryNorm B) := by
    intro i j
    calc
      |p29MatMul A B i j|
          ≤ ∑ k : Fin n, |A i k * B k j| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, p29EntryNorm A * p29EntryNorm B := by
            apply Finset.sum_le_sum
            intro k hk
            rw [abs_mul]
            exact mul_le_mul (p29_abs_entry_le_norm A i k)
              (p29_abs_entry_le_norm B k j) (abs_nonneg _)
              (p29EntryNorm_nonneg A)
      _ = (n : ℝ) * (p29EntryNorm A * p29EntryNorm B) := by simp
  unfold p29EntryNorm
  calc
    ∑ i : Fin n, ∑ j : Fin n, |p29MatMul A B i j|
        ≤ ∑ _i : Fin n, ∑ _j : Fin n,
            (n : ℝ) * (p29EntryNorm A * p29EntryNorm B) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact hpoint i j
    _ = (n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B := by
          simp
          ring

lemma p29EntryNorm_tripleMul_le (n : ℕ) (A B C : P29Matrix n n) :
    p29EntryNorm (p29MatMul (p29MatMul A B) C) ≤
      (n : ℝ) ^ 6 * p29EntryNorm A * p29EntryNorm B * p29EntryNorm C := by
  calc
    p29EntryNorm (p29MatMul (p29MatMul A B) C)
        ≤ (n : ℝ) ^ 3 * p29EntryNorm (p29MatMul A B) *
            p29EntryNorm C := p29EntryNorm_matMul_le n _ _
    _ ≤ (n : ℝ) ^ 3 *
            ((n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B) *
            p29EntryNorm C := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (p29EntryNorm_matMul_le n A B)
              (by positivity)) (p29EntryNorm_nonneg C)
    _ = (n : ℝ) ^ 6 * p29EntryNorm A * p29EntryNorm B *
            p29EntryNorm C := by ring

lemma p29MatMul_vec_assoc (n : ℕ) (A B : P29Matrix n n)
    (x : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin n, p29MatMul A B i j * x j =
      ∑ k : Fin n, A i k * (∑ j : Fin n, B k j * x j) := by
  unfold p29MatMul
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma p29TripleMul_vec_assoc (n : ℕ) (A B C : P29Matrix n n)
    (x : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin n, p29MatMul (p29MatMul A B) C i j * x j =
      ∑ k : Fin n, A i k *
        (∑ q : Fin n, B k q * (∑ j : Fin n, C q j * x j)) := by
  rw [p29MatMul_vec_assoc]
  exact p29MatMul_vec_assoc n A B
    (fun q => ∑ j : Fin n, C q j * x j) i

lemma p29MatMul_add_left {n : ℕ} (A B C : P29Matrix n n) :
    p29MatMul (A + B) C = p29MatMul A C + p29MatMul B C := by
  funext i j
  simp only [p29MatMul, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

lemma p29MatMul_add_right {n : ℕ} (A B C : P29Matrix n n) :
    p29MatMul A (B + C) = p29MatMul A B + p29MatMul A C := by
  funext i j
  simp only [p29MatMul, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

lemma p29CombinedBackwardError_eq {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) :
    p29CombinedBackwardError L D ΔL ΔD ΔU =
      p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L D) ΔU := by
  unfold p29CombinedBackwardError p29PerturbedLDLT p29LDLT
  rw [p29MatMul_add_left, p29MatMul_add_left,
    p29MatMul_add_right L D ΔD, p29MatMul_add_left,
    p29MatMul_add_right (p29MatMul L D)]
  abel

lemma p29EntryNorm_add_three_le {m n : ℕ}
    (A B C : P29Matrix m n) :
    p29EntryNorm (A + B + C) ≤
      p29EntryNorm A + p29EntryNorm B + p29EntryNorm C := by
  exact le_trans (p29EntryNorm_add_le (A + B) C)
    (add_le_add (p29EntryNorm_add_le A B) (le_refl _))

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
  let nfp : NumStability.FPModel := p29AsFPModel fp
  have hnfp : NumStability.gammaValid nfp n := by
    exact hvalid
  obtain ⟨ΔL, hΔL, hforward⟩ :=
    NumStability.forwardSub_backward_error nfp n L b hdiag hlower hnfp
  change P29Matrix n n at ΔL
  have hΔL' : ∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j| := by
    simpa only [nfp, p29AsFPModel_gamma] using hΔL
  have hforward' : ∀ i, ∑ j : Fin n, (L i j + ΔL i j) *
      p29ForwardSub fp n L b j = b i := by
    simpa only [nfp, p29AsFPModel_forwardSub] using hforward
  have htdiag : ∀ i, p29Transpose L i i ≠ 0 := by
    intro i
    exact hdiag i
  have htupper : ∀ i j : Fin n, j.val < i.val →
      p29Transpose L i j = 0 := by
    intro i j hij
    exact hlower j i hij
  obtain ⟨ΔU, hΔU, hback⟩ :=
    NumStability.backSub_backward_error nfp n (p29Transpose L) z
      htdiag htupper hnfp
  change P29Matrix n n at ΔU
  have hΔU' : ∀ i j, |ΔU i j| ≤
      p29Gamma fp.u n * |p29Transpose L i j| := by
    simpa only [nfp, p29AsFPModel_gamma] using hΔU
  have hback' : ∀ i, ∑ j : Fin n,
      (p29Transpose L i j + ΔU i j) *
        p29BackSub fp n (p29Transpose L) z j = z i := by
    simpa only [nfp, p29AsFPModel_backSub] using hback
  obtain ⟨ΔD, hΔD, hblock⟩ := hDsolve
  let F : P29Matrix n n := p29TotalBackwardError E0 L D ΔL ΔD ΔU
  refine ⟨ΔL, ΔD, ΔU, F, hΔL', hΔD, hΔU', rfl, ?_, ?_⟩
  · intro i
    let x := p29BackSub fp n (p29Transpose L) z
    have hAF : ∀ r s, A r s + F r s =
        p29PerturbedLDLT L D ΔL ΔD ΔU r s := by
      intro r s
      have hfactor_rs := congrFun (congrFun hfactor r) s
      simp only [p29LDLT, Matrix.add_apply] at hfactor_rs
      simp only [F, p29TotalBackwardError, p29CombinedBackwardError,
        p29LDLT, Matrix.add_apply, Matrix.sub_apply]
      rw [hfactor_rs]
      ring
    calc
      ∑ j : Fin n, (A i j + F i j) * x j =
          ∑ j : Fin n,
            p29PerturbedLDLT L D ΔL ΔD ΔU i j * x j := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hAF]
      _ = ∑ k : Fin n, (L i k + ΔL i k) *
            (∑ q : Fin n, (D k q + ΔD k q) *
              (∑ j : Fin n, (p29Transpose L q j + ΔU q j) * x j)) := by
              exact p29TripleMul_vec_assoc n (L + ΔL) (D + ΔD)
                (p29Transpose L + ΔU) x i
      _ = ∑ k : Fin n, (L i k + ΔL i k) *
            (∑ q : Fin n, (D k q + ΔD k q) * z q) := by
              apply Finset.sum_congr rfl
              intro k hk
              congr 1
              apply Finset.sum_congr rfl
              intro q hq
              rw [show (∑ j : Fin n,
                (p29Transpose L q j + ΔU q j) * x j) = z q from hback' q]
      _ = ∑ k : Fin n, (L i k + ΔL i k) *
            p29ForwardSub fp n L b k := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [hblock k]
      _ = b i := hforward' i
  · let γ := p29Gamma fp.u n
    let U : P29Matrix n n := p29Transpose L
    have hγ : 0 ≤ γ := by
      simpa only [γ, nfp, p29AsFPModel_gamma] using
        (NumStability.gamma_nonneg nfp hnfp)
    have hL0 : 0 ≤ p29EntryNorm L := p29EntryNorm_nonneg L
    have hD0 : 0 ≤ p29EntryNorm D := p29EntryNorm_nonneg D
    have hU0 : 0 ≤ p29EntryNorm U := p29EntryNorm_nonneg U
    have hΔLnorm : p29EntryNorm ΔL ≤ γ * p29EntryNorm L :=
      p29EntryNorm_componentwise hγ hΔL'
    have hΔUnorm : p29EntryNorm ΔU ≤ γ * p29EntryNorm U :=
      p29EntryNorm_componentwise hγ hΔU'
    have hDplus : p29EntryNorm (D + ΔD) ≤
        (1 + eta) * p29EntryNorm D := by
      calc
        p29EntryNorm (D + ΔD) ≤
            p29EntryNorm D + p29EntryNorm ΔD := p29EntryNorm_add_le D ΔD
        _ ≤ p29EntryNorm D + eta * p29EntryNorm D :=
          add_le_add (le_refl _) hΔD
        _ = (1 + eta) * p29EntryNorm D := by ring
    have hUplus : p29EntryNorm (U + ΔU) ≤
        (1 + γ) * p29EntryNorm U := by
      calc
        p29EntryNorm (U + ΔU) ≤
            p29EntryNorm U + p29EntryNorm ΔU := p29EntryNorm_add_le U ΔU
        _ ≤ p29EntryNorm U + γ * p29EntryNorm U :=
          add_le_add (le_refl _) hΔUnorm
        _ = (1 + γ) * p29EntryNorm U := by ring
    have hDplus0 : 0 ≤ p29EntryNorm (D + ΔD) :=
      p29EntryNorm_nonneg _
    have hUplus0 : 0 ≤ p29EntryNorm (U + ΔU) :=
      p29EntryNorm_nonneg _
    have hΔL0 : 0 ≤ p29EntryNorm ΔL := p29EntryNorm_nonneg _
    have hΔD0 : 0 ≤ p29EntryNorm ΔD := p29EntryNorm_nonneg _
    have hΔU0 : 0 ≤ p29EntryNorm ΔU := p29EntryNorm_nonneg _
    have hn60 : 0 ≤ (n : ℝ) ^ 6 := by positivity
    let T1 := p29MatMul (p29MatMul ΔL (D + ΔD)) (U + ΔU)
    let T2 := p29MatMul (p29MatMul L ΔD) (U + ΔU)
    let T3 := p29MatMul (p29MatMul L D) ΔU
    have hT1 : p29EntryNorm T1 ≤
        (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D * p29EntryNorm U *
          (γ * (1 + eta) * (1 + γ)) := by
      calc
        p29EntryNorm T1 ≤ (n : ℝ) ^ 6 * p29EntryNorm ΔL *
            p29EntryNorm (D + ΔD) * p29EntryNorm (U + ΔU) :=
          p29EntryNorm_tripleMul_le n _ _ _
        _ ≤ (n : ℝ) ^ 6 * (γ * p29EntryNorm L) *
            ((1 + eta) * p29EntryNorm D) *
            ((1 + γ) * p29EntryNorm U) := by
              gcongr
        _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
            p29EntryNorm U * (γ * (1 + eta) * (1 + γ)) := by ring
    have hT2 : p29EntryNorm T2 ≤
        (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D * p29EntryNorm U *
          (eta * (1 + γ)) := by
      calc
        p29EntryNorm T2 ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
            p29EntryNorm ΔD * p29EntryNorm (U + ΔU) :=
          p29EntryNorm_tripleMul_le n _ _ _
        _ ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
            (eta * p29EntryNorm D) * ((1 + γ) * p29EntryNorm U) := by
              gcongr
        _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
            p29EntryNorm U * (eta * (1 + γ)) := by ring
    have hT3 : p29EntryNorm T3 ≤
        (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D * p29EntryNorm U * γ := by
      calc
        p29EntryNorm T3 ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
            p29EntryNorm D * p29EntryNorm ΔU :=
          p29EntryNorm_tripleMul_le n _ _ _
        _ ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
            p29EntryNorm D * (γ * p29EntryNorm U) := by
              gcongr
        _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
            p29EntryNorm U * γ := by ring
    have hcombined : p29CombinedBackwardError L D ΔL ΔD ΔU =
        T1 + T2 + T3 := by
      simpa only [T1, T2, T3, U] using
        (p29CombinedBackwardError_eq L D ΔL ΔD ΔU)
    have hcombinedNorm : p29EntryNorm
        (p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
        (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D * p29EntryNorm U *
          (γ * (1 + eta) * (1 + γ) + eta * (1 + γ) + γ) := by
      rw [hcombined]
      calc
        p29EntryNorm (T1 + T2 + T3) ≤
            p29EntryNorm T1 + p29EntryNorm T2 + p29EntryNorm T3 :=
          p29EntryNorm_add_three_le T1 T2 T3
        _ ≤
            ((n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
              p29EntryNorm U * (γ * (1 + eta) * (1 + γ))) +
            ((n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
              p29EntryNorm U * (eta * (1 + γ))) +
            ((n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
              p29EntryNorm U * γ) := by linarith
        _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
            p29EntryNorm U *
              (γ * (1 + eta) * (1 + γ) + eta * (1 + γ) + γ) := by
              ring
    unfold F p29TotalBackwardBound p29SolveBackwardFactor
    change p29EntryNorm
        (E0 + p29CombinedBackwardError L D ΔL ΔD ΔU) ≤ _
    calc
      p29EntryNorm
          (E0 + p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
          p29EntryNorm E0 +
            p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) :=
        p29EntryNorm_add_le _ _
      _ ≤ factorEta * p29EntryNorm A +
          ((n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
            p29EntryNorm U *
              (γ * (1 + eta) * (1 + γ) + eta * (1 + γ) + γ)) := by
        linarith
      _ = factorEta * p29EntryNorm A +
          (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
            p29EntryNorm (p29Transpose L) *
            (p29Gamma fp.u n * (1 + eta) * (1 + p29Gamma fp.u n) +
              eta * (1 + p29Gamma fp.u n) + p29Gamma fp.u n) := by
        rfl

end HighamBench
