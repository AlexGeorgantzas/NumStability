import HighamBench.P29Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Source.Higham.Chapter11.Section02.Aasen

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

@[simp] lemma p29AsFPModel_u (fp : P29FPModel) :
    (p29AsFPModel fp).u = fp.u := rfl

lemma p29_gamma_eq (fp : P29FPModel) (n : ℕ) :
    p29Gamma fp.u n = NumStability.gamma (p29AsFPModel fp) n := rfl

lemma p29_forwardSubSteps_eq (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p29ForwardSubSteps fp n L b k hk x =
        NumStability.fl_forwardSub_steps (p29AsFPModel fp) n L b k hk x := by
  intro k
  induction k with
  | zero => intro hk x; rfl
  | succ k ih =>
      intro hk x
      rw [p29ForwardSubSteps, NumStability.fl_forwardSub_steps]
      apply ih

lemma p29_forwardSub_eq (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) :
    p29ForwardSub fp n L b =
      NumStability.fl_forwardSub (p29AsFPModel fp) n L b := by
  exact p29_forwardSubSteps_eq fp n L b n (le_refl n) (fun _ => 0)

lemma p29_backSubSteps_eq (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p29BackSubSteps fp n U b k hk x =
        NumStability.fl_backSub_steps (p29AsFPModel fp) n U b k hk x := by
  intro k
  induction k with
  | zero => intro hk x; rfl
  | succ k ih =>
      intro hk x
      rw [p29BackSubSteps, NumStability.fl_backSub_steps]
      apply ih

lemma p29_backSub_eq (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) :
    p29BackSub fp n U b =
      NumStability.fl_backSub (p29AsFPModel fp) n U b := by
  exact p29_backSubSteps_eq fp n U b n (le_refl n) (fun _ => 0)

lemma p29_entryNorm_nonneg {m n : ℕ} (M : P29Matrix m n) :
    0 ≤ p29EntryNorm M := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _

lemma p29_abs_entry_le_norm {m n : ℕ} (M : P29Matrix m n)
    (i : Fin m) (j : Fin n) :
    |M i j| ≤ p29EntryNorm M := by
  unfold p29EntryNorm
  calc
    |M i j| ≤ ∑ j' : Fin n, |M i j'| :=
      Finset.single_le_sum (fun j' _ => abs_nonneg (M i j')) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin m, ∑ j' : Fin n, |M i' j'| :=
      Finset.single_le_sum
        (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg (M i' j'))
        (Finset.mem_univ i)

lemma p29_entryNorm_add_le {m n : ℕ} (M N : P29Matrix m n) :
    p29EntryNorm (M + N) ≤ p29EntryNorm M + p29EntryNorm N := by
  unfold p29EntryNorm
  simp only [Matrix.add_apply]
  calc
    ∑ i : Fin m, ∑ j : Fin n, |M i j + N i j|
        ≤ ∑ i : Fin m, ∑ j : Fin n, (|M i j| + |N i j|) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          exact abs_add_le _ _
    _ = (∑ i : Fin m, ∑ j : Fin n, |M i j|) +
          ∑ i : Fin m, ∑ j : Fin n, |N i j| := by
          simp_rw [Finset.sum_add_distrib]

lemma p29_ldlt_entry_expansion {n : ℕ} (L D : P29Matrix n n)
    (i j : Fin n) :
    p29LDLT L D i j =
      ∑ p : Fin n, ∑ q : Fin n, L i p * D p q * p29Transpose L q j := by
  unfold p29LDLT p29MatMul
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

lemma p29_perturbed_entry_expansion {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) (i j : Fin n) :
    p29PerturbedLDLT L D ΔL ΔD ΔU i j =
      ∑ p : Fin n, ∑ q : Fin n,
        (L i p + ΔL i p) * (D p q + ΔD p q) *
          (p29Transpose L q j + ΔU q j) := by
  unfold p29PerturbedLDLT p29MatMul
  simp only [Matrix.add_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

lemma p29_combined_eq_aasen_delta {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) (i j : Fin n) :
    p29CombinedBackwardError L D ΔL ΔD ΔU i j =
      NumStability.higham11_15_aasenChainDeltaA n L D (p29Transpose L)
        ΔL ΔD ΔU i j := by
  unfold p29CombinedBackwardError
  simp only [Matrix.sub_apply]
  rw [p29_perturbed_entry_expansion, p29_ldlt_entry_expansion]
  rfl

lemma p29_combined_entryNorm_bound {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) (γ eta : ℝ)
    (hγ : 0 ≤ γ) (heta : 0 ≤ eta)
    (hΔL : ∀ i j, |ΔL i j| ≤ γ * |L i j|)
    (hΔD : p29EntryNorm ΔD ≤ eta * p29EntryNorm D)
    (hΔU : ∀ i j, |ΔU i j| ≤ γ * |p29Transpose L i j|) :
    p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
      (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        p29EntryNorm (p29Transpose L) *
        (γ * (1 + eta) * (1 + γ) + eta * (1 + γ) + γ) := by
  let NL := p29EntryNorm L
  let ND := p29EntryNorm D
  let NU := p29EntryNorm (p29Transpose L)
  let coeff := γ * (1 + eta) * (1 + γ) + eta * (1 + γ) + γ
  let C := NL * ND * NU * coeff
  have hNL : 0 ≤ NL := p29_entryNorm_nonneg L
  have hND : 0 ≤ ND := p29_entryNorm_nonneg D
  have hNU : 0 ≤ NU := p29_entryNorm_nonneg (p29Transpose L)
  have hγa : 0 ≤ 2 * γ + γ ^ 2 := by nlinarith [sq_nonneg γ]
  have hγb : 0 ≤ 1 + 2 * γ + γ ^ 2 := by
    nlinarith [sq_nonneg (1 + γ)]
  have hcoeff_eq :
      coeff = (2 * γ + γ ^ 2) + eta * (1 + 2 * γ + γ ^ 2) := by
    dsimp [coeff]
    ring
  have hcoeff : 0 ≤ coeff := by
    rw [hcoeff_eq]
    exact add_nonneg hγa (mul_nonneg heta hγb)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hΔDentry : ∀ i j, |ΔD i j| ≤ eta * ND := by
    intro i j
    exact le_trans (p29_abs_entry_le_norm ΔD i j) hΔD
  have hentry : ∀ i j,
      |p29CombinedBackwardError L D ΔL ΔD ΔU i j| ≤
        (n : ℝ) ^ 2 * C := by
    intro i j
    rw [p29_combined_eq_aasen_delta]
    have hchain :=
      NumStability.higham11_15_aasenChainDeltaA_abs_bound_gamma
        n L D (p29Transpose L) ΔL ΔD ΔU
        (fun _ _ => eta * ND) γ hγ
        (fun _ _ => mul_nonneg heta hND) hΔL hΔDentry hΔU i j
    refine le_trans hchain ?_
    unfold NumStability.higham11_15_aasenChainDeltaABound
    calc
      ∑ p : Fin n, ∑ q : Fin n,
          ((2 * γ + γ ^ 2) * |L i p| * |D p q| * |p29Transpose L q j| +
            (1 + 2 * γ + γ ^ 2) * |L i p| * (eta * ND) *
              |p29Transpose L q j|)
          ≤ ∑ p : Fin n, ∑ q : Fin n, C := by
            apply Finset.sum_le_sum
            intro p _
            apply Finset.sum_le_sum
            intro q _
            calc
              (2 * γ + γ ^ 2) * |L i p| * |D p q| *
                    |p29Transpose L q j| +
                  (1 + 2 * γ + γ ^ 2) * |L i p| * (eta * ND) *
                    |p29Transpose L q j|
                  ≤ (2 * γ + γ ^ 2) * NL * ND * NU +
                      (1 + 2 * γ + γ ^ 2) * NL * (eta * ND) * NU := by
                        gcongr
                        · exact p29_abs_entry_le_norm L i p
                        · exact p29_abs_entry_le_norm D p q
                        · exact p29_abs_entry_le_norm (p29Transpose L) q j
                        · exact p29_abs_entry_le_norm L i p
                        · exact p29_abs_entry_le_norm (p29Transpose L) q j
              _ = C := by
                    dsimp [C]
                    rw [hcoeff_eq]
                    ring
      _ = (n : ℝ) ^ 2 * C := by
            simp
            ring
  unfold p29EntryNorm
  calc
    ∑ i : Fin n, ∑ j : Fin n,
        |p29CombinedBackwardError L D ΔL ΔD ΔU i j|
        ≤ ∑ i : Fin n, ∑ j : Fin n, (n : ℝ) ^ 2 * C := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          exact hentry i j
    _ = (n : ℝ) ^ 4 * C := by
          simp
          ring
    _ ≤ (n : ℝ) ^ 6 * C := by
          by_cases hn0 : n = 0
          · subst n
            norm_num
          · have hn1 : (1 : ℝ) ≤ n := by
              exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
            have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
              nlinarith [sq_nonneg ((n : ℝ) - 1)]
            have hp : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 6 := by
              calc
                (n : ℝ) ^ 4 = (n : ℝ) ^ 4 * 1 := by ring
                _ ≤ (n : ℝ) ^ 4 * (n : ℝ) ^ 2 := by
                  exact mul_le_mul_of_nonneg_left hn2 (pow_nonneg (Nat.cast_nonneg n) 4)
                _ = (n : ℝ) ^ 6 := by ring
            exact mul_le_mul_of_nonneg_right hp hC
    _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          p29EntryNorm (p29Transpose L) *
          (γ * (1 + eta) * (1 + γ) + eta * (1 + γ) + γ) := by
            dsimp [C, NL, ND, NU, coeff]
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
  let nfp := p29AsFPModel fp
  have hn : NumStability.gammaValid nfp n := hvalid
  obtain ⟨ΔL, hΔL, hforward⟩ :=
    NumStability.forwardSub_backward_error nfp n L b hdiag hlower hn
  rw [← p29_gamma_eq] at hΔL
  rw [← p29_forwardSub_eq] at hforward
  obtain ⟨ΔD, hΔD, hmiddle⟩ := hDsolve
  have hUdiag : ∀ i, p29Transpose L i i ≠ 0 := by
    intro i
    exact hdiag i
  have hUupper : ∀ i j : Fin n, j.val < i.val → p29Transpose L i j = 0 := by
    intro i j hij
    exact hlower j i hij
  obtain ⟨ΔU, hΔU, hback⟩ :=
    NumStability.backSub_backward_error nfp n (p29Transpose L) z
      hUdiag hUupper hn
  rw [← p29_gamma_eq] at hΔU
  rw [← p29_backSub_eq] at hback
  let x := p29BackSub fp n (p29Transpose L) z
  have hpert : ∀ i, ∑ j : Fin n,
      p29PerturbedLDLT L D ΔL ΔD ΔU i j * x j = b i := by
    intro i
    rw [← hforward i]
    unfold p29PerturbedLDLT p29MatMul
    simp only [Pi.add_apply, Matrix.add_apply]
    calc
      ∑ j : Fin n,
          (∑ q : Fin n, (∑ p : Fin n, (L i p + ΔL i p) * (D p q + ΔD p q)) *
            (p29Transpose L q j + ΔU q j)) * x j
          = ∑ j : Fin n, (∑ p : Fin n, ∑ q : Fin n,
              (L i p + ΔL i p) * (D p q + ΔD p q) *
                (p29Transpose L q j + ΔU q j)) * x j := by
              apply Finset.sum_congr rfl
              intro j _
              congr 1
              simp_rw [Finset.sum_mul]
              rw [Finset.sum_comm]
      _ = ∑ p : Fin n, (L i p + ΔL i p) *
              (∑ q : Fin n, (D p q + ΔD p q) *
                (∑ j : Fin n, (p29Transpose L q j + ΔU q j) * x j)) := by
              simp_rw [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro p _
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro q _
              ring_nf
      _ = ∑ p : Fin n, (L i p + ΔL i p) *
              (∑ q : Fin n, (D p q + ΔD p q) * z q) := by
            apply Finset.sum_congr rfl
            intro p _
            congr 1
            apply Finset.sum_congr rfl
            intro q _
            rw [hback q]
      _ = ∑ p : Fin n, (L i p + ΔL i p) * p29ForwardSub fp n L b p := by
            apply Finset.sum_congr rfl
            intro p _
            rw [hmiddle p]
  let F := p29TotalBackwardError E0 L D ΔL ΔD ΔU
  have hAF : ∀ i j, A i j + F i j = p29PerturbedLDLT L D ΔL ΔD ΔU i j := by
    intro i j
    have hf := congrFun (congrFun hfactor i) j
    simp only [Matrix.add_apply] at hf
    unfold F p29TotalBackwardError p29CombinedBackwardError
    simp only [Matrix.add_apply, Matrix.sub_apply]
    rw [hf]
    ring
  refine ⟨ΔL, ΔD, ΔU, F, hΔL, hΔD, hΔU, rfl, ?_, ?_⟩
  · intro i
    rw [← hpert i]
    apply Finset.sum_congr rfl
    intro j _
    rw [hAF i j]
  · have hγnonneg : 0 ≤ p29Gamma fp.u n := by
      rw [p29_gamma_eq]
      exact NumStability.gamma_nonneg nfp hn
    have hcombined := p29_combined_entryNorm_bound
      L D ΔL ΔD ΔU (p29Gamma fp.u n) eta
      hγnonneg heta hΔL hΔD hΔU
    change p29EntryNorm
        (E0 + p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p29TotalBackwardBound fp n eta factorEta A L D
    unfold p29TotalBackwardBound p29SolveBackwardFactor
    exact le_trans
      (p29_entryNorm_add_le E0
        (p29CombinedBackwardError L D ΔL ΔD ΔU))
      (add_le_add hE0 hcombined)

end HighamBench
