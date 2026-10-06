import NumStability.Analysis.SemiconvergentLimitGeneral

/-!
# Higham Chapter 17, Equation 17.22

Canonical source-correspondence owner for the general-complex semiconvergent block form obtained from convergence of every real orbit, including its exact spectral-radius condition and power limit.
-/

namespace NumStability

open scoped BigOperators Topology Matrix
open Module

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Masking the complement action does not change the block diagonal matrix:
`diag(I_r, compBlock C) = diag(I_r, C)`. -/
theorem blockJ_compBlock_eq (n r : ℕ) (C : Fin n → Fin n → ℝ) :
    blockJ n r (compBlock n r C) = blockJ n r C := by
  funext i j
  unfold blockJ compBlock
  by_cases hi : (i : ℕ) < r
  · simp [hi]
  · by_cases hj : (j : ℕ) < r
    · simp [hi, hj]
    · simp [hi, hj]

/-- If the powers of `diag(I_r, C)` tend to `diag(I_r, 0)`, then the powers of
the zero-padded complement block tend entrywise to zero. -/
theorem matPow_compBlock_tendsto_zero_of_blockJ_tendsto_topProjector
    (n r : ℕ) (C : Fin n → Fin n → ℝ)
    (hJ : ∀ i j : Fin n,
      Filter.Tendsto (fun m => matPow n (blockJ n r C) m i j) Filter.atTop
        (nhds (topProjector n r i j))) :
    ∀ i j : Fin n,
      Filter.Tendsto (fun m => matPow n (compBlock n r C) m i j) Filter.atTop
        (nhds 0) := by
  intro i j
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  have hshift := (hJ i j).comp (Filter.tendsto_add_atTop_nat 1)
  have hsub := hshift.sub (tendsto_const_nhds :
    Filter.Tendsto (fun _ : ℕ => topProjector n r i j) Filter.atTop
      (nhds (topProjector n r i j)))
  have hsub' :
      Filter.Tendsto
        (fun m => matPow n (blockJ n r C) (m + 1) i j - topProjector n r i j)
        Filter.atTop (nhds 0) := by
    simpa using hsub
  exact hsub'.congr (fun m => by
    have hsplit := congrFun (congrFun (matPow_blockJ_eq n r C m) i) j
    rw [hsplit]
    ring)

/-- Entrywise decay of all powers forces the genuine spectral radius of the
complexification to be strictly below one.  The strictness is obtained from a
single positive power whose norm is below one, followed by
`spectralRadius_pow_le` and `spectralRadius_le_nnnorm`; no contraction norm for
the original matrix is assumed. -/
theorem spectralRadius_complexifyMat_lt_one_of_matPow_tendsto_zero
    {n : ℕ} (B : Fin n → Fin n → ℝ)
    (hzero : ∀ i j : Fin n,
      Filter.Tendsto (fun m => matPow n B m i j) Filter.atTop (nhds 0)) :
    spectralRadius ℂ (complexifyMat n B) < 1 := by
  by_cases hn : n = 0
  · subst n
    have hmat : complexifyMat 0 B = 0 := Subsingleton.elim _ _
    rw [hmat, spectrum.spectralRadius_zero]
    exact zero_lt_one
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
    haveI hfd : FiniteDimensional ℂ (Matrix (Fin n) (Fin n) ℂ) :=
      Matrix.finiteDimensional
    haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) :=
      FiniteDimensional.complete ℂ _
    have hpow :
        Filter.Tendsto (fun m => (complexifyMat n B) ^ m) Filter.atTop (nhds 0) := by
      refine tendsto_pi_nhds.2 (fun i => tendsto_pi_nhds.2 (fun j => ?_))
      have hmap := (Complex.continuous_ofReal.tendsto 0).comp (hzero i j)
      have hentry : ∀ m : ℕ,
          ((complexifyMat n B) ^ m) i j = (matPow n B m i j : ℂ) := by
        intro m
        rw [complexifyMat, ← map_ofReal_pow, ← matPow_eq_matrix_pow]
        rfl
      simpa using hmap.congr (fun m => (hentry m).symm)
    have hnorm :
        Filter.Tendsto (fun m => ‖(complexifyMat n B) ^ m‖) Filter.atTop (nhds 0) := by
      simpa using hpow.norm
    have hsmall : ∀ᶠ m : ℕ in Filter.atTop, ‖(complexifyMat n B) ^ m‖ < 1 :=
      hnorm.eventually_lt_const zero_lt_one
    obtain ⟨m, hmnorm, hmpos⟩ :=
      (hsmall.and (Filter.eventually_ge_atTop 1)).exists
    have hmne : m ≠ 0 := Nat.ne_of_gt hmpos
    have hnnnorm : (↑‖(complexifyMat n B) ^ m‖₊ : ENNReal) < 1 := by
      exact_mod_cast hmnorm
    have hrpow :
        (spectralRadius ℂ (complexifyMat n B)) ^ m < 1 :=
      (spectrum.spectralRadius_pow_le (𝕜 := ℂ) (complexifyMat n B) m hmne).trans_lt
        ((spectrum.spectralRadius_le_nnnorm (𝕜 := ℂ) ((complexifyMat n B) ^ m)).trans_lt
          hnnnorm)
    by_contra hnot
    have hge : (1 : ENNReal) ≤ spectralRadius ℂ (complexifyMat n B) :=
      le_of_not_gt hnot
    exact (not_lt_of_ge (one_le_pow₀ hge)) hrpow

/-- The exact source-level data of Higham (17.22).  `Gamma` is the lower-right
complement block embedded in the ambient coordinates and zero elsewhere, so
`blockJ n r Gamma` is literally `diag(I_r, Gamma)`. -/
def Higham17_22SourceBlockForm (n : ℕ) (G : Fin n → Fin n → ℝ) : Prop :=
  ∃ (r : ℕ) (P P_inv Gamma : Fin n → Fin n → ℝ),
    r ≤ n ∧
    IsRightInverse n P P_inv ∧
    IsRightInverse n P_inv P ∧
    (∀ i j : Fin n, (i : ℕ) < r ∨ (j : ℕ) < r → Gamma i j = 0) ∧
    matMul n P_inv (matMul n G P) = blockJ n r Gamma ∧
    G = matMul n P (matMul n (blockJ n r Gamma) P_inv) ∧
    spectralRadius ℂ (complexifyMat n Gamma) < 1 ∧
    ∀ i j : Fin n,
      Filter.Tendsto (fun m => matPow n G m i j) Filter.atTop
        (nhds (oneEigenProjector n r P P_inv i j))

/-- **Higham Chapter 17, equation (17.22), general-complex source closure.**

From the sole source assumption that every orbit of `G` converges, this theorem
constructs an invertible real change of basis and the exact block form

`G = P * diag(I_r, Gamma) * P^{-1}`

with the genuine complex spectral-radius condition `rho(Gamma) < 1`.  It also
returns the corresponding power limit.  There is no supplied basis, invariant
complement, block decomposition, spectral-radius bound, or infinity-norm
contraction premise. -/
theorem higham17_22_sourceBlockForm_of_forall_orbit_tendsto
    {n : ℕ} (G : Fin n → Fin n → ℝ)
    (hconv : ∀ x : Fin n → ℝ, ∃ z : Fin n → ℝ,
      Filter.Tendsto (fun m : ℕ => (Matrix.mulVecLin G ^ m) x) Filter.atTop (𝓝 z)) :
    Higham17_22SourceBlockForm n G := by
  classical
  obtain ⟨F, hCompl, hEig1, hInvF⟩ :=
    exists_real_primary_splitting_of_forall_orbit_tendsto G hconv
  set E1 : Submodule ℝ (Fin n → ℝ) :=
    Module.End.eigenspace (Matrix.mulVecLin G) 1 with hE1
  set r : ℕ := Module.finrank ℝ E1 with hr
  set mm : ℕ := Module.finrank ℝ F with hmm
  have hrm : r + mm = n := by
    rw [hr, hmm, Submodule.finrank_add_eq_of_isCompl hCompl, Module.finrank_fin_fun]
  set bV : Module.Basis (Fin r) ℝ E1 := Module.finBasis ℝ E1 with hbV
  set bW : Module.Basis (Fin mm) ℝ F := Module.finBasis ℝ F with hbW
  set b := adaptedBasis hrm hCompl bV bW with hb
  set P : Fin n → Fin n → ℝ := basisColMatrix b with hP
  set P_inv : Fin n → Fin n → ℝ := basisRowMatrix b with hP_inv
  set C : Fin n → Fin n → ℝ := basisActionMatrix G b with hC
  set Gamma : Fin n → Fin n → ℝ := compBlock n r C with hGamma

  have hGcolTop : ∀ (k : Fin n), (k : ℕ) < r →
      ∀ i : Fin n, matMul n G P i k = P i k :=
    fun k hk i => basisColMatrix_colTop G b r
      (fun k' hk' => adaptedBasis_hEig hrm hCompl bV bW G hEig1 k' hk') k hk i
  have hGcolBot : ∀ (k : Fin n), ¬(k : ℕ) < r →
      ∀ i : Fin n, matMul n G P i k =
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r), P i l * C l k :=
    fun k hk i => basisColMatrix_colBot G b r
      (fun k' hk' l hl => adaptedBasis_hInv hrm hCompl bV bW G hInvF k' hk' l hl)
      k hk i
  have hPr : IsRightInverse n P P_inv := basisColMatrix_isRightInverse b
  have hPl : IsRightInverse n P_inv P := basisRowMatrix_isRightInverse b
  have hsimC : matMul n P_inv (matMul n G P) = blockJ n r C :=
    X_inv_G_X_eq_blockJ n G P P_inv (blockJ n r C) hPl
      (matMul_G_X_eq_X_blockJ n r G P C hGcolTop hGcolBot)
  have hsimGamma : matMul n P_inv (matMul n G P) = blockJ n r Gamma := by
    rw [hGamma, blockJ_compBlock_eq]
    exact hsimC

  have hGconv : ∀ a b' : Fin n, ∃ c : ℝ,
      Filter.Tendsto (fun m => matPow n G m a b') Filter.atTop (nhds c) := by
    intro a b'
    have hconv' : ∀ x : Fin n → ℝ, ∃ z : Fin n → ℝ,
        Filter.Tendsto (fun m : ℕ => (Matrix.mulVecLin (Matrix.of G) ^ m) x)
          Filter.atTop (𝓝 z) := hconv
    exact matPow_entry_converges_of_forall_orbit_tendsto n G hconv' a b'
  have hFixSub : ∀ x : Fin n → ℝ, G *ᵥ x = x → x ∈ E1 := by
    intro x hx
    rw [hE1, Module.End.mem_eigenspace_iff, one_smul, Matrix.mulVecLin_apply]
    exact hx
  have hNoFix : ∀ w : Fin n → ℝ, (∀ l : Fin n, (l : ℕ) < r → w l = 0) →
      (∀ i : Fin n, (∑ l : Fin n, compBlock n r C i l * w l) = w i) → w = 0 :=
    fun w hwtop hfix =>
      compBlock_no_comp_fixed hrm hCompl bV bW G hFixSub hInvF hwtop hfix
  have hJlimC : ∀ i j : Fin n,
      Filter.Tendsto (fun m => matPow n (blockJ n r C) m i j) Filter.atTop
        (nhds (topProjector n r i j)) :=
    fun i j => matPow_blockJ_tendsto_topProjector_of_convergence r G P P_inv C
      hPr hPl hsimC hGconv hNoFix i j
  have hGammaPow : ∀ i j : Fin n,
      Filter.Tendsto (fun m => matPow n Gamma m i j) Filter.atTop (nhds 0) := by
    rw [hGamma]
    exact matPow_compBlock_tendsto_zero_of_blockJ_tendsto_topProjector n r C hJlimC
  have hspec : spectralRadius ℂ (complexifyMat n Gamma) < 1 :=
    spectralRadius_complexifyMat_lt_one_of_matPow_tendsto_zero Gamma hGammaPow
  have hsource : G = matMul n P (matMul n (blockJ n r Gamma) P_inv) :=
    eq_conjugate_of_similarity n G P P_inv (blockJ n r Gamma) hPr hsimGamma
  have hJlimGamma : ∀ i j : Fin n,
      Filter.Tendsto (fun m => matPow n (blockJ n r Gamma) m i j) Filter.atTop
        (nhds (topProjector n r i j)) := by
    intro i j
    rw [hGamma, blockJ_compBlock_eq]
    exact hJlimC i j
  have hlimit : ∀ i j : Fin n,
      Filter.Tendsto (fun m => matPow n G m i j) Filter.atTop
        (nhds (oneEigenProjector n r P P_inv i j)) :=
    fun i j => matPow_G_tendsto_oneEigenProjector_of_matPow_J_tendsto
      n r G P P_inv (blockJ n r Gamma) hPr hPl hsimGamma hJlimGamma i j

  refine ⟨r, P, P_inv, Gamma, by omega, hPr, hPl, ?_, hsimGamma, hsource, hspec, hlimit⟩
  intro i j hij
  rw [hGamma]
  exact compBlock_top_zero n r C i j hij

/-- Fully expanded existential form of
`higham17_22_sourceBlockForm_of_forall_orbit_tendsto`, convenient for direct
consumption and strict premise audits. -/
theorem higham17_22_exists_blockForm_spectralRadius_lt_one_of_forall_orbit_tendsto
    {n : ℕ} (G : Fin n → Fin n → ℝ)
    (hconv : ∀ x : Fin n → ℝ, ∃ z : Fin n → ℝ,
      Filter.Tendsto (fun m : ℕ => (Matrix.mulVecLin G ^ m) x) Filter.atTop (𝓝 z)) :
    ∃ (r : ℕ) (P P_inv Gamma : Fin n → Fin n → ℝ),
      r ≤ n ∧
      IsRightInverse n P P_inv ∧
      IsRightInverse n P_inv P ∧
      (∀ i j : Fin n, (i : ℕ) < r ∨ (j : ℕ) < r → Gamma i j = 0) ∧
      matMul n P_inv (matMul n G P) = blockJ n r Gamma ∧
      G = matMul n P (matMul n (blockJ n r Gamma) P_inv) ∧
      spectralRadius ℂ (complexifyMat n Gamma) < 1 ∧
      ∀ i j : Fin n,
        Filter.Tendsto (fun m => matPow n G m i j) Filter.atTop
          (nhds (oneEigenProjector n r P P_inv i j)) := by
  simpa only [Higham17_22SourceBlockForm] using
    higham17_22_sourceBlockForm_of_forall_orbit_tendsto G hconv

end NumStability
