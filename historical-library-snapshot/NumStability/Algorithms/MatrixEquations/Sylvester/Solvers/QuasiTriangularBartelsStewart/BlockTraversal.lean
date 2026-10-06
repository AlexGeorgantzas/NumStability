import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.PracticalErrorBounds
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Rectangular
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.ComplexSchur.SpectralSolvability
import NumStability.Analysis.LinearOperators.Schur.Real.InvariantSubspace.TwoByTwo
import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.API
import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.Basic
import NumStability.Analysis.MatrixAlgebra

/-!
# Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.BlockTraversal

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16Spectrum.lean
--
-- Constructive spectral directions for the vec/Kronecker Sylvester
-- coefficient (Higham, Accuracy and Stability of Numerical Algorithms,
-- 2nd ed., Chapter 16.1, equation (16.3)) and the Bartels-Stewart
-- supplied-triangular column recurrence (Higham, 2nd ed., Chapter 16.2,
-- equations (16.4)-(16.8)).  This file complements `Higham16.lean`, whose
-- namespace and matrix conventions it follows exactly; it adds the general
-- (non-diagonal) constructive halves of those two source rows:
--
-- * every pairwise difference of supplied real eigenpairs of `A` and `B^T`
--   is an eigenvalue of `I_n kron A - B^T kron I_m`, and a shared eigenvalue
--   makes the coefficient singular (the constructive directions of (16.3));
-- * with a SUPPLIED upper-triangular `T`, the transformed equation
--   `AX - XT = C` decouples column by column into
--   `(A - t_kk I) x_k = c_k + sum_{j<k} t_jk x_j`, and per-column
--   nonsingularity of the shifted matrices gives a unique exact solution by
--   forward substitution over columns; this is the (16.5)/(16.6)
--   Bartels-Stewart existence statement at the supplied-factor level.
--
-- Honest scope:
-- * The complex Schur route is imported to prove determinant nonsingularity
--   of the real vec/Kronecker coefficient from a supplied no-common complex
--   right-eigenpair hypothesis on the entrywise complexifications of `A` and
--   `B`.  The complex coefficient now also has the shifted determinant form of
--   the full spectrum-characterization statement: a scalar shift is singular
--   exactly when it is a difference `lambda(A) - mu(B)`.
-- * The quasi-triangular (2x2 diagonal block, real-Schur) Bartels-Stewart
--   route behind equations (16.4), (16.7), and (16.8) is represented by an
--   imported real quasi-Schur existence wrapper plus supplied adjacent
--   two-column exact block-equation lemmas; the full block solver and
--   floating-point error propagation remain open.
-- * No floating-point rounding analysis: triangular and eigenpair data in the
--   solver wrappers are supplied hypotheses, exactly as in the supplied-factor
--   diagonal case of `Higham16.lean`.






namespace NumStability

open scoped BigOperators

-- ============================================================
-- (16.4): real quasi-Schur factors for both Sylvester sides
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equation (16.4), real Schur form
    packaged for the Sylvester equation: both real square factors have
    orthogonal changes of basis to real quasi-upper-triangular factors, with
    explicit block maps whose fibers have size at most two.  This is only the
    exact real quasi-Schur existence step used before the Bartels-Stewart
    recurrence; it does not assert the block solve, nonsingularity of the
    resulting Sylvester coefficient, or any floating-point stability bound. -/
theorem sylvester_realQuasiSchur_factors (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) :
    ∃ (U R : Matrix (Fin m) (Fin m) Real)
      (V S : Matrix (Fin n) (Fin n) Real)
      (pA : Fin m -> Nat) (pB : Fin n -> Nat),
      U ∈ Matrix.orthogonalGroup (Fin m) Real ∧
      V ∈ Matrix.orthogonalGroup (Fin n) Real ∧
      Matrix.transpose U * Matrix.of A * U = R ∧
      Matrix.transpose V * Matrix.of B * V = S ∧
      Monotone pA ∧
      (∀ c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) ∧
      (∀ i j : Fin m, pA j < pA i -> R i j = 0) ∧
      Monotone pB ∧
      (∀ c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) ∧
      (∀ i j : Fin n, pB j < pB i -> S i j = 0) := by
  obtain ⟨U, pA, hU, hpAmono, hpAcard, hAzero⟩ :=
    real_quasi_schur_blocks (Matrix.of A)
  obtain ⟨V, pB, hV, hpBmono, hpBcard, hBzero⟩ :=
    real_quasi_schur_blocks (Matrix.of B)
  refine ⟨U, Matrix.transpose U * Matrix.of A * U,
    V, Matrix.transpose V * Matrix.of B * V, pA, pB,
    hU, hV, rfl, rfl, hpAmono, hpAcard, ?_, hpBmono, hpBcard, ?_⟩
  · intro i j hij
    exact hAzero i j hij
  · intro i j hij
    exact hBzero i j hij

/-- Higham, 2nd ed., Chapter 16.2, equation (16.4), real Schur form
    packaged for the Sylvester equation with the source-side spectral
    certificates for adjacent `2 x 2` blocks.  This strengthens
    `sylvester_realQuasiSchur_factors` by exposing the
    `HasRealQuasiSchurTwoBlockSpectral` data produced by the constructed real
    quasi-Schur decomposition.  It still does not assert Sylvester separation,
    the block solve, or any floating-point stability bound. -/
theorem sylvester_realQuasiSchur_factors_twoBlockSpectral (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) :
    ∃ (U R : Matrix (Fin m) (Fin m) Real)
      (V S : Matrix (Fin n) (Fin n) Real)
      (pA : Fin m -> Nat) (pB : Fin n -> Nat),
      U ∈ Matrix.orthogonalGroup (Fin m) Real ∧
      V ∈ Matrix.orthogonalGroup (Fin n) Real ∧
      Matrix.transpose U * Matrix.of A * U = R ∧
      Matrix.transpose V * Matrix.of B * V = S ∧
      Monotone pA ∧
      (∀ c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) ∧
      (∀ i j : Fin m, pA j < pA i -> R i j = 0) ∧
      HasRealQuasiSchurTwoBlockSpectral R pA ∧
      Monotone pB ∧
      (∀ c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) ∧
      (∀ i j : Fin n, pB j < pB i -> S i j = 0) ∧
      HasRealQuasiSchurTwoBlockSpectral S pB := by
  obtain ⟨U, pA, hU, hpAmono, hpAcard, hAzero, hAspectral⟩ :=
    real_quasi_schur_blocks_twoBlockSpectral (Matrix.of A)
  obtain ⟨V, pB, hV, hpBmono, hpBcard, hBzero, hBspectral⟩ :=
    real_quasi_schur_blocks_twoBlockSpectral (Matrix.of B)
  refine ⟨U, Matrix.transpose U * Matrix.of A * U,
    V, Matrix.transpose V * Matrix.of B * V, pA, pB,
    hU, hV, rfl, rfl, hpAmono, hpAcard, ?_, hAspectral,
    hpBmono, hpBcard, ?_, hBspectral⟩
  · intro i j hij
    exact hAzero i j hij
  · intro i j hij
    exact hBzero i j hij

/-- Adapter from Mathlib's orthogonal-group predicate to the repository's
    function-matrix orthogonality predicate. -/
theorem IsOrthogonal.of_mem_orthogonalGroup {n : Nat}
    (Q : Matrix (Fin n) (Fin n) Real)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) Real) :
    IsOrthogonal n (fun i j => Q i j) := by
  apply IsOrthogonal.of_col_orthonormal
  intro i j
  rw [Matrix.mem_orthogonalGroup_iff'] at hQ
  have hentry := congrFun (congrFun hQ i) j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hentry









































































































































































































































































-- ============================================================
-- (16.3): constructive spectral directions
-- ============================================================























































































































































































































































































































































































-- ============================================================
-- (16.4)-(16.8): Bartels-Stewart supplied-triangular column solve
-- ============================================================

/-- Upper triangularity for the function-shaped square matrices used by the
    Chapter 16 rectangular Sylvester surfaces: all entries strictly below the
    diagonal vanish.  This is the supplied-factor structure of the
    Bartels-Stewart matrix `S` in Higham, 2nd ed., Chapter 16.2, equations
    (16.4)-(16.5); it agrees with Mathlib's `Matrix.BlockTriangular T id`. -/
def IsUpperTriangularFn (n : Nat) (T : RMatFn n n) : Prop :=
  forall i j : Fin n, j < i -> T i j = 0

/-- A real quasi-Schur zero pattern becomes an ordinary upper-triangular
    pattern when the supplied block map has no repeated adjacent block labels.
    This is only a structural adapter; it does not assert that real Schur
    factors are triangular in general. -/
theorem IsUpperTriangularFn.of_quasiSchur_strictBlockMap (n : Nat)
    (T : RMatFn n n) (p : Fin n -> Nat)
    (hzero : ∀ i j : Fin n, p j < p i -> T i j = 0)
    (hp : ∀ i j : Fin n, j < i -> p j < p i) :
    IsUpperTriangularFn n T := by
  intro i j hij
  exact hzero i j (hp i j hij)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6):
    the shifted column coefficient `A - t I` appearing in the
    Bartels-Stewart column solve `(A - t_kk I) x_k = ...`. -/
noncomputable def sylvesterTriangularShiftedCoeff (m : Nat)
    (A : RMatFn m m) (t : Real) : Matrix (Fin m) (Fin m) Real :=
  Matrix.of A - t • (1 : Matrix (Fin m) (Fin m) Real)

/-- Entrywise action of the shifted column coefficient:
    `((A - t I) x)_i = (sum_l a_il x_l) - t x_i`. -/
theorem sylvesterTriangularShiftedCoeff_mulVec_apply (m : Nat)
    (A : RMatFn m m) (t : Real) (x : Fin m -> Real) (i : Fin m) :
    Matrix.mulVec (sylvesterTriangularShiftedCoeff m A t) x i =
      (Finset.sum Finset.univ fun l : Fin m => A i l * x l) - t * x i := by
  unfold sylvesterTriangularShiftedCoeff
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.of_apply]

/-- The one-column vec/Kronecker product index `(0,i)` is equivalent to the
    active column index `i`. -/
def sylvesterOneColumnIndexEquiv (m : Nat) : Fin m ≃ Prod (Fin 1) (Fin m) where
  toFun i := (0, i)
  invFun p := p.2
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨j, i⟩
    have hj : j = 0 := Subsingleton.elim j (0 : Fin 1)
    cases hj
    rfl

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6): the singleton shifted
    column coefficient is the one-column vec/Kronecker Sylvester coefficient,
    after the canonical product-index reindexing. -/
theorem sylvesterVecCoeff_one_reindex_eq_sylvesterTriangularShiftedCoeff
    (m : Nat) (A : RMatFn m m) (t : Real) :
    Matrix.reindex (sylvesterOneColumnIndexEquiv m).symm
        (sylvesterOneColumnIndexEquiv m).symm
        (sylvesterVecCoeff m 1 A (fun _ _ : Fin 1 => t)) =
      sylvesterTriangularShiftedCoeff m A t := by
  ext i j
  simp [sylvesterOneColumnIndexEquiv, sylvesterVecCoeff,
    sylvesterTriangularShiftedCoeff, Matrix.reindex_apply, Matrix.kronecker,
    Matrix.transpose_apply, Matrix.one_apply, Matrix.of_apply]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6): determinant form of the
    one-column vec/Kronecker bridge for the shifted column coefficient. -/
theorem sylvesterVecCoeff_one_det_eq_sylvesterTriangularShiftedCoeff_det
    (m : Nat) (A : RMatFn m m) (t : Real) :
    Matrix.det (sylvesterVecCoeff m 1 A (fun _ _ : Fin 1 => t)) =
      Matrix.det (sylvesterTriangularShiftedCoeff m A t) := by
  let e := sylvesterOneColumnIndexEquiv m
  have hdet_reindex :
      Matrix.det (Matrix.reindex e.symm e.symm
          (sylvesterVecCoeff m 1 A (fun _ _ : Fin 1 => t))) =
        Matrix.det (sylvesterVecCoeff m 1 A (fun _ _ : Fin 1 => t)) :=
    Matrix.det_reindex_self e.symm
      (sylvesterVecCoeff m 1 A (fun _ _ : Fin 1 => t))
  rw [← hdet_reindex,
    sylvesterVecCoeff_one_reindex_eq_sylvesterTriangularShiftedCoeff]




















































/-- Supplied adjacent `2 x 2` diagonal block shape for the function-shaped
    quasi-upper-triangular factors used in the real Bartels-Stewart route:
    columns `p` and `q` are adjacent, and entries below row `q` vanish in
    those two columns.  The in-block subdiagonal entry `T q p` may be nonzero. -/
def IsAdjacentQuasiTriangularBlockFn (n : Nat) (T : RMatFn n n)
    (p q : Fin n) : Prop :=
  q.val = p.val + 1 ∧
    (∀ j : Fin n, q < j → T j p = 0) ∧
    (∀ j : Fin n, q < j → T j q = 0)

/-- A size-at-most-two real quasi-Schur block map is strict after an adjacent
    same-block pair.  This is the small order-theoretic adapter needed to turn
    the exported block-map zeros of `real_quasi_schur_blocks` into the supplied
    adjacent two-column zero pattern used by the real Bartels-Stewart block
    recurrence. -/
theorem quasiSchur_blockMap_strict_after_adjacent_same_block (n : Nat)
    (pmap : Fin n -> Nat) (p q j : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hqj : q < j) :
    pmap q < pmap j := by
  have hle : pmap q <= pmap j := hmono (le_of_lt hqj)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hpq_lt : p < q := Fin.lt_def.mpr (by omega)
  have hp_ne_q : p ≠ q := ne_of_lt hpq_lt
  have hp_ne_j : p ≠ j := ne_of_lt (lt_trans hpq_lt hqj)
  have hq_ne_j : q ≠ j := ne_of_lt hqj
  let fiber : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => pmap i = pmap q)
  have hsubset : ({p, q, j} : Finset (Fin n)) ⊆ fiber := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · subst x
      simp [fiber, hsame]
    · subst x
      simp [fiber]
    · subst x
      simp [fiber, heq.symm]
  have hthree : 3 <= fiber.card := by
    have hcard_three : ({p, q, j} : Finset (Fin n)).card = 3 := by
      simp [hp_ne_q, hp_ne_j, hq_ne_j]
    calc
      3 = ({p, q, j} : Finset (Fin n)).card := hcard_three.symm
      _ <= fiber.card := Finset.card_le_card hsubset
  have htwo : fiber.card <= 2 := hcard (pmap q)
  omega

/-- A size-at-most-two real quasi-Schur block map has no third index in a
    same-labelled adjacent two-column block.  This is the finite-index
    bookkeeping needed when a `2 x 2` real-Schur block is transported back to
    a full quasi-Schur factor. -/
theorem quasiSchur_blockMap_eq_left_or_right_of_adjacent_same_block (n : Nat)
    (pmap : Fin n -> Nat) (p q i : Fin n)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hi : pmap i = pmap p) :
    i = p \/ i = q := by
  by_cases hip : i = p
  · exact Or.inl hip
  by_cases hiq : i = q
  · exact Or.inr hiq
  exfalso
  have hpq_lt : p < q := Fin.lt_def.mpr (by omega)
  have hp_ne_q : p ≠ q := ne_of_lt hpq_lt
  have hp_ne_i : p ≠ i := fun h => hip h.symm
  have hq_ne_i : q ≠ i := fun h => hiq h.symm
  let fiber : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => pmap i = pmap p)
  have hsubset : ({p, q, i} : Finset (Fin n)) ⊆ fiber := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · subst x
      simp [fiber]
    · subst x
      simp [fiber, hsame.symm]
    · subst x
      simp [fiber, hi]
  have hthree : 3 <= fiber.card := by
    have hcard_three : ({p, q, i} : Finset (Fin n)).card = 3 := by
      simp [hp_ne_q, hp_ne_i, hq_ne_i]
    calc
      3 = ({p, q, i} : Finset (Fin n)).card := hcard_three.symm
      _ <= fiber.card := Finset.card_le_card hsubset
  have htwo : fiber.card <= 2 := hcard (pmap p)
  omega

/-- A same-labelled adjacent `2 x 2` real quasi-Schur block is exactly the
    fiber of its block label.  The equivalence is ordered so `0` names the
    left column `p` and `1` names the right column `q`; this is the index
    bridge used when comparing Mathlib's `toSquareBlock` fiber matrix with the
    repository's concrete `Fin 2` active block. -/
noncomputable def adjacentSameBlockFiberEquiv (n : Nat)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q) :
    Fin 2 ≃ { i : Fin n // pmap i = pmap p } where
  toFun k := if k = 0 then ⟨p, rfl⟩ else ⟨q, hsame.symm⟩
  invFun s := if s.1 = p then 0 else 1
  left_inv := by
    intro k
    have hpq_lt : p < q := Fin.lt_def.mpr (by omega)
    have hq_ne_p : q ≠ p := ne_of_gt hpq_lt
    fin_cases k
    · simp
    · simp [hq_ne_p]
  right_inv := by
    intro s
    have hpq_lt : p < q := Fin.lt_def.mpr (by omega)
    have hq_ne_p : q ≠ p := ne_of_gt hpq_lt
    rcases quasiSchur_blockMap_eq_left_or_right_of_adjacent_same_block
        n pmap p q s.1 hcard hpq hsame s.2 with hleft | hright
    · ext
      simp [hleft]
    · ext
      simp [hright, hq_ne_p]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): a same-labelled
    adjacent two-column block in the exported real quasi-Schur block map gives
    the supplied adjacent quasi-triangular block predicate used by the exact
    two-column Bartels-Stewart recurrence.  The theorem supplies only the zero
    pattern; nonsingularity of the induced `2 x 2` block coefficient remains a
    separate spectral/block-separation certificate. -/
theorem IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block (n : Nat)
    (T : RMatFn n n) (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q) :
    IsAdjacentQuasiTriangularBlockFn n T p q := by
  refine ⟨hpq, ?_, ?_⟩
  · intro j hqj
    apply hzero j p
    rw [hsame]
    exact quasiSchur_blockMap_strict_after_adjacent_same_block
      n pmap p q j hmono hcard hpq hsame hqj
  · intro j hqj
    apply hzero j q
    exact quasiSchur_blockMap_strict_after_adjacent_same_block
      n pmap p q j hmono hcard hpq hsame hqj

/-- A monotone real quasi-Schur block map is strict after a singleton column:
    if the immediate successor is not in the same block label, every later
    column has a strictly larger block label.  The statement is vacuous for
    the last column, but the proof only constructs the successor in the
    nonvacuous `k < j` case. -/
theorem quasiSchur_blockMap_strict_after_singleton_successor (n : Nat)
    (pmap : Fin n -> Nat) (k j : Fin n)
    (hmono : Monotone pmap)
    (hnext : forall q : Fin n, q.val = k.val + 1 -> pmap k ≠ pmap q)
    (hkj : k < j) :
    pmap k < pmap j := by
  have hle : pmap k <= pmap j := hmono (le_of_lt hkj)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hk1lt : k.val + 1 < n := by
    have hkjNat : k.val < j.val := Fin.lt_def.mp hkj
    have hjlt : j.val < n := j.isLt
    omega
  let q : Fin n := ⟨k.val + 1, hk1lt⟩
  have hkq : k <= q := Fin.le_def.mpr (by dsimp [q]; omega)
  have hqj : q <= j := Fin.le_def.mpr (by
    dsimp [q]
    have hkjNat : k.val < j.val := Fin.lt_def.mp hkj
    omega)
  have hkq_eq : pmap k = pmap q := by
    have hkq_le : pmap k <= pmap q := hmono hkq
    have hqj_le : pmap q <= pmap j := hmono hqj
    omega
  exact hnext q rfl hkq_eq

/-- A singleton column in the real quasi-Schur block map has the ordinary
    upper-triangular zero-below-column property needed by the one-column
    Bartels-Stewart recurrence. -/
theorem quasiSchur_zero_below_of_singleton_successor (n : Nat)
    (T : RMatFn n n) (pmap : Fin n -> Nat) (k : Fin n)
    (hmono : Monotone pmap)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hnext : forall q : Fin n, q.val = k.val + 1 -> pmap k ≠ pmap q) :
    forall j : Fin n, k < j -> T j k = 0 := by
  intro j hkj
  apply hzero j k
  exact quasiSchur_blockMap_strict_after_singleton_successor
    n pmap k j hmono hnext hkj





































































/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    adjacent `2 x 2` quasi-triangular block system: the two active columns
    are kept on the left-hand side, while only previously solved columns
    `j < p` appear in the right-hand side. -/
def IsSylvesterTwoColumnBlockSystem (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n) : Prop :=
  (fun i =>
      Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T p p))
          (fun i' => X i' p) i - T q p * X i q) =
    (fun i =>
      C i p +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j p * X i j)) ∧
  (fun i =>
      Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T q q))
          (fun i' => X i' q) i - T p q * X i p) =
    (fun i =>
      C i q +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j q * X i j))

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), supplied adjacent
    `2 x 2` block coefficient for the two active block columns in the real
    Bartels-Stewart recurrence.  The diagonal blocks are the shifted column
    coefficients, and the off-diagonal blocks are the scalar couplings inside
    the supplied quasi-triangular diagonal block.  Scope: exact supplied-block
    algebra only; no Schur existence, block nonsingularity, or floating-point
    error propagation from (16.7)-(16.8) is asserted. -/
noncomputable def sylvesterTwoColumnBlockCoeff (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n) :
    Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real :=
  Matrix.fromBlocks
    (sylvesterTriangularShiftedCoeff m A (T p p))
    ((- (T q p)) • (1 : Matrix (Fin m) (Fin m) Real))
    ((- (T p q)) • (1 : Matrix (Fin m) (Fin m) Real))
    (sylvesterTriangularShiftedCoeff m A (T q q))

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), first-column
    quadratic coefficient induced by the supplied adjacent two-column block.
    A zero vector for the full block coefficient forces the first active
    column through this product-shift coefficient. -/
noncomputable def sylvesterTwoColumnBlockFirstQuadraticCoeff (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n) :
    Matrix (Fin m) (Fin m) Real :=
  sylvesterTriangularShiftedCoeff m A (T q q) *
      sylvesterTriangularShiftedCoeff m A (T p p) -
    Matrix.scalar (Fin m) (T q p * T p q)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), second-column
    quadratic coefficient induced by the supplied adjacent two-column block.
    This is the companion product-shift condition for the second active
    column. -/
noncomputable def sylvesterTwoColumnBlockSecondQuadraticCoeff (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n) :
    Matrix (Fin m) (Fin m) Real :=
  sylvesterTriangularShiftedCoeff m A (T p p) *
      sylvesterTriangularShiftedCoeff m A (T q q) -
    Matrix.scalar (Fin m) (T p q * T q p)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), structural
    kernel reduction for the supplied adjacent two-column block: a vector in
    the kernel of the `2 x 2` block coefficient has first and second active
    components in the kernels of the two product-shift quadratic coefficients.
    This is exact block algebra and does not use a supplied inverse. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_quadratic (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (z : Sum (Fin m) (Fin m) -> Real)
    (hz : Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0) :
    Matrix.mulVec (sylvesterTwoColumnBlockFirstQuadraticCoeff m n A T p q)
        (fun i : Fin m => z (Sum.inl i)) = 0 /\
      Matrix.mulVec (sylvesterTwoColumnBlockSecondQuadraticCoeff m n A T p q)
        (fun i : Fin m => z (Sum.inr i)) = 0 := by
  let u : Fin m -> Real := fun i => z (Sum.inl i)
  let v : Fin m -> Real := fun i => z (Sum.inr i)
  let P : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T p p)
  let Q : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T q q)
  have hP : Matrix.mulVec P u = fun i : Fin m => T q p * v i := by
    funext i
    have hi := congrFun hz (Sum.inl i)
    have hi' : Matrix.mulVec P u i + (-(T q p)) * v i = 0 := by
      simpa [sylvesterTwoColumnBlockCoeff, P, Q, u, v,
        Matrix.fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hi
    linarith
  have hQ : Matrix.mulVec Q v = fun i : Fin m => T p q * u i := by
    funext i
    have hi := congrFun hz (Sum.inr i)
    have hi' : Matrix.mulVec Q v i + (-(T p q)) * u i = 0 := by
      simpa [sylvesterTwoColumnBlockCoeff, P, Q, u, v,
        Matrix.fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        add_comm, add_left_comm, add_assoc] using hi
    linarith
  constructor
  case left =>
    funext i
    have hsmul : Matrix.mulVec Q (fun i : Fin m => T q p * v i) =
        fun i : Fin m => T q p * Matrix.mulVec Q v i := by
      simpa using Matrix.mulVec_smul Q (T q p) v
    calc
      Matrix.mulVec (sylvesterTwoColumnBlockFirstQuadraticCoeff m n A T p q) u i =
          Matrix.mulVec Q (Matrix.mulVec P u) i - (T q p * T p q) * u i := by
        simp [sylvesterTwoColumnBlockFirstQuadraticCoeff, P, Q, Matrix.sub_mulVec,
          Matrix.mulVec_mulVec, Matrix.scalar_apply]
      _ = Matrix.mulVec Q (fun i : Fin m => T q p * v i) i -
            (T q p * T p q) * u i := by rw [hP]
      _ = T q p * Matrix.mulVec Q v i - (T q p * T p q) * u i := by rw [hsmul]
      _ = T q p * (T p q * u i) - (T q p * T p q) * u i := by rw [hQ]
      _ = 0 := by ring
  case right =>
    funext i
    have hsmul : Matrix.mulVec P (fun i : Fin m => T p q * u i) =
        fun i : Fin m => T p q * Matrix.mulVec P u i := by
      simpa using Matrix.mulVec_smul P (T p q) u
    calc
      Matrix.mulVec (sylvesterTwoColumnBlockSecondQuadraticCoeff m n A T p q) v i =
          Matrix.mulVec P (Matrix.mulVec Q v) i - (T p q * T q p) * v i := by
        simp [sylvesterTwoColumnBlockSecondQuadraticCoeff, P, Q, Matrix.sub_mulVec,
          Matrix.mulVec_mulVec, Matrix.scalar_apply]
      _ = Matrix.mulVec P (fun i : Fin m => T p q * u i) i -
            (T p q * T q p) * v i := by rw [hQ]
      _ = T p q * Matrix.mulVec P u i - (T p q * T q p) * v i := by rw [hsmul]
      _ = T p q * (T q p * v i) - (T p q * T q p) * v i := by rw [hP]
      _ = 0 := by ring

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    bridge for the supplied adjacent two-column block: nonsingularity of the
    two induced product-shift quadratic coefficients rules out a kernel vector
    of the full `2 x 2` block coefficient. This removes the need for a
    supplied left/right inverse certificate at this local block step; the
    remaining source-level route is to derive these quadratic determinant
    hypotheses from the real-Schur scalar block separation data. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_quadratic_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hfirst :
      Not (Matrix.det
        (sylvesterTwoColumnBlockFirstQuadraticCoeff m n A T p q) = 0))
    (hsecond :
      Not (Matrix.det
        (sylvesterTwoColumnBlockSecondQuadraticCoeff m n A T p q) = 0)) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  intro hdet
  cases Matrix.exists_mulVec_eq_zero_iff.mpr hdet with
  | intro z hz =>
      have hzne : Not (z = 0) := hz.1
      have hzzero :
          Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0 := hz.2
      have hquad :=
        sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_quadratic
          m n A T p q z hzzero
      let u : Fin m -> Real := fun i => z (Sum.inl i)
      let v : Fin m -> Real := fun i => z (Sum.inr i)
      let M1 : Matrix (Fin m) (Fin m) Real :=
        sylvesterTwoColumnBlockFirstQuadraticCoeff m n A T p q
      let M2 : Matrix (Fin m) (Fin m) Real :=
        sylvesterTwoColumnBlockSecondQuadraticCoeff m n A T p q
      have hinj1 : Function.Injective (Matrix.mulVec M1) := by
        intro x y hxy
        have h := congrArg (Matrix.mulVec (Inv.inv M1)) hxy
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          Matrix.nonsing_inv_mul M1
            (isUnit_iff_ne_zero.mpr (by simpa [M1] using hfirst)),
          Matrix.one_mulVec, Matrix.one_mulVec] at h
        exact h
      have hinj2 : Function.Injective (Matrix.mulVec M2) := by
        intro x y hxy
        have h := congrArg (Matrix.mulVec (Inv.inv M2)) hxy
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          Matrix.nonsing_inv_mul M2
            (isUnit_iff_ne_zero.mpr (by simpa [M2] using hsecond)),
          Matrix.one_mulVec, Matrix.one_mulVec] at h
        exact h
      have hu : u = 0 := by
        apply hinj1
        rw [hquad.1, Matrix.mulVec_zero]
      have hv : v = 0 := by
        apply hinj2
        rw [hquad.2, Matrix.mulVec_zero]
      apply hzne
      funext r
      cases r with
      | inl i => simpa [u] using congrFun hu i
      | inr i => simpa [v] using congrFun hv i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    determinant symmetry for the supplied adjacent two-column block: the two
    quadratic coefficients have the same determinant.  This is exact algebra
    (`det (Q * P - c I) = det (P * Q - c I)`) and reduces the structural
    block nonsingularity route to a single product-shift determinant
    certificate. -/
theorem sylvesterTwoColumnBlockFirstQuadraticCoeff_det_eq_secondQuadraticCoeff_det
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n) :
    Matrix.det (sylvesterTwoColumnBlockFirstQuadraticCoeff m n A T p q) =
      Matrix.det (sylvesterTwoColumnBlockSecondQuadraticCoeff m n A T p q) := by
  let P : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T p p)
  let Q : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T q q)
  let c : Real := T q p * T p q
  have hchar := congrArg (fun f : Polynomial Real => f.eval c)
    (Matrix.charpoly_mul_comm Q P)
  change (Q * P).charpoly.eval c = (P * Q).charpoly.eval c at hchar
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly] at hchar
  have hleft : Matrix.scalar (Fin m) c - Q * P = -(Q * P - Matrix.scalar (Fin m) c) := by
    simp [neg_sub]
  have hright : Matrix.scalar (Fin m) c - P * Q = -(P * Q - Matrix.scalar (Fin m) c) := by
    simp [neg_sub]
  rw [hleft, hright, Matrix.det_neg, Matrix.det_neg] at hchar
  have hneg : Not ((-1 : Real) = 0) := by norm_num
  have hfactor : Not (((-1 : Real) ^ Fintype.card (Fin m)) = 0) :=
    pow_ne_zero (Fintype.card (Fin m)) hneg
  have hdet : Matrix.det (Q * P - Matrix.scalar (Fin m) c) =
      Matrix.det (P * Q - Matrix.scalar (Fin m) c) :=
    (mul_eq_mul_left_iff.mp hchar).resolve_right hfactor
  simpa [sylvesterTwoColumnBlockFirstQuadraticCoeff,
    sylvesterTwoColumnBlockSecondQuadraticCoeff, P, Q, c, mul_comm] using hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), structural
    determinant bridge for a supplied adjacent two-column block: it is enough
    to prove nonsingularity of one product-shift quadratic coefficient.  The
    companion quadratic determinant condition follows from
    `det (Q * P - c I) = det (P * Q - c I)`, so this is the one-certificate
    block nonsingularity surface needed before deriving the product-shift
    condition from real-Schur spectral separation data. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_first_quadratic_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hfirst :
      Not (Matrix.det
        (sylvesterTwoColumnBlockFirstQuadraticCoeff m n A T p q) = 0)) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  apply sylvesterTwoColumnBlockCoeff_det_ne_zero_of_quadratic_det_ne_zero
    m n A T p q hfirst
  intro hsecond
  exact hfirst
    ((sylvesterTwoColumnBlockFirstQuadraticCoeff_det_eq_secondQuadraticCoeff_det
      m n A T p q).trans hsecond)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    spectral certificate for a supplied adjacent two-column block: if the
    coupling product is not a root of the characteristic polynomial of the
    product of the two shifted column coefficients, then the full block
    coefficient is nonsingular.  This is the spectral-facing form of the
    one-quadratic determinant certificate. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_charpoly
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hchar :
      Not ((sylvesterTriangularShiftedCoeff m A (T q q) *
        sylvesterTriangularShiftedCoeff m A (T p p)).charpoly.eval
          (T q p * T p q) = 0)) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  apply sylvesterTwoColumnBlockCoeff_det_ne_zero_of_first_quadratic_det_ne_zero
  intro hdet
  let P : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T p p)
  let Q : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T q q)
  let c : Real := T q p * T p q
  have hdet' : Matrix.det (Q * P - Matrix.scalar (Fin m) c) = 0 := by
    simpa [sylvesterTwoColumnBlockFirstQuadraticCoeff, P, Q, c] using hdet
  have hleft : Matrix.scalar (Fin m) c - Q * P =
      -(Q * P - Matrix.scalar (Fin m) c) := by
    simp [neg_sub]
  have hcharzero : (Q * P).charpoly.eval c = 0 := by
    rw [Matrix.eval_charpoly, hleft, Matrix.det_neg, hdet', mul_zero]
  exact hchar (by simpa [P, Q, c] using hcharzero)



























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    spectral bridge for a supplied adjacent two-column block: a trivial kernel
    for the eigen-equation of the product of the two shifted column
    coefficients proves the characteristic-polynomial nonroot certificate. -/
theorem sylvesterTwoColumnBlockCoeff_product_shift_charpoly_ne_zero_of_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0) :
    Not ((sylvesterTriangularShiftedCoeff m A (T q q) *
      sylvesterTriangularShiftedCoeff m A (T p p)).charpoly.eval
        (T q p * T p q) = 0) := by
  exact
    finiteMatrix_charpoly_eval_ne_zero_of_mulVec_no_eigenvector
      (sylvesterTriangularShiftedCoeff m A (T q q) *
        sylvesterTriangularShiftedCoeff m A (T p p))
      (T q p * T p q) hker

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    nonroot bridge for a supplied adjacent two-column block: the source-shaped
    characteristic-polynomial exclusion for the shifted product implies the
    no-eigenvector hypothesis used by the active-block solve wrappers. -/
theorem sylvesterTwoColumnBlockCoeff_product_shift_no_eigenvector_of_charpoly_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hchar :
      Not ((sylvesterTriangularShiftedCoeff m A (T q q) *
        sylvesterTriangularShiftedCoeff m A (T p p)).charpoly.eval
          (T q p * T p q) = 0)) :
    forall x : Fin m -> Real,
      Matrix.mulVec
          (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p)) x =
        (fun i => (T q p * T p q) * x i) ->
      x = 0 := by
  exact
    finiteMatrix_mulVec_no_eigenvector_of_charpoly_eval_ne_zero
      (sylvesterTriangularShiftedCoeff m A (T q q) *
        sylvesterTriangularShiftedCoeff m A (T p p))
      (T q p * T p q) hchar

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    determinant bridge for a supplied adjacent two-column block: a nonsingular
    shifted product `(A - T_qq I) (A - T_pp I) - T_qp T_pq I` gives the
    no-eigenvector hypothesis needed by the existing block determinant and
    solve consequences. -/
theorem sylvesterTwoColumnBlockCoeff_product_shift_no_eigenvector_of_product_shift_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det
        (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p) -
          Matrix.scalar (Fin m) (T q p * T p q)) = 0)) :
    forall x : Fin m -> Real,
      Matrix.mulVec
          (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p)) x =
        (fun i => (T q p * T p q) * x i) ->
      x = 0 := by
  exact
    finiteMatrix_mulVec_no_eigenvector_of_det_sub_scalar_ne_zero
      (sylvesterTriangularShiftedCoeff m A (T q q) *
        sylvesterTriangularShiftedCoeff m A (T p p))
      (T q p * T p q) hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), structural
    spectrum bridge for a supplied adjacent two-column block: if the
    product-shift eigen-equation
    `(A - T_qq I) (A - T_pp I) x = (T_qp T_pq) x` has only the zero solution,
    then the full real-Schur two-column block coefficient is nonsingular. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  apply sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_charpoly
  exact
    sylvesterTwoColumnBlockCoeff_product_shift_charpoly_ne_zero_of_no_eigenvector
      m n A T p q hker

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    certificate through the no-eigenvector bridge: nonsingularity of the
    product-shift matrix gives nonsingularity of the supplied two-column block
    coefficient via the same product-shift kernel surface used by later solve
    wrappers. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det
        (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p) -
          Matrix.scalar (Fin m) (T q p * T p q)) = 0)) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  apply sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
  exact
    sylvesterTwoColumnBlockCoeff_product_shift_no_eigenvector_of_product_shift_det_ne_zero
      m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), block action
    of the left Sylvester factor on the two active columns.  This packages
    the exact operation `A [u v]` as one block-vector matrix action; it is
    only algebraic infrastructure for the real-Schur two-column route. -/
noncomputable def sylvesterTwoColumnBlockLeftAction (m : Nat)
    (A : RMatFn m m) :
    Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real :=
  Matrix.fromBlocks (Matrix.of A) 0 0 (Matrix.of A)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), block action
    of the supplied adjacent `2 x 2` real-Schur diagonal block on the two
    active columns.  The top-right and bottom-left scalar identity blocks
    follow the column equations
    `A u = T_pp u + T_qp v` and `A v = T_pq u + T_qq v`. -/
noncomputable def sylvesterTwoColumnBlockSchurAction (m n : Nat)
    (T : RMatFn n n) (p q : Fin n) :
    Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real :=
  Matrix.fromBlocks
    ((T p p) • (1 : Matrix (Fin m) (Fin m) Real))
    ((T q p) • (1 : Matrix (Fin m) (Fin m) Real))
    ((T p q) • (1 : Matrix (Fin m) (Fin m) Real))
    ((T q q) • (1 : Matrix (Fin m) (Fin m) Real))

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), two active
    columns packaged as an `m x 2` matrix.  Column `0` is `u` and column `1`
    is `v`; this is the standard matrix-intertwining shape behind the
    block-action certificate. -/
def sylvesterTwoColumnBlockColumnPair (m : Nat)
    (u v : Fin m -> Real) : Matrix (Fin m) (Fin 2) Real :=
  fun i k => if k = 0 then u i else v i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), the supplied
    adjacent real `2 x 2` Schur block acting on the two active columns. -/
def sylvesterTwoColumnRealSchurBlock (n : Nat)
    (T : RMatFn n n) (p q : Fin n) : Matrix (Fin 2) (Fin 2) Real :=
  fun r c =>
    if r = 0 then
      if c = 0 then T p p else T p q
    else
      if c = 0 then T q p else T q q

/-- A concrete complex eigenvector candidate for the adjacent `2 x 2` block,
    using a supplied complex root `mu` and the nonzero subdiagonal entry. -/
def sylvesterTwoColumnRealSchurBlockComplexRootVector (n : Nat)
    (T : RMatFn n n) (p q : Fin n) (mu : Complex) :
    Fin 2 -> Complex :=
  fun k => if k = 0 then mu - (T q q : Complex) else (T q p : Complex)

/-- The concrete complex root vector is nonzero when the subdiagonal entry of
    the adjacent `2 x 2` block is nonzero. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRootVector_ne_zero
    (n : Nat) (T : RMatFn n n) (p q : Fin n) (mu : Complex)
    (hsub : T q p ≠ 0) :
    sylvesterTwoColumnRealSchurBlockComplexRootVector n T p q mu ≠ 0 := by
  intro hzero
  have hentry := congrFun hzero (1 : Fin 2)
  have hc : ((T q p : Real) : Complex) = 0 := by
    simpa [sylvesterTwoColumnRealSchurBlockComplexRootVector] using hentry
  exact hsub (Complex.ofReal_eq_zero.mp hc)

/-- If `mu` is a supplied complex root of the characteristic equation of the
    adjacent `2 x 2` block and the subdiagonal entry is used in the concrete
    vector, then the vector is a complex eigenvector of the block. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRootVector_mulVec
    (n : Nat) (T : RMatFn n n) (p q : Fin n) (mu : Complex)
    (hroot :
      (((T p p : Real) : Complex) - mu) *
        (((T q q : Real) : Complex) - mu) -
          ((T p q : Real) : Complex) * ((T q p : Real) : Complex) = 0) :
    Matrix.mulVec
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
        (sylvesterTwoColumnRealSchurBlockComplexRootVector n T p q mu) =
      fun k => mu *
        sylvesterTwoColumnRealSchurBlockComplexRootVector n T p q mu k := by
  funext k
  fin_cases k
  · have hcoord :
        ((T p p : Real) : Complex) * (mu - ((T q q : Real) : Complex)) +
            ((T p q : Real) : Complex) * ((T q p : Real) : Complex) =
          mu * (mu - ((T q q : Real) : Complex)) := by
      calc
        ((T p p : Real) : Complex) * (mu - ((T q q : Real) : Complex)) +
            ((T p q : Real) : Complex) * ((T q p : Real) : Complex) =
          mu * (mu - ((T q q : Real) : Complex)) -
            ((((T p p : Real) : Complex) - mu) *
              (((T q q : Real) : Complex) - mu) -
                ((T p q : Real) : Complex) * ((T q p : Real) : Complex)) := by
          ring
        _ = mu * (mu - ((T q q : Real) : Complex)) := by rw [hroot, sub_zero]
    simpa [Matrix.mulVec, dotProduct, realMatrixToComplex,
      sylvesterTwoColumnRealSchurBlock,
      sylvesterTwoColumnRealSchurBlockComplexRootVector,
      Fin.sum_univ_two] using hcoord
  · have hcoord :
        ((T q p : Real) : Complex) * (mu - ((T q q : Real) : Complex)) +
            ((T q q : Real) : Complex) * ((T q p : Real) : Complex) =
          mu * ((T q p : Real) : Complex) := by
      ring
    simpa [Matrix.mulVec, dotProduct, realMatrixToComplex,
      sylvesterTwoColumnRealSchurBlock,
      sylvesterTwoColumnRealSchurBlockComplexRootVector,
      Fin.sum_univ_two] using hcoord

/-- The standard complex root of the adjacent real `2 x 2` block when the
    real discriminant is negative and `delta` supplies its positive square
    root magnitude. -/
noncomputable def sylvesterTwoColumnRealSchurBlockComplexRoot (n : Nat)
    (T : RMatFn n n) (p q : Fin n) (delta : Real) : Complex :=
  ((((T p p + T q q) / 2 : Real) : Complex) +
    Complex.I * (((delta / 2 : Real) : Complex)))

/-- The standard complex root satisfies the characteristic equation of the
    adjacent real `2 x 2` block whenever `delta^2` is the negative
    discriminant. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRoot_root_of_delta_sq
    (n : Nat) (T : RMatFn n n) (p q : Fin n) (delta : Real)
    (hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p)) :
    (((T p p : Real) : Complex) -
        sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta) *
      (((T q q : Real) : Complex) -
        sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta) -
        ((T p q : Real) : Complex) * ((T q p : Real) : Complex) = 0 := by
  apply Complex.ext
  · simp [sylvesterTwoColumnRealSchurBlockComplexRoot, Complex.mul_re,
      Complex.mul_im]
    nlinarith [hdelta]
  · simp [sylvesterTwoColumnRealSchurBlockComplexRoot, Complex.mul_re,
      Complex.mul_im]
    ring

/-- A nonzero negative-discriminant square-root certificate rules out real
    eigenlines for the adjacent `2 x 2` block. -/
theorem sylvesterTwoColumnRealSchurBlock_no_real_eigenvector_of_delta_sq_ne_zero
    (n : Nat) (T : RMatFn n n) (p q : Fin n) (delta : Real)
    (hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p))
    (hdelta_ne : delta ≠ 0) :
    ∀ x : Fin 2 -> Real, x ≠ 0 ->
      ¬ ∃ nu : Real,
        Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
          fun k => nu * x k := by
  intro x hxne hEig
  rcases hEig with ⟨nu, hnu⟩
  have hxzero :
      Matrix.mulVec
          (sylvesterTwoColumnRealSchurBlock n T p q -
            Matrix.scalar (Fin 2) nu) x = 0 := by
    funext k
    have hk := congrFun hnu k
    have hcoord :
        Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x k -
            nu * x k = 0 := by
      rw [hk]
      ring
    simpa [Matrix.sub_mulVec, Matrix.scalar_apply] using hcoord
  have hdet :
      Matrix.det
          (sylvesterTwoColumnRealSchurBlock n T p q -
            Matrix.scalar (Fin 2) nu) = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hxne, hxzero⟩
  have hroot :
      (T p p - nu) * (T q q - nu) - T p q * T q p = 0 := by
    simpa [sylvesterTwoColumnRealSchurBlock, Matrix.det_fin_two,
      Matrix.scalar_apply] using hdet
  have hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p =
        (T p p + T q q - 2 * nu) ^ 2 := by
    nlinarith [hroot]
  have hsum :
      delta ^ 2 + (T p p + T q q - 2 * nu) ^ 2 = 0 := by
    nlinarith [hdelta, hdisc]
  have hdelta_pos : 0 < delta ^ 2 := sq_pos_of_ne_zero hdelta_ne
  have hsquare_nonneg : 0 ≤ (T p p + T q q - 2 * nu) ^ 2 := sq_nonneg _
  nlinarith

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), converse
    two-by-two spectral certificate: a nonnegative real discriminant for the
    adjacent real Schur block gives a concrete real eigenline.  This is the
    algebraic obstruction to treating such a block as a genuine irreducible
    real `2 x 2` block. -/
theorem sylvesterTwoColumnRealSchurBlock_exists_real_eigenvector_of_disc_nonneg
    (n : Nat) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      0 ≤ (T p p - T q q) ^ 2 + 4 * T p q * T q p) :
    exists x : Fin 2 -> Real, x ≠ 0 ∧
      exists nu : Real,
        Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
          fun k => nu * x k := by
  by_cases hsub : T q p = 0
  · let x : Fin 2 -> Real := fun k => if k = 0 then 1 else 0
    refine ⟨x, ?_, T p p, ?_⟩
    · intro hx
      have hcoord := congrFun hx (0 : Fin 2)
      norm_num [x] at hcoord
    · funext k
      fin_cases k
      · simp [x, Matrix.mulVec, dotProduct, sylvesterTwoColumnRealSchurBlock]
      · simp [x, Matrix.mulVec, dotProduct, sylvesterTwoColumnRealSchurBlock,
          hsub]
  · let disc : Real := (T p p - T q q) ^ 2 + 4 * T p q * T q p
    let nu : Real := (T p p + T q q + Real.sqrt disc) / 2
    let x : Fin 2 -> Real := fun k => if k = 0 then nu - T q q else T q p
    have hdisc_nonneg : 0 ≤ disc := by
      dsimp [disc]
      exact hdisc
    have hsqrt : (Real.sqrt disc) ^ 2 = disc := Real.sq_sqrt hdisc_nonneg
    have hroot : (T p p - nu) * (T q q - nu) - T p q * T q p = 0 := by
      dsimp [nu, disc] at hsqrt ⊢
      nlinarith [hsqrt]
    refine ⟨x, ?_, nu, ?_⟩
    · intro hx
      have hcoord := congrFun hx (1 : Fin 2)
      exact hsub (by simpa [x] using hcoord)
    · funext k
      fin_cases k
      · have hcoord :
            T p p * (nu - T q q) + T p q * T q p =
              nu * (nu - T q q) := by
          nlinarith [hroot]
        simpa [x, Matrix.mulVec, dotProduct, sylvesterTwoColumnRealSchurBlock,
          Fin.sum_univ_two] using hcoord
      · have hcoord :
            T q p * (nu - T q q) + T q q * T q p =
              nu * T q p := by
          ring
        simpa [x, Matrix.mulVec, dotProduct, sylvesterTwoColumnRealSchurBlock,
          Fin.sum_univ_two] using hcoord

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), irreducible
    real `2 x 2` block discriminant certificate: if the adjacent real Schur
    block has no nonzero real eigenline, then its discriminant is negative. -/
theorem sylvesterTwoColumnRealSchurBlock_disc_neg_of_no_real_eigenvector
    (n : Nat) (T : RMatFn n n) (p q : Fin n)
    (hno :
      forall x : Fin 2 -> Real, x ≠ 0 ->
        Not (exists nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k)) :
    (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0 := by
  by_contra hnot
  have hdisc :
      0 ≤ (T p p - T q q) ^ 2 + 4 * T p q * T q p := by
    linarith
  rcases sylvesterTwoColumnRealSchurBlock_exists_real_eigenvector_of_disc_nonneg
      n T p q hdisc with ⟨x, hxne, nu, hnu⟩
  exact hno x hxne ⟨nu, hnu⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), matrix
    intertwining form: the coupled active-column equations are equivalent to
    `A * U = U * J`, where `U` is the two-column matrix `(u, v)` and `J` is
    the supplied adjacent real `2 x 2` Schur block.  This is the standard
    spectral-facing target for the still-open complex separation proof. -/
theorem sylvesterTwoColumnBlock_coupled_block_action_iff_columnPair_intertwining
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (u v : Fin m -> Real) :
    (Matrix.mulVec (Matrix.of A) u =
          (fun i => T p p * u i + T q p * v i) ∧
        Matrix.mulVec (Matrix.of A) v =
          (fun i => T p q * u i + T q q * v i)) ↔
      Matrix.of A * sylvesterTwoColumnBlockColumnPair m u v =
        sylvesterTwoColumnBlockColumnPair m u v *
          sylvesterTwoColumnRealSchurBlock n T p q := by
  constructor
  · intro h
    rcases h with ⟨hu, hv⟩
    ext i k
    fin_cases k
    · have hi := congrFun hu i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        sylvesterTwoColumnBlockColumnPair, sylvesterTwoColumnRealSchurBlock,
        Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc] using hi
    · have hi := congrFun hv i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        sylvesterTwoColumnBlockColumnPair, sylvesterTwoColumnRealSchurBlock,
        Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc] using hi
  · intro h
    constructor
    · funext i
      have hi := congrFun (congrFun h i) (0 : Fin 2)
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        sylvesterTwoColumnBlockColumnPair, sylvesterTwoColumnRealSchurBlock,
        Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc] using hi
    · funext i
      have hi := congrFun (congrFun h i) (1 : Fin 2)
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        sylvesterTwoColumnBlockColumnPair, sylvesterTwoColumnRealSchurBlock,
        Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc] using hi

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): for a leading
    same-labelled adjacent `2 x 2` real-quasi-Schur block, the two coordinate
    columns intertwine the full Schur factor with its extracted principal
    block.  The `hmin` hypothesis says that this block has no earlier block
    labels; it is essential, since an interior upper-quasi-triangular block
    can have nonzero couplings from earlier rows into these two columns. -/
theorem sylvesterTwoColumnLeadingBlock_columnPair_intertwining_of_quasiSchur
    (n : Nat) (T : RMatFn n n) (pmap : Fin n -> Nat) (p q : Fin n)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hmin : forall i : Fin n, Not (pmap i < pmap p)) :
    Matrix.of T *
        sylvesterTwoColumnBlockColumnPair n
          (fun i : Fin n => if i = p then 1 else 0)
          (fun i : Fin n => if i = q then 1 else 0) =
      sylvesterTwoColumnBlockColumnPair n
          (fun i : Fin n => if i = p then 1 else 0)
          (fun i : Fin n => if i = q then 1 else 0) *
        sylvesterTwoColumnRealSchurBlock n T p q := by
  classical
  let u : Fin n -> Real := fun i => if i = p then 1 else 0
  let v : Fin n -> Real := fun i => if i = q then 1 else 0
  have hpq_lt : p < q := Fin.lt_def.mpr (by omega)
  have hp_ne_q : p ≠ q := ne_of_lt hpq_lt
  have hzero_out :
      forall i : Fin n, i ≠ p -> i ≠ q -> T i p = 0 /\ T i q = 0 := by
    intro i hip hiq
    have hlabel_ne : pmap i ≠ pmap p := by
      intro hlabel
      rcases quasiSchur_blockMap_eq_left_or_right_of_adjacent_same_block
          n pmap p q i hcard hpq hsame hlabel with hleft | hright
      · exact hip hleft
      · exact hiq hright
    have hle : pmap p <= pmap i := le_of_not_gt (hmin i)
    have hlt : pmap p < pmap i := lt_of_le_of_ne hle hlabel_ne.symm
    exact ⟨hzero i p hlt, hzero i q (by simpa [hsame] using hlt)⟩
  have hcolp : Matrix.mulVec (Matrix.of T) u = fun i : Fin n => T i p := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.of_apply, u]
  have hcolq : Matrix.mulVec (Matrix.of T) v = fun i : Fin n => T i q := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.of_apply, v]
  apply
    (sylvesterTwoColumnBlock_coupled_block_action_iff_columnPair_intertwining
      n n T T p q u v).mp
  constructor
  · funext i
    rw [hcolp]
    by_cases hip : i = p
    · subst i
      simp [u, v, hp_ne_q]
    by_cases hiq : i = q
    · subst i
      simp [u, v, hip]
    have hz := hzero_out i hip hiq
    simp [u, v, hip, hiq, hz.1]
  · funext i
    rw [hcolq]
    by_cases hip : i = p
    · subst i
      simp [u, v, hp_ne_q]
    by_cases hiq : i = q
    · subst i
      simp [u, v, hip]
    have hz := hzero_out i hip hiq
    simp [u, v, hip, hiq, hz.2]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): a complex right
    eigenvalue of a leading real-quasi-Schur `2 x 2` block is a complex right
    eigenvalue of the full complexified Schur factor.  This is the leading
    block case of the spectral transport needed to turn global no-common
    spectrum assumptions into local Bartels-Stewart block certificates. -/
theorem hasComplexRightEigenvalue_realMatrixToComplex_of_leading_twoBlock_quasiSchur
    (n : Nat) (T : RMatFn n n) (pmap : Fin n -> Nat) (p q : Fin n)
    (mu : Complex)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hmin : forall i : Fin n, Not (pmap i < pmap p))
    (hblock :
      HasComplexRightEigenvalue
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) mu) :
    HasComplexRightEigenvalue (realMatrixToComplex (Matrix.of T)) mu := by
  classical
  rcases hblock with ⟨w, hwne, hw⟩
  let u : Fin n -> Real := fun i => if i = p then 1 else 0
  let v : Fin n -> Real := fun i => if i = q then 1 else 0
  let X : Matrix (Fin n) (Fin 2) Real := sylvesterTwoColumnBlockColumnPair n u v
  have hpq_lt : p < q := Fin.lt_def.mpr (by omega)
  have hp_ne_q : p ≠ q := ne_of_lt hpq_lt
  have hXreal :
      Matrix.of T * X = X * sylvesterTwoColumnRealSchurBlock n T p q := by
    simpa [X, u, v] using
      sylvesterTwoColumnLeadingBlock_columnPair_intertwining_of_quasiSchur
        n T pmap p q hcard hzero hpq hsame hmin
  have hXc :
      realMatrixToComplex (Matrix.of T) * realMatrixToComplex X =
        realMatrixToComplex X *
          realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q) :=
    realMatrixToComplex_intertwining_of_real
      (Matrix.of T) (sylvesterTwoColumnRealSchurBlock n T p q) X hXreal
  have hXw : Matrix.mulVec (realMatrixToComplex X) w ≠ 0 := by
    intro hzero
    have hw0 : w 0 = 0 := by
      have hpcoord := congrFun hzero p
      simpa [X, u, v, sylvesterTwoColumnBlockColumnPair,
        realMatrixToComplex, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        hp_ne_q] using hpcoord
    have hw1 : w 1 = 0 := by
      have hqcoord := congrFun hzero q
      simpa [X, u, v, sylvesterTwoColumnBlockColumnPair,
        realMatrixToComplex, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Ne.symm hp_ne_q] using hqcoord
    exact hwne (by
      funext k
      fin_cases k
      · exact hw0
      · exact hw1)
  exact
    finiteComplexMatrix_exists_mulVec_eigenpair_of_intertwiner_image_ne_zero
      (realMatrixToComplex (Matrix.of T))
      (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
      (realMatrixToComplex X) mu w hXc hw hXw

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): leading-block
    transport from a global no-common-complex-right-eigenvalue hypothesis for
    the full Schur factor to the local no-common hypothesis for the extracted
    adjacent `2 x 2` real-Schur block. -/
theorem noCommonComplexRightEigenvalue_of_leading_twoBlock_quasiSchur
    (m n : Nat) (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hmin : forall i : Fin n, Not (pmap i < pmap p))
    (hno :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of A))
        (realMatrixToComplex (Matrix.of T))) :
    NoCommonComplexRightEigenvalue
      (realMatrixToComplex (Matrix.of A))
      (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) := by
  intro mu hpair
  exact hno mu ⟨hpair.1,
    hasComplexRightEigenvalue_realMatrixToComplex_of_leading_twoBlock_quasiSchur
      n T pmap p q mu hcard hzero hpq hsame hmin hpair.2⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): the `toSquareBlock`
    fiber of a same-labelled adjacent real-quasi-Schur `2 x 2` block is the
    concrete adjacent block used by the two-column Sylvester recurrence, after
    reindexing the fiber by `0 ↦ p`, `1 ↦ q`. -/
theorem realMatrixToComplex_toSquareBlock_sameBlock_reindex
    (n : Nat) (T : RMatFn n n) (pmap : Fin n -> Nat) (p q : Fin n)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q) :
    Matrix.reindex
        (adjacentSameBlockFiberEquiv n pmap p q hcard hpq hsame).symm
        (adjacentSameBlockFiberEquiv n pmap p q hcard hpq hsame).symm
        ((realMatrixToComplex (Matrix.of T)).toSquareBlock pmap (pmap p)) =
      realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.reindex_apply, Matrix.toSquareBlock_def,
      adjacentSameBlockFiberEquiv, realMatrixToComplex,
      sylvesterTwoColumnRealSchurBlock, Matrix.of_apply]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): an eigenvalue of
    an arbitrary same-labelled adjacent `2 x 2` real-quasi-Schur block is an
    eigenvalue of the full complexified Schur factor.  Unlike the leading-block
    transport above, this proof uses Mathlib's block-triangular charpoly
    factorization, so it also handles interior blocks with upper couplings from
    earlier Schur blocks. -/
theorem hasComplexRightEigenvalue_realMatrixToComplex_of_sameBlock_twoBlock_quasiSchur
    (n : Nat) (T : RMatFn n n) (pmap : Fin n -> Nat) (p q : Fin n)
    (mu : Complex)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hBT :
      (realMatrixToComplex (Matrix.of T)).BlockTriangular pmap)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hblock :
      HasComplexRightEigenvalue
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) mu) :
    HasComplexRightEigenvalue (realMatrixToComplex (Matrix.of T)) mu := by
  classical
  let e := adjacentSameBlockFiberEquiv n pmap p q hcard hpq hsame
  let M : Matrix (Fin n) (Fin n) Complex := realMatrixToComplex (Matrix.of T)
  let N : Matrix { i : Fin n // pmap i = pmap p } { i : Fin n // pmap i = pmap p } Complex :=
    M.toSquareBlock pmap (pmap p)
  let B : Matrix (Fin 2) (Fin 2) Complex :=
    realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)
  have hreindex : Matrix.reindex e.symm e.symm N = B := by
    simpa [e, M, N, B] using
      realMatrixToComplex_toSquareBlock_sameBlock_reindex
        n T pmap p q hcard hpq hsame
  have hBchar : B.charpoly.eval mu = 0 :=
    (finiteComplexMatrix_hasComplexRightEigenvalue_iff_charpoly_eval_eq_zero
      B mu).mp (by simpa [B] using hblock)
  have hNchar : N.charpoly.eval mu = 0 := by
    have hcharReindex :=
      congrArg (fun P : Polynomial Complex => P.eval mu)
        (Matrix.charpoly_reindex e.symm N)
    rw [hreindex] at hcharReindex
    exact hcharReindex.symm.trans hBchar
  have hN :
      HasComplexRightEigenvalue N mu :=
    (finiteComplexMatrix_hasComplexRightEigenvalue_iff_charpoly_eval_eq_zero
      N mu).mpr hNchar
  exact
    hasComplexRightEigenvalue_of_blockTriangular_toSquareBlock
      M pmap (pmap p) mu (by simpa [M] using hBT) hN

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): transport a
    global no-common-complex-right-eigenvalue hypothesis for the full Schur
    factor to an arbitrary same-labelled adjacent `2 x 2` block. -/
theorem noCommonComplexRightEigenvalue_of_sameBlock_twoBlock_quasiSchur
    (m n : Nat) (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hBT :
      (realMatrixToComplex (Matrix.of T)).BlockTriangular pmap)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hno :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of A))
        (realMatrixToComplex (Matrix.of T))) :
    NoCommonComplexRightEigenvalue
      (realMatrixToComplex (Matrix.of A))
      (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) := by
  intro mu hpair
  exact hno mu ⟨hpair.1,
    hasComplexRightEigenvalue_realMatrixToComplex_of_sameBlock_twoBlock_quasiSchur
      n T pmap p q mu hcard hBT hpq hsame hpair.2⟩

/-- The fiber over a singleton real-quasi-Schur block label is canonically a
    one-element index set. -/
def singletonBlockFiberEquiv (n : Nat) (pmap : Fin n -> Nat) (k : Fin n)
    (hsingle : forall i : Fin n, pmap i = pmap k -> i = k) :
    Fin 1 ≃ { i : Fin n // pmap i = pmap k } where
  toFun _ := ⟨k, rfl⟩
  invFun _ := 0
  left_inv i := Subsingleton.elim _ _
  right_inv i := by
    apply Subtype.ext
    exact (hsingle i.1 i.2).symm

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): the
    `toSquareBlock` fiber of a singleton-labelled real-quasi-Schur block is
    the scalar `1 x 1` block containing the diagonal entry. -/
theorem realMatrixToComplex_toSquareBlock_singleton_reindex
    (n : Nat) (T : RMatFn n n) (pmap : Fin n -> Nat) (k : Fin n)
    (hsingle : forall i : Fin n, pmap i = pmap k -> i = k) :
    Matrix.reindex
        (singletonBlockFiberEquiv n pmap k hsingle).symm
        (singletonBlockFiberEquiv n pmap k hsingle).symm
        ((realMatrixToComplex (Matrix.of T)).toSquareBlock pmap (pmap k)) =
      realMatrixToComplex (Matrix.of (fun _ _ : Fin 1 => T k k)) := by
  ext r c
  fin_cases r
  fin_cases c
  simp [Matrix.reindex_apply, Matrix.toSquareBlock_def,
    singletonBlockFiberEquiv, realMatrixToComplex, Matrix.of_apply]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): an eigenvalue of
    a singleton scalar block in a block-triangular real-quasi-Schur factor is
    an eigenvalue of the full complexified Schur factor. -/
theorem hasComplexRightEigenvalue_realMatrixToComplex_of_singletonBlock_quasiSchur
    (n : Nat) (T : RMatFn n n) (pmap : Fin n -> Nat) (k : Fin n)
    (mu : Complex)
    (hBT :
      (realMatrixToComplex (Matrix.of T)).BlockTriangular pmap)
    (hsingle : forall i : Fin n, pmap i = pmap k -> i = k)
    (hblock :
      HasComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of (fun _ _ : Fin 1 => T k k))) mu) :
    HasComplexRightEigenvalue (realMatrixToComplex (Matrix.of T)) mu := by
  classical
  let e := singletonBlockFiberEquiv n pmap k hsingle
  let M : Matrix (Fin n) (Fin n) Complex := realMatrixToComplex (Matrix.of T)
  let N : Matrix { i : Fin n // pmap i = pmap k }
      { i : Fin n // pmap i = pmap k } Complex :=
    M.toSquareBlock pmap (pmap k)
  let B : Matrix (Fin 1) (Fin 1) Complex :=
    realMatrixToComplex (Matrix.of (fun _ _ : Fin 1 => T k k))
  have hreindex : Matrix.reindex e.symm e.symm N = B := by
    simpa [e, M, N, B] using
      realMatrixToComplex_toSquareBlock_singleton_reindex
        n T pmap k hsingle
  have hBchar : B.charpoly.eval mu = 0 :=
    (finiteComplexMatrix_hasComplexRightEigenvalue_iff_charpoly_eval_eq_zero
      B mu).mp (by simpa [B] using hblock)
  have hNchar : N.charpoly.eval mu = 0 := by
    have hcharReindex :=
      congrArg (fun P : Polynomial Complex => P.eval mu)
        (Matrix.charpoly_reindex e.symm N)
    rw [hreindex] at hcharReindex
    exact hcharReindex.symm.trans hBchar
  have hN :
      HasComplexRightEigenvalue N mu :=
    (finiteComplexMatrix_hasComplexRightEigenvalue_iff_charpoly_eval_eq_zero
      N mu).mpr hNchar
  exact
    hasComplexRightEigenvalue_of_blockTriangular_toSquareBlock
      M pmap (pmap k) mu (by simpa [M] using hBT) hN

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): transport a
    global no-common-complex-right-eigenvalue hypothesis for the full Schur
    factor to a singleton scalar block. -/
theorem noCommonComplexRightEigenvalue_of_singletonBlock_quasiSchur
    (m n : Nat) (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (k : Fin n)
    (hBT :
      (realMatrixToComplex (Matrix.of T)).BlockTriangular pmap)
    (hsingle : forall i : Fin n, pmap i = pmap k -> i = k)
    (hno :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of A))
        (realMatrixToComplex (Matrix.of T))) :
    NoCommonComplexRightEigenvalue
      (realMatrixToComplex (Matrix.of A))
      (realMatrixToComplex (Matrix.of (fun _ _ : Fin 1 => T k k))) := by
  intro mu hpair
  exact hno mu ⟨hpair.1,
    hasComplexRightEigenvalue_realMatrixToComplex_of_singletonBlock_quasiSchur
      n T pmap k mu hBT hsingle hpair.2⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), complexified
    two-column intertwining bridge: a real identity `A * U = U * J` for the
    active two-column matrix and supplied adjacent real Schur block remains
    valid after entrywise complexification, so it can be consumed by complex
    spectral/eigenvector lemmas. -/
theorem sylvesterTwoColumnBlock_columnPair_intertwining_complexification
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (u v : Fin m -> Real)
    (hX :
      Matrix.of A * sylvesterTwoColumnBlockColumnPair m u v =
        sylvesterTwoColumnBlockColumnPair m u v *
          sylvesterTwoColumnRealSchurBlock n T p q) :
    realMatrixToComplex (Matrix.of A) *
        realMatrixToComplex (sylvesterTwoColumnBlockColumnPair m u v) =
      realMatrixToComplex (sylvesterTwoColumnBlockColumnPair m u v) *
        realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q) :=
  realMatrixToComplex_intertwining_of_real
    (Matrix.of A) (sylvesterTwoColumnRealSchurBlock n T p q)
    (sylvesterTwoColumnBlockColumnPair m u v) hX

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), kernel
    invariance for a two-column intertwiner: if the active column pair
    satisfies `A * U = U * J`, then the real kernel of `U` is invariant under
    the supplied adjacent `2 x 2` Schur block `J`.  This is a preparatory
    algebraic step for ruling out nonzero block-action witnesses from
    irreducible real-Schur block separation. -/
theorem sylvesterTwoColumnBlock_columnPair_kernel_invariant
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (u v : Fin m -> Real)
    (hX :
      Matrix.of A * sylvesterTwoColumnBlockColumnPair m u v =
        sylvesterTwoColumnBlockColumnPair m u v *
          sylvesterTwoColumnRealSchurBlock n T p q)
    {x : Fin 2 -> Real}
    (hx :
      Matrix.mulVec (sylvesterTwoColumnBlockColumnPair m u v) x = 0) :
    Matrix.mulVec (sylvesterTwoColumnBlockColumnPair m u v)
        (Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x) = 0 :=
  finiteRealMatrix_intertwiner_kernel_invariant
    (Matrix.of A) (sylvesterTwoColumnRealSchurBlock n T p q)
    (sylvesterTwoColumnBlockColumnPair m u v) hX hx

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), no-real-line
    consequence for the two-column intertwiner: if the supplied adjacent
    `2 x 2` Schur block has no real eigenvector and the active column-pair
    map is nonzero, then the column-pair map has trivial real kernel.  This
    is the source-shaped irreducibility dependency before deriving the full
    no-block-action certificate from complex spectral separation. -/
theorem sylvesterTwoColumnBlock_columnPair_mulVec_eq_zero_of_no_real_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (u v : Fin m -> Real)
    (hX :
      Matrix.of A * sylvesterTwoColumnBlockColumnPair m u v =
        sylvesterTwoColumnBlockColumnPair m u v *
          sylvesterTwoColumnRealSchurBlock n T p q)
    (hU : sylvesterTwoColumnBlockColumnPair m u v ≠ 0)
    (hno :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ mu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => mu * x k) :
    ∀ x : Fin 2 -> Real,
      Matrix.mulVec (sylvesterTwoColumnBlockColumnPair m u v) x = 0 ->
        x = 0 :=
  finiteRealMatrix_intertwiner_mulVec_eq_zero_of_no_real_eigenvector
    (Matrix.of A) (sylvesterTwoColumnRealSchurBlock n T p q)
    (sylvesterTwoColumnBlockColumnPair m u v) hX hU hno

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), complexified
    nonzero-image bridge for the two-column intertwiner: if the adjacent
    `2 x 2` real Schur block has no real eigenvector and the active
    column-pair map is nonzero, then every nonzero complex vector has nonzero
    image under the complexified column-pair map. -/
theorem sylvesterTwoColumnBlock_columnPair_complex_mulVec_ne_zero_of_no_real_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (u v : Fin m -> Real)
    (hX :
      Matrix.of A * sylvesterTwoColumnBlockColumnPair m u v =
        sylvesterTwoColumnBlockColumnPair m u v *
          sylvesterTwoColumnRealSchurBlock n T p q)
    (hU : sylvesterTwoColumnBlockColumnPair m u v ≠ 0)
    (hno :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ mu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => mu * x k)
    {w : Fin 2 -> Complex}
    (hw : w ≠ 0) :
    Matrix.mulVec
        (realMatrixToComplex (sylvesterTwoColumnBlockColumnPair m u v)) w ≠ 0 :=
  realMatrixToComplex_mulVec_ne_zero_of_real_kernel_trivial
    (sylvesterTwoColumnBlockColumnPair m u v)
    (sylvesterTwoColumnBlock_columnPair_mulVec_eq_zero_of_no_real_eigenvector
      m n A T p q u v hX hU hno)
    hw

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), block-action
    packaging: the two coupled active-column equations are equivalent to
    equality of the left `A` action and the supplied `2 x 2` Schur-block
    action on the concatenated vector `(u, v)`.  This is the algebraic target
    that a future real-Schur spectral-separation theorem can rule out. -/
theorem sylvesterTwoColumnBlock_coupled_block_action_iff_leftAction_eq_schurAction
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (u v : Fin m -> Real) :
    (Matrix.mulVec (Matrix.of A) u =
          (fun i => T p p * u i + T q p * v i) ∧
        Matrix.mulVec (Matrix.of A) v =
          (fun i => T p q * u i + T q q * v i)) ↔
      Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A)
          (Sum.elim u v) =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q)
          (Sum.elim u v) := by
  constructor
  · intro h
    rcases h with ⟨hu, hv⟩
    funext r
    cases r with
    | inl i =>
        have hi := congrFun hu i
        rw [sylvesterTwoColumnBlockLeftAction, sylvesterTwoColumnBlockSchurAction,
          Matrix.fromBlocks_mulVec, Matrix.fromBlocks_mulVec]
        simp only [Sum.elim_inl, Matrix.smul_mulVec, Matrix.one_mulVec,
          Pi.add_apply]
        simpa using hi
    | inr i =>
        have hi := congrFun hv i
        rw [sylvesterTwoColumnBlockLeftAction, sylvesterTwoColumnBlockSchurAction,
          Matrix.fromBlocks_mulVec, Matrix.fromBlocks_mulVec]
        simp only [Sum.elim_inr, Matrix.smul_mulVec, Matrix.one_mulVec,
          Pi.add_apply]
        simpa [add_comm, add_left_comm, add_assoc] using hi
  · intro h
    constructor
    · funext i
      have hi := congrFun h (Sum.inl i)
      rw [sylvesterTwoColumnBlockLeftAction, sylvesterTwoColumnBlockSchurAction,
        Matrix.fromBlocks_mulVec, Matrix.fromBlocks_mulVec] at hi
      simp only [Sum.elim_inl, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.add_apply] at hi
      simpa using hi
    · funext i
      have hi := congrFun h (Sum.inr i)
      rw [sylvesterTwoColumnBlockLeftAction, sylvesterTwoColumnBlockSchurAction,
        Matrix.fromBlocks_mulVec, Matrix.fromBlocks_mulVec] at hi
      simp only [Sum.elim_inr, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.add_apply] at hi
      simpa [add_comm, add_left_comm, add_assoc] using hi

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), active-block
    kernel packaging: the supplied two-column block coefficient kills the
    concatenated vector `(u, v)` exactly when the two coupled column-action
    equations hold. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_sumElim_eq_zero_iff_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (u v : Fin m -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
        (Sum.elim u v) = 0 ↔
      Matrix.mulVec (Matrix.of A) u =
          (fun i => T p p * u i + T q p * v i) ∧
        Matrix.mulVec (Matrix.of A) v =
          (fun i => T p q * u i + T q q * v i) := by
  constructor
  · intro hzero
    constructor
    · funext i
      have hi := congrFun hzero (Sum.inl i)
      have hi' :
          Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T p p)) u i +
              (-(T q p)) * v i = 0 := by
        simpa [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec,
          Matrix.smul_mulVec, Matrix.one_mulVec] using hi
      have hP := sylvesterTriangularShiftedCoeff_mulVec_apply m A (T p p) u i
      have hP' :
          Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T p p)) u i =
            Matrix.mulVec (Matrix.of A) u i - T p p * u i := by
        simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using hP
      linarith
    · funext i
      have hi := congrFun hzero (Sum.inr i)
      have hi' :
          Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T q q)) v i +
              (-(T p q)) * u i = 0 := by
        simpa [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec,
          Matrix.smul_mulVec, Matrix.one_mulVec, add_comm, add_left_comm, add_assoc]
          using hi
      have hQ := sylvesterTriangularShiftedCoeff_mulVec_apply m A (T q q) v i
      have hQ' :
          Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T q q)) v i =
            Matrix.mulVec (Matrix.of A) v i - T q q * v i := by
        simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using hQ
      linarith
  · intro haction
    rcases haction with ⟨hu, hv⟩
    funext r
    cases r with
    | inl i =>
        have hi := congrFun hu i
        have hP := sylvesterTriangularShiftedCoeff_mulVec_apply m A (T p p) u i
        have hP' :
            Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T p p)) u i =
              Matrix.mulVec (Matrix.of A) u i - T p p * u i := by
          simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using hP
        have hgoal :
            Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T p p)) u i +
                (-(T q p)) * v i = 0 := by
          linarith
        simpa [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec,
          Matrix.smul_mulVec, Matrix.one_mulVec] using hgoal
    | inr i =>
        have hi := congrFun hv i
        have hQ := sylvesterTriangularShiftedCoeff_mulVec_apply m A (T q q) v i
        have hQ' :
            Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T q q)) v i =
              Matrix.mulVec (Matrix.of A) v i - T q q * v i := by
          simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using hQ
        have hgoal :
            Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T q q)) v i +
                (-(T p q)) * u i = 0 := by
          linarith
        simpa [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec,
          Matrix.smul_mulVec, Matrix.one_mulVec, add_comm, add_left_comm, add_assoc]
          using hgoal

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), block-kernel
    separation packaging: the supplied two-column coefficient has a nonzero
    kernel vector exactly when the left `A` block action agrees with the
    supplied `2 x 2` Schur-block action on a nonzero concatenated vector. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_leftAction_eq_schurAction
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0 ↔
      Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z := by
  let u : Fin m -> Real := fun i => z (Sum.inl i)
  let v : Fin m -> Real := fun i => z (Sum.inr i)
  have hz : z = Sum.elim u v := by
    funext r
    cases r <;> rfl
  rw [hz]
  exact
    (sylvesterTwoColumnBlockCoeff_mulVec_sumElim_eq_zero_iff_coupled_block_action
      m n A T p q u v).trans
      (sylvesterTwoColumnBlock_coupled_block_action_iff_leftAction_eq_schurAction
        m n A T p q u v)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), direct
    block-action separation certificate: if no nonzero concatenated two-column
    vector makes the left `A` action agree with the supplied `2 x 2`
    Schur-block action, then the supplied two-column block coefficient is
    nonsingular.  This is the determinant-facing form of the still-open
    spectral-separation target. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hno :
      ∀ z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
        ¬ Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
          Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  intro hdet
  obtain ⟨z, hz_ne, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hno z hz_ne
    ((sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_leftAction_eq_schurAction
      m n A T p q z).mp hzero)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    complex-separation bridge to the no-block-action certificate: if the
    adjacent real `2 x 2` block has no real eigenline, has a supplied complex
    eigenpair `(mu, w)`, and `A` has no complex eigenvector for that same
    `mu`, then no nonzero two-column block-action witness can exist. -/
theorem sylvesterTwoColumnBlock_no_block_action_of_complex_eigenpair_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (mu : Complex) (w : Fin 2 -> Complex)
    (hwne : w ≠ 0)
    (hwJ :
      Matrix.mulVec (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) w =
        fun k => mu * w k)
    (hnoReal :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k)
    (hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i => mu * y i) :
    ∀ z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
      ¬ Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z := by
  intro z hz hblock
  let u : Fin m -> Real := fun i => z (Sum.inl i)
  let v : Fin m -> Real := fun i => z (Sum.inr i)
  have hz_sum : z = Sum.elim u v := by
    funext r
    cases r <;> rfl
  have hblock_uv :
      Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) (Sum.elim u v) =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q)
          (Sum.elim u v) := by
    simpa [hz_sum] using hblock
  have hcoupled :
      Matrix.mulVec (Matrix.of A) u =
          (fun i => T p p * u i + T q p * v i) ∧
        Matrix.mulVec (Matrix.of A) v =
          (fun i => T p q * u i + T q q * v i) :=
    (sylvesterTwoColumnBlock_coupled_block_action_iff_leftAction_eq_schurAction
      m n A T p q u v).mpr hblock_uv
  have hX :
      Matrix.of A * sylvesterTwoColumnBlockColumnPair m u v =
        sylvesterTwoColumnBlockColumnPair m u v *
          sylvesterTwoColumnRealSchurBlock n T p q :=
    (sylvesterTwoColumnBlock_coupled_block_action_iff_columnPair_intertwining
      m n A T p q u v).mp hcoupled
  have hU : sylvesterTwoColumnBlockColumnPair m u v ≠ 0 := by
    intro hzero
    apply hz
    rw [hz_sum]
    funext r
    cases r with
    | inl i =>
        have hentry := congrFun (congrFun hzero i) (0 : Fin 2)
        simpa [u, sylvesterTwoColumnBlockColumnPair] using hentry
    | inr i =>
        have hentry := congrFun (congrFun hzero i) (1 : Fin 2)
        simpa [v, sylvesterTwoColumnBlockColumnPair] using hentry
  have hXc :
      realMatrixToComplex (Matrix.of A) *
          realMatrixToComplex (sylvesterTwoColumnBlockColumnPair m u v) =
        realMatrixToComplex (sylvesterTwoColumnBlockColumnPair m u v) *
          realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q) :=
    sylvesterTwoColumnBlock_columnPair_intertwining_complexification
      m n A T p q u v hX
  have hXw :
      Matrix.mulVec
          (realMatrixToComplex (sylvesterTwoColumnBlockColumnPair m u v)) w ≠ 0 :=
    sylvesterTwoColumnBlock_columnPair_complex_mulVec_ne_zero_of_no_real_eigenvector
      m n A T p q u v hX hU hnoReal hwne
  exact hnoA
    (finiteComplexMatrix_exists_mulVec_eigenpair_of_intertwiner_image_ne_zero
      (realMatrixToComplex (Matrix.of A))
      (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
      (realMatrixToComplex (sylvesterTwoColumnBlockColumnPair m u v))
      mu w hXc hwJ hXw)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    consequence of a supplied complex eigenpair/separation certificate for the
    adjacent real `2 x 2` block.  This is still a supplied-certificates route:
    it does not construct the complex eigenpair or no-common-spectrum
    hypothesis from a full Schur spectral theorem. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_eigenpair_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (mu : Complex) (w : Fin 2 -> Complex)
    (hwne : w ≠ 0)
    (hwJ :
      Matrix.mulVec (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) w =
        fun k => mu * w k)
    (hnoReal :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k)
    (hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i => mu * y i) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
  sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action m n A T p q
    (sylvesterTwoColumnBlock_no_block_action_of_complex_eigenpair_separation
      m n A T p q mu w hwne hwJ hnoReal hnoA)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), root-based
    complex-separation bridge to the no-block-action certificate: a supplied
    complex root of the adjacent `2 x 2` characteristic equation gives the
    concrete eigenvector used by the complex-separation bridge. -/
theorem sylvesterTwoColumnBlock_no_block_action_of_complex_root_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (mu : Complex)
    (hsub : T q p ≠ 0)
    (hroot :
      (((T p p : Real) : Complex) - mu) *
        (((T q q : Real) : Complex) - mu) -
          ((T p q : Real) : Complex) * ((T q p : Real) : Complex) = 0)
    (hnoReal :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k)
    (hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i => mu * y i) :
    ∀ z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
      ¬ Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z :=
  sylvesterTwoColumnBlock_no_block_action_of_complex_eigenpair_separation
    m n A T p q mu
    (sylvesterTwoColumnRealSchurBlockComplexRootVector n T p q mu)
    (sylvesterTwoColumnRealSchurBlockComplexRootVector_ne_zero n T p q mu hsub)
    (sylvesterTwoColumnRealSchurBlockComplexRootVector_mulVec n T p q mu hroot)
    hnoReal hnoA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    consequence of a supplied complex root/separation certificate for the
    adjacent real `2 x 2` block. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_root_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (mu : Complex)
    (hsub : T q p ≠ 0)
    (hroot :
      (((T p p : Real) : Complex) - mu) *
        (((T q q : Real) : Complex) - mu) -
          ((T p q : Real) : Complex) * ((T q p : Real) : Complex) = 0)
    (hnoReal :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k)
    (hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i => mu * y i) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
  sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action m n A T p q
    (sylvesterTwoColumnBlock_no_block_action_of_complex_root_separation
      m n A T p q mu hsub hroot hnoReal hnoA)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    consequence from a supplied negative-discriminant square-root certificate:
    `delta` constructs the standard complex root of the adjacent real `2 x 2`
    block, and the root-based separation bridge proves nonsingularity of the
    active block coefficient. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_delta_root_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (delta : Real)
    (hsub : T q p ≠ 0)
    (hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p))
    (hnoReal :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k)
    (hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta *
                y i) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
  sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_root_separation
    m n A T p q
    (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)
    hsub
    (sylvesterTwoColumnRealSchurBlockComplexRoot_root_of_delta_sq
      n T p q delta hdelta)
    hnoReal hnoA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    consequence from a nonzero negative-discriminant square-root certificate:
    the same certificate supplies both the standard complex root and the
    no-real-eigenline hypothesis for the adjacent real `2 x 2` block. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_delta_root_no_real_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (delta : Real)
    (hsub : T q p ≠ 0)
    (hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p))
    (hdelta_ne : delta ≠ 0)
    (hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta *
                y i) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
  sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_delta_root_separation
    m n A T p q delta hsub hdelta
    (sylvesterTwoColumnRealSchurBlock_no_real_eigenvector_of_delta_sq_ne_zero
      n T p q delta hdelta hdelta_ne)
    hnoA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    consequence from fully determinant-shaped supplied spectral separation:
    a nonzero shifted complex determinant for `A` at the constructed
    negative-discriminant root supplies the remaining no-common-eigenvalue
    exclusion used by the delta-root route. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_delta_root_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (delta : Real)
    (hsub : T q p ≠ 0)
    (hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p))
    (hdelta_ne : delta ≠ 0)
    (hdetA :
      Not (Matrix.det
        (realMatrixToComplex (Matrix.of A) -
          Matrix.scalar (Fin m)
            (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)) = 0)) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
  sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_delta_root_no_real_separation
    m n A T p q delta hsub hdelta hdelta_ne
    (finiteComplexMatrix_no_eigenpair_of_det_sub_scalar_ne_zero
      (realMatrixToComplex (Matrix.of A))
      (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)
      hdetA)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), scalar
    discriminant fact for a genuine adjacent real `2 x 2` block: if the real
    block discriminant is negative, then the subdiagonal entry `T q p` cannot
    vanish.  This is the small algebraic certificate needed by the concrete
    complex-root vector `(mu - T_qq, T_qp)`. -/
theorem sylvesterTwoColumnRealSchurBlock_subdiagonal_ne_zero_of_disc_neg
    (n : Nat) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0) :
    Not (T q p = 0) := by
  intro hzero_qp
  have hsq : 0 <= (T p p - T q q) ^ 2 :=
    sq_nonneg (T p p - T q q)
  have hdisc_nonneg :
      0 <= (T p p - T q q) ^ 2 + 4 * T p q * T q p := by
    simpa [hzero_qp] using hsq
  linarith

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), negative
    discriminant implies no real eigenline for the adjacent real `2 x 2`
    block.  The proof instantiates the existing nonzero square-root route with
    `delta = sqrt (-disc)`. -/
theorem sylvesterTwoColumnRealSchurBlock_no_real_eigenvector_of_disc_neg
    (n : Nat) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0) :
    forall x : Fin 2 -> Real, x ≠ 0 ->
      Not (exists nu : Real,
        Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
          fun k => nu * x k) := by
  let delta : Real := Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))
  have hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p) := by
    dsimp [delta]
    rw [Real.sq_sqrt]
    linarith
  have hdelta_ne : Not (delta = 0) := by
    intro hzero_delta
    rw [hzero_delta] at hdelta
    norm_num at hdelta
    linarith
  exact
    sylvesterTwoColumnRealSchurBlock_no_real_eigenvector_of_delta_sq_ne_zero
      n T p q delta hdelta hdelta_ne

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): if an adjacent
    real Schur `2 x 2` block has negative discriminant, the standard complex
    root `sqrt (-disc)` is a supplied complex right eigenvalue of the
    complexified block. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRoot_hasComplexRightEigenvalue_of_disc_neg
    (n : Nat) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0) :
    HasComplexRightEigenvalue
      (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
      (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
        (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p)))) := by
  let delta : Real := Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))
  have hsub : Not (T q p = 0) :=
    sylvesterTwoColumnRealSchurBlock_subdiagonal_ne_zero_of_disc_neg
      n T p q hdisc
  have hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p) := by
    dsimp [delta]
    rw [Real.sq_sqrt]
    linarith
  exact
    ⟨sylvesterTwoColumnRealSchurBlockComplexRootVector n T p q
        (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta),
      sylvesterTwoColumnRealSchurBlockComplexRootVector_ne_zero
        n T p q (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta) hsub,
      sylvesterTwoColumnRealSchurBlockComplexRootVector_mulVec
        n T p q (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)
        (sylvesterTwoColumnRealSchurBlockComplexRoot_root_of_delta_sq
          n T p q delta hdelta)⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): a
    no-common-complex-eigenpair hypothesis between the adjacent real-Schur
    block and the left matrix supplies the shifted determinant certificate at
    the standard complex root `sqrt (-disc)`.  This is the source-facing route
    that remains after the constructed real-quasi-Schur API supplies the
    negative-discriminant side. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRoot_det_separation_of_disc_no_common_complex_eigenpair
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hnoCommon :
      ∀ mu : Complex,
        (∃ w : Fin 2 -> Complex,
          w ≠ 0 ∧
            Matrix.mulVec (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) w =
              fun k => mu * w k) ->
        ¬ ∃ y : Fin m -> Complex,
          y ≠ 0 ∧
            Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
              fun i => mu * y i) :
    Not
      ((Matrix.det
        (realMatrixToComplex (Matrix.of A) -
          Matrix.scalar (Fin m)
            (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
              (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0)) := by
  let delta : Real := Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))
  have hsub : Not (T q p = 0) :=
    sylvesterTwoColumnRealSchurBlock_subdiagonal_ne_zero_of_disc_neg
      n T p q hdisc
  have hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p) := by
    dsimp [delta]
    rw [Real.sq_sqrt]
    linarith
  have hblockEig :
      ∃ w : Fin 2 -> Complex,
        w ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) w =
            fun k => sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta * w k :=
    ⟨sylvesterTwoColumnRealSchurBlockComplexRootVector n T p q
        (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta),
      sylvesterTwoColumnRealSchurBlockComplexRootVector_ne_zero
        n T p q (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta) hsub,
      sylvesterTwoColumnRealSchurBlockComplexRootVector_mulVec
        n T p q (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)
        (sylvesterTwoColumnRealSchurBlockComplexRoot_root_of_delta_sq
          n T p q delta hdelta)⟩
  have hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i => sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta * y i :=
    hnoCommon (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta) hblockEig
  have hdet :=
    finiteComplexMatrix_det_sub_scalar_ne_zero_of_no_eigenpair
      (realMatrixToComplex (Matrix.of A))
      (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)
      hnoA
  simpa [delta] using hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): named
    no-common-complex-right-eigenvalue version of the adjacent real-Schur
    block shifted determinant certificate. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRoot_det_separation_of_disc_no_common_complex_right_eigenvalue
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hnoCommon :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
        (realMatrixToComplex (Matrix.of A))) :
    Not
      ((Matrix.det
        (realMatrixToComplex (Matrix.of A) -
          Matrix.scalar (Fin m)
            (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
              (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0)) := by
  exact
    sylvesterTwoColumnRealSchurBlockComplexRoot_det_separation_of_disc_no_common_complex_eigenpair
      m n A T p q hdisc
      (fun mu hblock hA => hnoCommon mu ⟨hblock, hA⟩)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): left-matrix-first
    no-common-complex-right-eigenvalue version of the adjacent real-Schur
    block shifted determinant certificate.  The block eigenvalue at the
    standard complex root is produced locally from the negative discriminant. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRoot_det_separation_of_disc_no_common_complex_right_eigenvalue_left
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hnoCommon :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of A))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))) :
    Not
      ((Matrix.det
        (realMatrixToComplex (Matrix.of A) -
          Matrix.scalar (Fin m)
            (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
              (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0)) := by
  exact
    finiteComplexMatrix_det_sub_scalar_ne_zero_of_no_common_right_eigenvalue_left
      (realMatrixToComplex (Matrix.of A))
      (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
      (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
        (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))
      hnoCommon
      (sylvesterTwoColumnRealSchurBlockComplexRoot_hasComplexRightEigenvalue_of_disc_neg
        n T p q hdisc)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), named
    no-common-complex-right-eigenvalue bridge to the no-block-action
    certificate: no-real-eigenline supplies the nonreal block root, and a
    left-matrix-first no-common hypothesis rules out the induced eigenpair of
    `A`. -/
theorem sylvesterTwoColumnBlock_no_block_action_of_no_real_eigenvector_no_common_complex_right_eigenvalue_left
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hnoReal :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k)
    (hnoCommon :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of A))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))) :
    ∀ z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
      ¬ Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z := by
  let delta : Real :=
    Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))
  let mu : Complex := sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta
  have hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0 :=
    sylvesterTwoColumnRealSchurBlock_disc_neg_of_no_real_eigenvector
      n T p q hnoReal
  have hblockEig :
      HasComplexRightEigenvalue
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) mu := by
    simpa [mu, delta] using
      sylvesterTwoColumnRealSchurBlockComplexRoot_hasComplexRightEigenvalue_of_disc_neg
        n T p q hdisc
  rcases hblockEig with ⟨w, hwne, hwJ⟩
  have hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i => mu * y i := by
    intro hA
    exact hnoCommon mu ⟨hA, ⟨w, hwne, hwJ⟩⟩
  exact
    sylvesterTwoColumnBlock_no_block_action_of_complex_eigenpair_separation
      m n A T p q mu w hwne hwJ hnoReal hnoA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    consequence of no-real-eigenline plus a local left-oriented
    no-common-complex-right-eigenvalue hypothesis for the adjacent real
    Schur block. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_real_eigenvector_no_common_complex_right_eigenvalue_left
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hnoReal :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k)
    (hnoCommon :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of A))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
  sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action m n A T p q
    (sylvesterTwoColumnBlock_no_block_action_of_no_real_eigenvector_no_common_complex_right_eigenvalue_left
      m n A T p q hnoReal hnoCommon)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), direct
    no-block-action certificate from a negative real discriminant and a
    shifted complex determinant separation certificate for `A`.  This is the
    source-shaped spectral obstruction before taking determinants of the
    active two-column coefficient. -/
theorem sylvesterTwoColumnBlock_no_block_action_of_complex_disc_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    forall z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
      Not (Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z) := by
  let delta : Real := Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))
  have hsub : Not (T q p = 0) :=
    sylvesterTwoColumnRealSchurBlock_subdiagonal_ne_zero_of_disc_neg
      n T p q hdisc
  have hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p) := by
    dsimp [delta]
    rw [Real.sq_sqrt]
    linarith
  have hnoReal :
      forall x : Fin 2 -> Real, x ≠ 0 ->
        Not (exists nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k) :=
    sylvesterTwoColumnRealSchurBlock_no_real_eigenvector_of_disc_neg
      n T p q hdisc
  have hdetA_delta :
      Not (Matrix.det
        (realMatrixToComplex (Matrix.of A) -
          Matrix.scalar (Fin m)
            (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)) = 0) := by
    simpa [delta] using hdetA
  have hnoA :
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta *
                y i) :=
    finiteComplexMatrix_no_eigenpair_of_det_sub_scalar_ne_zero
      (realMatrixToComplex (Matrix.of A))
      (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)
      hdetA_delta
  exact
    sylvesterTwoColumnBlock_no_block_action_of_complex_root_separation
      m n A T p q
      (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)
      hsub
      (sylvesterTwoColumnRealSchurBlockComplexRoot_root_of_delta_sq
        n T p q delta hdelta)
      hnoReal hnoA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), explicit
    source-shaped separation certificate for a supplied adjacent real
    `2 x 2` Schur block: the block discriminant is negative and the
    complexified left coefficient has nonzero shifted determinant at the
    standard complex root `sqrt (-disc)`.  This predicate records concrete
    spectral data; it is not the no-block-action conclusion itself. -/
def IsSylvesterTwoColumnRealSchurBlockSeparation
    (m n : Nat) (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n) : Prop :=
  (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0 ∧
    Not
      ((Matrix.det
        (realMatrixToComplex (Matrix.of A) -
          Matrix.scalar (Fin m)
            (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
              (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), direct producer
    for the explicit real-Schur block-separation predicate from the two
    spectral certificates that a stronger real-Schur block API should export:
    negative discriminant for the adjacent `2 x 2` block and shifted complex
    determinant separation for `A`. -/
theorem sylvesterTwoColumnRealSchurBlock_separation_of_disc_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsSylvesterTwoColumnRealSchurBlockSeparation m n A T p q :=
  ⟨hdisc, hdetA⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), direct producer
    for the explicit real-Schur block-separation predicate from an
    irreducibility-shaped `2 x 2` block certificate: no nonzero real
    eigenline supplies the negative discriminant, while the shifted complex
    determinant separation for `A` remains explicit. -/
theorem sylvesterTwoColumnRealSchurBlock_separation_of_no_real_eigenvector_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hno :
      forall x : Fin 2 -> Real, x ≠ 0 ->
        Not (exists nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k))
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsSylvesterTwoColumnRealSchurBlockSeparation m n A T p q := by
  exact
    sylvesterTwoColumnRealSchurBlock_separation_of_disc_det_separation
      m n A T p q
      (sylvesterTwoColumnRealSchurBlock_disc_neg_of_no_real_eigenvector
        n T p q hno)
      hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), canonical
    real `2 x 2` rotation-scaling block algebra: if the adjacent block has
    entries `[[alpha, beta], [-beta, alpha]]` in the `(p,q)` order and
    `beta != 0`, then its real Schur discriminant is negative.  This is the
    local algebraic bridge needed by a future stronger real-Schur export. -/
theorem sylvesterTwoColumnRealSchurBlock_disc_neg_of_rotation_scaling_entries
    (n : Nat) (T : RMatFn n n) (p q : Fin n) (alpha beta : Real)
    (hpp : T p p = alpha)
    (hqq : T q q = alpha)
    (hpq : T p q = beta)
    (hqp : T q p = -beta)
    (hbeta : beta ≠ 0) :
    (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0 := by
  have hbeta_sq_pos : 0 < beta ^ 2 := sq_pos_of_ne_zero hbeta
  rw [hpp, hqq, hpq, hqp]
  nlinarith

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), canonical
    real `2 x 2` block producer for the explicit block-separation predicate:
    rotation-scaling block entries provide the negative discriminant, while
    the shifted determinant separation for `A` remains an explicit spectral
    certificate. -/
theorem sylvesterTwoColumnRealSchurBlock_separation_of_rotation_scaling_entries
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n) (alpha beta : Real)
    (hpp : T p p = alpha)
    (hqq : T q q = alpha)
    (hpq : T p q = beta)
    (hqp : T q p = -beta)
    (hbeta : beta ≠ 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsSylvesterTwoColumnRealSchurBlockSeparation m n A T p q := by
  exact
    sylvesterTwoColumnRealSchurBlock_separation_of_disc_det_separation
      m n A T p q
      (sylvesterTwoColumnRealSchurBlock_disc_neg_of_rotation_scaling_entries
        n T p q alpha beta hpp hqq hpq hqp hbeta)
      hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), named
    no-block-action bridge from the explicit real-Schur block-separation
    certificate.  The remaining open source work is to derive
    `IsSylvesterTwoColumnRealSchurBlockSeparation` automatically from the
    stronger real-Schur block API, not from the current block-map predicate
    alone. -/
theorem sylvesterTwoColumnBlock_no_block_action_of_realSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealSchurBlockSeparation m n A T p q) :
    forall z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
      Not (Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z) := by
  exact sylvesterTwoColumnBlock_no_block_action_of_complex_disc_det_separation
    m n A T p q hsep.1 hsep.2

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    consequence of the explicit real-Schur block-separation certificate. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_realSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealSchurBlockSeparation m n A T p q) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  exact sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action
    m n A T p q
    (sylvesterTwoColumnBlock_no_block_action_of_realSchur_block_separation
      m n A T p q hsep)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur two-column separation certificate: the exported
    quasi-Schur block-map data identifies an adjacent same-block pair, and
    the block carries the explicit real-Schur separation certificate used by
    the no-block-action bridge.  This is a convenient supplied-certificate
    surface; deriving it from `real_quasi_schur_blocks` alone remains open
    because that API exports only block size and below-block zeros. -/
def IsSylvesterTwoColumnRealQuasiSchurBlockSeparation
    (m n : Nat) (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n) : Prop :=
  Monotone pmap ∧
    (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2) ∧
    (forall i j : Fin n, pmap j < pmap i -> T i j = 0) ∧
    q.val = p.val + 1 ∧
    pmap p = pmap q ∧
    IsSylvesterTwoColumnRealSchurBlockSeparation m n A T p q

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur separation producer from block-map data, adjacent
    same-block provenance, a negative-discriminant certificate for the block,
    and shifted determinant separation for `A`.  This is the direct adapter
    for a future strengthened `real_quasi_schur_blocks` theorem that exports
    irreducible `2 x 2` block discriminants. -/
theorem sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_disc_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q := by
  exact
    ⟨hmono, hcard, hzero, hpq_adj, hsame,
      sylvesterTwoColumnRealSchurBlock_separation_of_disc_det_separation
        m n A T p q hdisc hdetA⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur separation producer from block-map data, adjacent
    same-block provenance, a no-real-eigenline certificate for the adjacent
    `2 x 2` block, and shifted determinant separation for `A`. -/
theorem sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_no_real_eigenvector_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hno :
      forall x : Fin 2 -> Real, x ≠ 0 ->
        Not (exists nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k))
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q := by
  exact
    sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_disc_det_separation
      m n A T pmap p q hmono hcard hzero hpq_adj hsame
      (sylvesterTwoColumnRealSchurBlock_disc_neg_of_no_real_eigenvector
        n T p q hno)
      hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur separation producer from the constructed spectral
    certificate exported by `real_quasi_schur_blocks_twoBlockSpectral`, plus
    the still-explicit shifted determinant separation for the left matrix. -/
theorem sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q := by
  have hno :
      forall x : Fin 2 -> Real, x ≠ 0 ->
        Not (exists nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k) := by
    simpa [HasRealQuasiSchurTwoBlockSpectral, MatrixNoRealEigenline,
      principalTwoBlock, sylvesterTwoColumnRealSchurBlock, Matrix.of_apply] using
      (hspectral p q hpq_adj hsame).1
  exact
    sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_no_real_eigenvector_det_separation
      m n A T pmap p q hmono hcard hzero hpq_adj hsame hno hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur separation producer from constructed two-block spectral
    data plus exclusion of the matching complex root for `A`. -/
theorem sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_complex_root_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hnoA :
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))) *
                  y i)) :
    IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q := by
  let mu : Complex :=
    sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
      (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p)))
  have hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m) mu)) = 0) :=
    finiteComplexMatrix_det_sub_scalar_ne_zero_of_no_eigenpair
      (realMatrixToComplex (Matrix.of A)) mu
      (by
        simpa [mu] using hnoA)
  exact
    sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_det_separation
      m n A T pmap p q hmono hcard hzero hpq_adj hsame hspectral
      (by
        simpa [mu] using hdetA)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), local
    block-first no-common-complex-right-eigenvalue data excludes the
    constructed adjacent-block complex root from the left matrix. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRoot_no_eigenpair_of_twoBlockSpectral_no_common_complex_right_eigenvalue
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hnoCommon :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
        (realMatrixToComplex (Matrix.of A))) :
    Not (exists y : Fin m -> Complex,
      y ≠ 0 ∧
        Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
          fun i =>
            sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
              (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))) *
                y i) := by
  let mu : Complex :=
    sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
      (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p)))
  have hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0 := by
    simpa [Matrix.of_apply] using (hspectral p q hpq_adj hsame).2
  have hblockEig :
      HasComplexRightEigenvalue
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) mu := by
    simpa [mu] using
      sylvesterTwoColumnRealSchurBlockComplexRoot_hasComplexRightEigenvalue_of_disc_neg
        n T p q hdisc
  intro hA
  exact hnoCommon mu ⟨hblockEig, by simpa [mu] using hA⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), local
    left-matrix-first no-common-complex-right-eigenvalue data excludes the
    constructed adjacent-block complex root from the left matrix. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRoot_no_eigenpair_of_twoBlockSpectral_no_common_complex_right_eigenvalue_left
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hnoCommon :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of A))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))) :
    Not (exists y : Fin m -> Complex,
      y ≠ 0 ∧
        Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
          fun i =>
            sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
              (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))) *
                y i) := by
  let mu : Complex :=
    sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
      (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p)))
  have hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0 := by
    simpa [Matrix.of_apply] using (hspectral p q hpq_adj hsame).2
  have hblockEig :
      HasComplexRightEigenvalue
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) mu := by
    simpa [mu] using
      sylvesterTwoColumnRealSchurBlockComplexRoot_hasComplexRightEigenvalue_of_disc_neg
        n T p q hdisc
  intro hA
  exact hnoCommon mu ⟨by simpa [mu] using hA, hblockEig⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur separation producer from constructed two-block spectral
    data and a block-first no-common-complex-right-eigenvalue certificate. -/
theorem sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_no_common_complex_right_eigenvalue
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hnoCommon :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
        (realMatrixToComplex (Matrix.of A))) :
    IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q := by
  have hnoA :
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))) *
                  y i) :=
    sylvesterTwoColumnRealSchurBlockComplexRoot_no_eigenpair_of_twoBlockSpectral_no_common_complex_right_eigenvalue
      m n A T pmap p q hpq_adj hsame hspectral hnoCommon
  exact
    sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_complex_root_separation
      m n A T pmap p q hmono hcard hzero hpq_adj hsame hspectral
      hnoA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur separation producer from constructed two-block spectral
    data and a left-matrix-first no-common-complex-right-eigenvalue
    certificate. -/
theorem sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_no_common_complex_right_eigenvalue_left
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hnoCommon :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of A))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))) :
    IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q := by
  have hnoA :
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))) *
                  y i) :=
    sylvesterTwoColumnRealSchurBlockComplexRoot_no_eigenpair_of_twoBlockSpectral_no_common_complex_right_eigenvalue_left
      m n A T pmap p q hpq_adj hsame hspectral hnoCommon
  exact
    sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_complex_root_separation
      m n A T pmap p q hmono hcard hzero hpq_adj hsame hspectral
      hnoA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): global
    vec/Kronecker determinant nonsingularity supplies the bundled real
    quasi-Schur block-separation predicate for an adjacent same-block `2 x 2`
    active Bartels-Stewart block. -/
theorem sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_global_vecCoeff_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hdetGlobal : Not (Matrix.det (sylvesterVecCoeff m n A T) = 0)) :
    IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q := by
  have hBT : (realMatrixToComplex (Matrix.of T)).BlockTriangular pmap := by
    intro i j hij
    simp [realMatrixToComplex, Matrix.of_apply, hzero i j hij]
  have hnoGlobal :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of A))
        (realMatrixToComplex (Matrix.of T)) := by
    simpa [Matrix.of_apply] using
      no_common_complex_right_eigenvalue_of_sylvesterVecCoeff_det_ne_zero
        m n A T hdetGlobal
  exact
    sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_no_common_complex_right_eigenvalue_left
      m n A T pmap p q hmono hcard hzero hpq_adj hsame hspectral
      (noCommonComplexRightEigenvalue_of_sameBlock_twoBlock_quasiSchur
        m n A T pmap p q hcard hBT hpq_adj hsame hnoGlobal)







/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), constructed
    two-block spectral data plus exclusion of the matching complex root for
    `A` gives the active two-column no-block-action certificate. -/
theorem sylvesterTwoColumnBlock_no_block_action_of_twoBlockSpectral_complex_root_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hnoA :
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))) *
                  y i)) :
    forall z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
      Not (Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z) := by
  let mu : Complex :=
    sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
      (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p)))
  have hnoReal :
      forall x : Fin 2 -> Real, x ≠ 0 ->
        Not (exists nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k) := by
    simpa [HasRealQuasiSchurTwoBlockSpectral, MatrixNoRealEigenline,
      principalTwoBlock, sylvesterTwoColumnRealSchurBlock, Matrix.of_apply] using
      (hspectral p q hpq_adj hsame).1
  have hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0 :=
    sylvesterTwoColumnRealSchurBlock_disc_neg_of_no_real_eigenvector
      n T p q hnoReal
  have hblockEig :
      HasComplexRightEigenvalue
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) mu := by
    simpa [mu] using
      sylvesterTwoColumnRealSchurBlockComplexRoot_hasComplexRightEigenvalue_of_disc_neg
        n T p q hdisc
  rcases hblockEig with ⟨w, hwne, hwJ⟩
  have hnoA_mu :
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i => mu * y i) := by
    simpa [mu] using hnoA
  exact
    sylvesterTwoColumnBlock_no_block_action_of_complex_eigenpair_separation
      m n A T p q mu w hwne hwJ hnoReal hnoA_mu

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), determinant
    consequence of constructed two-block spectral data plus exclusion of the
    matching complex root for `A`. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_complex_root_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hnoA :
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))) *
                  y i)) :
    IsAdjacentQuasiTriangularBlockFn n T p q /\
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  refine ⟨?_, ?_⟩
  · exact IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block
      n T pmap p q hmono hcard hzero hpq_adj hsame
  · exact sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action
      m n A T p q
      (sylvesterTwoColumnBlock_no_block_action_of_twoBlockSpectral_complex_root_separation
        m n A T pmap p q hpq_adj hsame hspectral hnoA)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur block-separation producer from canonical rotation-scaling
    entries for the adjacent `2 x 2` block.  The current `real_quasi_schur_blocks`
    API does not export these entries; this theorem closes the algebra once a
    stronger real-Schur construction provides them. -/
theorem sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_rotation_scaling_entries
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n) (alpha beta : Real)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpp : T p p = alpha)
    (hqq : T q q = alpha)
    (hpq_entry : T p q = beta)
    (hqp : T q p = -beta)
    (hbeta : beta ≠ 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q := by
  exact
    sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_disc_det_separation
      m n A T pmap p q hmono hcard hzero hpq_adj hsame
      (sylvesterTwoColumnRealSchurBlock_disc_neg_of_rotation_scaling_entries
        n T p q alpha beta hpp hqq hpq_entry hqp hbeta)
      hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur block-separation bridge to the adjacent-block predicate
    and no-block-action certificate. -/
theorem sylvesterTwoColumnBlock_block_and_no_block_action_of_realQuasiSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q) :
    IsAdjacentQuasiTriangularBlockFn n T p q /\
      (forall z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
        Not (Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
          Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z)) := by
  rcases hsep with ⟨hmono, hcard, hzero, hpq, hsame, hblockSep⟩
  refine ⟨?_, ?_⟩
  · exact IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block
      n T pmap p q hmono hcard hzero hpq hsame
  · exact sylvesterTwoColumnBlock_no_block_action_of_realSchur_block_separation
      m n A T p q hblockSep

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), determinant
    consequence of the bundled real-quasi-Schur block-separation certificate. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q) :
    IsAdjacentQuasiTriangularBlockFn n T p q /\
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  have hcert :=
    sylvesterTwoColumnBlock_block_and_no_block_action_of_realQuasiSchur_block_separation
      m n A T pmap p q hsep
  exact ⟨hcert.1,
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action
      m n A T p q hcert.2⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), determinant
    consequence of the constructed real-quasi-Schur two-block spectral
    certificate plus shifted determinant separation. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsAdjacentQuasiTriangularBlockFn n T p q /\
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  exact
    sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
      m n A T pmap p q
      (sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_det_separation
        m n A T pmap p q hmono hcard hzero hpq_adj hsame hspectral hdetA)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): the constructed
    real-quasi-Schur two-block spectral certificate plus a global
    no-common-complex-eigenpair hypothesis for the adjacent block supplies the
    active two-column block shape and determinant nonsingularity. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_no_common_complex_eigenpair
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hnoCommon :
      ∀ mu : Complex,
        (∃ w : Fin 2 -> Complex,
          w ≠ 0 ∧
            Matrix.mulVec (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) w =
              fun k => mu * w k) ->
        ¬ ∃ y : Fin m -> Complex,
          y ≠ 0 ∧
            Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
              fun i => mu * y i) :
    IsAdjacentQuasiTriangularBlockFn n T p q ∧
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  have hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0 := by
    simpa [Matrix.of_apply] using (hspectral p q hpq_adj hsame).2
  have hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0)) :=
    sylvesterTwoColumnRealSchurBlockComplexRoot_det_separation_of_disc_no_common_complex_eigenpair
      m n A T p q hdisc hnoCommon
  exact
    sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_det_separation
      m n A T pmap p q hmono hcard hzero hpq_adj hsame hspectral hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): named
    no-common-complex-right-eigenvalue version of the two-block spectral route
    to adjacent active-block shape and determinant nonsingularity. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_no_common_complex_right_eigenvalue
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hnoCommon :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
        (realMatrixToComplex (Matrix.of A))) :
    IsAdjacentQuasiTriangularBlockFn n T p q ∧
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  exact
    sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_no_common_complex_eigenpair
      m n A T pmap p q hmono hcard hzero hpq_adj hsame hspectral
      (fun mu hblock hA => hnoCommon mu ⟨hblock, hA⟩)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): left-matrix-first
    no-common-complex-right-eigenvalue version of the constructed
    two-block-spectral route to adjacent active-block shape and determinant
    nonsingularity. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_no_common_complex_right_eigenvalue_left
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hnoCommon :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of A))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))) :
    IsAdjacentQuasiTriangularBlockFn n T p q ∧
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  have hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0 := by
    simpa [Matrix.of_apply] using (hspectral p q hpq_adj hsame).2
  have hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0)) :=
    sylvesterTwoColumnRealSchurBlockComplexRoot_det_separation_of_disc_no_common_complex_right_eigenvalue_left
      m n A T p q hdisc hnoCommon
  exact
    sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_det_separation
      m n A T pmap p q hmono hcard hzero hpq_adj hsame hspectral hdetA

















































































































/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): full Schur-factor
    no-common-complex-right-eigenvalue version of the constructed
    two-block-spectral route.  The block-triangular charpoly lift transports
    the global spectral separation to the local adjacent `2 x 2` block before
    applying the existing determinant/nonsingularity bridge. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hnoGlobal :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of A))
        (realMatrixToComplex (Matrix.of T))) :
    IsAdjacentQuasiTriangularBlockFn n T p q ∧
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  have hBT : (realMatrixToComplex (Matrix.of T)).BlockTriangular pmap := by
    intro i j hij
    simp [realMatrixToComplex, Matrix.of_apply, hzero i j hij]
  exact
    sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_no_common_complex_right_eigenvalue_left
      m n A T pmap p q hmono hcard hzero hpq_adj hsame hspectral
      (noCommonComplexRightEigenvalue_of_sameBlock_twoBlock_quasiSchur
        m n A T pmap p q hcard hBT hpq_adj hsame hnoGlobal)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): global
    vec/Kronecker determinant nonsingularity is a source-level way to supply
    the no-common-complex spectrum certificate needed by the same-block
    two-block determinant route. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_global_vecCoeff_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hdetGlobal : Not (Matrix.det (sylvesterVecCoeff m n A T) = 0)) :
    IsAdjacentQuasiTriangularBlockFn n T p q /\
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  exact
    sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left
      m n A T pmap p q hmono hcard hzero hpq_adj hsame hspectral
      (by
        simpa [Matrix.of_apply] using
          no_common_complex_right_eigenvalue_of_sylvesterVecCoeff_det_ne_zero
            m n A T hdetGlobal)







/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): supplied real
    orthogonal Schur factorizations transport original-coordinate
    no-common-complex-right-eigenvalue data to the Schur-coordinate factors,
    then feed the same-block two-block spectral determinant route for an
    adjacent active `2 x 2` Bartels-Stewart block. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left
    (m n : Nat)
    (U R Aorig : RMatFn m m) (V S Borig : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : Aorig = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : Borig = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex Aorig)
        (realMatrixToComplex Borig)) :
    IsAdjacentQuasiTriangularBlockFn n S p q ∧
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n R S p q) = 0) := by
  have hnoRS :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex R)
        (realMatrixToComplex S) :=
    noCommonComplexRightEigenvalue_realQuasiSchur_factors
      m n U R Aorig V S Borig hU hV hA hB hnoOrig
  exact
    sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left
      m n R S pmap p q hmono hcard hzero hpq_adj hsame hspectral
      (by simpa [Matrix.of_apply] using hnoRS)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): supplied real
    orthogonal Schur factorizations plus original-coordinate vec/Kronecker
    determinant nonsingularity give the active same-block two-column
    determinant certificate. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_factors_twoBlockSpectral_global_vecCoeff_det_ne_zero
    (m n : Nat)
    (U R Aorig : RMatFn m m) (V S Borig : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : Aorig = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : Borig = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hdetOrig :
      Not (Matrix.det (sylvesterVecCoeff m n Aorig Borig) = 0)) :
    IsAdjacentQuasiTriangularBlockFn n S p q /\
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n R S p q) = 0) := by
  exact
    sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left
      m n U R Aorig V S Borig pmap p q hU hV hA hB hmono hcard hzero
      hpq_adj hsame hspectral
      (no_common_complex_right_eigenvalue_of_sylvesterVecCoeff_det_ne_zero
        m n Aorig Borig hdetOrig)































































































/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): supplied real
    orthogonal Schur factorizations transport original-coordinate
    no-common-complex-right-eigenvalue data to the Schur-coordinate factors,
    then derive the bundled real-quasi-Schur separation predicate for an
    adjacent active `2 x 2` Bartels-Stewart block. -/
theorem sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left
    (m n : Nat)
    (U R Aorig : RMatFn m m) (V S Borig : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : Aorig = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : Borig = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex Aorig)
        (realMatrixToComplex Borig)) :
    IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n R S pmap p q := by
  have hnoRS :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex R)
        (realMatrixToComplex S) :=
    noCommonComplexRightEigenvalue_realQuasiSchur_factors
      m n U R Aorig V S Borig hU hV hA hB hnoOrig
  have hBT : (realMatrixToComplex (Matrix.of S)).BlockTriangular pmap := by
    intro i j hij
    simp [realMatrixToComplex, Matrix.of_apply, hzero i j hij]
  exact
    sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_no_common_complex_right_eigenvalue_left
      m n R S pmap p q hmono hcard hzero hpq_adj hsame hspectral
      (noCommonComplexRightEigenvalue_of_sameBlock_twoBlock_quasiSchur
        m n R S pmap p q hcard hBT hpq_adj hsame
        (by simpa [Matrix.of_apply] using hnoRS))

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): supplied real
    orthogonal Schur factorizations plus original-coordinate vec/Kronecker
    determinant nonsingularity give the bundled active same-block
    real-quasi-Schur separation predicate. -/
theorem sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_realQuasiSchur_factors_twoBlockSpectral_global_vecCoeff_det_ne_zero
    (m n : Nat)
    (U R Aorig : RMatFn m m) (V S Borig : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : Aorig = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : Borig = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hdetOrig :
      Not (Matrix.det (sylvesterVecCoeff m n Aorig Borig) = 0)) :
    IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n R S pmap p q := by
  exact
    sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left
      m n U R Aorig V S Borig pmap p q hU hV hA hB hmono hcard hzero
      hpq_adj hsame hspectral
      (no_common_complex_right_eigenvalue_of_sylvesterVecCoeff_det_ne_zero
        m n Aorig Borig hdetOrig)


















































































/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), direct
    determinant-shaped complex-separation route from a negative real
    discriminant: `sqrt (-disc)` supplies the complex root and no-real-line
    certificate, while the shifted complex determinant for `A` remains an
    explicit separation hypothesis. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_disc_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  exact sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action
    m n A T p q
    (sylvesterTwoColumnBlock_no_block_action_of_complex_disc_det_separation
      m n A T p q hdisc hdetA)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), real-Schur
    same-block determinant-shaped complex-separation certificate: an adjacent
    same-labelled block in the exported quasi-Schur block map supplies the
    two-column zero pattern, while a supplied negative-discriminant square-root
    and shifted complex determinant separation certificate make the active
    two-column block coefficient nonsingular.  This packages the proved
    complex-root route with the structural quasi-Schur block-map data; it does
    not construct the spectral certificates from the quasi-Schur predicate. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_complex_delta_root_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (delta : Real)
    (hsub : Not (T q p = 0))
    (hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p))
    (hdelta_ne : Not (delta = 0))
    (hdetA :
      Not (Matrix.det
        (realMatrixToComplex (Matrix.of A) -
          Matrix.scalar (Fin m)
            (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)) = 0)) :
    IsAdjacentQuasiTriangularBlockFn n T p q /\
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  refine ⟨?_, ?_⟩
  · exact IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block
      n T pmap p q hmono hcard hzero hpq hsame
  · exact sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_delta_root_det_separation
      m n A T p q delta hsub hdelta hdelta_ne hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), real-Schur
    same-block no-block-action certificate from a negative real discriminant
    and a shifted complex determinant separation certificate.  The same-block
    quasi-Schur data supplies the adjacent two-column zero pattern, while the
    spectral obstruction is still an explicit supplied-certificate route. -/
theorem sylvesterTwoColumnBlock_block_and_no_block_action_of_quasiSchur_complex_disc_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsAdjacentQuasiTriangularBlockFn n T p q /\
      (forall z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
        Not (Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
          Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z)) := by
  refine ⟨?_, ?_⟩
  · exact IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block
      n T pmap p q hmono hcard hzero hpq hsame
  · exact sylvesterTwoColumnBlock_no_block_action_of_complex_disc_det_separation
      m n A T p q hdisc hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), real-Schur
    same-block determinant-shaped complex-separation certificate from a
    negative real discriminant: the square-root `sqrt (-disc)` supplies the
    complex root used by the two-column block determinant bridge, and the
    negative discriminant also forces the subdiagonal coupling `T q p` to be
    nonzero.  The shifted complex determinant separation for `A` remains an
    explicit supplied certificate. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_complex_disc_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsAdjacentQuasiTriangularBlockFn n T p q /\
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  have hcert :=
    sylvesterTwoColumnBlock_block_and_no_block_action_of_quasiSchur_complex_disc_det_separation
      m n A T pmap p q hmono hcard hzero hpq hsame hdisc hdetA
  exact ⟨hcert.1,
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action
      m n A T p q hcert.2⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), block-local
    spectral obstruction for a supplied real `2 x 2` Schur block: a nonzero
    product-shift kernel vector yields two real vectors satisfying the same
    coupled two-column block action, provided the subdiagonal coupling is
    nonzero.  This is the forward algebraic step needed for the real-Schur
    block-separation route: a future separation theorem can rule out these
    coupled block-action witnesses to obtain the product-shift no-eigenvector
    certificate. -/
theorem sylvesterTwoColumnBlock_product_shift_kernel_to_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hsub : T q p ≠ 0)
    {u : Fin m -> Real}
    (hker :
      Matrix.mulVec
          (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p)) u =
        (fun i => (T q p * T p q) * u i)) :
    ∃ v : Fin m -> Real,
      Matrix.mulVec (Matrix.of A) u =
          (fun i => T p p * u i + T q p * v i) ∧
      Matrix.mulVec (Matrix.of A) v =
          (fun i => T p q * u i + T q q * v i) := by
  let P : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T p p)
  let Q : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T q q)
  let v : Fin m -> Real := fun i => (T q p)⁻¹ * Matrix.mulVec P u i
  refine ⟨v, ?_, ?_⟩
  · funext i
    have hv : T q p * v i = Matrix.mulVec P u i := by
      simp [v, hsub]
    have hP := sylvesterTriangularShiftedCoeff_mulVec_apply m A (T p p) u i
    have hP' : Matrix.mulVec P u i =
        Matrix.mulVec (Matrix.of A) u i - T p p * u i := by
      simpa [P, Matrix.mulVec, dotProduct, Matrix.of_apply] using hP
    calc
      Matrix.mulVec (Matrix.of A) u i =
          Matrix.mulVec P u i + T p p * u i := by linarith
      _ = T p p * u i + T q p * v i := by rw [hv]; ring
  · funext i
    have hQPu : Matrix.mulVec Q (Matrix.mulVec P u) i =
        (T q p * T p q) * u i := by
      have hi := congrFun hker i
      simpa [P, Q, Matrix.mulVec_mulVec] using hi
    have hQv : Matrix.mulVec Q v i = T p q * u i := by
      have hsmul : Matrix.mulVec Q v =
          fun i : Fin m => (T q p)⁻¹ * Matrix.mulVec Q (Matrix.mulVec P u) i := by
        simpa [v] using Matrix.mulVec_smul Q (T q p)⁻¹ (Matrix.mulVec P u)
      calc
        Matrix.mulVec Q v i =
            (T q p)⁻¹ * Matrix.mulVec Q (Matrix.mulVec P u) i := by
              rw [hsmul]
        _ = (T q p)⁻¹ * ((T q p * T p q) * u i) := by rw [hQPu]
        _ = T p q * u i := by
              field_simp [hsub]
    have hQ := sylvesterTriangularShiftedCoeff_mulVec_apply m A (T q q) v i
    have hQ' : Matrix.mulVec Q v i =
        Matrix.mulVec (Matrix.of A) v i - T q q * v i := by
      simpa [Q, Matrix.mulVec, dotProduct, Matrix.of_apply] using hQ
    calc
      Matrix.mulVec (Matrix.of A) v i =
          Matrix.mulVec Q v i + T q q * v i := by linarith
      _ = T p q * u i + T q q * v i := by rw [hQv]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), contrapositive
    block-separation certificate for a supplied real `2 x 2` Schur block: if
    no nonzero vector can be extended to a coupled two-vector block action
    matching the supplied diagonal block, then the product-shift eigen-equation
    has only the zero solution.  Together with the existing
    `sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector`,
    this is the next block-local spectral bridge before a full real-Schur
    separation theorem supplies the `hno` hypothesis from source-level
    spectral disjointness. -/
theorem sylvesterTwoColumnBlockCoeff_product_shift_no_eigenvector_of_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)) :
    forall u : Fin m -> Real,
      Matrix.mulVec
          (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p)) u =
        (fun i => (T q p * T p q) * u i) ->
      u = 0 := by
  intro u hker
  by_contra hune
  exact hno u hune
    (sylvesterTwoColumnBlock_product_shift_kernel_to_coupled_block_action
      m n A T p q hsub hker)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), block-action
    separation bridge: if no nonzero concatenated two-column vector can make
    the left `A` action equal the supplied `2 x 2` Schur-block action, then
    the product-shift eigen-equation has only the zero solution.  This is the
    block-matrix target for the still-open spectral-separation proof; it does
    not itself derive separation from eigenvalue disjointness. -/
theorem sylvesterTwoColumnBlockCoeff_product_shift_no_eigenvector_of_no_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
        ¬ Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
          Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z) :
    forall u : Fin m -> Real,
      Matrix.mulVec
          (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p)) u =
        (fun i => (T q p * T p q) * u i) ->
      u = 0 := by
  intro u hker
  by_contra hune
  obtain ⟨v, haction⟩ :=
    sylvesterTwoColumnBlock_product_shift_kernel_to_coupled_block_action
      m n A T p q hsub hker
  have hz_ne : Sum.elim u v ≠ 0 := by
    intro hz
    apply hune
    funext i
    have hi := congrFun hz (Sum.inl i)
    simpa using hi
  have hblock :
      Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) (Sum.elim u v) =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q)
          (Sum.elim u v) :=
    (sylvesterTwoColumnBlock_coupled_block_action_iff_leftAction_eq_schurAction
      m n A T p q u v).mp haction
  exact hno (Sum.elim u v) hz_ne hblock



















/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), real-Schur
    same-block spectral certificate: an adjacent same-labelled block in the
    exported quasi-Schur block map supplies the two-column zero pattern, and a
    supplied no-coupled-action separation condition makes the corresponding
    two-column block coefficient nonsingular.  This is a source-shaped adapter
    for downstream Bartels-Stewart block solves; it still assumes the
    separation/no-action condition rather than proving it from a full real
    Schur spectral theorem. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)) :
    IsAdjacentQuasiTriangularBlockFn n T p q ∧
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  refine ⟨?_, ?_⟩
  · exact IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block
      n T pmap p q hmono hcard hzero hpq hsame
  · apply sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
    exact
      sylvesterTwoColumnBlockCoeff_product_shift_no_eigenvector_of_no_coupled_block_action
        m n A T p q hsub hno

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), structural
    determinant bridge for a supplied adjacent two-column block with zero
    coupling product: if the two scalar shifted column coefficients
    `A - T_pp I` and `A - T_qq I` are nonsingular and
    `T_qp * T_pq = 0`, then the full two-column block coefficient is
    nonsingular. This instantiates the product-shift quadratic bridge from
    the existing shifted determinant assumptions in the triangular or
    degenerate-block case, avoiding a supplied block inverse/determinant
    certificate for that local step. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  apply sylvesterTwoColumnBlockCoeff_det_ne_zero_of_quadratic_det_ne_zero
    m n A T p q
  · intro hdet
    have hprod :
        Matrix.det
          (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p)) = 0 := by
      simpa [sylvesterTwoColumnBlockFirstQuadraticCoeff, hcouple] using hdet
    rw [Matrix.det_mul] at hprod
    exact (mul_ne_zero hqdet hpdet) hprod
  · intro hdet
    have hcouple' : T p q * T q p = 0 := by
      rw [mul_comm]
      exact hcouple
    have hprod :
        Matrix.det
          (sylvesterTriangularShiftedCoeff m A (T p p) *
            sylvesterTriangularShiftedCoeff m A (T q q)) = 0 := by
      simpa [sylvesterTwoColumnBlockSecondQuadraticCoeff, hcouple'] using hdet
    rw [Matrix.det_mul] at hprod
    exact (mul_ne_zero hpdet hqdet) hprod

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), degenerate
    same-block real-Schur adapter: the exported quasi-Schur block-map data
    supplies the adjacent two-column zero pattern, while nonsingularity of
    the two shifted column coefficients and zero coupling product prove the
    active two-column block coefficient is nonsingular.  This closes the
    zero-coupling subcase of the real `2 x 2` block route; the genuinely
    coupled block still requires a spectral separation/no-coupled-action
    certificate. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    IsAdjacentQuasiTriangularBlockFn n T p q ∧
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  refine ⟨?_, ?_⟩
  · exact IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block
      n T pmap p q hmono hcard hzero hpq hsame
  · exact sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple





































/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), right-hand side for
    the supplied adjacent two-column block recurrence.  It collects the
    two active column equations into the same `Sum`-indexed vector space as
    `sylvesterTwoColumnBlockCoeff`; only previously solved columns `j < p`
    appear on this side. -/
def sylvesterTwoColumnBlockRhs (m n : Nat)
    (T : RMatFn n n) (C X : RMatFn m n) (p q : Fin n) :
    Sum (Fin m) (Fin m) -> Real :=
  Sum.elim
    (fun i =>
      C i p +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j p * X i j))
    (fun i =>
      C i q +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j q * X i j))

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    two-column block recurrence: the block right-hand side depends on `X`
    only through previously solved columns `j < p`. -/
theorem sylvesterTwoColumnBlockRhs_eq_of_prev_columns_eq (m n : Nat)
    (T : RMatFn n n) (C X Y : RMatFn m n) (p q : Fin n)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    sylvesterTwoColumnBlockRhs m n T C X p q =
      sylvesterTwoColumnBlockRhs m n T C Y p q := by
  funext r
  cases r with
  | inl i =>
      have hsum :
          Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
              (fun j => T j p * X i j) =
            Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
              (fun j => T j p * Y i j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjp : j < p := (Finset.mem_filter.mp hj).2
        rw [hprev j hjp i]
      simp [sylvesterTwoColumnBlockRhs, hsum]
  | inr i =>
      have hsum :
          Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
              (fun j => T j q * X i j) =
            Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
              (fun j => T j q * Y i j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjp : j < p := (Finset.mem_filter.mp hj).2
        rw [hprev j hjp i]
      simp [sylvesterTwoColumnBlockRhs, hsum]

/-- Updating a column at or to the right of `p` does not change the singleton
    recurrence right-hand side for column `p`, because that side only sees
    columns `j < p`.  This is the column-update bookkeeping needed by a future
    recursive quasi-Schur candidate construction. -/
theorem sylvesterSingletonColumnRhs_eq_of_column_update_ge
    (m n : Nat) (T : RMatFn n n) (C X : RMatFn m n)
    (p k : Fin n) (xk : Fin m -> Real)
    (hpk : p.val <= k.val) :
    (fun i : Fin m => C i p +
      Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
        (fun j => T j p *
          (fun i j => Function.update (fun j => X i j) k (xk i) j) i j)) =
    (fun i : Fin m => C i p +
      Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
        (fun j => T j p * X i j)) := by
  funext i
  have hsum :
      Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j p *
            (fun i j => Function.update (fun j => X i j) k (xk i) j) i j) =
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j p * X i j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjp : j.val < p.val := Fin.lt_def.mp (Finset.mem_filter.mp hj).2
    have hjne : Not (j = k) := by
      intro hje
      have hjval : j.val = k.val := by rw [hje]
      omega
    simp [Function.update_of_ne hjne]
  rw [hsum]

/-- Updating a column at or to the right of the active two-column block does
    not change the block right-hand side, because that side only depends on
    columns `j < p`. -/
theorem sylvesterTwoColumnBlockRhs_eq_of_column_update_ge
    (m n : Nat) (T : RMatFn n n) (C X : RMatFn m n)
    (p q k : Fin n) (xk : Fin m -> Real)
    (hpk : p.val <= k.val) :
    sylvesterTwoColumnBlockRhs m n T C
        (fun i j => Function.update (fun j => X i j) k (xk i) j) p q =
      sylvesterTwoColumnBlockRhs m n T C X p q := by
  apply sylvesterTwoColumnBlockRhs_eq_of_prev_columns_eq
  intro j hjp i
  have hjpNat : j.val < p.val := Fin.lt_def.mp hjp
  have hjne : Not (j = k) := by
    intro hje
    have hjval : j.val = k.val := by rw [hje]
    omega
  rw [Function.update_of_ne hjne]

/-- Column-family version of
    `sylvesterTwoColumnBlockRhs_eq_of_column_update_ge`: updating the recursive
    column state at or to the right of the active block does not change the
    two-column recurrence right-hand side. -/
theorem sylvesterTwoColumnBlockRhs_eq_of_column_update_at_or_after
    (m n : Nat)
    (T : RMatFn n n) (C : RMatFn m n)
    (x : Fin n -> Fin m -> Real) (p q l : Fin n) (xl : Fin m -> Real)
    (hle : p <= l) :
    sylvesterTwoColumnBlockRhs m n T C
        (fun i j => Function.update x l xl j i) p q =
      sylvesterTwoColumnBlockRhs m n T C
        (fun i j => x j i) p q := by
  exact
    sylvesterTwoColumnBlockRhs_eq_of_prev_columns_eq m n T C
      (fun i j => Function.update x l xl j i)
      (fun i j => x j i) p q
      (by
        intro j hj i
        have hjne : Not (j = l) := by
          intro h
          have hlt : l < p := by simpa [h] using hj
          exact (not_lt_of_ge hle) hlt
        simp [Function.update_of_ne hjne])

/-- Updating two recursive-state columns at or to the right of the active
    block still leaves the two-column recurrence right-hand side unchanged. -/
theorem sylvesterTwoColumnBlockRhs_eq_of_two_column_updates_at_or_after
    (m n : Nat)
    (T : RMatFn n n) (C : RMatFn m n)
    (x : Fin n -> Fin m -> Real) (p q k l : Fin n)
    (xk xl : Fin m -> Real)
    (hpk : p <= k) (hpl : p <= l) :
    sylvesterTwoColumnBlockRhs m n T C
        (fun i j => Function.update (Function.update x k xk) l xl j i) p q =
      sylvesterTwoColumnBlockRhs m n T C
        (fun i j => x j i) p q := by
  calc
    sylvesterTwoColumnBlockRhs m n T C
        (fun i j => Function.update (Function.update x k xk) l xl j i) p q
        = sylvesterTwoColumnBlockRhs m n T C
            (fun i j => Function.update x k xk j i) p q := by
            exact
              sylvesterTwoColumnBlockRhs_eq_of_column_update_at_or_after
                m n T C (Function.update x k xk) p q l xl hpl
    _ = sylvesterTwoColumnBlockRhs m n T C
          (fun i j => x j i) p q := by
          exact
            sylvesterTwoColumnBlockRhs_eq_of_column_update_at_or_after
              m n T C x p q k xk hpk

/-- A singleton recursive-state column update preserves every earlier column.
    This is the prefix-invariant bookkeeping used by the eventual scheduled
    quasi-Schur candidate. -/
theorem sylvesterColumnFamily_update_eq_of_lt
    {m n : Nat} (x : Fin n -> Fin m -> Real)
    (p j : Fin n) (xp : Fin m -> Real)
    (hjp : j < p) :
    Function.update x p xp j = x j := by
  rw [Function.update_of_ne (ne_of_lt hjp)]

/-- A two-column recursive-state update at `p` and `q`, with `p <= q`,
    preserves every column strictly before `p`. -/
theorem sylvesterColumnFamily_two_updates_eq_of_lt
    {m n : Nat} (x : Fin n -> Fin m -> Real)
    (p q j : Fin n) (xp xq : Fin m -> Real)
    (hpq : p <= q) (hjp : j < p) :
    Function.update (Function.update x p xp) q xq j = x j := by
  have hjq : j ≠ q := by
    intro hjq
    have hq_lt_p : q < p := by simpa [hjq] using hjp
    exact (not_lt_of_ge hpq) hq_lt_p
  rw [Function.update_of_ne hjq]
  exact sylvesterColumnFamily_update_eq_of_lt x p j xp hjp

/-- A recursive-state update at or beyond a natural-number frontier preserves
    every column strictly before that frontier. -/
theorem sylvesterColumnFamily_prefix_eq_of_column_update_ge_nat
    {m n : Nat} (x : Fin n -> Fin m -> Real)
    (N : Nat) (k : Fin n) (xk : Fin m -> Real)
    (hNk : N <= k.val) :
    forall j : Fin n, j.val < N -> forall i : Fin m,
      Function.update x k xk j i = x j i := by
  intro j hj i
  have hjne : Not (j = k) := by
    intro h
    have hjk : j.val = k.val := by
      exact congrArg Fin.val h
    omega
  rw [Function.update_of_ne hjne]

/-- Two recursive-state updates at or beyond a natural-number frontier preserve
    every column strictly before that frontier. -/
theorem sylvesterColumnFamily_prefix_eq_of_two_column_updates_ge_nat
    {m n : Nat} (x : Fin n -> Fin m -> Real)
    (N : Nat) (k l : Fin n) (xk xl : Fin m -> Real)
    (hNk : N <= k.val) (hNl : N <= l.val) :
    forall j : Fin n, j.val < N -> forall i : Fin m,
      Function.update (Function.update x k xk) l xl j i = x j i := by
  intro j hj i
  have hjl : Not (j = l) := by
    intro h
    have hjlval : j.val = l.val := by
      exact congrArg Fin.val h
    omega
  rw [Function.update_of_ne hjl]
  exact
    sylvesterColumnFamily_prefix_eq_of_column_update_ge_nat
      x N k xk hNk j hj i

/-- A direct two-column recursive-state update satisfies the generated
    two-column block formula against the final updated state.  This is the local
    block-step counterpart to the prefix-stability lemmas used by a future
    recursive quasi-Schur candidate construction. -/
theorem sylvesterTwoColumnBlock_formula_of_column_family_block_update
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C : RMatFn m n)
    (x : Fin n -> Fin m -> Real) (p q : Fin n)
    (hpq : q.val = p.val + 1) :
    let z : Sum (Fin m) (Fin m) -> Real :=
      Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
        (sylvesterTwoColumnBlockRhs m n S C (fun i j => x j i) p q)
    let xNew : Fin n -> Fin m -> Real :=
      Function.update (Function.update x p (fun i => z (Sum.inl i))) q
        (fun i => z (Sum.inr i))
    (forall i : Fin m,
      xNew p i =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C (fun i j => xNew j i) p q)
          (Sum.inl i)) /\
    (forall i : Fin m,
      xNew q i =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C (fun i j => xNew j i) p q)
          (Sum.inr i)) := by
  let z : Sum (Fin m) (Fin m) -> Real :=
    Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
      (sylvesterTwoColumnBlockRhs m n S C (fun i j => x j i) p q)
  let xNew : Fin n -> Fin m -> Real :=
    Function.update (Function.update x p (fun i => z (Sum.inl i))) q
      (fun i => z (Sum.inr i))
  change
    (forall i : Fin m,
      xNew p i =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C (fun i j => xNew j i) p q)
          (Sum.inl i)) /\
    (forall i : Fin m,
      xNew q i =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C (fun i j => xNew j i) p q)
          (Sum.inr i))
  have hp_le_q : p <= q := Fin.le_def.mpr (by omega)
  have hp_ne_q : p ≠ q := by
    intro hpqeq
    have hval : p.val = q.val := congrArg Fin.val hpqeq
    omega
  have hRhs :
      sylvesterTwoColumnBlockRhs m n S C (fun i j => xNew j i) p q =
        sylvesterTwoColumnBlockRhs m n S C (fun i j => x j i) p q := by
    dsimp [xNew]
    exact
      sylvesterTwoColumnBlockRhs_eq_of_two_column_updates_at_or_after
        m n S C x p q p q
        (fun i => z (Sum.inl i)) (fun i => z (Sum.inr i))
        (le_rfl) hp_le_q
  constructor
  · intro i
    rw [hRhs]
    dsimp [xNew, z]
    rw [Function.update_of_ne hp_ne_q, Function.update_self]
  · intro i
    rw [hRhs]
    dsimp [xNew, z]
    rw [Function.update_self]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), exact block-vector form:
    the supplied adjacent two-column predicate is equivalent to one combined
    linear system for the concatenated unknown vector `(Z(:,p), Z(:,q))`.
    This packages the algebra needed by later block-solve/nonsingularity
    statements without claiming those statements here. -/
theorem sylvester_two_column_block_system_iff_blockCoeff_mulVec (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q <->
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
          (Sum.elim (fun i => X i p) (fun i => X i q)) =
        Sum.elim
          (fun i =>
            C i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => T j p * X i j))
          (fun i =>
            C i q +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => T j q * X i j)) := by
  constructor
  · intro hsys
    rcases hsys with ⟨hp, hq⟩
    funext r
    cases r with
    | inl i =>
        have hi := congrFun hp i
        rw [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec]
        simp only [Sum.elim_inl, Pi.add_apply]
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
        simpa [sub_eq_add_neg, neg_mul] using hi
    | inr i =>
        have hi := congrFun hq i
        rw [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec]
        simp only [Sum.elim_inr, Pi.add_apply]
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
        simpa [sub_eq_add_neg, neg_mul, add_comm, add_left_comm, add_assoc] using hi
  · intro hmul
    constructor
    · funext i
      have hi := congrFun hmul (Sum.inl i)
      rw [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec] at hi
      simp only [Sum.elim_inl, Pi.add_apply] at hi
      rw [Matrix.smul_mulVec, Matrix.one_mulVec] at hi
      simpa [sub_eq_add_neg, neg_mul] using hi
    · funext i
      have hi := congrFun hmul (Sum.inr i)
      rw [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec] at hi
      simp only [Sum.elim_inr, Pi.add_apply] at hi
      rw [Matrix.smul_mulVec, Matrix.one_mulVec] at hi
      simpa [sub_eq_add_neg, neg_mul, add_comm, add_left_comm, add_assoc] using hi

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    right-inverse certificate for the two-column block coefficient: if
    `K` is a right inverse of `sylvesterTwoColumnBlockCoeff`, then applying
    `K` to the block right-hand side gives a vector that solves the combined
    two-column linear system. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_rightInverse_rhs (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (K : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
        (Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q)) =
      sylvesterTwoColumnBlockRhs m n T C X p q := by
  rw [Matrix.mulVec_mulVec, hRight, Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    two-column block structural certificate: a supplied right inverse of the
    active block coefficient forces the coefficient determinant to be nonzero.
    This is pure exact algebra around the supplied inverse certificate; it does
    not prove that the real-Schur block is nonsingular from spectral separation. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_rightInverse (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (K : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  intro hdet
  have h := congrArg Matrix.det hRight
  rw [Matrix.det_mul, hdet, zero_mul, Matrix.det_one] at h
  exact zero_ne_one h

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    right-inverse structural certificate: a supplied right inverse makes the
    active block coefficient map onto every right-hand side.  Scope: exact
    supplied-block algebra only, not a proof of the missing quasi-triangular
    block nonsingularity condition. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_rightInverse
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (K : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  intro b
  refine ⟨Matrix.mulVec K b, ?_⟩
  rw [Matrix.mulVec_mulVec, hRight, Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    block-vector-to-column wrapper: any vector solving the supplied
    two-column block system yields `IsSylvesterTwoColumnBlockSystem` once
    columns `p` and `q` of `X` are defined by that vector. -/
theorem sylvesterTwoColumnBlockSystem_of_blockCoeff_solutionVector (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n) (z : Sum (Fin m) (Fin m) -> Real)
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q)
    (hXp : forall i : Fin m, X i p = z (Sum.inl i))
    (hXq : forall i : Fin m, X i q = z (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  apply (sylvester_two_column_block_system_iff_blockCoeff_mulVec
    m n A T C X p q).mpr
  have hcol :
      Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) = z := by
    funext r
    cases r with
    | inl i => exact hXp i
    | inr i => exact hXq i
  rw [hcol]
  simpa [sylvesterTwoColumnBlockRhs] using hz

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    right-inverse column wrapper: if columns `p` and `q` of `X` are the
    components of `K` applied to the block right-hand side, and `K` is a
    right inverse of the block coefficient, then `X` satisfies the supplied
    two-column block system. -/
theorem sylvesterTwoColumnBlockSystem_of_rightInverse_columns (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (K : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  refine sylvesterTwoColumnBlockSystem_of_blockCoeff_solutionVector
    m n A T C X p q
    (Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q)) ?_ hXp hXq
  exact sylvesterTwoColumnBlockCoeff_mulVec_rightInverse_rhs
    m n A T C X p q K hRight

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    left-inverse certificate: a supplied left inverse of the two-column
    block coefficient makes its `mulVec` action injective. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_injective_of_leftInverse (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    {x y : Sum (Fin m) (Fin m) -> Real}
    (hxy :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) x =
        Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) y) :
    x = y := by
  have h := congrArg (Matrix.mulVec L) hxy
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hLeft, Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    two-column block structural certificate: a supplied left inverse of the
    active block coefficient forces the coefficient determinant to be nonzero.
    Scope: exact supplied-block algebra only. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_leftInverse (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  intro hdet
  have h := congrArg Matrix.det hLeft
  rw [Matrix.det_mul, hdet, mul_zero, Matrix.det_one] at h
  exact zero_ne_one h

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    active-block linear algebra wrapper: matching supplied right- and
    left-inverse certificates make the two-column block coefficient map
    bijective.  This packages the finite-dimensional exact algebra that the
    quasi-triangular block nonsingularity row can reuse. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_rightInverse_leftInverse
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  constructor
  · intro x y hxy
    exact sylvesterTwoColumnBlockCoeff_mulVec_injective_of_leftInverse
      m n A T p q L hLeft hxy
  · exact sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_rightInverse
      m n A T p q K hRight

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    active-block linear solve: if `K` is a supplied right inverse and `L` is a
    supplied left inverse of the same two-column block coefficient, then the
    active block right-hand side has a unique solution vector.  The witness is
    `K` applied to the supplied block right-hand side; uniqueness uses only the
    supplied left-inverse injectivity certificate.  Scope: exact supplied-block
    algebra only; no Schur existence, structural block nonsingularity, or
    floating-point stability is asserted. -/
theorem existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_rightInverse_leftInverse
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1) :
    ExistsUnique fun z : Sum (Fin m) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := by
  refine ⟨Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q), ?_, ?_⟩
  · exact sylvesterTwoColumnBlockCoeff_mulVec_rightInverse_rhs
      m n A T C X p q K hRight
  · intro z hz
    apply sylvesterTwoColumnBlockCoeff_mulVec_injective_of_leftInverse
      m n A T p q L hLeft
    calc
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
          sylvesterTwoColumnBlockRhs m n T C X p q := hz
      _ =
          Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
            (Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q)) := by
            symm
            exact sylvesterTwoColumnBlockCoeff_mulVec_rightInverse_rhs
              m n A T C X p q K hRight

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    active-block solution identification: with matching supplied right- and
    left-inverse certificates, every solution of the active block linear system
    is the vector obtained by applying `K` to the supplied block right-hand
    side.  Scope: exact supplied-block algebra only. -/
theorem sylvesterTwoColumnBlockCoeff_solutionVector_eq_rightInverse_rhs_of_rightInverse_leftInverse
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    {z : Sum (Fin m) (Fin m) -> Real}
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q) :
    z = Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  apply sylvesterTwoColumnBlockCoeff_mulVec_injective_of_leftInverse
    m n A T p q L hLeft
  calc
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := hz
    _ =
        Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
          (Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q)) := by
          symm
          exact sylvesterTwoColumnBlockCoeff_mulVec_rightInverse_rhs
            m n A T C X p q K hRight

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    route for the supplied adjacent two-column block coefficient: a nonzero
    determinant gives Mathlib's nonsingular inverse as a left inverse.  Scope:
    exact supplied-block algebra only; this does not prove real-Schur block
    nonsingularity from spectral separation. -/
theorem sylvesterTwoColumnBlockCoeff_nonsingInv_mul (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0)) :
    Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q) *
        sylvesterTwoColumnBlockCoeff m n A T p q =
      1 := by
  exact Matrix.nonsing_inv_mul (sylvesterTwoColumnBlockCoeff m n A T p q)
    (isUnit_iff_ne_zero.mpr hdet)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    route for the supplied adjacent two-column block coefficient: a nonzero
    determinant gives Mathlib's nonsingular inverse as a right inverse. -/
theorem sylvesterTwoColumnBlockCoeff_mul_nonsingInv (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0)) :
    sylvesterTwoColumnBlockCoeff m n A T p q *
        Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q) =
      1 := by
  exact Matrix.mul_nonsing_inv (sylvesterTwoColumnBlockCoeff m n A T p q)
    (isUnit_iff_ne_zero.mpr hdet)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based left action: applying the nonsingular inverse after the
    supplied two-column block coefficient recovers the input vector. -/
theorem sylvesterTwoColumnBlockCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z) =
      z := by
  rw [Matrix.mulVec_mulVec,
    sylvesterTwoColumnBlockCoeff_nonsingInv_mul m n A T p q hdet,
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based right action: the supplied two-column block coefficient
    maps the nonsingular-inverse solution of any block right-hand side back to
    that right-hand side. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (rhs : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
        (Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          rhs) =
      rhs := by
  rw [Matrix.mulVec_mulVec,
    sylvesterTwoColumnBlockCoeff_mul_nonsingInv m n A T p q hdet,
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based active-block injectivity: a nonzero determinant of the
    supplied two-column block coefficient makes its `mulVec` action injective.
    Scope: exact supplied-block algebra only. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_injective_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0)) :
    Function.Injective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  intro x y hxy
  calc
    x =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) x) := by
        symm
        exact
          sylvesterTwoColumnBlockCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
            m n A T p q hdet x
    _ =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) y) := by
        rw [hxy]
    _ = y := by
        exact
          sylvesterTwoColumnBlockCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
            m n A T p q hdet y

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based active-block surjectivity: a nonzero determinant of the
    supplied two-column block coefficient makes its `mulVec` action
    surjective. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0)) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  intro rhs
  refine
    ⟨Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        rhs, ?_⟩
  exact sylvesterTwoColumnBlockCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
    m n A T p q hdet rhs

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based active-block bijectivity wrapper. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0)) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) :=
  ⟨sylvesterTwoColumnBlockCoeff_mulVec_injective_of_det_ne_zero
      m n A T p q hdet,
    sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_det_ne_zero
      m n A T p q hdet⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based trivial-kernel wrapper for the supplied two-column block
    coefficient. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0 <->
      z = 0 := by
  constructor
  · intro hz
    calc
      z =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
            (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z) := by
          symm
          exact
            sylvesterTwoColumnBlockCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
              m n A T p q hdet z
      _ = 0 := by
          rw [hz]
          exact Matrix.mulVec_zero _
  · intro hz
    rw [hz]
    exact Matrix.mulVec_zero _

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based active-block linear solve: if the supplied two-column
    block coefficient has nonzero determinant, then the block right-hand side
    has a unique exact solution vector.  The witness is Mathlib's nonsingular
    inverse applied to the supplied block right-hand side. -/
theorem existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0)) :
    ExistsUnique fun z : Sum (Fin m) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := by
  refine
    ⟨Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (sylvesterTwoColumnBlockRhs m n T C X p q), ?_, ?_⟩
  · exact
      sylvesterTwoColumnBlockCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
        m n A T p q hdet (sylvesterTwoColumnBlockRhs m n T C X p q)
  · intro z hz
    calc
      z =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
            (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z) := by
          symm
          exact
            sylvesterTwoColumnBlockCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
              m n A T p q hdet z
      _ =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
            (sylvesterTwoColumnBlockRhs m n T C X p q) := by
          rw [hz]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based active-block solution identification: every vector
    solving the supplied two-column block system equals the nonsingular inverse
    applied to the block right-hand side. -/
theorem sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    {z : Sum (Fin m) (Fin m) -> Real}
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q) :
    z =
      Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  calc
    z =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z) := by
        symm
        exact
          sylvesterTwoColumnBlockCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
            m n A T p q hdet z
    _ =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) := by
        rw [hz]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), active-block
    injectivity from the bundled real-quasi-Schur block-separation predicate. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_injective_of_realQuasiSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q) :
    Function.Injective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
      m n A T pmap p q hsep).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_injective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), active-block
    surjectivity from the bundled real-quasi-Schur block-separation predicate. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_realQuasiSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
      m n A T pmap p q hsep).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), active-block
    bijectivity from the bundled real-quasi-Schur block-separation predicate. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_realQuasiSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
      m n A T pmap p q hsep).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), active-block
    unique solve from the bundled real-quasi-Schur block-separation predicate. -/
theorem existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_realQuasiSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q) :
    ExistsUnique fun z : Sum (Fin m) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
      m n A T pmap p q hsep).2
  exact existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_det_ne_zero
    m n A T C X p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), active-block
    solution identification from the bundled real-quasi-Schur
    block-separation predicate. -/
theorem sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_realQuasiSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q)
    {z : Sum (Fin m) (Fin m) -> Real}
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q) :
    z =
      Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
      m n A T pmap p q hsep).2
  exact
    sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_det_ne_zero
      m n A T C X p q hdet hz

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    active-block injectivity: a trivial kernel for the eigen-equation of the
    product of the two shifted column coefficients makes the supplied
    two-column block `mulVec` action injective. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_injective_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0) :
    Function.Injective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact sylvesterTwoColumnBlockCoeff_mulVec_injective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    active-block surjectivity: the no-eigenvector product-shift certificate
    makes every supplied two-column block right-hand side reachable. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    active-block bijectivity wrapper for the supplied two-column block. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    trivial-kernel wrapper for the supplied two-column block coefficient. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0)
    (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0 <->
      z = 0 := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_det_ne_zero
    m n A T p q hdet z

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    active-block linear solve: the no-eigenvector product-shift certificate
    gives existence and uniqueness for the supplied two-column block right-hand
    side, with witness Mathlib's nonsingular inverse. -/
theorem existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0) :
    ExistsUnique fun z : Sum (Fin m) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_det_ne_zero
    m n A T C X p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    active-block solution identification: any vector solving the supplied
    two-column block system is the nonsingular-inverse solution once the
    product-shift no-eigenvector certificate is available. -/
theorem sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0)
    {z : Sum (Fin m) (Fin m) -> Real}
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q) :
    z =
      Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact
    sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_det_ne_zero
      m n A T C X p q hdet hz

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block active-block injectivity: an adjacent same-labelled block in a
    supplied quasi-Schur block map, together with the supplied no-coupled-action
    separation condition, makes the two-column block `mulVec` action injective.
    Scope: exact supplied-block algebra only. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_injective_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)) :
    Function.Injective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_injective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block active-block surjectivity: the quasi-Schur/no-coupled-action
    route makes every supplied two-column block right-hand side reachable by
    the block coefficient. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block active-block bijectivity wrapper from the quasi-Schur
    no-coupled-action route. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block trivial-kernel wrapper for the supplied two-column block
    coefficient under the quasi-Schur/no-coupled-action hypotheses. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i))
    (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0 <->
      z = 0 := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_det_ne_zero
    m n A T p q hdet z

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block active-block linear solve: the quasi-Schur/no-coupled-action
    route gives existence and uniqueness for the supplied two-column block
    right-hand side, with witness Mathlib's nonsingular inverse. -/
theorem existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)) :
    ExistsUnique fun z : Sum (Fin m) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_det_ne_zero
    m n A T C X p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block active-block solution identification: any vector solving the
    supplied two-column block system is the nonsingular-inverse solution under
    the quasi-Schur/no-coupled-action hypotheses. -/
theorem sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i))
    {z : Sum (Fin m) (Fin m) -> Real}
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q) :
    z =
      Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact
    sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_det_ne_zero
      m n A T C X p q hdet hz

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    active-block injectivity: nonsingular shifted column coefficients and a
    zero coupling product make the supplied two-column block coefficient
    injective.  This is the exact algebraic zero-coupling route, without
    carrying quasi-Schur block-map provenance. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_injective_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    Function.Injective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact sylvesterTwoColumnBlockCoeff_mulVec_injective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    active-block surjectivity from nonsingular shifted column coefficients and
    a zero coupling product. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    active-block bijectivity from nonsingular shifted column coefficients and
    a zero coupling product. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    active-block trivial-kernel wrapper for the supplied two-column block
    coefficient under shifted determinant and zero-coupling hypotheses. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0 <->
      z = 0 := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_det_ne_zero
    m n A T p q hdet z

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    active-block linear solve from nonsingular shifted column coefficients and
    a zero coupling product. -/
theorem existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    ExistsUnique fun z : Sum (Fin m) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_det_ne_zero
    m n A T C X p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    active-block solution identification under shifted determinant and
    zero-coupling hypotheses. -/
theorem sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    {z : Sum (Fin m) (Fin m) -> Real}
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q) :
    z =
      Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact
    sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_det_ne_zero
      m n A T C X p q hdet hz

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block active-block injectivity: same-block quasi-Schur block-map data,
    nonsingular shifted column coefficients, and zero coupling product make the
    supplied two-column block coefficient injective. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_injective_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    Function.Injective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_injective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block active-block surjectivity from same-block quasi-Schur data,
    nonsingular shifted column coefficients, and zero coupling product. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block active-block bijectivity wrapper from the same-block
    quasi-Schur/shifted-determinant/zero-coupling route. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block trivial-kernel wrapper for the supplied two-column block
    coefficient under the same-block quasi-Schur/zero-coupling hypotheses. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0 <->
      z = 0 := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_det_ne_zero
    m n A T p q hdet z

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block active-block linear solve from same-block quasi-Schur data,
    nonsingular shifted column coefficients, and zero coupling product. -/
theorem existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    ExistsUnique fun z : Sum (Fin m) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_det_ne_zero
    m n A T C X p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block active-block solution identification under same-block
    quasi-Schur data, nonsingular shifted column coefficients, and zero
    coupling product. -/
theorem sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    {z : Sum (Fin m) (Fin m) -> Real}
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q) :
    z =
      Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact
    sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_det_ne_zero
      m n A T C X p q hdet hz

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant-based
    column wrapper for the supplied adjacent two-column block solve: assigning
    columns `p` and `q` from the nonsingular-inverse block solution makes `X`
    satisfy the supplied two-column block recurrence. -/
theorem sylvesterTwoColumnBlockSystem_of_nonsingInv_columns (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  refine sylvesterTwoColumnBlockSystem_of_blockCoeff_solutionVector
    m n A T C X p q
    (Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
      (sylvesterTwoColumnBlockRhs m n T C X p q)) ?_ hXp hXq
  exact sylvesterTwoColumnBlockCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
    m n A T p q hdet (sylvesterTwoColumnBlockRhs m n T C X p q)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    column wrapper for the supplied adjacent two-column block solve: assigning
    columns `p` and `q` from the nonsingular-inverse block solution makes `X`
    satisfy the supplied two-column block recurrence once the product-shift
    no-eigenvector certificate is available. -/
theorem sylvesterTwoColumnBlockSystem_of_nonsingInv_columns_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact sylvesterTwoColumnBlockSystem_of_nonsingInv_columns
    m n A T C X p q hdet hXp hXq

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    two-column block inverse consistency: any supplied left inverse and right
    inverse of the same block coefficient coincide.  Scope: exact supplied-block
    algebra only; no Schur existence, structural block nonsingularity, or
    floating-point stability is asserted. -/
theorem sylvesterTwoColumnBlockCoeff_leftInverse_eq_rightInverse (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1) :
    L = K := by
  calc
    L = L * 1 := by rw [mul_one]
    _ = L * (sylvesterTwoColumnBlockCoeff m n A T p q * K) := by rw [hRight]
    _ = (L * sylvesterTwoColumnBlockCoeff m n A T p q) * K := by rw [mul_assoc]
    _ = 1 * K := by rw [hLeft]
    _ = K := by rw [one_mul]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    two-column block solve-vector consistency: applying a supplied left inverse
    or a supplied right inverse to the same active block right-hand side gives
    the same vector.  Scope: exact supplied-block algebra only. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_leftInverse_rhs_eq_rightInverse_rhs
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1) :
    Matrix.mulVec L (sylvesterTwoColumnBlockRhs m n T C X p q) =
      Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  have hLK := sylvesterTwoColumnBlockCoeff_leftInverse_eq_rightInverse
    m n A T p q K L hRight hLeft
  simp [hLK]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    left-inverse/right-inverse column wrapper: if columns `p` and `q` of `X`
    are defined by a supplied left inverse, and matching right/left inverse
    certificates are supplied, then `X` satisfies the same two-column block
    system as in the right-inverse wrapper.  Scope: exact supplied-block algebra
    only; no Schur existence, structural block nonsingularity, or floating-point
    stability is asserted. -/
theorem sylvesterTwoColumnBlockSystem_of_leftInverse_rightInverse_columns
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec L (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec L (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  have hLK := sylvesterTwoColumnBlockCoeff_leftInverse_eq_rightInverse
    m n A T p q K L hRight hLeft
  refine sylvesterTwoColumnBlockSystem_of_rightInverse_columns
    m n A T C X p q K hRight ?_ ?_
  · intro i
    simpa [hLK] using hXp i
  · intro i
    simpa [hLK] using hXq i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    right-inverse/left-inverse bridge for the supplied adjacent two-column
    block system: if `K` is a supplied right inverse of the block coefficient,
    `L` is a supplied left inverse, `Y` solves the supplied block system, and
    the right-hand side source `X` agrees with `Y` on the previous columns
    `j < p`, then the active vector obtained by applying `K` to the `X`-based
    block right-hand side is exactly the active vector of `Y`.  Scope: exact
    supplied-block algebra only; no Schur existence, structural block
    nonsingularity, or floating-point stability is asserted. -/
theorem sylvesterTwoColumnBlockCoeff_rightInverse_solutionVector_eq_of_leftInverse_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  apply sylvesterTwoColumnBlockCoeff_mulVec_injective_of_leftInverse
    m n A T p q L hLeft
  have hYm := (sylvester_two_column_block_system_iff_blockCoeff_mulVec
    m n A T C Y p q).mp hY
  calc
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
        (Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q))
        = sylvesterTwoColumnBlockRhs m n T C X p q := by
          exact sylvesterTwoColumnBlockCoeff_mulVec_rightInverse_rhs
            m n A T C X p q K hRight
    _ = sylvesterTwoColumnBlockRhs m n T C Y p q := by
          exact sylvesterTwoColumnBlockRhs_eq_of_prev_columns_eq
            m n T C X Y p q hprev
    _ = Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
        (Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q)) := by
          simpa [sylvesterTwoColumnBlockRhs] using hYm.symm

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), uniqueness
    wrapper for the supplied two-column block system: if two block-system
    solutions have the same block right-hand side, a supplied left inverse
    forces their active column vectors to be equal. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_leftInverse (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hRhs :
      sylvesterTwoColumnBlockRhs m n T C X p q =
        sylvesterTwoColumnBlockRhs m n T C Y p q) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  apply sylvesterTwoColumnBlockCoeff_mulVec_injective_of_leftInverse
    m n A T p q L hLeft
  have hXm := (sylvester_two_column_block_system_iff_blockCoeff_mulVec
    m n A T C X p q).mp hX
  have hYm := (sylvester_two_column_block_system_iff_blockCoeff_mulVec
    m n A T C Y p q).mp hY
  calc
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
        (Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q))
        = sylvesterTwoColumnBlockRhs m n T C X p q := by
          simpa [sylvesterTwoColumnBlockRhs] using hXm
    _ = sylvesterTwoColumnBlockRhs m n T C Y p q := hRhs
    _ = Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
        (Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q)) := by
          simpa [sylvesterTwoColumnBlockRhs] using hYm.symm

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), component form
    of the left-inverse uniqueness wrapper for supplied two-column block
    systems with the same block right-hand side. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_leftInverse (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hRhs :
      sylvesterTwoColumnBlockRhs m n T C X p q =
        sylvesterTwoColumnBlockRhs m n T C Y p q) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hvec := sylvesterTwoColumnBlockSystem_activeColumns_eq_of_leftInverse
    m n A T C X Y p q L hLeft hX hY hRhs
  constructor
  · intro i
    simpa using congrFun hvec (Sum.inl i)
  · intro i
    simpa using congrFun hvec (Sum.inr i)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    two-column recurrence uniqueness bridge: if two block-system solutions
    agree on all previously solved columns `j < p`, then the shared supplied
    left inverse forces their active columns `p` and `q` to agree. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_leftInverse_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  apply sylvesterTwoColumnBlockSystem_columns_eq_of_leftInverse
    m n A T C X Y p q L hLeft hX hY
  exact sylvesterTwoColumnBlockRhs_eq_of_prev_columns_eq m n T C X Y p q hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    uniqueness wrapper for the supplied two-column block system: a nonzero
    determinant of the supplied block coefficient replaces the separate
    left-inverse certificate when two block systems have the same right-hand
    side.  Scope: exact supplied-block algebra only; this does not prove the
    determinant hypothesis from real-Schur spectral separation. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_det_ne_zero (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hRhs :
      sylvesterTwoColumnBlockRhs m n T C X p q =
        sylvesterTwoColumnBlockRhs m n T C Y p q) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  exact sylvesterTwoColumnBlockSystem_activeColumns_eq_of_leftInverse
    m n A T C X Y p q
    (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
    (sylvesterTwoColumnBlockCoeff_nonsingInv_mul m n A T p q hdet)
    hX hY hRhs

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), component form
    of the determinant uniqueness wrapper for supplied two-column block systems
    with the same block right-hand side. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_det_ne_zero (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hRhs :
      sylvesterTwoColumnBlockRhs m n T C X p q =
        sylvesterTwoColumnBlockRhs m n T C Y p q) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hvec := sylvesterTwoColumnBlockSystem_activeColumns_eq_of_det_ne_zero
    m n A T C X Y p q hdet hX hY hRhs
  constructor
  · intro i
    simpa using congrFun hvec (Sum.inl i)
  · intro i
    simpa using congrFun hvec (Sum.inr i)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    two-column recurrence uniqueness bridge: if two block-system solutions
    agree on all previously solved columns `j < p`, then a nonzero determinant
    of the supplied block coefficient forces their active columns to agree. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_det_ne_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  apply sylvesterTwoColumnBlockSystem_columns_eq_of_det_ne_zero
    m n A T C X Y p q hdet hX hY
  exact sylvesterTwoColumnBlockRhs_eq_of_prev_columns_eq m n T C X Y p q hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), vector form of
    the determinant previous-column uniqueness bridge for supplied adjacent
    two-column block systems. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_det_ne_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_det_ne_zero_of_prev_columns_eq
      m n A T C X Y p q hdet hX hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    nonsingular-inverse solve/uniqueness bridge: if the supplied two-column
    block coefficient has nonzero determinant, columns `p` and `q` of `X` are
    defined by Mathlib's nonsingular inverse applied to the supplied
    `X`-based block right-hand side, and a supplied block-system solution `Y`
    agrees with `X` on the previous columns `j < p`, then the active columns
    agree.  Scope: exact supplied-block algebra only; this does not prove the
    determinant hypothesis from real-Schur spectral separation. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q :=
    sylvesterTwoColumnBlockSystem_of_nonsingInv_columns
      m n A T C X p q hdet hXp hXq
  exact sylvesterTwoColumnBlockSystem_columns_eq_of_det_ne_zero_of_prev_columns_eq
    m n A T C X Y p q hdet hX hY hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), vector form of
    the determinant nonsingular-inverse solve/uniqueness bridge for supplied
    adjacent two-column block systems. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
      m n A T C X Y p q hdet hXp hXq hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    nonsingular-inverse solve/uniqueness bridge: if the supplied two-column
    block columns of `X` are defined by the nonsingular-inverse solve and a
    supplied block-system solution `Y` agrees with `X` on previous columns,
    then the active columns agree under the product-shift no-eigenvector
    certificate. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_product_shift_no_eigenvector_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
      m n A T C X Y p q hdet hXp hXq hY hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), vector form of
    the product-shift nonsingular-inverse solve/uniqueness bridge for supplied
    adjacent two-column block systems. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_nonsingInv_columns_of_product_shift_no_eigenvector_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_product_shift_no_eigenvector_of_prev_columns_eq
      m n A T C X Y p q hker hXp hXq hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block column wrapper for the supplied adjacent two-column block solve:
    assigning columns `p` and `q` from the nonsingular-inverse block solution
    makes `X` satisfy the supplied two-column block recurrence under the
    quasi-Schur/no-coupled-action hypotheses. -/
theorem sylvesterTwoColumnBlockSystem_of_nonsingInv_columns_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      forall u : Fin m -> Real, u ≠ 0 ->
        Not (exists v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) /\
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact sylvesterTwoColumnBlockSystem_of_nonsingInv_columns
    m n A T C X p q hdet hXp hXq

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block nonsingular-inverse solve/uniqueness bridge: if the supplied
    two-column block columns of `X` are defined by the nonsingular-inverse
    solve and a supplied block-system solution `Y` agrees with `X` on previous
    columns, then the active columns agree under the quasi-Schur/no-coupled
    route. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_quasiSchur_no_coupled_block_action_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      forall u : Fin m -> Real, u ≠ 0 ->
        Not (exists v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) /\
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
      m n A T C X Y p q hdet hXp hXq hY hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), vector form of
    the real-Schur same-block nonsingular-inverse solve/uniqueness bridge for
    supplied adjacent two-column block systems. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_nonsingInv_columns_of_quasiSchur_no_coupled_block_action_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      forall u : Fin m -> Real, u ≠ 0 ->
        Not (exists v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) /\
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_quasiSchur_no_coupled_block_action_of_prev_columns_eq
      m n A T C X Y pmap p q hmono hcard hzero hpq hsame hsub hno
      hXp hXq hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), supplied
    real-Schur same-block column wrapper: assigning columns `p` and `q` from
    the nonsingular-inverse block solution makes `X` satisfy the supplied
    Schur-coordinate two-column recurrence, when original-coordinate
    no-common-complex-right-eigenvalue data is transported through the supplied
    orthogonal Schur factors and the same-block two-block spectral API. -/
theorem sylvesterTwoColumnBlockSystem_of_nonsingInv_columns_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left
    (m n : Nat)
    (U R Aorig : RMatFn m m) (V S Borig : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : Aorig = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : Borig = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex Aorig)
        (realMatrixToComplex Borig))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n R S C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n R S p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left
      m n U R Aorig V S Borig pmap p q hU hV hA hB hmono hcard hzero
      hpq_adj hsame hspectral hnoOrig).2
  exact sylvesterTwoColumnBlockSystem_of_nonsingInv_columns
    m n R S C X p q hdet hXp hXq

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), supplied
    real-Schur same-block nonsingular-inverse solve/uniqueness bridge: the
    transported original-coordinate no-common hypothesis gives active-column
    uniqueness once previous columns agree. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left_of_prev_columns_eq
    (m n : Nat)
    (U R Aorig : RMatFn m m) (V S Borig : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : Aorig = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : Borig = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex Aorig)
        (realMatrixToComplex Borig))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n R S C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) ∧
      (forall i : Fin m, X i q = Y i q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n R S p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left
      m n U R Aorig V S Borig pmap p q hU hV hA hB hmono hcard hzero
      hpq_adj hsame hspectral hnoOrig).2
  exact
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
      m n R S C X Y p q hdet hXp hXq hY hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), vector form of
    the supplied real-Schur same-block nonsingular-inverse solve/uniqueness
    bridge. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_nonsingInv_columns_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left_of_prev_columns_eq
    (m n : Nat)
    (U R Aorig : RMatFn m m) (V S Borig : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : Aorig = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : Borig = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex Aorig)
        (realMatrixToComplex Borig))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n R S C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left_of_prev_columns_eq
      m n U R Aorig V S Borig C X Y pmap p q hU hV hA hB hmono hcard hzero
      hpq_adj hsame hspectral hnoOrig hXp hXq hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    column wrapper for the supplied two-column block solve: assigning columns
    `p` and `q` from the nonsingular-inverse block solution makes `X` satisfy
    the supplied two-column recurrence under shifted determinant and
    zero-coupling hypotheses. -/
theorem sylvesterTwoColumnBlockSystem_of_nonsingInv_columns_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact sylvesterTwoColumnBlockSystem_of_nonsingInv_columns
    m n A T C X p q hdet hXp hXq

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    nonsingular-inverse solve/uniqueness bridge: the shifted determinant and
    zero-coupling route gives active-column uniqueness once previous columns
    agree. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_shifted_det_product_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
      m n A T C X Y p q hdet hXp hXq hY hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), vector form of
    the degenerate nonsingular-inverse solve/uniqueness bridge under shifted
    determinant and zero-coupling hypotheses. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_nonsingInv_columns_of_shifted_det_product_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_shifted_det_product_zero_of_prev_columns_eq
      m n A T C X Y p q hpdet hqdet hcouple hXp hXq hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block column wrapper for the supplied adjacent two-column block solve:
    assigning columns `p` and `q` from the nonsingular-inverse block solution
    makes `X` satisfy the supplied two-column recurrence under same-block
    quasi-Schur data, shifted determinant certificates, and zero coupling. -/
theorem sylvesterTwoColumnBlockSystem_of_nonsingInv_columns_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact sylvesterTwoColumnBlockSystem_of_nonsingInv_columns
    m n A T C X p q hdet hXp hXq

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block nonsingular-inverse solve/uniqueness bridge: the zero-coupling
    quasi-Schur determinant route gives active-column uniqueness once previous
    columns agree. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_quasiSchur_shifted_det_product_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
      m n A T C X Y p q hdet hXp hXq hY hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), vector form of
    the degenerate same-block nonsingular-inverse solve/uniqueness bridge. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_nonsingInv_columns_of_quasiSchur_shifted_det_product_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_quasiSchur_shifted_det_product_zero_of_prev_columns_eq
      m n A T C X Y pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple
      hXp hXq hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    two-column solve/uniqueness bridge: if a supplied right inverse defines
    the active columns of `X` from the block right-hand side, and a supplied
    left inverse gives uniqueness among block-system solutions with the same
    previous columns, then any other supplied block-system solution `Y` that
    agrees with `X` on columns `j < p` has the same active columns.  Scope:
    exact supplied-block algebra only; no Schur existence, structural block
    nonsingularity, or floating-point stability is asserted. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_rightInverse_leftInverse_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q :=
    sylvesterTwoColumnBlockSystem_of_rightInverse_columns
      m n A T C X p q K hRight hXp hXq
  exact sylvesterTwoColumnBlockSystem_columns_eq_of_leftInverse_of_prev_columns_eq
    m n A T C X Y p q L hLeft hX hY hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), vector form of
    the exact supplied two-column solve/uniqueness bridge: under the same
    supplied right-inverse/left-inverse and previous-column agreement
    hypotheses as the component wrapper, the combined active-column vectors
    `(X(:,p), X(:,q))` and `(Y(:,p), Y(:,q))` agree.  Scope: exact
    supplied-block algebra only; no Schur existence, structural block
    nonsingularity, or floating-point stability is asserted. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_rightInverse_leftInverse_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_rightInverse_leftInverse_prev_columns_eq
      m n A T C X Y p q K L hRight hLeft hXp hXq hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

































































































































































































































































/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column block:
    a nonsingular shifted coefficient `A - t I` has Mathlib's nonsingular
    inverse as a left inverse.  This is the exact-arithmetic certificate used
    by the Bartels-Stewart column solve, not a Schur-existence statement. -/
theorem sylvesterTriangularShiftedCoeff_nonsingInv_mul (m : Nat)
    (A : RMatFn m m) (t : Real)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A t) = 0)) :
    (sylvesterTriangularShiftedCoeff m A t)⁻¹ *
        sylvesterTriangularShiftedCoeff m A t =
      1 := by
  exact Matrix.nonsing_inv_mul (sylvesterTriangularShiftedCoeff m A t)
    (isUnit_iff_ne_zero.mpr hdet)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column block:
    a nonsingular shifted coefficient `A - t I` has Mathlib's nonsingular
    inverse as a right inverse. -/
theorem sylvesterTriangularShiftedCoeff_mul_nonsingInv (m : Nat)
    (A : RMatFn m m) (t : Real)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A t) = 0)) :
    sylvesterTriangularShiftedCoeff m A t *
        (sylvesterTriangularShiftedCoeff m A t)⁻¹ =
      1 := by
  exact Matrix.mul_nonsing_inv (sylvesterTriangularShiftedCoeff m A t)
    (isUnit_iff_ne_zero.mpr hdet)
























































































































































































































































/-- The singleton-column right-hand side depends only on earlier columns. -/
theorem sylvester_singleton_column_rhs_eq_of_prev_columns_eq (m n : Nat)
    (T : RMatFn n n) (C X Y : RMatFn m n) (k : Fin n)
    (hprev : forall j : Fin n, j < k -> forall i : Fin m, X i j = Y i j) :
    (fun i : Fin m => C i k +
      Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
        (fun j => T j k * X i j)) =
    (fun i : Fin m => C i k +
      Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
        (fun j => T j k * Y i j)) := by
  funext i
  have hsum : Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
        (fun j => T j k * X i j) =
      Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
        (fun j => T j k * Y i j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j < k := (Finset.mem_filter.mp hj).2
    rw [hprev j hjk i]
  rw [hsum]

/-- Column-family version of
    `sylvester_singleton_column_rhs_eq_of_prev_columns_eq`: updating the
    recursive column state at or after the active singleton column does not
    change that singleton recurrence right-hand side. -/
theorem sylvester_singleton_column_rhs_eq_of_column_update_at_or_after
    (m n : Nat)
    (T : RMatFn n n) (C : RMatFn m n)
    (x : Fin n -> Fin m -> Real) (k l : Fin n) (xl : Fin m -> Real)
    (hle : k <= l) :
    (fun i : Fin m => C i k +
      Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
        (fun j => T j k * Function.update x l xl j i)) =
    (fun i : Fin m => C i k +
      Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
        (fun j => T j k * x j i)) := by
  exact
    sylvester_singleton_column_rhs_eq_of_prev_columns_eq m n T C
      (fun i j => Function.update x l xl j i)
      (fun i j => x j i) k
      (by
        intro j hj i
        have hjne : Not (j = l) := by
          intro h
          have hlt : l < k := by simpa [h] using hj
          exact (not_lt_of_ge hle) hlt
        simp [Function.update_of_ne hjne])

/-- A direct singleton recursive-state update satisfies the generated singleton
    formula against the final updated state.  This is the local one-column
    counterpart to `sylvesterTwoColumnBlock_formula_of_column_family_block_update`.
    It is bookkeeping for the future scheduled quasi-Schur candidate, not the
    full recursive construction. -/
theorem sylvesterSingleton_formula_of_column_family_update
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C : RMatFn m n)
    (x : Fin n -> Fin m -> Real) (p : Fin n) :
    let xp : Fin m -> Real :=
      Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
        (fun i => C i p +
          Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
            (fun j => S j p * x j i))
    let xNew : Fin n -> Fin m -> Real := Function.update x p xp
    forall i : Fin m,
      xNew p i =
        Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
          (fun i => C i p +
            Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
              (fun j => S j p * xNew j i)) i := by
  let xp : Fin m -> Real :=
    Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
      (fun i => C i p +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => S j p * x j i))
  let xNew : Fin n -> Fin m -> Real := Function.update x p xp
  change forall i : Fin m,
    xNew p i =
      Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
        (fun i => C i p +
          Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
            (fun j => S j p * xNew j i)) i
  have hRhs :
      (fun i : Fin m => C i p +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => S j p * xNew j i)) =
      (fun i : Fin m => C i p +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => S j p * x j i)) := by
    dsimp [xNew]
    exact
      sylvester_singleton_column_rhs_eq_of_column_update_at_or_after
        m n S C x p p xp le_rfl
  intro i
  rw [hRhs]
  dsimp [xNew, xp]
  rw [Function.update_self]











































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- A true singleton fiber in the real-quasi-Schur block map rules out a
    same-block immediate successor. -/
theorem quasiSchur_singleton_successor_not_same_of_singleton_fiber
    (n : Nat) (pmap : Fin n -> Nat) (p : Fin n)
    (hsingle : forall i : Fin n, pmap i = pmap p -> i = p) :
    forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q) := by
  intro q hq hsame
  have hqp : q = p := hsingle q hsame.symm
  have hval : q.val = p.val := congrArg Fin.val hqp
  omega

/-- A monotone real quasi-Schur block map has a true singleton fiber at `p`
    when neither the immediate predecessor nor the immediate successor has the
    same block label.  The edge cases are vacuous because the corresponding
    neighbor index does not exist. -/
theorem quasiSchur_singleton_fiber_of_prev_next_not_same
    (n : Nat) (pmap : Fin n -> Nat) (p : Fin n)
    (hmono : Monotone pmap)
    (hprev : forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p)
    (hnext : forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) :
    forall i : Fin n, pmap i = pmap p -> i = p := by
  intro i hi
  apply Fin.ext
  by_cases hlt : i.val < p.val
  · exfalso
    have hq_lt : p.val - 1 < n := by
      have hp_lt := p.isLt
      omega
    let q : Fin n := ⟨p.val - 1, hq_lt⟩
    have hqprev : q.val + 1 = p.val := by
      dsimp [q]
      omega
    have hiq : i <= q := Fin.le_def.mpr (by
      dsimp [q]
      omega)
    have hqp : q <= p := Fin.le_def.mpr (by
      dsimp [q]
      omega)
    have hipmap : pmap p <= pmap q := by
      rw [← hi]
      exact hmono hiq
    have hqmap : pmap q <= pmap p := hmono hqp
    have hqeq : pmap q = pmap p := le_antisymm hqmap hipmap
    exact hprev q hqprev hqeq
  · by_cases hgt : p.val < i.val
    · exfalso
      have hq_lt : p.val + 1 < n := by
        have hi_lt := i.isLt
        omega
      let q : Fin n := ⟨p.val + 1, hq_lt⟩
      have hqnext : q.val = p.val + 1 := rfl
      have hpq : p <= q := Fin.le_def.mpr (by
        dsimp [q]
        omega)
      have hqi : q <= i := Fin.le_def.mpr (by
        dsimp [q]
        omega)
      have hpmap : pmap p <= pmap q := hmono hpq
      have hqmap : pmap q <= pmap p := by
        rw [← hi]
        exact hmono hqi
      have hqeq : pmap p = pmap q := le_antisymm hpmap hqmap
      exact hnext q hqnext hqeq
    · omega

/-- A frontier index with no same-labelled immediate predecessor is either a
    singleton step, certified by no same-labelled immediate successor, or the
    left column of an adjacent same-labelled two-column step.  This is the
    local branch-selection lemma needed for automatically generated
    real-quasi-Schur traversal schedules. -/
theorem quasiSchur_frontier_step_of_boundary
    (n : Nat) (pmap : Fin n -> Nat) (k : Nat) (hk : k < n)
    (hprev : forall q : Fin n, q.val + 1 = k -> pmap q ≠ pmap ⟨k, hk⟩) :
    (exists p : Fin n,
      p.val = k /\
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) /\
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q))
    \/
    (exists p q : Fin n,
      p.val = k /\
      q.val = k + 1 /\
      pmap p = pmap q) := by
  let p : Fin n := ⟨k, hk⟩
  by_cases hsucc : k + 1 < n
  · let q : Fin n := ⟨k + 1, hsucc⟩
    by_cases hsame : pmap p = pmap q
    · exact Or.inr ⟨p, q, rfl, rfl, hsame⟩
    · refine Or.inl ⟨p, rfl, ?_, ?_⟩
      · intro q' hq'
        exact hprev q' (by simpa [p] using hq')
      · intro q' hq'
        have hqeq : q' = q := Fin.ext (by
          dsimp [q]
          omega)
        subst q'
        exact hsame
  · refine Or.inl ⟨p, rfl, ?_, ?_⟩
    · intro q hq
      exact hprev q (by simpa [p] using hq)
    · intro q hq _
      have hqval : q.val = k + 1 := by
        simpa [p] using hq
      have hq_lt := q.isLt
      exact hsucc (by omega)

/-- After a singleton frontier step, the next frontier again has no
    same-labelled immediate predecessor. -/
theorem quasiSchur_boundary_after_singleton_step
    (n : Nat) (pmap : Fin n -> Nat) (p : Fin n)
    (hnext : forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q)
    (hsucc : p.val + 1 < n) :
    forall q : Fin n, q.val + 1 = p.val + 1 ->
      pmap q ≠ pmap ⟨p.val + 1, hsucc⟩ := by
  intro q hq
  have hqp : q = p := Fin.ext (by omega)
  subst q
  exact hnext ⟨p.val + 1, hsucc⟩ rfl

/-- After an adjacent same-labelled two-column frontier step, the frontier
    after the pair again has no same-labelled immediate predecessor.  The
    size-at-most-two fiber invariant rules out a third same-labelled column. -/
theorem quasiSchur_boundary_after_adjacent_same_block
    (n : Nat) (pmap : Fin n -> Nat) (p q : Fin n)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hnext : q.val + 1 < n) :
    forall r : Fin n, r.val + 1 = q.val + 1 ->
      pmap r ≠ pmap ⟨q.val + 1, hnext⟩ := by
  intro r hr
  have hrq : r = q := Fin.ext (by omega)
  subst r
  intro hqnext
  let j : Fin n := ⟨q.val + 1, hnext⟩
  have hjfiber : pmap j = pmap p := by
    exact (hsame.trans hqnext).symm
  rcases quasiSchur_blockMap_eq_left_or_right_of_adjacent_same_block
      n pmap p q j hcard hpq hsame hjfiber with hjp | hjq
  · have hval : j.val = p.val := congrArg Fin.val hjp
    dsimp [j] at hval
    omega
  · have hval : j.val = q.val := congrArg Fin.val hjq
    dsimp [j] at hval
    omega

/-- Internal schedule constructor for Higham, 2nd ed., Chapter 16.2,
    equations (16.4)-(16.8): starting from a boundary index whose immediate
    predecessor, when present, has a different block label, recursively build a
    finite frontier schedule.  Each step is either a singleton with both
    neighbor-label separations or an adjacent same-labelled two-column block. -/
theorem quasiSchur_exists_frontier_schedule_from_boundary
    (n : Nat) (pmap : Fin n -> Nat)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (k : Nat) (hk : k <= n)
    (hboundary : forall hklt : k < n, forall q : Fin n,
      q.val + 1 = k -> pmap q ≠ pmap ⟨k, hklt⟩) :
    exists (r : Nat) (frontier : Nat -> Nat),
      frontier 0 = k /\
      frontier r = n /\
      (forall t : Nat, t < r -> frontier t < n) /\
      (forall t : Nat, t < r ->
        (exists p : Fin n,
          p.val = frontier t /\
          frontier (t + 1) = frontier t + 1 /\
          (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) /\
          (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q))
        \/
        (exists p q : Fin n,
          p.val = frontier t /\
          q.val = frontier t + 1 /\
          frontier (t + 1) = frontier t + 2 /\
          pmap p = pmap q)) := by
  have H : forall d k : Nat, k <= n -> n - k = d ->
      (forall hklt : k < n, forall q : Fin n,
        q.val + 1 = k -> pmap q ≠ pmap ⟨k, hklt⟩) ->
      exists (r : Nat) (frontier : Nat -> Nat),
        frontier 0 = k /\
        frontier r = n /\
        (forall t : Nat, t < r -> frontier t < n) /\
        (forall t : Nat, t < r ->
          (exists p : Fin n,
            p.val = frontier t /\
            frontier (t + 1) = frontier t + 1 /\
            (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) /\
            (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q))
          \/
          (exists p q : Fin n,
            p.val = frontier t /\
            q.val = frontier t + 1 /\
            frontier (t + 1) = frontier t + 2 /\
            pmap p = pmap q)) := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
        intro k hk hdist hboundary
        by_cases hklt : k < n
        · rcases quasiSchur_frontier_step_of_boundary n pmap k hklt
              (hboundary hklt) with hsingle | hblock
          · rcases hsingle with ⟨p, hpval, hprev, hnext⟩
            have hk1 : k + 1 <= n := by omega
            have hboundary1 : forall hk1lt : k + 1 < n, forall q : Fin n,
                q.val + 1 = k + 1 -> pmap q ≠ pmap ⟨k + 1, hk1lt⟩ := by
              intro hk1lt q hq
              have hsuccp : p.val + 1 < n := by omega
              have hb := quasiSchur_boundary_after_singleton_step
                n pmap p hnext hsuccp q (by omega)
              simpa [hpval] using hb
            have hfuel1 : n - (k + 1) < d := by omega
            rcases ih (n - (k + 1)) hfuel1 (k + 1) hk1 rfl hboundary1 with
              ⟨rTail, tail, htail0, htailEnd, htailLt, htailStep⟩
            let frontier : Nat -> Nat := fun t =>
              match t with
              | 0 => k
              | s + 1 => tail s
            refine ⟨rTail + 1, frontier, rfl, ?_, ?_, ?_⟩
            · change frontier (rTail + 1) = n
              simpa [frontier, Nat.succ_eq_add_one] using htailEnd
            · intro t ht
              cases t with
              | zero =>
                  simpa [frontier] using hklt
              | succ s =>
                  have hs : s < rTail := by omega
                  simpa [frontier] using htailLt s hs
            · intro t ht
              cases t with
              | zero =>
                  refine Or.inl ⟨p, ?_, ?_, hprev, hnext⟩
                  · simpa [frontier] using hpval
                  · simpa [frontier, hpval, Nat.succ_eq_add_one] using htail0
              | succ s =>
                  have hs : s < rTail := by omega
                  rcases htailStep s hs with htailSingle | htailBlock
                  · rcases htailSingle with ⟨p', hpval', hfront', hprev', hnext'⟩
                    refine Or.inl ⟨p', ?_, ?_, hprev', hnext'⟩
                    · simpa [frontier] using hpval'
                    · simpa [frontier, Nat.succ_eq_add_one] using hfront'
                  · rcases htailBlock with ⟨p', q', hpval', hqval', hfront', hsame'⟩
                    refine Or.inr ⟨p', q', ?_, ?_, ?_, hsame'⟩
                    · simpa [frontier] using hpval'
                    · simpa [frontier, Nat.succ_eq_add_one] using hqval'
                    · simpa [frontier, Nat.succ_eq_add_one] using hfront'
          · rcases hblock with ⟨p, q, hpval, hqval, hsame⟩
            have hk2 : k + 2 <= n := by
              have hq_lt := q.isLt
              omega
            have hboundary2 : forall hk2lt : k + 2 < n, forall r : Fin n,
                r.val + 1 = k + 2 -> pmap r ≠ pmap ⟨k + 2, hk2lt⟩ := by
              intro hk2lt r hr
              have hpq : q.val = p.val + 1 := by omega
              have hnextq : q.val + 1 < n := by omega
              have hb := quasiSchur_boundary_after_adjacent_same_block
                n pmap p q hcard hpq hsame hnextq r (by omega)
              simpa [hpval, hqval] using hb
            have hfuel2 : n - (k + 2) < d := by omega
            rcases ih (n - (k + 2)) hfuel2 (k + 2) hk2 rfl hboundary2 with
              ⟨rTail, tail, htail0, htailEnd, htailLt, htailStep⟩
            let frontier : Nat -> Nat := fun t =>
              match t with
              | 0 => k
              | s + 1 => tail s
            refine ⟨rTail + 1, frontier, rfl, ?_, ?_, ?_⟩
            · change frontier (rTail + 1) = n
              simpa [frontier, Nat.succ_eq_add_one] using htailEnd
            · intro t ht
              cases t with
              | zero =>
                  simpa [frontier] using hklt
              | succ s =>
                  have hs : s < rTail := by omega
                  simpa [frontier] using htailLt s hs
            · intro t ht
              cases t with
              | zero =>
                  refine Or.inr ⟨p, q, ?_, ?_, ?_, hsame⟩
                  · simpa [frontier] using hpval
                  · simpa [frontier, Nat.succ_eq_add_one] using hqval
                  · simpa [frontier, hpval, Nat.succ_eq_add_one] using htail0
              | succ s =>
                  have hs : s < rTail := by omega
                  rcases htailStep s hs with htailSingle | htailBlock
                  · rcases htailSingle with ⟨p', hpval', hfront', hprev', hnext'⟩
                    refine Or.inl ⟨p', ?_, ?_, hprev', hnext'⟩
                    · simpa [frontier] using hpval'
                    · simpa [frontier, Nat.succ_eq_add_one] using hfront'
                  · rcases htailBlock with ⟨p', q', hpval', hqval', hfront', hsame'⟩
                    refine Or.inr ⟨p', q', ?_, ?_, ?_, hsame'⟩
                    · simpa [frontier] using hpval'
                    · simpa [frontier, Nat.succ_eq_add_one] using hqval'
                    · simpa [frontier, Nat.succ_eq_add_one] using hfront'
        · have hkn : k = n := by omega
          subst k
          refine ⟨0, fun _ => n, rfl, rfl, ?_, ?_⟩
          · intro t ht
            omega
          · intro t ht
            omega
  exact H (n - k) k hk rfl hboundary

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): every
    size-at-most-two real-quasi-Schur block map admits a finite frontier
    schedule whose steps are singleton columns with local neighbor separation
    or adjacent same-labelled two-column blocks. -/
theorem quasiSchur_exists_frontier_schedule
    (n : Nat) (pmap : Fin n -> Nat)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2) :
    exists (r : Nat) (frontier : Nat -> Nat),
      frontier 0 = 0 /\
      frontier r = n /\
      (forall t : Nat, t < r -> frontier t < n) /\
      (forall t : Nat, t < r ->
        (exists p : Fin n,
          p.val = frontier t /\
          frontier (t + 1) = frontier t + 1 /\
          (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) /\
          (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q))
        \/
        (exists p q : Fin n,
          p.val = frontier t /\
          q.val = frontier t + 1 /\
          frontier (t + 1) = frontier t + 2 /\
          pmap p = pmap q)) := by
  refine quasiSchur_exists_frontier_schedule_from_boundary
    n pmap hcard 0 (Nat.zero_le n) ?_
  intro h0lt q hq
  omega












































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Generated-frontier Bartels-Stewart candidate formula oracle for a real
    quasi-Schur block map.  Singleton columns are supplied by the shifted
    inverse recurrence when both neighbor labels differ; adjacent same-block
    columns are supplied by the two-column block inverse recurrence. -/
def IsSylvesterQuasiSchurGeneratedStepFormula (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (C X : RMatFn m n) (pmap : Fin n -> Nat) : Prop :=
  (forall p : Fin n,
    (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
    (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
    forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
          (fun i => C i p +
            Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
              (fun j => S j p * X i j)) i) ∧
  (forall p q : Fin n,
    q.val = p.val + 1 ->
    pmap p = pmap q ->
    (forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) ∧
    (forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i)))

/-- Prefix form of the generated Bartels-Stewart column formulas for a
    recursive column-family state.  The predicate records that every singleton
    or adjacent same-block formula whose active columns lie strictly before the
    natural-number frontier `N` has already been established. -/
def IsSylvesterColumnFamilyGeneratedPrefix (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (C : RMatFn m n) (x : Fin n -> Fin m -> Real)
    (pmap : Fin n -> Nat) (N : Nat) : Prop :=
  (forall p : Fin n, p.val < N ->
    (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
    (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
    forall i : Fin m,
      x p i =
        Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
          (fun i => C i p +
            Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
              (fun j => S j p * x j i)) i) /\
  (forall p q : Fin n, p.val < N -> q.val < N ->
    q.val = p.val + 1 ->
    pmap p = pmap q ->
    (forall i : Fin m,
      x p i =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C (fun i j => x j i) p q)
          (Sum.inl i)) /\
    (forall i : Fin m,
      x q i =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C (fun i j => x j i) p q)
          (Sum.inr i)))

/-- Empty generated-prefix base case. -/
theorem isSylvesterColumnFamilyGeneratedPrefix_zero
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (C : RMatFn m n) (x : Fin n -> Fin m -> Real)
    (pmap : Fin n -> Nat) :
    IsSylvesterColumnFamilyGeneratedPrefix m n R S C x pmap 0 := by
  constructor
  · intro p hp _ _ _
    omega
  · intro p q hp _ _ _
    omega

/-- A generated-prefix certificate can be restricted to any earlier frontier. -/
theorem isSylvesterColumnFamilyGeneratedPrefix_mono
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (C : RMatFn m n) (x : Fin n -> Fin m -> Real)
    (pmap : Fin n -> Nat) {M N : Nat}
    (hMN : M <= N)
    (hprefix : IsSylvesterColumnFamilyGeneratedPrefix m n R S C x pmap N) :
    IsSylvesterColumnFamilyGeneratedPrefix m n R S C x pmap M := by
  rcases hprefix with ⟨hsingle, hblock⟩
  constructor
  · intro p hp hprev hnext i
    exact hsingle p (by omega) hprev hnext i
  · intro p q hp hq hpq hsame
    exact hblock p q (by omega) (by omega) hpq hsame

/-- A generated-prefix certificate through frontier `n` supplies the full
    generated-step formula predicate for the corresponding `RMatFn`. -/
theorem isSylvesterQuasiSchurGeneratedStepFormula_of_column_family_generated_prefix
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (C : RMatFn m n) (x : Fin n -> Fin m -> Real)
    (pmap : Fin n -> Nat)
    (hprefix : IsSylvesterColumnFamilyGeneratedPrefix m n R S C x pmap n) :
    IsSylvesterQuasiSchurGeneratedStepFormula m n R S C
      (fun i j => x j i) pmap := by
  rcases hprefix with ⟨hsingle, hblock⟩
  constructor
  · intro p hprev hnext i
    exact hsingle p p.isLt hprev hnext i
  · intro p q hpq hsame
    exact hblock p q p.isLt q.isLt hpq hsame







/-- A singleton recursive update extends the generated-prefix certificate by
    one frontier column, provided that the current frontier column is separated
    from its immediate predecessor in the quasi-Schur block map. -/
theorem isSylvesterColumnFamilyGeneratedPrefix_after_singleton_update
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (C : RMatFn m n) (x : Fin n -> Fin m -> Real)
    (pmap : Fin n -> Nat) (N : Nat) (p : Fin n)
    (hp : p.val = N)
    (hprefix : IsSylvesterColumnFamilyGeneratedPrefix m n R S C x pmap N)
    (hprev : forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) :
    let xp : Fin m -> Real :=
      Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
        (fun i => C i p +
          Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
            (fun j => S j p * x j i))
    let xNew : Fin n -> Fin m -> Real := Function.update x p xp
    IsSylvesterColumnFamilyGeneratedPrefix m n R S C xNew pmap (N + 1) := by
  let xp : Fin m -> Real :=
    Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
      (fun i => C i p +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => S j p * x j i))
  let xNew : Fin n -> Fin m -> Real := Function.update x p xp
  change IsSylvesterColumnFamilyGeneratedPrefix m n R S C xNew pmap (N + 1)
  rcases hprefix with ⟨hsingle, hblock⟩
  constructor
  · intro k hk hprevk hnextk i
    by_cases hkold : k.val < N
    · have hkp : k <= p := Fin.le_def.mpr (by rw [hp]; omega)
      have hk_ne_p : Not (k = p) := by
        intro h
        have hval : k.val = p.val := congrArg Fin.val h
        omega
      have hk_update : xNew k i = x k i := by
        dsimp [xNew]
        rw [Function.update_of_ne hk_ne_p]
      have hRhs :
          (fun i : Fin m => C i k +
            Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
              (fun j => S j k * xNew j i)) =
          (fun i : Fin m => C i k +
            Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
              (fun j => S j k * x j i)) := by
        dsimp [xNew]
        exact
          sylvester_singleton_column_rhs_eq_of_column_update_at_or_after
            m n S C x k p xp hkp
      rw [hk_update, hRhs]
      exact hsingle k hkold hprevk hnextk i
    · have hkp : k = p := by
        apply Fin.ext
        rw [hp]
        omega
      subst k
      dsimp [xNew]
      exact sylvesterSingleton_formula_of_column_family_update m n R S C x p i
  · intro k l hk hl hkl hsame
    by_cases hlold : l.val < N
    · have hkold : k.val < N := by omega
      have hkp : k <= p := Fin.le_def.mpr (by rw [hp]; omega)
      have hk_ne_p : Not (k = p) := by
        intro h
        have hval : k.val = p.val := congrArg Fin.val h
        omega
      have hl_ne_p : Not (l = p) := by
        intro h
        have hval : l.val = p.val := congrArg Fin.val h
        omega
      have hk_update : forall i : Fin m, xNew k i = x k i := by
        intro i
        dsimp [xNew]
        rw [Function.update_of_ne hk_ne_p]
      have hl_update : forall i : Fin m, xNew l i = x l i := by
        intro i
        dsimp [xNew]
        rw [Function.update_of_ne hl_ne_p]
      have hRhs :
          sylvesterTwoColumnBlockRhs m n S C (fun i j => xNew j i) k l =
          sylvesterTwoColumnBlockRhs m n S C (fun i j => x j i) k l := by
        dsimp [xNew]
        exact
          sylvesterTwoColumnBlockRhs_eq_of_column_update_at_or_after
            m n S C x k l p xp hkp
      rcases hblock k l hkold hlold hkl hsame with ⟨hkformula, hlformula⟩
      constructor
      · intro i
        rw [hk_update i, hRhs]
        exact hkformula i
      · intro i
        rw [hl_update i, hRhs]
        exact hlformula i
    · have hlp : l = p := by
        apply Fin.ext
        rw [hp]
        omega
      have hkpval : k.val + 1 = p.val := by
        simpa [hlp] using hkl.symm
      have hsame_kp : pmap k = pmap p := by
        simpa [hlp] using hsame
      exact False.elim ((hprev k hkpval) hsame_kp)

/-- An adjacent same-block recursive update extends the generated-prefix
    certificate by two frontier columns.  The size-at-most-two block-map
    hypothesis rules out a hidden same-labelled predecessor block ending at the
    first updated column. -/
theorem isSylvesterColumnFamilyGeneratedPrefix_after_two_column_update
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (C : RMatFn m n) (x : Fin n -> Fin m -> Real)
    (pmap : Fin n -> Nat) (N : Nat) (p q : Fin n)
    (hp : p.val = N) (hq : q.val = N + 1)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hsame : pmap p = pmap q)
    (hprefix : IsSylvesterColumnFamilyGeneratedPrefix m n R S C x pmap N) :
    let z : Sum (Fin m) (Fin m) -> Real :=
      Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
        (sylvesterTwoColumnBlockRhs m n S C (fun i j => x j i) p q)
    let xNew : Fin n -> Fin m -> Real :=
      Function.update (Function.update x p (fun i => z (Sum.inl i))) q
        (fun i => z (Sum.inr i))
    IsSylvesterColumnFamilyGeneratedPrefix m n R S C xNew pmap (N + 2) := by
  let z : Sum (Fin m) (Fin m) -> Real :=
    Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
      (sylvesterTwoColumnBlockRhs m n S C (fun i j => x j i) p q)
  let xNew : Fin n -> Fin m -> Real :=
    Function.update (Function.update x p (fun i => z (Sum.inl i))) q
      (fun i => z (Sum.inr i))
  have hpq : q.val = p.val + 1 := by omega
  have hNp : N <= p.val := by omega
  have hNq : N <= q.val := by omega
  change IsSylvesterColumnFamilyGeneratedPrefix m n R S C xNew pmap (N + 2)
  rcases hprefix with ⟨hsingle, hblock⟩
  constructor
  · intro k hk hprevk hnextk i
    by_cases hkold : k.val < N
    · have hk_update : xNew k i = x k i := by
        dsimp [xNew]
        exact
          sylvesterColumnFamily_prefix_eq_of_two_column_updates_ge_nat
            x N p q (fun i => z (Sum.inl i)) (fun i => z (Sum.inr i))
            hNp hNq k hkold i
      have hkp : k <= p := Fin.le_def.mpr (by rw [hp]; omega)
      have hkq : k <= q := Fin.le_def.mpr (by rw [hq]; omega)
      have hRhs :
          (fun i : Fin m => C i k +
            Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
              (fun j => S j k * xNew j i)) =
          (fun i : Fin m => C i k +
            Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
              (fun j => S j k * x j i)) := by
        dsimp [xNew]
        calc
          (fun i : Fin m => C i k +
            Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
              (fun j =>
                S j k *
                  Function.update (Function.update x p (fun i => z (Sum.inl i)))
                    q (fun i => z (Sum.inr i)) j i)) =
              (fun i : Fin m => C i k +
                Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
                  (fun j =>
                    S j k * Function.update x p (fun i => z (Sum.inl i)) j i)) := by
                exact
                  sylvester_singleton_column_rhs_eq_of_column_update_at_or_after
                    m n S C (Function.update x p (fun i => z (Sum.inl i)))
                    k q (fun i => z (Sum.inr i)) hkq
          _ =
              (fun i : Fin m => C i k +
                Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
                  (fun j => S j k * x j i)) := by
                exact
                  sylvester_singleton_column_rhs_eq_of_column_update_at_or_after
                    m n S C x k p (fun i => z (Sum.inl i)) hkp
      rw [hk_update, hRhs]
      exact hsingle k hkold hprevk hnextk i
    · have hkcase : k = p ∨ k = q := by
        have hkval : k.val = N ∨ k.val = N + 1 := by omega
        rcases hkval with hkN | hkN1
        · exact Or.inl (Fin.ext (by rw [hkN, hp]))
        · exact Or.inr (Fin.ext (by rw [hkN1, hq]))
      rcases hkcase with hkp_eq | hkq_eq
      · subst k
        exact False.elim ((hnextk q hpq) hsame)
      · subst k
        exact False.elim ((hprevk p hpq.symm) hsame)
  · intro k l hk hl hkl hsamekl
    by_cases hlold : l.val < N
    · have hkold : k.val < N := by omega
      have hkp : k <= p := Fin.le_def.mpr (by rw [hp]; omega)
      have hkq : k <= q := Fin.le_def.mpr (by rw [hq]; omega)
      have hk_update : forall i : Fin m, xNew k i = x k i := by
        intro i
        dsimp [xNew]
        exact
          sylvesterColumnFamily_prefix_eq_of_two_column_updates_ge_nat
            x N p q (fun i => z (Sum.inl i)) (fun i => z (Sum.inr i))
            hNp hNq k hkold i
      have hl_update : forall i : Fin m, xNew l i = x l i := by
        intro i
        dsimp [xNew]
        exact
          sylvesterColumnFamily_prefix_eq_of_two_column_updates_ge_nat
            x N p q (fun i => z (Sum.inl i)) (fun i => z (Sum.inr i))
            hNp hNq l hlold i
      have hRhs :
          sylvesterTwoColumnBlockRhs m n S C (fun i j => xNew j i) k l =
          sylvesterTwoColumnBlockRhs m n S C (fun i j => x j i) k l := by
        dsimp [xNew]
        exact
          sylvesterTwoColumnBlockRhs_eq_of_two_column_updates_at_or_after
            m n S C x k l p q
            (fun i => z (Sum.inl i)) (fun i => z (Sum.inr i)) hkp hkq
      rcases hblock k l hkold hlold hkl hsamekl with ⟨hkformula, hlformula⟩
      constructor
      · intro i
        rw [hk_update i, hRhs]
        exact hkformula i
      · intro i
        rw [hl_update i, hRhs]
        exact hlformula i
    · have hlcase : l.val = N ∨ l.val = N + 1 := by omega
      rcases hlcase with hlN | hlN1
      · have hlp : l = p := Fin.ext (by rw [hlN, hp])
        have hkpmap : pmap k = pmap p := by
          simpa [hlp] using hsamekl
        rcases quasiSchur_blockMap_eq_left_or_right_of_adjacent_same_block
            n pmap p q k hcard hpq hsame hkpmap with hk_eq_p | hk_eq_q
        · have hkval : k.val = p.val := congrArg Fin.val hk_eq_p
          omega
        · have hkval : k.val = q.val := congrArg Fin.val hk_eq_q
          omega
      · have hlq : l = q := Fin.ext (by rw [hlN1, hq])
        have hkpval : k.val = N := by
          rw [hlN1] at hkl
          omega
        have hkp_eq : k = p := Fin.ext (by rw [hkpval, hp])
        subst k
        subst l
        exact sylvesterTwoColumnBlock_formula_of_column_family_block_update
          m n R S C x p q hpq

/-- A supplied generated frontier schedule constructs a terminal recursive
    column-family state satisfying all generated singleton and adjacent-block
    formulas.  This is the noncomputable existence form of the scheduled
    Bartels-Stewart candidate; it is still exact arithmetic and does not model
    rounded residuals or estimator data. -/
theorem exists_isSylvesterColumnFamilyGeneratedPrefix_of_frontier_schedule
    (m n r : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (C : RMatFn m n) (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hstart : frontier 0 = 0) (hend : frontier r = n)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) /\
        (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q)) :
    exists x : Fin n -> Fin m -> Real,
      IsSylvesterColumnFamilyGeneratedPrefix m n R S C x pmap n := by
  have hstates : forall t : Nat, t <= r ->
      exists x : Fin n -> Fin m -> Real,
        IsSylvesterColumnFamilyGeneratedPrefix m n R S C x pmap (frontier t) := by
    intro t
    induction t with
    | zero =>
        intro _ht
        refine ⟨fun _ _ => 0, ?_⟩
        simpa [hstart] using
          isSylvesterColumnFamilyGeneratedPrefix_zero
            m n R S C (fun _ _ => 0) pmap
    | succ t ih =>
        intro ht
        have htlt : t < r := by omega
        rcases ih (by omega) with ⟨x, hprefix⟩
        rcases hstep t htlt with hsingle | hblock
        · rcases hsingle with ⟨p, hp, hfront, hprev, _hnext⟩
          let xp : Fin m -> Real :=
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => C i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * x j i))
          let xNew : Fin n -> Fin m -> Real := Function.update x p xp
          refine ⟨xNew, ?_⟩
          have hprefix' :=
            isSylvesterColumnFamilyGeneratedPrefix_after_singleton_update
              m n R S C x pmap (frontier t) p hp hprefix hprev
          simpa [xNew, xp, hfront] using hprefix'
        · rcases hblock with ⟨p, q, hp, hq, hfront, hsame⟩
          let z : Sum (Fin m) (Fin m) -> Real :=
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C (fun i j => x j i) p q)
          let xNew : Fin n -> Fin m -> Real :=
            Function.update (Function.update x p (fun i => z (Sum.inl i))) q
              (fun i => z (Sum.inr i))
          refine ⟨xNew, ?_⟩
          have hprefix' :=
            isSylvesterColumnFamilyGeneratedPrefix_after_two_column_update
              m n R S C x pmap (frontier t) p q hp hq hcard hsame hprefix
          simpa [xNew, z, hfront] using hprefix'
  rcases hstates r le_rfl with ⟨x, hprefix⟩
  exact ⟨x, by simpa [hend] using hprefix⟩

/-- A supplied generated frontier schedule constructs an `RMatFn` candidate
    satisfying the packaged generated-step formula predicate. -/
theorem exists_isSylvesterQuasiSchurGeneratedStepFormula_of_frontier_schedule
    (m n r : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (C : RMatFn m n) (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hstart : frontier 0 = 0) (hend : frontier r = n)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) /\
        (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q)) :
    exists X : RMatFn m n,
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S C X pmap := by
  rcases exists_isSylvesterColumnFamilyGeneratedPrefix_of_frontier_schedule
      m n r R S C pmap frontier hstart hend hcard hstep with ⟨x, hprefix⟩
  exact
    ⟨fun i j => x j i,
      isSylvesterQuasiSchurGeneratedStepFormula_of_column_family_generated_prefix
        m n R S C x pmap hprefix⟩

/-- The automatically generated real-quasi-Schur frontier schedule constructs
    an exact recursive Bartels-Stewart candidate satisfying the packaged
    generated-step formula predicate. -/
theorem exists_isSylvesterQuasiSchurGeneratedStepFormula_of_quasiSchur_schedule
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (C : RMatFn m n) (pmap : Fin n -> Nat)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2) :
    exists X : RMatFn m n,
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S C X pmap := by
  rcases quasiSchur_exists_frontier_schedule n pmap hcard with
    ⟨r, frontier, hstart, hend, _hfrontLt, hstep⟩
  exact
    exists_isSylvesterQuasiSchurGeneratedStepFormula_of_frontier_schedule
      m n r R S C pmap frontier hstart hend hcard hstep



















/-- Column-family packaging for
    `IsSylvesterQuasiSchurGeneratedStepFormula`.  A recursive construction often
    maintains state as `Fin n -> Fin m -> Real`; this wrapper turns singleton
    and block formulas for that state into the existing `RMatFn` predicate. -/
theorem isSylvesterQuasiSchurGeneratedStepFormula_of_column_family
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (C : RMatFn m n) (x : Fin n -> Fin m -> Real)
    (pmap : Fin n -> Nat)
    (hsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      forall i : Fin m,
        x p i =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => C i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * x j i)) i)
    (hblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        x p i =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C (fun i j => x j i) p q)
            (Sum.inl i)) /\
      (forall i : Fin m,
        x q i =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C (fun i j => x j i) p q)
            (Sum.inr i))) :
    IsSylvesterQuasiSchurGeneratedStepFormula m n R S C
      (fun i j => x j i) pmap := by
  constructor
  · intro p hprev hnext i
    exact hsingle p hprev hnext i
  · intro p q hpq hsame
    exact hblock p q hpq hsame


















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.2, equation (16.4), strict singleton-block
    specialization of the supplied real quasi-Schur block map: if the supplied
    block map strictly increases with the matrix index, then the quasi-Schur
    below-block zero condition is ordinary upper triangularity. -/
theorem isUpperTriangularFn_of_strictBlockMap (n : Nat)
    (S : RMatFn n n) (p : Fin n -> Nat)
    (hpstrict : forall {i j : Fin n}, j < i -> p j < p i)
    (hSstrict : forall i j : Fin n, p j < p i -> S i j = 0) :
    IsUpperTriangularFn n S := by
  intro i j hji
  exact hSstrict i j (hpstrict hji)




















































































































































































































































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with a packaged computed-residual budget
    certificate. The strict block-map hypotheses are supplied factors, while
    vec/Kronecker nonsingularity remains an explicit determinant certificate. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  have _hU := hU
  have _hV := hV
  have _hA := hA
  have _hB := hB
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  have _hSstrict := hSstrict
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with a packaged computed-residual budget
    certificate and a scalar cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have _hU := hU
  have _hV := hV
  have _hA := hA
  have _hB := hB
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  have _hSstrict := hSstrict
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with a packaged computed-residual budget
    certificate and componentwise larger practical-budget inputs. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  have _hU := hU
  have _hV := hV
  have _hA := hA
  have _hB := hB
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  have _hSstrict := hSstrict
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono
      m n A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with a packaged computed-residual budget
    certificate, monotone supplied estimates, and a scalar cap. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have _hU := hU
  have _hV := hV
  have _hA := hA
  have _hB := hB
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  have _hSstrict := hSstrict
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar
      m n A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with an explicit residual error model:
    package `Rhat = R(Xhat) + dR` and `|dR| <= Ru` as a computed-residual
    certificate, then use the supplied strict-block certificate. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_error_model
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate
      m n U R A V S B pA pB C X Xhat Rhat Ru
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with an explicit residual error model
    and a scalar cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_error_model_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru dR : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_scalar
      m n U R A V S B pA pB C X Xhat Rhat Ru eta
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with an explicit residual error model and
    componentwise larger practical-budget inputs. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_error_model_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono
      m n U R A V S B pA pB C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with an explicit residual error model and
    a monotone scalar cap on an estimated practical budget. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono_scalar
      m n U R A V S B pA pB C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with raw computed-residual budget
    assumptions and a scalar cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_budget_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have _hU := hU
  have _hV := hV
  have _hA := hA
  have _hB := hB
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  have _hSstrict := hSstrict
  exact
    sylvester_practical_error_bound_of_computed_residual_budget_scalar m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hRu hRhat heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with raw computed-residual budget
    assumptions and componentwise larger practical-budget inputs. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_budget_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  have _hU := hU
  have _hV := hV
  have _hA := hA
  have _hB := hB
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  have _hSstrict := hSstrict
  exact
    sylvester_practical_error_bound_of_computed_residual_budget_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hRu hRhat hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with raw computed-residual budget
    assumptions, monotone supplied estimates, and a scalar cap. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_budget_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have _hU := hU
  have _hV := hV
  have _hA := hA
  have _hB := hB
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  have _hSstrict := hSstrict
  exact
    sylvester_practical_error_bound_of_computed_residual_budget_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hRu hRhat hRhat_le hRu_le heta hcomponent hXhat




















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end NumStability
