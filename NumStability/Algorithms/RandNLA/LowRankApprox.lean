import Mathlib.Tactic.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Matrix.PosDef
import NumStability.Analysis.MatrixSpectral
import NumStability.Algorithms.MatrixInversion
import NumStability.Algorithms.LU.Doolittle
import NumStability.Algorithms.RandNLA.Preconditioning

/-!
# Low-rank approximation foundations for the RandNLA CACM formalization

This file begins the local foundation for the paper's low-rank approximation
claims, including the structural condition around equation (9).  It deliberately
separates exact analysis objects from implementation-facing floating-point
objects: sampling probabilities remain exact mathematical inputs by the current
project convention, while computed projectors/bases are handled in
`Preconditioning.lean` by explicit certificates.
-/

namespace NumStability

open scoped BigOperators

/-- An exact rectangular rank factorization certificate `A = X Y` through an
inner dimension `r`.  This is the local rank vocabulary used before importing a
full rectangular SVD/rank/pseudoinverse library. -/
structure RectRankFactorization (m n r : ℕ) (A : Fin m → Fin n → ℝ) where
  left : Fin m → Fin r → ℝ
  right : Fin r → Fin n → ℝ
  factorization : ∀ i j, A i j = ∑ a : Fin r, left i a * right a j

/-- Repository-local predicate for "rectangular rank at most `r`", represented
by an explicit exact factorization. -/
def RectRankAtMost (m n r : ℕ) (A : Fin m → Fin n → ℝ) : Prop :=
  Nonempty (RectRankFactorization m n r A)

/-- Exact column reindexing along an equivalence between possibly different
finite right-coordinate domains.  This is analysis-object reindexing only; it
does not compute or round any matrix entries. -/
def rectReindexCols {m n p : ℕ} (π : Fin p ≃ Fin n)
    (A : Fin m → Fin n → ℝ) : Fin m → Fin p → ℝ :=
  fun i j => A i (π j)

/-- Exact column-permutation transport for an explicit rectangular rank
factorization.  This is a reindexing adapter only: it does not compute a
permutation or any floating-point quantity. -/
def RectRankFactorization.permuteCols {m n r : ℕ}
    {A : Fin m → Fin n → ℝ}
    (fac : RectRankFactorization m n r A) (π : Fin n ≃ Fin n) :
    RectRankFactorization m n r (rectPermuteCols π A) where
  left := fac.left
  right := fun a j => fac.right a (π j)
  factorization := by
    intro i j
    change A i (π j) = ∑ a : Fin r, fac.left i a * fac.right a (π j)
    exact fac.factorization i (π j)

/-- Rank-at-most is preserved by exact column permutation. -/
theorem RectRankAtMost.permuteCols {m n r : ℕ}
    {A : Fin m → Fin n → ℝ} (π : Fin n ≃ Fin n)
    (hA : RectRankAtMost m n r A) :
    RectRankAtMost m n r (rectPermuteCols π A) := by
  rcases hA with ⟨fac⟩
  exact ⟨fac.permuteCols π⟩

/-- Rank-at-most can be transported back across an exact column permutation. -/
theorem RectRankAtMost.of_permuteCols {m n r : ℕ}
    {A : Fin m → Fin n → ℝ} (π : Fin n ≃ Fin n)
    (hA : RectRankAtMost m n r (rectPermuteCols π A)) :
  RectRankAtMost m n r A := by
  rcases hA with ⟨fac⟩
  exact
    ⟨{ left := fac.left
       right := fun a j => fac.right a (π.symm j)
       factorization := by
        intro i j
        have h := fac.factorization i (π.symm j)
        simpa [rectPermuteCols] using h }⟩

/-- Exact column-equivalence transport for an explicit rectangular rank
factorization across possibly different finite right-coordinate domains. -/
def RectRankFactorization.reindexCols {m n p r : ℕ}
    {A : Fin m → Fin n → ℝ}
    (fac : RectRankFactorization m n r A) (π : Fin p ≃ Fin n) :
    RectRankFactorization m p r (rectReindexCols π A) where
  left := fac.left
  right := fun a j => fac.right a (π j)
  factorization := by
    intro i j
    change A i (π j) = ∑ a : Fin r, fac.left i a * fac.right a (π j)
    exact fac.factorization i (π j)

/-- Rank-at-most is preserved by exact column reindexing across an equivalence
of finite right-coordinate domains. -/
theorem RectRankAtMost.reindexCols {m n p r : ℕ}
    {A : Fin m → Fin n → ℝ} (π : Fin p ≃ Fin n)
    (hA : RectRankAtMost m n r A) :
    RectRankAtMost m p r (rectReindexCols π A) := by
  rcases hA with ⟨fac⟩
  exact ⟨fac.reindexCols π⟩

/-- Rank-at-most transports back across exact column reindexing by an
equivalence of finite right-coordinate domains. -/
theorem RectRankAtMost.of_reindexCols {m n p r : ℕ}
    {A : Fin m → Fin n → ℝ} (π : Fin p ≃ Fin n)
    (hA : RectRankAtMost m p r (rectReindexCols π A)) :
    RectRankAtMost m n r A := by
  rcases hA with ⟨fac⟩
  exact
    ⟨{ left := fac.left
       right := fun a j => fac.right a (π.symm j)
       factorization := by
        intro i j
        have h := fac.factorization i (π.symm j)
        simpa [rectReindexCols] using h }⟩

/-- Exact column reindexing along an equivalence preserves the squared
rectangular Frobenius norm. -/
theorem frobNormSqRect_reindexCols {m n p : ℕ}
    (π : Fin p ≃ Fin n) (A : Fin m → Fin n → ℝ) :
    frobNormSqRect (rectReindexCols π A) = frobNormSqRect A := by
  unfold frobNormSqRect rectReindexCols
  congr 1
  ext i
  exact
    Fintype.sum_equiv π
      (fun j : Fin p => A i (π j) ^ 2)
      (fun j : Fin n => A i j ^ 2)
      (fun _ => rfl)

/-- Exact column reindexing along an equivalence preserves the rectangular
Frobenius norm. -/
theorem frobNormRect_reindexCols {m n p : ℕ}
    (π : Fin p ≃ Fin n) (A : Fin m → Fin n → ℝ) :
    frobNormRect (rectReindexCols π A) = frobNormRect A := by
  unfold frobNormRect
  rw [frobNormSqRect_reindexCols π A]

/-- Transport a repository rank-at-most certificate across an explicit equality
of displayed rank parameters. -/
theorem rectRankAtMost_of_eq_rank {m n r k : ℕ}
    {A : Fin m → Fin n → ℝ}
    (h : r = k) (hr : RectRankAtMost m n r A) :
    RectRankAtMost m n k A := by
  subst k
  exact hr

/-- Linear map induced by the right factor in a rectangular rank
factorization.  Its kernel is the right nullspace used by the q-dimensional
Eckart--Young min-max route. -/
def rectRankRightFactorMap {n r : ℕ}
    (right : Fin r → Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin r → ℝ) where
  toFun := fun x => fun a => ∑ j : Fin n, right a j * x j
  map_add' := by
    intro x y
    ext a
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    ext a
    change (∑ j : Fin n, right a j * (c * x j)) =
      c * ∑ j : Fin n, right a j * x j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Euclidean-coordinate version of `rectRankRightFactorMap`.

The repository's matrix entries are plain finite functions, which carry the
linear algebra structure needed by rank-nullity but not the inner-product
instance used by mathlib's orthonormal-basis API in this project setup.  This
map puts only the kernel-selection layer in `EuclideanSpace`, while preserving
the same coordinate formula. -/
def rectRankRightFactorEuclideanMap {n r : ℕ}
    (right : Fin r → Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin r → ℝ) where
  toFun := fun x => fun a => ∑ j : Fin n, right a j * x j
  map_add' := by
    intro x y
    ext a
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    ext a
    change (∑ j : Fin n, right a j * (c * x j)) =
      c * ∑ j : Fin n, right a j * x j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The right factor of an `r`-column factorization on `r+q` coordinates has a
right kernel of dimension at least `q`.

This is exact rank-nullity infrastructure for the multi-tail
Eckart--Young route.  It does not select the `q`-dimensional witness family or
prove the tail Frobenius lower bound. -/
theorem rectRankRightFactorMap_ker_finrank_ge {r q : ℕ}
    (right : Fin r → Fin (r + q) → ℝ) :
    q ≤ Module.finrank ℝ (LinearMap.ker (rectRankRightFactorMap right)) := by
  classical
  let Rmap : (Fin (r + q) → ℝ) →ₗ[ℝ] (Fin r → ℝ) :=
    rectRankRightFactorMap right
  have hrange :
      Module.finrank ℝ (LinearMap.range Rmap) ≤ r := by
    calc
      Module.finrank ℝ (LinearMap.range Rmap) ≤
          Module.finrank ℝ (Fin r → ℝ) :=
        (LinearMap.range Rmap).finrank_le
      _ = r := by
        simp
  have hsum :
      Module.finrank ℝ (LinearMap.range Rmap) +
          Module.finrank ℝ (LinearMap.ker Rmap) =
        r + q := by
    simpa using
      (LinearMap.finrank_range_add_finrank_ker
        (K := ℝ) (V := Fin (r + q) → ℝ)
        (V₂ := Fin r → ℝ) Rmap)
  have hle :
      r + q ≤ r + Module.finrank ℝ (LinearMap.ker Rmap) := by
    calc
      r + q =
          Module.finrank ℝ (LinearMap.range Rmap) +
            Module.finrank ℝ (LinearMap.ker Rmap) := hsum.symm
      _ ≤ r + Module.finrank ℝ (LinearMap.ker Rmap) :=
          Nat.add_le_add_right hrange _
  exact Nat.le_of_add_le_add_left hle

/-- Rank-nullity lower bound specialized to an explicit repository
rank-factorization certificate. -/
theorem rectRankFactorization_rightKernel_finrank_ge {m r q : ℕ}
    {B : Fin m → Fin (r + q) → ℝ}
    (fac : RectRankFactorization m (r + q) r B) :
    q ≤ Module.finrank ℝ
      (LinearMap.ker (rectRankRightFactorMap fac.right)) :=
  rectRankRightFactorMap_ker_finrank_ge fac.right

/-- Euclidean-coordinate kernel dimension lower bound for the right factor of
an `r`-column factorization on `r+q` coordinates. -/
theorem rectRankRightFactorEuclideanMap_ker_finrank_ge {r q : ℕ}
    (right : Fin r → Fin (r + q) → ℝ) :
    q ≤ Module.finrank ℝ
      (LinearMap.ker (rectRankRightFactorEuclideanMap right)) := by
  classical
  let Rmap : EuclideanSpace ℝ (Fin (r + q)) →ₗ[ℝ] (Fin r → ℝ) :=
    rectRankRightFactorEuclideanMap right
  have hrange :
      Module.finrank ℝ (LinearMap.range Rmap) ≤ r := by
    calc
      Module.finrank ℝ (LinearMap.range Rmap) ≤
          Module.finrank ℝ (Fin r → ℝ) :=
        (LinearMap.range Rmap).finrank_le
      _ = r := by
        simp
  have hsum :
      Module.finrank ℝ (LinearMap.range Rmap) +
          Module.finrank ℝ (LinearMap.ker Rmap) =
        r + q := by
    simpa using
      (LinearMap.finrank_range_add_finrank_ker
        (K := ℝ) (V := EuclideanSpace ℝ (Fin (r + q)))
        (V₂ := Fin r → ℝ) Rmap)
  have hle :
      r + q ≤ r + Module.finrank ℝ (LinearMap.ker Rmap) := by
    calc
      r + q =
          Module.finrank ℝ (LinearMap.range Rmap) +
            Module.finrank ℝ (LinearMap.ker Rmap) := hsum.symm
      _ ≤ r + Module.finrank ℝ (LinearMap.ker Rmap) :=
          Nat.add_le_add_right hrange _
  exact Nat.le_of_add_le_add_left hle

/-- Euclidean-coordinate rank-nullity lower bound specialized to an explicit
repository rank-factorization certificate. -/
theorem rectRankFactorization_euclideanRightKernel_finrank_ge {m r q : ℕ}
    {B : Fin m → Fin (r + q) → ℝ}
    (fac : RectRankFactorization m (r + q) r B) :
    q ≤ Module.finrank ℝ
      (LinearMap.ker (rectRankRightFactorEuclideanMap fac.right)) :=
  rectRankRightFactorEuclideanMap_ker_finrank_ge fac.right

/-- A vector killed by the right factor is killed by the represented matrix.

This is the q-dimensional analogue of the algebra hidden inside the earlier
`r+1` rank-nullity bridge. -/
theorem rectRankFactorization_matrix_rightKernel_of_rightFactor_ker
    {m r q : ℕ}
    {B : Fin m → Fin (r + q) → ℝ}
    (fac : RectRankFactorization m (r + q) r B)
    {x : Fin (r + q) → ℝ}
    (hx : x ∈ LinearMap.ker (rectRankRightFactorMap fac.right)) :
    ∀ i : Fin m, (∑ j : Fin (r + q), B i j * x j) = 0 := by
  classical
  have hRzero : rectRankRightFactorMap fac.right x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have hright :
      ∀ a : Fin r, (∑ j : Fin (r + q), fac.right a j * x j) = 0 := by
    intro a
    simpa [rectRankRightFactorMap] using congrFun hRzero a
  intro i
  calc
    (∑ j : Fin (r + q), B i j * x j)
        =
          ∑ j : Fin (r + q),
            (∑ a : Fin r, fac.left i a * fac.right a j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [fac.factorization i j]
    _ =
          ∑ j : Fin (r + q), ∑ a : Fin r,
            (fac.left i a * fac.right a j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ =
          ∑ a : Fin r, ∑ j : Fin (r + q),
            (fac.left i a * fac.right a j) * x j := by
            rw [Finset.sum_comm]
    _ =
          ∑ a : Fin r,
            fac.left i a *
              (∑ j : Fin (r + q), fac.right a j * x j) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = 0 := by
            simp [hright]

/-- Euclidean-coordinate right-factor kernel membership still annihilates the
represented matrix entrywise. -/
theorem rectRankFactorization_matrix_rightKernel_of_euclideanRightFactor_ker
    {m r q : ℕ}
    {B : Fin m → Fin (r + q) → ℝ}
    (fac : RectRankFactorization m (r + q) r B)
    {x : EuclideanSpace ℝ (Fin (r + q))}
    (hx : x ∈ LinearMap.ker (rectRankRightFactorEuclideanMap fac.right)) :
    ∀ i : Fin m, (∑ j : Fin (r + q), B i j * x j) = 0 := by
  classical
  have hRzero : rectRankRightFactorEuclideanMap fac.right x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have hright :
      ∀ a : Fin r, (∑ j : Fin (r + q), fac.right a j * x j) = 0 := by
    intro a
    simpa [rectRankRightFactorEuclideanMap] using congrFun hRzero a
  intro i
  calc
    (∑ j : Fin (r + q), B i j * x j)
        =
          ∑ j : Fin (r + q),
            (∑ a : Fin r, fac.left i a * fac.right a j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [fac.factorization i j]
    _ =
          ∑ j : Fin (r + q), ∑ a : Fin r,
            (fac.left i a * fac.right a j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ =
          ∑ a : Fin r, ∑ j : Fin (r + q),
            (fac.left i a * fac.right a j) * x j := by
            rw [Finset.sum_comm]
    _ =
          ∑ a : Fin r,
            fac.left i a *
              (∑ j : Fin (r + q), fac.right a j * x j) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = 0 := by
            simp [hright]

/-- Select `q` linearly independent vectors inside the right-factor kernel of
a rank-`r` competitor on `r+q` right coordinates, and push each selected vector
through the stored factorization to get an entrywise right-kernel equation for
the represented matrix.

This is exact-object vector-selection infrastructure for the multi-tail
Eckart--Young route.  It does not prove the tail Frobenius lower bound or any
computed SVD/projector/sketch routine. -/
theorem rectRankFactorization_exists_rightKernelFamily {m r q : ℕ}
    {B : Fin m → Fin (r + q) → ℝ}
    (fac : RectRankFactorization m (r + q) r B) :
    ∃ x : Fin q → LinearMap.ker (rectRankRightFactorMap fac.right),
      LinearIndependent ℝ x ∧
        ∀ c : Fin q, ∀ i : Fin m,
          (∑ j : Fin (r + q), B i j *
            (x c : Fin (r + q) → ℝ) j) = 0 := by
  classical
  have hdim :
      q ≤ Module.finrank ℝ
        (LinearMap.ker (rectRankRightFactorMap fac.right)) :=
    rectRankFactorization_rightKernel_finrank_ge fac
  rcases
      exists_linearIndependent_of_le_finrank
        (R := ℝ)
        (M := LinearMap.ker (rectRankRightFactorMap fac.right))
        hdim with
    ⟨x, hxli⟩
  refine ⟨x, hxli, ?_⟩
  intro c i
  exact
    rectRankFactorization_matrix_rightKernel_of_rightFactor_ker
      fac (x c).property i

/-- Select `q` orthonormal vectors inside the right-factor kernel of a
rank-`r` competitor on `r+q` right coordinates, and push each selected vector
through the stored factorization to get an entrywise right-kernel equation for
the represented matrix.

This strengthens `rectRankFactorization_exists_rightKernelFamily` to the
orthonormal witness shape needed by the multi-tail min--max route.  It remains
exact-object infrastructure: it does not prove the tail Frobenius lower bound
or certify computed SVD/projector/sketch routines. -/
theorem rectRankFactorization_exists_orthonormalRightKernelFamily {m r q : ℕ}
    {B : Fin m → Fin (r + q) → ℝ}
    (fac : RectRankFactorization m (r + q) r B) :
    ∃ x : Fin q → LinearMap.ker (rectRankRightFactorEuclideanMap fac.right),
      Orthonormal ℝ x ∧
        ∀ c : Fin q, ∀ i : Fin m,
          (∑ j : Fin (r + q), B i j *
            (x c : EuclideanSpace ℝ (Fin (r + q))) j) = 0 := by
  classical
  let K : Type :=
    LinearMap.ker (rectRankRightFactorEuclideanMap fac.right)
  have hdim : q ≤ Module.finrank ℝ K := by
    simpa [K] using rectRankFactorization_euclideanRightKernel_finrank_ge fac
  let b : OrthonormalBasis (Fin (Module.finrank ℝ K)) ℝ K :=
    stdOrthonormalBasis ℝ K
  let x : Fin q → K := fun c => b (Fin.castLE hdim c)
  refine ⟨x, ?_, ?_⟩
  · have hb : Orthonormal ℝ
        (b : Fin (Module.finrank ℝ K) → K) :=
      b.orthonormal
    have hinj :
        Function.Injective
          (Fin.castLE hdim : Fin q → Fin (Module.finrank ℝ K)) :=
      Fin.castLE_injective hdim
    simpa [x, Function.comp_def] using hb.comp (Fin.castLE hdim) hinj
  · intro c i
    exact
      rectRankFactorization_matrix_rightKernel_of_euclideanRightFactor_ker
        fac (x c).property i

/-- A rank-at-most-`r` factorization with `r+1` right coordinates has a
nonzero right-kernel vector.

This is the first rank-nullity foundation for the Eckart--Young route: the
standard min-max lower-bound argument needs a nonzero vector in an
`r+1`-dimensional right subspace that is annihilated by any competing
rank-`r` matrix.  This theorem is exact-object algebra only; it does not prove
the singular-value lower bound or any computed SVD/projector routine. -/
theorem rectRankFactorization_exists_rightKernelVector_succ {m r : ℕ}
    {B : Fin m → Fin (r + 1) → ℝ}
    (fac : RectRankFactorization m (r + 1) r B) :
    ∃ x : Fin (r + 1) → ℝ,
      x ≠ 0 ∧
        ∀ i : Fin m, (∑ j : Fin (r + 1), B i j * x j) = 0 := by
  classical
  let Rmap : (Fin (r + 1) → ℝ) →ₗ[ℝ] (Fin r → ℝ) := {
    toFun := fun x => fun a => ∑ j : Fin (r + 1), fac.right a j * x j
    map_add' := by
      intro x y
      ext a
      simp [mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c x
      ext a
      simp [Finset.mul_sum, mul_assoc, mul_comm]
  }
  have hdim :
      Module.finrank ℝ (Fin r → ℝ) <
        Module.finrank ℝ (Fin (r + 1) → ℝ) := by
    simp
  have hker : LinearMap.ker Rmap ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (f := Rmap) hdim
  rcases (Submodule.ne_bot_iff (LinearMap.ker Rmap)).1 hker with
    ⟨x, hxmem, hxne⟩
  refine ⟨x, hxne, ?_⟩
  have hRzero : Rmap x = 0 := by
    simpa [LinearMap.mem_ker] using hxmem
  have hright :
      ∀ a : Fin r, (∑ j : Fin (r + 1), fac.right a j * x j) = 0 := by
    intro a
    simpa [Rmap] using congrFun hRzero a
  intro i
  calc
    (∑ j : Fin (r + 1), B i j * x j)
        =
          ∑ j : Fin (r + 1),
            (∑ a : Fin r, fac.left i a * fac.right a j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [fac.factorization i j]
    _ =
          ∑ j : Fin (r + 1), ∑ a : Fin r,
            (fac.left i a * fac.right a j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ =
          ∑ a : Fin r, ∑ j : Fin (r + 1),
            (fac.left i a * fac.right a j) * x j := by
            rw [Finset.sum_comm]
    _ =
          ∑ a : Fin r,
            fac.left i a *
              (∑ j : Fin (r + 1), fac.right a j * x j) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = 0 := by
            simp [hright]

/-- The rank-nullity kernel vector specialized to the repository
`RectRankAtMost` predicate. -/
theorem rectRankAtMost_exists_rightKernelVector_succ {m r : ℕ}
    {B : Fin m → Fin (r + 1) → ℝ}
    (hB : RectRankAtMost m (r + 1) r B) :
    ∃ x : Fin (r + 1) → ℝ,
      x ≠ 0 ∧
        ∀ i : Fin m, (∑ j : Fin (r + 1), B i j * x j) = 0 := by
  rcases hB with ⟨fac⟩
  exact rectRankFactorization_exists_rightKernelVector_succ fac

/-- Exact right Gram matrix `A^T A` for a rectangular real matrix.  This is an
analysis object.  Implementation-facing theorems must separately certify any
computed Gram entries. -/
noncomputable def rectRightGram {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ i : Fin m, A i j * A i k

/-- The exact right Gram matrix is symmetric. -/
theorem rectRightGram_symmetric {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (rectRightGram A) := by
  intro j k
  unfold rectRightGram
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The quadratic form of `A^T A` is the squared norm of `A x`. -/
theorem finiteQuadraticForm_rectRightGram_eq_sum_sq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    finiteQuadraticForm (rectRightGram A) x =
      ∑ i : Fin m, (∑ j : Fin n, A i j * x j) ^ 2 := by
  classical
  unfold finiteQuadraticForm finiteMatVec rectRightGram
  calc
    ∑ a : Fin n,
        x a *
          ∑ b : Fin n,
            (∑ i : Fin m, A i a * A i b) * x b
        =
          ∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin m,
            (A i a * x a) * (A i b * x b) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ =
          ∑ b : Fin n, ∑ a : Fin n, ∑ i : Fin m,
            (A i a * x a) * (A i b * x b) := by
            rw [Finset.sum_comm]
    _ =
          ∑ b : Fin n, ∑ i : Fin m, ∑ a : Fin n,
            (A i a * x a) * (A i b * x b) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m, ∑ b : Fin n, ∑ a : Fin n,
            (A i a * x a) * (A i b * x b) := by
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m, ∑ a : Fin n, ∑ b : Fin n,
            (A i a * x a) * (A i b * x b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m,
            (∑ a : Fin n, A i a * x a) *
              (∑ b : Fin n, A i b * x b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
    _ =
          ∑ i : Fin m, (∑ j : Fin n, A i j * x j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- The exact right Gram matrix is positive semidefinite. -/
theorem rectRightGram_finitePSD {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    finitePSD (rectRightGram A) := by
  intro x
  rw [finiteQuadraticForm_rectRightGram_eq_sum_sq A x]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Mathlib positive-semidefinite form of `rectRightGram_finitePSD`. -/
theorem rectRightGram_matrix_posSemidef {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    Matrix.PosSemidef ((rectRightGram A) : Matrix (Fin n) (Fin n) ℝ) :=
  finitePSD.to_matrix_posSemidef
    (rectRightGram A) (rectRightGram_symmetric A) (rectRightGram_finitePSD A)

/-- Canonical order-preserving cast from `Fin n` to mathlib's zero-indexed
Hermitian-eigenvalue domain for matrices indexed by `Fin n`. -/
def finCardIndex (n : ℕ) (j : Fin n) : Fin (Fintype.card (Fin n)) :=
  Fin.cast (by simp) j

/-- The canonical cast preserves the natural `Fin` order. -/
theorem finCardIndex_le {n : ℕ} {i j : Fin n} (hij : i ≤ j) :
    finCardIndex n i ≤ finCardIndex n j := by
  rw [Fin.le_def] at hij ⊢
  simpa [finCardIndex] using hij

/-- Exact singular-value squares, defined as the ordered zero-indexed Hermitian
eigenvalues of the exact right Gram `A^T A`.  This does not construct singular
vectors or an SVD. -/
noncomputable def rectSingularValueSq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j => (rectRightGram_matrix_posSemidef A).1.eigenvalues₀
    (finCardIndex n j)

/-- Exact singular values, obtained by square-rooting the right-Gram
eigenvalues. -/
noncomputable def rectSingularValue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (rectSingularValueSq A j)

/-- The right-Gram singular-value squares are nonnegative. -/
theorem rectSingularValueSq_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    0 ≤ rectSingularValueSq A j := by
  let hpsd := rectRightGram_matrix_posSemidef A
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let j0 : Fin (Fintype.card (Fin n)) := finCardIndex n j
  have h := hpsd.eigenvalues_nonneg (e j0)
  change 0 ≤ hpsd.1.eigenvalues₀ (e.symm (e j0)) at h
  have hej : e.symm (e j0) = j0 := e.symm_apply_apply j0
  rw [hej] at h
  simpa [rectSingularValueSq, hpsd, j0] using h

/-- The right-Gram singular-value squares are ordered in the mathlib
zero-indexed Hermitian eigenvalue order. -/
theorem rectSingularValueSq_antitone {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    Antitone (rectSingularValueSq A) := by
  intro i j hij
  let hpsd := rectRightGram_matrix_posSemidef A
  have hanti := hpsd.1.eigenvalues₀_antitone
  have hcast : finCardIndex n i ≤ finCardIndex n j :=
    finCardIndex_le hij
  exact hanti hcast

/-- Exact singular values are nonnegative. -/
theorem rectSingularValue_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    0 ≤ rectSingularValue A j := by
  unfold rectSingularValue
  exact Real.sqrt_nonneg _

/-- Exact singular values inherit the Hermitian eigenvalue order from the
right-Gram singular-value squares. -/
theorem rectSingularValue_antitone {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    Antitone (rectSingularValue A) := by
  intro i j hij
  unfold rectSingularValue
  exact Real.sqrt_le_sqrt (rectSingularValueSq_antitone A hij)

/-- Squaring the exact singular values recovers the right-Gram eigenvalues. -/
theorem rectSingularValue_sq_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    (rectSingularValue A j) ^ 2 = rectSingularValueSq A j := by
  unfold rectSingularValue
  exact Real.sq_sqrt (rectSingularValueSq_nonneg A j)

/-- Basis-indexed exact eigenvalues of the right Gram `A^T A`.  This index is
the one used by mathlib's Hermitian eigenvector basis; it is intentionally
separate from the ordered zero-indexed sequence `rectSingularValueSq`. -/
noncomputable def rectRightGramEigenvalue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j => (rectRightGram_matrix_posSemidef A).1.eigenvalues j

/-- Exact right-Gram eigenvector table, represented as a real square matrix.
Its columns are the mathlib Hermitian eigenvectors of the exact analysis Gram
`A^T A`.  Implementation-facing theorems must separately certify any computed
singular-vector table. -/
noncomputable def rectRightGramEigenbasis {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    ((Matrix.IsHermitian.eigenvectorUnitary
      (rectRightGram_matrix_posSemidef A).1 :
      Matrix (Fin n) (Fin n) ℝ) i j)

/-- Basis-indexed exact singular values attached to
`rectRightGramEigenbasis`. -/
noncomputable def rectRightGramBasisSingularValue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (rectRightGramEigenvalue A j)

/-- The right-Gram eigenvector table is orthogonal. -/
theorem rectRightGramEigenbasis_isOrthogonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    IsOrthogonal n (rectRightGramEigenbasis A) := by
  constructor
  · intro i j
    let U :=
      Matrix.IsHermitian.eigenvectorUnitary
        (rectRightGram_matrix_posSemidef A).1
    have h := Unitary.coe_star_mul_self U
    have hij := congr_fun (congr_fun h i) j
    simpa [rectRightGramEigenbasis, U, Matrix.mul_apply, Matrix.one_apply,
      matTranspose, idMatrix] using hij
  · intro i j
    let U :=
      Matrix.IsHermitian.eigenvectorUnitary
        (rectRightGram_matrix_posSemidef A).1
    have h := Unitary.coe_mul_star_self U
    have hij := congr_fun (congr_fun h i) j
    simpa [rectRightGramEigenbasis, U, Matrix.mul_apply, Matrix.one_apply,
      matTranspose, idMatrix] using hij

/-- Column orthonormality of the right-Gram eigenvector table. -/
theorem rectRightGramEigenbasis_col_orthonormal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i j : Fin n) :
    ∑ k : Fin n,
        rectRightGramEigenbasis A k i *
          rectRightGramEigenbasis A k j =
      idMatrix n i j := by
  simpa [idMatrix] using
    (rectRightGramEigenbasis_isOrthogonal A).col_orthonormal i j

/-- Row orthonormality of the right-Gram eigenvector table. -/
theorem rectRightGramEigenbasis_row_orthonormal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i j : Fin n) :
    ∑ k : Fin n,
        rectRightGramEigenbasis A i k *
          rectRightGramEigenbasis A j k =
      idMatrix n i j := by
  simpa [idMatrix] using
    (rectRightGramEigenbasis_isOrthogonal A).row_orthonormal i j

/-- Basis-indexed right-Gram eigenvalues are nonnegative because
`A^T A` is positive semidefinite. -/
theorem rectRightGramEigenvalue_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    0 ≤ rectRightGramEigenvalue A j := by
  let hpsd := rectRightGram_matrix_posSemidef A
  simpa [rectRightGramEigenvalue, hpsd] using hpsd.eigenvalues_nonneg j

/-- Basis-indexed right-Gram singular values are nonnegative. -/
theorem rectRightGramBasisSingularValue_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    0 ≤ rectRightGramBasisSingularValue A j := by
  unfold rectRightGramBasisSingularValue
  exact Real.sqrt_nonneg _

/-- Squaring a basis-indexed right-Gram singular value recovers its
basis-indexed eigenvalue. -/
theorem rectRightGramBasisSingularValue_sq_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    (rectRightGramBasisSingularValue A j) ^ 2 =
      rectRightGramEigenvalue A j := by
  unfold rectRightGramBasisSingularValue
  exact Real.sq_sqrt (rectRightGramEigenvalue_nonneg A j)

/-- Each column of `rectRightGramEigenbasis` is an eigenvector of the exact
right Gram, with basis-indexed eigenvalue `rectRightGramEigenvalue`. -/
theorem rectRightGramEigenbasis_eigenvector {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a j : Fin n) :
    ∑ k : Fin n,
        rectRightGram A j k * rectRightGramEigenbasis A k a =
      rectRightGramEigenvalue A a * rectRightGramEigenbasis A j a := by
  let hG := (rectRightGram_matrix_posSemidef A).1
  have h := hG.mulVec_eigenvectorBasis a
  have hj := congr_fun h j
  simpa [rectRightGramEigenbasis, rectRightGramEigenvalue, hG, Matrix.mulVec,
    Matrix.IsHermitian.eigenvectorUnitary_apply] using hj

/-- Exact diagonalization of the right Gram by the right-Gram eigenvector table:
`V^T (A^T A) V` is diagonal with the basis-indexed eigenvalues. -/
theorem rectRightGramEigenbasis_diagonalizes {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a b : Fin n) :
    ∑ j : Fin n,
        rectRightGramEigenbasis A j a *
          (∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b) =
      if a = b then rectRightGramEigenvalue A a else 0 := by
  have heig :
      ∀ j : Fin n,
        ∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b =
          rectRightGramEigenvalue A b *
            rectRightGramEigenbasis A j b := by
    intro j
    exact rectRightGramEigenbasis_eigenvector A b j
  have horth :
      ∑ j : Fin n,
          rectRightGramEigenbasis A j a *
            rectRightGramEigenbasis A j b =
        idMatrix n a b :=
    rectRightGramEigenbasis_col_orthonormal A a b
  calc
    ∑ j : Fin n,
        rectRightGramEigenbasis A j a *
          (∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b)
        =
          ∑ j : Fin n,
            rectRightGramEigenbasis A j a *
              (rectRightGramEigenvalue A b *
                rectRightGramEigenbasis A j b) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [heig j]
    _ =
          rectRightGramEigenvalue A b *
            (∑ j : Fin n,
              rectRightGramEigenbasis A j a *
                rectRightGramEigenbasis A j b) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = if a = b then rectRightGramEigenvalue A a else 0 := by
            by_cases hab : a = b
            · subst b
              simp [horth, idMatrix]
            · simp [horth, idMatrix, hab]

/-- Singular-value-square form of the right-Gram diagonalization. -/
theorem rectRightGramEigenbasis_diagonalizes_singularValueSq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a b : Fin n) :
    ∑ j : Fin n,
        rectRightGramEigenbasis A j a *
          (∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b) =
      if a = b then (rectRightGramBasisSingularValue A a) ^ 2 else 0 := by
  rw [rectRightGramEigenbasis_diagonalizes]
  by_cases hab : a = b
  · simp [hab, rectRightGramBasisSingularValue_sq_eq]
  · simp [hab]

/-- The exact column `A v_a`, where `v_a` is a basis-indexed right-Gram
eigenvector. -/
noncomputable def rectRightGramProjectedColumn {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i a => ∑ j : Fin n, A i j * rectRightGramEigenbasis A j a

/-- Left singular-vector candidates obtained from the basis-indexed
right-Gram eigenbasis by `u_a = A v_a / tau_a`.  The main orthonormality and
reconstruction theorem below requires strict positivity of every displayed
basis-indexed singular value. -/
noncomputable def rectRightGramLeftSingularFromEigenbasis {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i a =>
    (1 / rectRightGramBasisSingularValue A a) *
      rectRightGramProjectedColumn A i a

/-- Diagonal matrix formed from the basis-indexed right-Gram singular values. -/
noncomputable def rectRightGramBasisSingularDiagonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun a b => if a = b then rectRightGramBasisSingularValue A a else 0

/-- The dot product of projected columns `A v_a` and `A v_b` is the corresponding
right-Gram quadratic form. -/
theorem rectRightGramProjectedColumn_dot {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a b : Fin n) :
    ∑ i : Fin m,
        rectRightGramProjectedColumn A i a *
          rectRightGramProjectedColumn A i b =
      ∑ j : Fin n,
        rectRightGramEigenbasis A j a *
          (∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b) := by
  classical
  unfold rectRightGramProjectedColumn rectRightGram
  calc
    ∑ i : Fin m,
        (∑ j : Fin n, A i j * rectRightGramEigenbasis A j a) *
          (∑ k : Fin n, A i k * rectRightGramEigenbasis A k b)
        =
          ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n,
            (A i j * rectRightGramEigenbasis A j a) *
              (A i k * rectRightGramEigenbasis A k b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
    _ =
          ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
            rectRightGramEigenbasis A j a *
              ((A i j * A i k) * rectRightGramEigenbasis A k b) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ =
          ∑ j : Fin n,
            rectRightGramEigenbasis A j a *
              (∑ k : Fin n,
                (∑ i : Fin m, A i j * A i k) *
                  rectRightGramEigenbasis A k b) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            calc
              ∑ i : Fin m,
                  rectRightGramEigenbasis A j a *
                    ((A i j * A i k) *
                      rectRightGramEigenbasis A k b)
                  =
                    rectRightGramEigenbasis A j a *
                      (∑ i : Fin m,
                        (A i j * A i k) *
                          rectRightGramEigenbasis A k b) := by
                    rw [Finset.mul_sum]
              _ =
                    rectRightGramEigenbasis A j a *
                      ((∑ i : Fin m, A i j * A i k) *
                        rectRightGramEigenbasis A k b) := by
                    rw [Finset.sum_mul]
    _ =
          ∑ j : Fin n,
            rectRightGramEigenbasis A j a *
              (∑ k : Fin n,
                (∑ i : Fin m, A i j * A i k) *
                  rectRightGramEigenbasis A k b) := rfl

/-- Diagonal form of `rectRightGramProjectedColumn_dot`. -/
theorem rectRightGramProjectedColumn_dot_diagonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a b : Fin n) :
    ∑ i : Fin m,
        rectRightGramProjectedColumn A i a *
          rectRightGramProjectedColumn A i b =
      if a = b then (rectRightGramBasisSingularValue A a) ^ 2 else 0 := by
  rw [rectRightGramProjectedColumn_dot]
  exact rectRightGramEigenbasis_diagonalizes_singularValueSq A a b

/-- The squared norm of the projected column `A v_a` is the corresponding
basis-indexed singular value squared. -/
theorem rectRightGramProjectedColumn_normSq_eq_singularValue_sq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n) :
    ∑ i : Fin m, (rectRightGramProjectedColumn A i a) ^ 2 =
      (rectRightGramBasisSingularValue A a) ^ 2 := by
  have h := rectRightGramProjectedColumn_dot_diagonal A a a
  simpa [pow_two] using h

/-- Eigenvalue form of the projected-column squared-norm identity. -/
theorem rectRightGramProjectedColumn_normSq_eq_eigenvalue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n) :
    ∑ i : Fin m, (rectRightGramProjectedColumn A i a) ^ 2 =
      rectRightGramEigenvalue A a := by
  rw [rectRightGramProjectedColumn_normSq_eq_singularValue_sq,
    rectRightGramBasisSingularValue_sq_eq]

/-- A zero basis-indexed right-Gram singular value forces the corresponding
projected column `A v_a` to vanish coordinatewise. -/
theorem rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n)
    (hτ : rectRightGramBasisSingularValue A a = 0)
    (i : Fin m) :
    rectRightGramProjectedColumn A i a = 0 := by
  have hsum :
      ∑ k : Fin m, (rectRightGramProjectedColumn A k a) ^ 2 = 0 := by
    simpa [hτ] using
      rectRightGramProjectedColumn_normSq_eq_singularValue_sq A a
  have hterm :
      (rectRightGramProjectedColumn A i a) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => sq_nonneg (rectRightGramProjectedColumn A k a))).mp
      hsum i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hterm

/-- Eigenvalue-zero variant of
`rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero`. -/
theorem rectRightGramProjectedColumn_eq_zero_of_eigenvalue_eq_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n)
    (hα : rectRightGramEigenvalue A a = 0)
    (i : Fin m) :
    rectRightGramProjectedColumn A i a = 0 := by
  apply rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero A a
  have hsq :
      (rectRightGramBasisSingularValue A a) ^ 2 = 0 := by
    simpa [hα] using rectRightGramBasisSingularValue_sq_eq A a
  exact sq_eq_zero_iff.mp hsq

/-- Zero-safe left singular-vector candidates.  When the basis-indexed singular
value vanishes we set the candidate column to zero; otherwise it is
`A v_a / tau_a`. -/
noncomputable def rectRightGramLeftSingularZeroSafe {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ := by
  classical
  exact fun i a =>
    if rectRightGramBasisSingularValue A a = 0 then 0
    else
      (1 / rectRightGramBasisSingularValue A a) *
        rectRightGramProjectedColumn A i a

/-- The zero-safe left candidate is zero on zero singular-value columns. -/
theorem rectRightGramLeftSingularZeroSafe_eq_zero_of_singularValue_eq_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n)
    (hτ : rectRightGramBasisSingularValue A a = 0)
    (i : Fin m) :
    rectRightGramLeftSingularZeroSafe A i a = 0 := by
  classical
  simp [rectRightGramLeftSingularZeroSafe, hτ]

/-- Away from zero singular values, the zero-safe left candidate is the usual
normalized projected column. -/
theorem rectRightGramLeftSingularZeroSafe_eq_inv_mul_of_singularValue_ne_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n)
    (hτ : rectRightGramBasisSingularValue A a ≠ 0)
    (i : Fin m) :
    rectRightGramLeftSingularZeroSafe A i a =
      (1 / rectRightGramBasisSingularValue A a) *
        rectRightGramProjectedColumn A i a := by
  classical
  simp [rectRightGramLeftSingularZeroSafe, hτ]

/-- The zero-safe left candidates satisfy `tau_a u_a = A v_a` for every basis
index, including zero singular values. -/
theorem rectRightGramLeftSingularZeroSafe_factor_column
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (a : Fin n) :
    rectRightGramBasisSingularValue A a *
        rectRightGramLeftSingularZeroSafe A i a =
      rectRightGramProjectedColumn A i a := by
  classical
  by_cases hτ : rectRightGramBasisSingularValue A a = 0
  · have hy :
        rectRightGramProjectedColumn A i a = 0 :=
      rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero A a hτ i
    simp [rectRightGramLeftSingularZeroSafe, hτ, hy]
  · rw [rectRightGramLeftSingularZeroSafe_eq_inv_mul_of_singularValue_ne_zero
      A a hτ i]
    field_simp [hτ]

/-- If every basis-indexed right-Gram singular value is strictly positive, the
left candidates `A v_a / tau_a` have orthonormal columns. -/
theorem rectRightGramLeftSingularFromEigenbasis_col_orthonormal_of_pos
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hpos : ∀ a : Fin n, 0 < rectRightGramBasisSingularValue A a)
    (a b : Fin n) :
    ∑ i : Fin m,
        rectRightGramLeftSingularFromEigenbasis A i a *
          rectRightGramLeftSingularFromEigenbasis A i b =
      idMatrix n a b := by
  let τ := rectRightGramBasisSingularValue A
  have hdot := rectRightGramProjectedColumn_dot_diagonal A a b
  calc
    ∑ i : Fin m,
        rectRightGramLeftSingularFromEigenbasis A i a *
          rectRightGramLeftSingularFromEigenbasis A i b
        =
          (1 / τ a) * (1 / τ b) *
            (∑ i : Fin m,
              rectRightGramProjectedColumn A i a *
                rectRightGramProjectedColumn A i b) := by
            unfold rectRightGramLeftSingularFromEigenbasis
            calc
              ∑ i : Fin m,
                  1 / rectRightGramBasisSingularValue A a *
                      rectRightGramProjectedColumn A i a *
                    (1 / rectRightGramBasisSingularValue A b *
                      rectRightGramProjectedColumn A i b)
                  =
                    ∑ i : Fin m,
                      ((1 / τ a) * (1 / τ b)) *
                        (rectRightGramProjectedColumn A i a *
                          rectRightGramProjectedColumn A i b) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    ring
              _ =
                    (1 / τ a) * (1 / τ b) *
                      (∑ i : Fin m,
                        rectRightGramProjectedColumn A i a *
                          rectRightGramProjectedColumn A i b) := by
                    rw [Finset.mul_sum]
    _ =
          (1 / τ a) * (1 / τ b) *
            (if a = b then τ a ^ 2 else 0) := by
            rw [hdot]
    _ = idMatrix n a b := by
            by_cases hab : a = b
            · subst b
              have hne : τ a ≠ 0 := ne_of_gt (hpos a)
              simp [idMatrix]
              field_simp [hne]
            · simp [idMatrix, hab]

/-- The zero-safe left candidates are orthonormal on any pair of strictly
positive basis-indexed singular values.  This is the selected-column version
needed by ordered top-`k` source-split constructors: positivity only has to be
known for the displayed columns under consideration, not for every singular
direction. -/
theorem rectRightGramLeftSingularZeroSafe_col_orthonormal_of_pos
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {a b : Fin n}
    (ha : 0 < rectRightGramBasisSingularValue A a)
    (hb : 0 < rectRightGramBasisSingularValue A b) :
    ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i a *
          rectRightGramLeftSingularZeroSafe A i b =
      idMatrix n a b := by
  let τ := rectRightGramBasisSingularValue A
  have hane : τ a ≠ 0 := ne_of_gt ha
  have hbne : τ b ≠ 0 := ne_of_gt hb
  have hdot := rectRightGramProjectedColumn_dot_diagonal A a b
  calc
    ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i a *
          rectRightGramLeftSingularZeroSafe A i b
        =
          (1 / τ a) * (1 / τ b) *
            (∑ i : Fin m,
              rectRightGramProjectedColumn A i a *
                rectRightGramProjectedColumn A i b) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [rectRightGramLeftSingularZeroSafe_eq_inv_mul_of_singularValue_ne_zero
              A a hane i,
              rectRightGramLeftSingularZeroSafe_eq_inv_mul_of_singularValue_ne_zero
                A b hbne i]
            ring
    _ =
          (1 / τ a) * (1 / τ b) *
            (if a = b then τ a ^ 2 else 0) := by
            rw [hdot]
    _ = idMatrix n a b := by
            by_cases hab : a = b
            · subst b
              simp [idMatrix]
              field_simp [hane]
            · simp [idMatrix, hab]

/-- A positive zero-safe left singular-vector candidate is orthogonal to any
distinct zero-safe candidate.  The second candidate may have zero singular
value, in which case it is the zero column by definition. -/
theorem rectRightGramLeftSingularZeroSafe_cross_zero_of_pos_ne
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {a b : Fin n}
    (ha : 0 < rectRightGramBasisSingularValue A a) (hab : a ≠ b) :
    ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i a *
          rectRightGramLeftSingularZeroSafe A i b =
      0 := by
  let τ := rectRightGramBasisSingularValue A
  by_cases hb0 : τ b = 0
  · calc
      ∑ i : Fin m,
          rectRightGramLeftSingularZeroSafe A i a *
            rectRightGramLeftSingularZeroSafe A i b
          =
            ∑ i : Fin m,
              rectRightGramLeftSingularZeroSafe A i a * 0 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [rectRightGramLeftSingularZeroSafe_eq_zero_of_singularValue_eq_zero
                A b hb0 i]
      _ = 0 := by simp
  · have hbpos : 0 < τ b := by
      exact lt_of_le_of_ne
        (rectRightGramBasisSingularValue_nonneg A b) (Ne.symm hb0)
    have horth :=
      rectRightGramLeftSingularZeroSafe_col_orthonormal_of_pos
        A ha hbpos
    simpa [idMatrix, hab] using horth

/-- Expanding in the exact right-Gram eigenbasis reconstructs every row of
`A`. -/
theorem rectRightGramProjectedColumn_reconstruct {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    ∑ a : Fin n,
        rectRightGramProjectedColumn A i a *
          rectRightGramEigenbasis A j a =
      A i j := by
  unfold rectRightGramProjectedColumn
  calc
    ∑ a : Fin n,
        (∑ k : Fin n, A i k * rectRightGramEigenbasis A k a) *
          rectRightGramEigenbasis A j a
        =
          ∑ k : Fin n,
            A i k *
              (∑ a : Fin n,
                rectRightGramEigenbasis A k a *
                  rectRightGramEigenbasis A j a) := by
            calc
              ∑ a : Fin n,
                  (∑ k : Fin n, A i k *
                    rectRightGramEigenbasis A k a) *
                    rectRightGramEigenbasis A j a
                  =
                    ∑ a : Fin n, ∑ k : Fin n,
                      (A i k * rectRightGramEigenbasis A k a) *
                        rectRightGramEigenbasis A j a := by
                    apply Finset.sum_congr rfl
                    intro a _
                    rw [Finset.sum_mul]
              _ =
                    ∑ k : Fin n, ∑ a : Fin n,
                      (A i k * rectRightGramEigenbasis A k a) *
                        rectRightGramEigenbasis A j a := by
                    rw [Finset.sum_comm]
              _ =
                    ∑ k : Fin n,
                      A i k *
                        (∑ a : Fin n,
                          rectRightGramEigenbasis A k a *
                            rectRightGramEigenbasis A j a) := by
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro a _
                    ring
    _ =
          ∑ k : Fin n, A i k * idMatrix n k j := by
            apply Finset.sum_congr rfl
            intro k _
            rw [rectRightGramEigenbasis_row_orthonormal A k j]
    _ = A i j := by
            simp [idMatrix]

/-- Basis-indexed SVD-style reconstruction from the zero-safe left candidates.
This removes the full-positive hypothesis but remains basis-indexed rather than
ordered. -/
theorem rectRightGram_basisSVD_representation {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    A i j =
      ∑ a : Fin n,
        rectRightGramLeftSingularZeroSafe A i a *
          rectRightGramBasisSingularValue A a *
          rectRightGramEigenbasis A j a := by
  rw [← rectRightGramProjectedColumn_reconstruct A i j]
  apply Finset.sum_congr rfl
  intro a _
  have hf := rectRightGramLeftSingularZeroSafe_factor_column A i a
  rw [← hf]
  ring

/-- Exact selected-index head from the zero-safe basis-indexed right-Gram
reconstruction.  This is an analysis object, not a computed SVD routine. -/
noncomputable def rectRightGramBasisSVDHead {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    s.sum fun a =>
      rectRightGramLeftSingularZeroSafe A i a *
        rectRightGramBasisSingularValue A a *
        rectRightGramEigenbasis A j a

/-- Exact complementary tail from the zero-safe basis-indexed right-Gram
reconstruction.  The complement is taken inside the finite right-index type. -/
noncomputable def rectRightGramBasisSVDTail {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    sᶜ.sum fun a =>
      rectRightGramLeftSingularZeroSafe A i a *
        rectRightGramBasisSingularValue A a *
        rectRightGramEigenbasis A j a

/-- The selected-index head plus the complementary tail reconstructs `A`
entrywise.  This is the basis-indexed source-split algebra needed before the
ordered head/tail handoff. -/
theorem rectRightGramBasisSVD_head_add_tail {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (i : Fin m) (j : Fin n) :
    rectRightGramBasisSVDHead A s i j +
        rectRightGramBasisSVDTail A s i j = A i j := by
  classical
  unfold rectRightGramBasisSVDHead rectRightGramBasisSVDTail
  let term : Fin n → ℝ :=
    fun a =>
      rectRightGramLeftSingularZeroSafe A i a *
        rectRightGramBasisSingularValue A a *
        rectRightGramEigenbasis A j a
  have hpartition :
      s.sum term + sᶜ.sum term =
        ∑ a : Fin n, term a := by
    rw [← Finset.sum_union disjoint_compl_right]
    rw [Finset.union_compl]
  rw [show
      s.sum (fun a =>
          rectRightGramLeftSingularZeroSafe A i a *
            rectRightGramBasisSingularValue A a *
            rectRightGramEigenbasis A j a) +
        sᶜ.sum (fun a =>
          rectRightGramLeftSingularZeroSafe A i a *
            rectRightGramBasisSingularValue A a *
            rectRightGramEigenbasis A j a) =
        s.sum term + sᶜ.sum term by rfl]
  rw [hpartition]
  exact (rectRightGram_basisSVD_representation A i j).symm

/-- Entrywise orientation of the selected-index head/tail split. -/
theorem rectRightGramBasisSVD_head_tail_entry {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (i : Fin m) (j : Fin n) :
    A i j =
      rectRightGramBasisSVDHead A s i j +
        rectRightGramBasisSVDTail A s i j := by
  exact (rectRightGramBasisSVD_head_add_tail A s i j).symm

/-- Rank factorization of the selected-index head through its selected
cardinality.  This is still exact-object algebra; it does not choose the
ordered top singular directions. -/
noncomputable def rectRightGramBasisSVDHeadRankFactorization {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    RectRankFactorization m n s.card (rectRightGramBasisSVDHead A s) where
  left := fun i a =>
    rectRightGramLeftSingularZeroSafe A i (s.orderEmbOfFin rfl a)
  right := fun a j =>
    rectRightGramBasisSingularValue A (s.orderEmbOfFin rfl a) *
      rectRightGramEigenbasis A j (s.orderEmbOfFin rfl a)
  factorization := by
    classical
    intro i j
    unfold rectRightGramBasisSVDHead
    let e : Fin s.card → Fin n := fun a => s.orderEmbOfFin rfl a
    let term : Fin n → ℝ :=
      fun a =>
        rectRightGramLeftSingularZeroSafe A i a *
          rectRightGramBasisSingularValue A a *
          rectRightGramEigenbasis A j a
    have hsum :
        s.sum term = ∑ a : Fin s.card, term (e a) := by
      have hsub :
          (∑ a : Fin s.card, term (e a)) = ∑ x : s, term x := by
        refine Fintype.sum_equiv (s.orderIsoOfFin rfl).toEquiv
          (fun a : Fin s.card => term (e a))
          (fun x : s => term x) ?_
        intro a
        simp [e]
      calc
        s.sum term = ∑ x : s, term x := by
              simpa using (Finset.sum_coe_sort s term).symm
        _ = ∑ a : Fin s.card, term (e a) := hsub.symm
    rw [hsum]
    apply Finset.sum_congr rfl
    intro a _
    simp [e, term]
    ring

/-- The selected-index right-Gram head has rank at most the selected
cardinality. -/
theorem rectRightGramBasisSVDHead_rankAtMost {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    RectRankAtMost m n s.card (rectRightGramBasisSVDHead A s) :=
  ⟨rectRightGramBasisSVDHeadRankFactorization A s⟩

/-- If the selected set has displayed cardinality `k`, the selected right-Gram
head has rank at most the paper-facing rank parameter `k`. -/
theorem rectRightGramBasisSVDHead_rankAtMost_of_card_eq {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (hcard : s.card = k) :
    RectRankAtMost m n k (rectRightGramBasisSVDHead A s) :=
  rectRankAtMost_of_eq_rank hcard
    (rectRightGramBasisSVDHead_rankAtMost A s)

/-- Selected basis-index set induced by an injective displayed index map
`Fin k ↪ Fin n`.  This is the exact-object selected-index vocabulary for the
paper-facing rank parameter before proving that a particular embedding
enumerates the ordered top singular directions. -/
def rectRightGramSelectedIndexSet {n k : ℕ} (e : Fin k ↪ Fin n) :
    Finset (Fin n) :=
  Finset.univ.map e

/-- The selected set induced by an embedding `Fin k ↪ Fin n` has cardinality
`k`. -/
theorem rectRightGramSelectedIndexSet_card {n k : ℕ}
    (e : Fin k ↪ Fin n) :
    (rectRightGramSelectedIndexSet e).card = k := by
  simp [rectRightGramSelectedIndexSet]

/-- The complement of an embedding-selected right-Gram index set has exactly
the remaining cardinality: selected plus complement directions account for all
ambient right coordinates.  This is the cardinality bridge needed before
reindexing constructed ordered head/tail source splits into a `k+q` rectangular
source-factor theorem. -/
theorem rectRightGramSelectedIndexSet_card_add_compl_card {n k : ℕ}
    (e : Fin k ↪ Fin n) :
    k + ((rectRightGramSelectedIndexSet e)ᶜ).card = n := by
  have h :=
    Finset.card_add_card_compl (rectRightGramSelectedIndexSet e)
  simpa [rectRightGramSelectedIndexSet_card e, Fintype.card_fin] using h

/-- Sums over an embedding-selected right-Gram index set are the corresponding
displayed sums over `Fin k`. -/
theorem rectRightGramSelectedIndexSet_sum {n k : ℕ}
    (e : Fin k ↪ Fin n) (term : Fin n → ℝ) :
    (rectRightGramSelectedIndexSet e).sum term =
      ∑ a : Fin k, term (e a) := by
  unfold rectRightGramSelectedIndexSet
  rw [Finset.sum_map]

/-- Sums over the complement of a right-Gram finite set are the corresponding
displayed sums over its canonical `orderEmbOfFin` enumeration. -/
theorem rectRightGramComplement_sum_orderEmbOfFin {n : ℕ}
    (s : Finset (Fin n)) (term : Fin n → ℝ) :
    (sᶜ).sum term =
      ∑ a : Fin ((sᶜ).card), term ((sᶜ).orderEmbOfFin rfl a) := by
  classical
  let e : Fin ((sᶜ).card) → Fin n := fun a => (sᶜ).orderEmbOfFin rfl a
  have hsub :
      (∑ a : Fin ((sᶜ).card), term (e a)) =
        ∑ x : {x // x ∈ (sᶜ)}, term x := by
    refine Fintype.sum_equiv ((sᶜ).orderIsoOfFin rfl).toEquiv
      (fun a : Fin ((sᶜ).card) => term (e a))
      (fun x : {x // x ∈ (sᶜ)} => term x) ?_
    intro a
    simp [e]
  calc
    (sᶜ).sum term = ∑ x : {x // x ∈ (sᶜ)}, term x := by
          simpa using (Finset.sum_coe_sort (sᶜ) term).symm
    _ = ∑ a : Fin ((sᶜ).card), term (e a) := hsub.symm

/-- Displayed top-`k` index cast into the ambient right-Gram index type.  The
semantic ordering certificate below uses this to compare the embedding-selected
basis directions with the ordered zero-indexed singular-value sequence. -/
def rectTopIndex {n k : ℕ} (hk : k ≤ n) (a : Fin k) : Fin n :=
  ⟨a.val, Nat.lt_of_lt_of_le a.isLt hk⟩

/-- The displayed top-index cast preserves the `Fin` order. -/
theorem rectTopIndex_le {n k : ℕ} {hk : k ≤ n}
    {a b : Fin k} (hab : a ≤ b) :
    rectTopIndex hk a ≤ rectTopIndex hk b := by
  rw [Fin.le_def] at hab ⊢
  exact hab

/-- Semantic certificate that an injective selected-index embedding enumerates
the ordered top right-Gram singular directions.  The certificate is intentionally
separate from the basis-indexed right-Gram eigenbasis construction: mathlib's
eigenbasis comes with an arbitrary finite basis order, while
`rectSingularValue` is the ordered zero-indexed right-Gram sequence. -/
structure RectRightGramOrderedTopEmbeddingCertificate {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (e : Fin k ↪ Fin n) : Prop where
  singularValue_eq :
    ∀ a : Fin k,
      rectRightGramBasisSingularValue A (e a) =
        rectSingularValue A (rectTopIndex hk a)

/-- Under the semantic ordered-top embedding certificate, the selected
basis-indexed singular-value squares agree with the ordered right-Gram
singular-value squares on the displayed first `k` indices. -/
theorem rectRightGramOrderedTopEmbeddingCertificate_selected_sq_eq {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (e : Fin k ↪ Fin n)
    (h : RectRightGramOrderedTopEmbeddingCertificate A hk e) (a : Fin k) :
    (rectRightGramBasisSingularValue A (e a)) ^ 2 =
      rectSingularValueSq A (rectTopIndex hk a) := by
  rw [h.singularValue_eq a]
  exact rectSingularValue_sq_eq A (rectTopIndex hk a)

/-- Under the semantic ordered-top embedding certificate, the selected
basis-indexed singular values inherit the ordered sequence's antitone order. -/
theorem rectRightGramOrderedTopEmbeddingCertificate_selected_antitone {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (e : Fin k ↪ Fin n)
    (h : RectRightGramOrderedTopEmbeddingCertificate A hk e) :
    Antitone fun a : Fin k => rectRightGramBasisSingularValue A (e a) := by
  intro a b hab
  change rectRightGramBasisSingularValue A (e b) ≤
    rectRightGramBasisSingularValue A (e a)
  rw [h.singularValue_eq b, h.singularValue_eq a]
  exact rectSingularValue_antitone A (rectTopIndex_le hab)

/-- The exact equivalence used by mathlib to reindex the ordered Hermitian
eigenvalue sequence into the matrix's basis-index type.  For the right-Gram
matrix this is also the bridge between ordered singular values and the
basis-indexed eigenvector table. -/
noncomputable def rectRightGramOrderedEigenbasisEquiv (n : ℕ) :
    Fin (Fintype.card (Fin n)) ≃ Fin n :=
  Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))

/-- Constructed embedding of the displayed top-`k` ordered singular directions
into the right-Gram basis-index type, using the same mathlib reindexing
equivalence as `Matrix.IsHermitian.eigenvalues` and `eigenvectorBasis`. -/
noncomputable def rectRightGramOrderedTopEmbedding {n k : ℕ}
    (hk : k ≤ n) : Fin k ↪ Fin n where
  toFun a := rectRightGramOrderedEigenbasisEquiv n
    (finCardIndex n (rectTopIndex hk a))
  inj' := by
    intro a b h
    have hidx :
        finCardIndex n (rectTopIndex hk a) =
          finCardIndex n (rectTopIndex hk b) :=
      (rectRightGramOrderedEigenbasisEquiv n).injective h
    apply Fin.ext
    simpa [finCardIndex, rectTopIndex] using congrArg Fin.val hidx

/-- The constructed ordered-top embedding satisfies the semantic certificate:
by construction it selects the right-Gram eigenbasis columns whose
basis-indexed eigenvalues are the first `k` ordered right-Gram eigenvalues. -/
theorem rectRightGramOrderedTopEmbedding_certificate {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    RectRightGramOrderedTopEmbeddingCertificate A hk
      (rectRightGramOrderedTopEmbedding hk) where
  singularValue_eq := by
    intro a
    unfold rectRightGramBasisSingularValue rectSingularValue
      rectRightGramEigenvalue rectSingularValueSq
      rectRightGramOrderedTopEmbedding rectRightGramOrderedEigenbasisEquiv
    simp [finCardIndex, Matrix.IsHermitian.eigenvalues]

/-- Ordered singular-value coordinate corresponding to a basis-indexed
right-Gram eigenvector.  This is the inverse of the same finite equivalence
used by mathlib's `eigenvalues` and `eigenvectorBasis` APIs, cast back to the
paper-facing `Fin n` index type. -/
noncomputable def rectRightGramBasisOrderedIndex (n : ℕ) (b : Fin n) : Fin n :=
  Fin.cast (by simp) ((rectRightGramOrderedEigenbasisEquiv n).symm b)

/-- Casting the ordered coordinate back to mathlib's cardinality index recovers
the inverse eigenbasis reindexing. -/
theorem finCardIndex_rectRightGramBasisOrderedIndex (n : ℕ) (b : Fin n) :
    finCardIndex n (rectRightGramBasisOrderedIndex n b) =
      (rectRightGramOrderedEigenbasisEquiv n).symm b := by
  apply Fin.ext
  simp [finCardIndex, rectRightGramBasisOrderedIndex]

/-- A basis-indexed right-Gram singular value is the ordered singular value at
the basis column's inverse mathlib reindexing coordinate. -/
theorem rectRightGramBasisSingularValue_eq_orderedIndex {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin n) :
    rectRightGramBasisSingularValue A b =
      rectSingularValue A (rectRightGramBasisOrderedIndex n b) := by
  unfold rectRightGramBasisSingularValue rectSingularValue
    rectRightGramEigenvalue rectSingularValueSq
    rectRightGramBasisOrderedIndex rectRightGramOrderedEigenbasisEquiv
  simp [finCardIndex, Matrix.IsHermitian.eigenvalues]

/-- If a basis index is not selected by the constructed top-`k` embedding, then
its ordered coordinate lies at or beyond the displayed top block. -/
theorem rectRightGramOrderedTopEmbedding_not_mem_index_ge {n k : ℕ}
    (hk : k ≤ n) {b : Fin n}
    (hb : b ∉ rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)) :
    k ≤ (rectRightGramBasisOrderedIndex n b).val := by
  classical
  by_contra hge
  have hlt : (rectRightGramBasisOrderedIndex n b).val < k :=
    Nat.lt_of_not_ge hge
  let a : Fin k := ⟨(rectRightGramBasisOrderedIndex n b).val, hlt⟩
  have heq : rectRightGramOrderedTopEmbedding hk a = b := by
    change rectRightGramOrderedEigenbasisEquiv n
        (finCardIndex n (rectTopIndex hk a)) = b
    rw [← (rectRightGramOrderedEigenbasisEquiv n).apply_symm_apply b]
    congr 1
  have hmem :
      b ∈ rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk) := by
    rw [← heq]
    simp [rectRightGramSelectedIndexSet]
  exact hb hmem

/-- Every displayed top index precedes the ordered coordinate of an unselected
basis direction. -/
theorem rectTopIndex_le_rectRightGramBasisOrderedIndex_of_not_mem_orderedTopEmbedding
    {n k : ℕ} (hk : k ≤ n) {b : Fin n}
    (hb : b ∉ rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))
    (a : Fin k) :
    rectTopIndex hk a ≤ rectRightGramBasisOrderedIndex n b := by
  rw [Fin.le_def]
  exact Nat.le_trans (Nat.le_of_lt a.isLt)
    (rectRightGramOrderedTopEmbedding_not_mem_index_ge hk hb)

/-- For the constructed ordered-top embedding, every selected singular value
dominates every unselected basis-indexed singular value.  This is the exact
spectral-index comparison needed before a future Eckart--Young/tail-optimality
step; it does not itself prove a best-rank theorem. -/
theorem rectRightGramOrderedTopEmbedding_complement_singularValue_le_selected
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) {b : Fin n}
    (hb : b ∉ rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))
    (a : Fin k) :
    rectRightGramBasisSingularValue A b ≤
      rectRightGramBasisSingularValue A (rectRightGramOrderedTopEmbedding hk a) := by
  rw [rectRightGramBasisSingularValue_eq_orderedIndex A b,
    (rectRightGramOrderedTopEmbedding_certificate A hk).singularValue_eq a]
  exact rectSingularValue_antitone A
    (rectTopIndex_le_rectRightGramBasisOrderedIndex_of_not_mem_orderedTopEmbedding
      hk hb a)

/-- Last displayed top index in a nonempty top-`k` block. -/
def rectTopLastIndex {k : ℕ} (hk0 : 0 < k) : Fin k :=
  ⟨k - 1, Nat.pred_lt (Nat.ne_of_gt hk0)⟩

/-- Every displayed top index is at most the last displayed top index. -/
theorem le_rectTopLastIndex {k : ℕ} (hk0 : 0 < k) (a : Fin k) :
    a ≤ rectTopLastIndex hk0 := by
  rw [Fin.le_def]
  exact Nat.le_pred_of_lt a.isLt

/-- The displayed top-index inclusion sends every selected index before the
last selected index. -/
theorem rectTopIndex_le_last {n k : ℕ} (hk : k ≤ n) (hk0 : 0 < k)
    (a : Fin k) :
    rectTopIndex hk a ≤ rectTopIndex hk (rectTopLastIndex hk0) :=
  rectTopIndex_le (le_rectTopLastIndex hk0 a)

/-- Positivity of the kth ordered singular value forces positivity of all
displayed top-`k` ordered singular values. -/
theorem rectSingularValue_top_pos_of_last_pos {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast : 0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0))) :
    ∀ a : Fin k, 0 < rectSingularValue A (rectTopIndex hk a) := by
  intro a
  have hle :
      rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)) ≤
        rectSingularValue A (rectTopIndex hk a) :=
    rectSingularValue_antitone A (rectTopIndex_le_last hk hk0 a)
  exact lt_of_lt_of_le hlast hle

/-- Positivity of the kth ordered singular value gives positive selected
basis-indexed singular values for the constructed ordered-top embedding. -/
theorem rectRightGramOrderedTopEmbedding_selected_pos_of_last_pos {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast : 0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0))) :
    ∀ a : Fin k,
      0 <
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a) := by
  intro a
  rw [(rectRightGramOrderedTopEmbedding_certificate A hk).singularValue_eq a]
  exact rectSingularValue_top_pos_of_last_pos A hk hk0 hlast a

/-- Positivity of the kth ordered singular value gives nonzero selected
basis-indexed singular values for the constructed ordered-top embedding. -/
theorem rectRightGramOrderedTopEmbedding_selected_nonzero_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast : 0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0))) :
    ∀ a : Fin k,
      rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a) ≠ 0 := by
  intro a
  exact ne_of_gt
    (rectRightGramOrderedTopEmbedding_selected_pos_of_last_pos
      A hk hk0 hlast a)

/-- Under a positive kth ordered singular value, the zero-safe left candidates
selected by the constructed ordered-top embedding have orthonormal columns.
This is an exact source-SVD left-basis ingredient; computed singular-vector
tables remain separate non-probability FP/certificate obligations. -/
theorem rectRightGramOrderedTopEmbedding_leftZeroSafe_col_orthonormal_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast : 0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (a b : Fin k) :
    ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i
            (rectRightGramOrderedTopEmbedding hk a) *
          rectRightGramLeftSingularZeroSafe A i
            (rectRightGramOrderedTopEmbedding hk b) =
      idMatrix k a b := by
  calc
    ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i
            (rectRightGramOrderedTopEmbedding hk a) *
          rectRightGramLeftSingularZeroSafe A i
            (rectRightGramOrderedTopEmbedding hk b)
        =
      idMatrix n (rectRightGramOrderedTopEmbedding hk a)
        (rectRightGramOrderedTopEmbedding hk b) := by
        exact
          rectRightGramLeftSingularZeroSafe_col_orthonormal_of_pos A
            (rectRightGramOrderedTopEmbedding_selected_pos_of_last_pos
              A hk hk0 hlast a)
            (rectRightGramOrderedTopEmbedding_selected_pos_of_last_pos
              A hk hk0 hlast b)
    _ = idMatrix k a b := by
        by_cases hab : a = b
        · subst b
          simp [idMatrix]
        · have hne :
              rectRightGramOrderedTopEmbedding hk a ≠
                rectRightGramOrderedTopEmbedding hk b := by
            intro h
            exact hab ((rectRightGramOrderedTopEmbedding hk).injective h)
          simp [idMatrix, hab, hne]

/-- Ordered top-`k` zero-safe left candidate table.  This is an exact analysis
object; a computed singular-vector table needs a separate non-probability
perturbation certificate. -/
noncomputable def rectRightGramOrderedHeadLeft {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) : Fin m → Fin k → ℝ :=
  fun i a => rectRightGramLeftSingularZeroSafe A i
    (rectRightGramOrderedTopEmbedding hk a)

/-- Ordered top-`k` right singular-vector table from the exact right-Gram
eigenbasis. -/
noncomputable def rectRightGramOrderedHeadRight {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) : Fin n → Fin k → ℝ :=
  fun j a => rectRightGramEigenbasis A j
    (rectRightGramOrderedTopEmbedding hk a)

/-- Ordered top-`k` diagonal singular-value table from the exact right-Gram
singular values selected by the constructed embedding. -/
noncomputable def rectRightGramOrderedHeadSingularDiagonal {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Fin k → Fin k → ℝ :=
  fun a b =>
    if a = b then
      rectRightGramBasisSingularValue A (rectRightGramOrderedTopEmbedding hk a)
    else
      0

/-- Complement-tail left candidate table obtained by enumerating the complement
of a selected right-Gram index set.  This is an exact analysis object; it is
not a computed tail-left basis, and zero singular values need a separate
nullspace completion before a full rectangular SVD certificate can use it as an
orthonormal tail basis. -/
noncomputable def rectRightGramBasisSVDTailLeft {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin m → Fin ((sᶜ).card) → ℝ :=
  fun i a =>
    rectRightGramLeftSingularZeroSafe A i ((sᶜ).orderEmbOfFin rfl a)

/-- Complement-tail right table obtained by enumerating the complement of a
selected right-Gram index set. -/
noncomputable def rectRightGramBasisSVDTailRight {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin n → Fin ((sᶜ).card) → ℝ :=
  fun j a => rectRightGramEigenbasis A j ((sᶜ).orderEmbOfFin rfl a)

/-- Complement-tail diagonal singular-value table obtained by enumerating the
complement of a selected right-Gram index set. -/
noncomputable def rectRightGramBasisSVDTailSingularDiagonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin ((sᶜ).card) → Fin ((sᶜ).card) → ℝ :=
  fun a b =>
    if a = b then
      rectRightGramBasisSingularValue A ((sᶜ).orderEmbOfFin rfl a)
    else
      0

/-- Ordered complement-tail left candidate table for the constructed top-`k`
selection. -/
noncomputable def rectRightGramOrderedTailLeft {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Fin m →
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
  rectRightGramBasisSVDTailLeft A
    (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))

/-- Ordered complement-tail right table for the constructed top-`k` selection. -/
noncomputable def rectRightGramOrderedTailRight {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Fin n →
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
  rectRightGramBasisSVDTailRight A
    (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))

/-- Ordered complement-tail diagonal singular-value table for the constructed
top-`k` selection. -/
noncomputable def rectRightGramOrderedTailSingularDiagonal {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) →
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
  rectRightGramBasisSVDTailSingularDiagonal A
    (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))

/-- If every complement-enumerated basis-indexed singular value is strictly
positive, the complement-tail zero-safe left candidate table has orthonormal
columns.  This closes the positive-complement branch only; if some complement
singular value vanishes, a separate nullspace-completed tail-left basis is
needed. -/
theorem rectRightGramBasisSVDTailLeft_col_orthonormal_of_pos
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (hpos :
      ∀ c : Fin ((sᶜ).card),
        0 < rectRightGramBasisSingularValue A
          ((sᶜ).orderEmbOfFin rfl c))
    (c d : Fin ((sᶜ).card)) :
    ∑ i : Fin m,
        rectRightGramBasisSVDTailLeft A s i c *
          rectRightGramBasisSVDTailLeft A s i d =
      idMatrix ((sᶜ).card) c d := by
  classical
  let ec : Fin n := (sᶜ).orderEmbOfFin rfl c
  let ed : Fin n := (sᶜ).orderEmbOfFin rfl d
  have horth :
      ∑ i : Fin m,
          rectRightGramLeftSingularZeroSafe A i ec *
            rectRightGramLeftSingularZeroSafe A i ed =
        idMatrix n ec ed :=
    rectRightGramLeftSingularZeroSafe_col_orthonormal_of_pos
      A (hpos c) (hpos d)
  calc
    ∑ i : Fin m,
        rectRightGramBasisSVDTailLeft A s i c *
          rectRightGramBasisSVDTailLeft A s i d
        =
          idMatrix n ec ed := by
          simpa [rectRightGramBasisSVDTailLeft, ec, ed] using horth
    _ = idMatrix ((sᶜ).card) c d := by
          by_cases hcd : c = d
          · subst d
            have heq : ec = ed := by
              simp [ec, ed]
            simp [idMatrix, heq]
          · have hne : ec ≠ ed := by
              intro h
              exact hcd (((sᶜ).orderEmbOfFin rfl).injective h)
            simp [idMatrix, hcd, hne]

/-- Ordered complement-tail left orthonormality under strict positivity of all
constructed complement singular values.  This is still an exact-object theorem:
computed singular vectors or tail-left basis routines need separate
non-probability FP certificates. -/
theorem rectRightGramOrderedTailLeft_col_orthonormal_of_complement_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (hpos :
      ∀ c :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        0 < rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c))
    (c d :
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)) :
    ∑ i : Fin m,
        rectRightGramOrderedTailLeft A hk i c *
          rectRightGramOrderedTailLeft A hk i d =
      idMatrix
        (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) c d := by
  simpa [rectRightGramOrderedTailLeft] using
    rectRightGramBasisSVDTailLeft_col_orthonormal_of_pos
      A (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))
      hpos c d

/-- If a complement-enumerated singular value is zero, the corresponding
zero-safe tail-left column is identically zero, so its self-dot is zero. -/
theorem rectRightGramBasisSVDTailLeft_self_dot_eq_zero_of_singularValue_eq_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    {c : Fin ((sᶜ).card)}
    (hzero :
      rectRightGramBasisSingularValue A
        ((sᶜ).orderEmbOfFin rfl c) = 0) :
    ∑ i : Fin m,
        rectRightGramBasisSVDTailLeft A s i c *
          rectRightGramBasisSVDTailLeft A s i c =
      0 := by
  unfold rectRightGramBasisSVDTailLeft
  calc
    ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i
            ((sᶜ).orderEmbOfFin rfl c) *
          rectRightGramLeftSingularZeroSafe A i
            ((sᶜ).orderEmbOfFin rfl c)
        =
          ∑ i : Fin m, 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [rectRightGramLeftSingularZeroSafe_eq_zero_of_singularValue_eq_zero
            A ((sᶜ).orderEmbOfFin rfl c) hzero i]
          ring
    _ = 0 := by simp

/-- The raw zero-safe complement-tail left table cannot itself be column
orthonormal if any complement singular value is zero.  This is the formal
obstruction that forces a nullspace-completed tail-left basis in the zero-tail
case. -/
theorem not_rectRightGramBasisSVDTailLeft_col_orthonormal_of_zero_singularValue
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    {c : Fin ((sᶜ).card)}
    (hzero :
      rectRightGramBasisSingularValue A
        ((sᶜ).orderEmbOfFin rfl c) = 0) :
    ¬ (∀ c d : Fin ((sᶜ).card),
      ∑ i : Fin m,
          rectRightGramBasisSVDTailLeft A s i c *
            rectRightGramBasisSVDTailLeft A s i d =
        idMatrix ((sᶜ).card) c d) := by
  intro horth
  have hself :=
    rectRightGramBasisSVDTailLeft_self_dot_eq_zero_of_singularValue_eq_zero
      A s hzero
  have hdiag := horth c c
  have hbad : (0 : ℝ) = 1 := by
    calc
      (0 : ℝ) =
          ∑ i : Fin m,
            rectRightGramBasisSVDTailLeft A s i c *
              rectRightGramBasisSVDTailLeft A s i c := hself.symm
      _ = idMatrix ((sᶜ).card) c c := hdiag
      _ = 1 := by simp [idMatrix]
  norm_num at hbad

/-- Ordered specialization of the zero-tail obstruction: the constructed
ordered zero-safe tail-left table cannot be orthonormal if any constructed
complement singular value is zero. -/
theorem not_rectRightGramOrderedTailLeft_col_orthonormal_of_zero_complement_singularValue
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    {c :
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)}
    (hzero :
      rectRightGramBasisSingularValue A
        (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) = 0) :
    ¬ (∀ c d :
        Fin (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
      ∑ i : Fin m,
          rectRightGramOrderedTailLeft A hk i c *
            rectRightGramOrderedTailLeft A hk i d =
        idMatrix
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card) c d) := by
  simpa [rectRightGramOrderedTailLeft] using
    not_rectRightGramBasisSVDTailLeft_col_orthonormal_of_zero_singularValue
      A (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))
      hzero

/-- Under a positive kth ordered singular value, the ordered head-left table
has orthonormal columns. -/
theorem rectRightGramOrderedHeadLeft_col_orthonormal_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast : 0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (a b : Fin k) :
    ∑ i : Fin m,
        rectRightGramOrderedHeadLeft A hk i a *
          rectRightGramOrderedHeadLeft A hk i b =
      idMatrix k a b := by
  simpa [rectRightGramOrderedHeadLeft] using
    rectRightGramOrderedTopEmbedding_leftZeroSafe_col_orthonormal_of_last_pos
      A hk hk0 hlast a b

/-- Under a positive kth ordered singular value, the constructed ordered
head-left block is left-orthogonal to the constructed complement-tail
zero-safe left block.  This closes the exact cross field
`U_ord^T U_tail = 0`; tail-left orthonormality still requires a separate
nullspace-completion argument. -/
theorem rectRightGramOrderedHeadTailLeft_cross_zero_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast : 0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (a : Fin k)
    (c :
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)) :
    ∑ i : Fin m,
        rectRightGramOrderedHeadLeft A hk i a *
          rectRightGramOrderedTailLeft A hk i c =
      0 := by
  classical
  let s := rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)
  let b : Fin n := (sᶜ).orderEmbOfFin rfl c
  have hhead_mem :
      rectRightGramOrderedTopEmbedding hk a ∈ s := by
    simp [s, rectRightGramSelectedIndexSet]
  have htail_mem : b ∈ sᶜ := by
    simp [b, Finset.orderEmbOfFin_mem]
  have htail_not_mem : b ∉ s := Finset.mem_compl.mp htail_mem
  have hne : rectRightGramOrderedTopEmbedding hk a ≠ b := by
    intro h
    exact htail_not_mem (by simpa [h] using hhead_mem)
  have hpos :=
    rectRightGramOrderedTopEmbedding_selected_pos_of_last_pos
      A hk hk0 hlast a
  simpa [rectRightGramOrderedHeadLeft, rectRightGramOrderedTailLeft,
    rectRightGramBasisSVDTailLeft, s, b] using
    rectRightGramLeftSingularZeroSafe_cross_zero_of_pos_ne
      A hpos hne

/-- The ordered head-right table has orthonormal columns by restriction of the
exact right-Gram eigenbasis to the constructed top-`k` embedding. -/
theorem rectRightGramOrderedHeadRight_col_orthonormal {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (a b : Fin k) :
    ∑ j : Fin n,
        rectRightGramOrderedHeadRight A hk j a *
          rectRightGramOrderedHeadRight A hk j b =
      idMatrix k a b := by
  calc
    ∑ j : Fin n,
        rectRightGramOrderedHeadRight A hk j a *
          rectRightGramOrderedHeadRight A hk j b
        =
      idMatrix n (rectRightGramOrderedTopEmbedding hk a)
        (rectRightGramOrderedTopEmbedding hk b) := by
        simpa [rectRightGramOrderedHeadRight] using
          rectRightGramEigenbasis_col_orthonormal A
            (rectRightGramOrderedTopEmbedding hk a)
            (rectRightGramOrderedTopEmbedding hk b)
    _ = idMatrix k a b := by
        by_cases hab : a = b
        · subst b
          simp [idMatrix]
        · have hne :
              rectRightGramOrderedTopEmbedding hk a ≠
                rectRightGramOrderedTopEmbedding hk b := by
            intro h
            exact hab ((rectRightGramOrderedTopEmbedding hk).injective h)
          simp [idMatrix, hab, hne]

/-- The complement-tail right table has orthonormal columns by restriction of
the exact right-Gram eigenbasis to the complement enumeration. -/
theorem rectRightGramBasisSVDTailRight_col_orthonormal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (a b : Fin ((sᶜ).card)) :
    ∑ j : Fin n,
        rectRightGramBasisSVDTailRight A s j a *
          rectRightGramBasisSVDTailRight A s j b =
      idMatrix ((sᶜ).card) a b := by
  calc
    ∑ j : Fin n,
        rectRightGramBasisSVDTailRight A s j a *
          rectRightGramBasisSVDTailRight A s j b
        =
      idMatrix n ((sᶜ).orderEmbOfFin rfl a)
        ((sᶜ).orderEmbOfFin rfl b) := by
        simpa [rectRightGramBasisSVDTailRight] using
          rectRightGramEigenbasis_col_orthonormal A
            ((sᶜ).orderEmbOfFin rfl a) ((sᶜ).orderEmbOfFin rfl b)
    _ = idMatrix ((sᶜ).card) a b := by
        by_cases hab : a = b
        · subst b
          simp [idMatrix]
        · have hne :
              (sᶜ).orderEmbOfFin rfl a ≠
                (sᶜ).orderEmbOfFin rfl b := by
            intro h
            exact hab (((sᶜ).orderEmbOfFin rfl).injective h)
          simp [idMatrix, hab, hne]

/-- The ordered complement-tail right table has orthonormal columns by
specializing the arbitrary-complement theorem to the constructed top-`k` set. -/
theorem rectRightGramOrderedTailRight_col_orthonormal {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (a b :
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)) :
    ∑ j : Fin n,
        rectRightGramOrderedTailRight A hk j a *
          rectRightGramOrderedTailRight A hk j b =
      idMatrix (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) a b := by
  simpa [rectRightGramOrderedTailRight] using
    rectRightGramBasisSVDTailRight_col_orthonormal A
      (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)) a b

/-- The selected right-Gram head induced by an injective selected-index map has
rank at most the displayed paper rank `k`. -/
theorem rectRightGramBasisSVDHead_rankAtMost_of_embedding {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (e : Fin k ↪ Fin n) :
    RectRankAtMost m n k
      (rectRightGramBasisSVDHead A (rectRightGramSelectedIndexSet e)) :=
  rectRightGramBasisSVDHead_rankAtMost_of_card_eq A
    (rectRightGramSelectedIndexSet e) (rectRightGramSelectedIndexSet_card e)

/-- The positive basis-indexed singular values convert the left-candidate
definition back into the projected column identity `tau_a u_a=A v_a`. -/
theorem rectRightGramLeftSingularFromEigenbasis_factor_column_of_pos
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hpos : ∀ a : Fin n, 0 < rectRightGramBasisSingularValue A a)
    (i : Fin m) (a : Fin n) :
    rectRightGramBasisSingularValue A a *
        rectRightGramLeftSingularFromEigenbasis A i a =
      rectRightGramProjectedColumn A i a := by
  have hne : rectRightGramBasisSingularValue A a ≠ 0 :=
    ne_of_gt (hpos a)
  unfold rectRightGramLeftSingularFromEigenbasis
  field_simp [hne]

/-- Full-positive basis-indexed SVD-style reconstruction from the right-Gram
eigenbasis.  This is exact-object algebra under a visible positivity
hypothesis; it is not yet the ordered rank-deficient rectangular SVD split. -/
theorem rectRightGram_fullPositive_basisSVD_representation {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hpos : ∀ a : Fin n, 0 < rectRightGramBasisSingularValue A a)
    (i : Fin m) (j : Fin n) :
    A i j =
      ∑ a : Fin n,
        rectRightGramLeftSingularFromEigenbasis A i a *
          rectRightGramBasisSingularValue A a *
          rectRightGramEigenbasis A j a := by
  rw [← rectRightGramProjectedColumn_reconstruct A i j]
  apply Finset.sum_congr rfl
  intro a _
  have hf :=
    rectRightGramLeftSingularFromEigenbasis_factor_column_of_pos A hpos i a
  rw [← hf]
  ring

/-- The Frobenius residual of a candidate low-rank approximation. -/
noncomputable def lowRankResidualFrob {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) : ℝ :=
  frobNormRect (fun i j => A i j - B i j)

/-- Exact column-permutation invariance of the Frobenius residual when the
same permutation is applied to the source matrix and the competitor. -/
theorem lowRankResidualFrob_permuteCols {m n : ℕ}
    (π : Fin n ≃ Fin n) (A B : Fin m → Fin n → ℝ) :
    lowRankResidualFrob (rectPermuteCols π A) (rectPermuteCols π B) =
      lowRankResidualFrob A B := by
  simpa [lowRankResidualFrob, rectPermuteCols] using
    (frobNormRect_permuteCols π (fun i j => A i j - B i j))

/-- Exact column-equivalence invariance of the Frobenius residual across
possibly different finite right-coordinate domains. -/
theorem lowRankResidualFrob_reindexCols {m n p : ℕ}
    (π : Fin p ≃ Fin n) (A B : Fin m → Fin n → ℝ) :
    lowRankResidualFrob (rectReindexCols π A) (rectReindexCols π B) =
      lowRankResidualFrob A B := by
  simpa [lowRankResidualFrob, rectReindexCols] using
    (frobNormRect_reindexCols π (fun i j => A i j - B i j))

/-- If `x` is in the right kernel of `B`, then the residual action `(A-B)x`
is exactly the source action `Ax`.  This is the algebraic bridge used by the
rank-nullity/Eckart--Young min-max route. -/
theorem rectMatMulVec_sub_eq_left_of_rightKernel {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hBx : ∀ i : Fin m, (∑ j : Fin n, B i j * x j) = 0) :
    rectMatMulVec (fun i j => A i j - B i j) x = rectMatMulVec A x := by
  ext i
  unfold rectMatMulVec
  calc
    (∑ j : Fin n, (A i j - B i j) * x j)
        = ∑ j : Fin n, (A i j * x j - B i j * x j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = (∑ j : Fin n, A i j * x j) -
          (∑ j : Fin n, B i j * x j) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ j : Fin n, A i j * x j := by
            rw [hBx i, sub_zero]

/-- Finite Bessel/Frobenius domination for an exact orthonormal family of
right probes.  Applying a rectangular matrix to `q` orthonormal right vectors
has total squared output energy at most the rectangular Frobenius square.

This is exact-object residual-energy infrastructure for the multi-tail
equation-(9) min--max route.  It charges no probability-construction error,
and any computed probe/SVD/projector routine remains a separate certificate
obligation. -/
theorem sum_vecNorm2Sq_rectMatMulVec_le_frobNormSqRect_of_orthonormal
    {m n q : ℕ}
    (M : Fin m → Fin n → ℝ)
    (x : Fin q → EuclideanSpace ℝ (Fin n))
    (hx : Orthonormal ℝ x) :
    (∑ c : Fin q,
        vecNorm2Sq (rectMatMulVec M
          (fun j : Fin n => (x c : EuclideanSpace ℝ (Fin n)) j))) ≤
      frobNormSqRect M := by
  have hrow : ∀ i : Fin m,
      (∑ c : Fin q,
          (∑ j : Fin n, M i j *
            (x c : EuclideanSpace ℝ (Fin n)) j) ^ 2) ≤
        ∑ j : Fin n, M i j ^ 2 := by
    intro i
    let row : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun j : Fin n => M i j)
    have hb :
        (∑ c : Fin q, ‖inner ℝ (x c) row‖ ^ 2) ≤ ‖row‖ ^ 2 := by
      simpa using
        (hx.sum_inner_products_le
          (x := row) (s := (Finset.univ : Finset (Fin q))))
    simpa [row, PiLp.inner_apply, EuclideanSpace.norm_sq_eq,
      Real.norm_eq_abs, sq_abs, mul_comm] using hb
  unfold vecNorm2Sq rectMatMulVec frobNormSqRect
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun i _ => hrow i)

/-- Right-kernel residual-energy domination.  If every exact orthonormal probe
lies in the right kernel of the competitor `B`, then the source actions
`A x_c` are exactly residual actions `(A-B)x_c`, and their total squared energy
is bounded by the residual Frobenius square.

This is exact-object min--max infrastructure only.  Sampling probabilities and
sampling laws remain exact mathematical inputs by convention. -/
theorem sum_vecNorm2Sq_rectMatMulVec_lowRankResidual_le_of_orthonormal_rightKernel
    {m n q : ℕ}
    (A B : Fin m → Fin n → ℝ)
    (x : Fin q → EuclideanSpace ℝ (Fin n))
    (hx : Orthonormal ℝ x)
    (hBx : ∀ c : Fin q, ∀ i : Fin m,
      (∑ j : Fin n, B i j *
        (x c : EuclideanSpace ℝ (Fin n)) j) = 0) :
    (∑ c : Fin q,
        vecNorm2Sq (rectMatMulVec A
          (fun j : Fin n => (x c : EuclideanSpace ℝ (Fin n)) j))) ≤
      frobNormSqRect (fun i j => A i j - B i j) := by
  have hbase :=
    sum_vecNorm2Sq_rectMatMulVec_le_frobNormSqRect_of_orthonormal
      (fun i j => A i j - B i j) x hx
  have heq :
      (∑ c : Fin q,
          vecNorm2Sq (rectMatMulVec A
            (fun j : Fin n => (x c : EuclideanSpace ℝ (Fin n)) j))) =
        ∑ c : Fin q,
          vecNorm2Sq
            (rectMatMulVec (fun i j => A i j - B i j)
              (fun j : Fin n => (x c : EuclideanSpace ℝ (Fin n)) j)) := by
    apply Finset.sum_congr rfl
    intro c _
    have hres :=
      rectMatMulVec_sub_eq_left_of_rightKernel A B
        (fun j : Fin n => (x c : EuclideanSpace ℝ (Fin n)) j)
        (hBx c)
    rw [hres]
  rw [heq]
  exact hbase

/-- The LR.1di orthonormal right-kernel family also gives a residual-energy
certificate: for every exact rank-`r` competitor on `r+q` right coordinates
there is an orthonormal `Fin q` family in the Euclidean-coordinate right-factor
kernel, it annihilates the competitor, and the source action on that family is
bounded by the competitor residual Frobenius square.

This is the residual side of the q-dimensional trace/Rayleigh lower-bound
route.  It does not prove the matching source-side tail-energy lower bound,
Ky Fan/Courant--Fischer comparison, Eckart--Young optimality, randomness, or
computed non-probability routine certificates. -/
theorem rectRankFactorization_exists_orthonormalRightKernelFamily_energy_le
    {m r q : ℕ}
    {A B : Fin m → Fin (r + q) → ℝ}
    (fac : RectRankFactorization m (r + q) r B) :
    ∃ x : Fin q →
        LinearMap.ker (rectRankRightFactorEuclideanMap fac.right),
      Orthonormal ℝ x ∧
        (∀ c : Fin q, ∀ i : Fin m,
          (∑ j : Fin (r + q), B i j *
            (x c : EuclideanSpace ℝ (Fin (r + q))) j) = 0) ∧
        (∑ c : Fin q,
          vecNorm2Sq (rectMatMulVec A
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j))) ≤
          frobNormSqRect (fun i j => A i j - B i j) := by
  rcases rectRankFactorization_exists_orthonormalRightKernelFamily fac with
    ⟨x, hx, hzero⟩
  refine ⟨x, hx, hzero, ?_⟩
  have hxAmbient :
      Orthonormal ℝ
        (fun c : Fin q => (x c : EuclideanSpace ℝ (Fin (r + q)))) := by
    rw [orthonormal_iff_ite] at hx ⊢
    intro c d
    have h := hx c d
    simpa [Submodule.coe_inner] using h
  exact
    sum_vecNorm2Sq_rectMatMulVec_lowRankResidual_le_of_orthonormal_rightKernel
      A B
      (fun c : Fin q => (x c : EuclideanSpace ℝ (Fin (r + q))))
      hxAmbient
      hzero

/-- Scalar head-tail mass-transfer inequality.

If the head weights `lambda` are all above a visible gap `eta`, the tail
weights `mu` are all below it, the nonnegative head coordinate mass balances
the missing tail coordinate mass, and each tail coordinate mass is at most one,
then the weighted head-plus-tail mass dominates the full tail sum.

This is the diagonal Ky Fan algebra used by LR.1dk.  It is exact-object
infrastructure only; ordered singular-value instantiation is a later
source-side obligation. -/
theorem headTail_weighted_tail_sum_le_of_gap {r q : ℕ}
    (lambda : Fin r → ℝ) (mu : Fin q → ℝ)
    (alpha : Fin r → ℝ) (beta : Fin q → ℝ) {eta : ℝ}
    (halpha_nonneg : ∀ a : Fin r, 0 ≤ alpha a)
    (hbeta_le_one : ∀ c : Fin q, beta c ≤ 1)
    (hbalance :
      (∑ a : Fin r, alpha a) =
        ∑ c : Fin q, (1 - beta c))
    (hhead : ∀ a : Fin r, eta ≤ lambda a)
    (htail : ∀ c : Fin q, mu c ≤ eta) :
    (∑ c : Fin q, mu c) ≤
      (∑ a : Fin r, lambda a * alpha a) +
        ∑ c : Fin q, mu c * beta c := by
  have hheadLower :
      eta * (∑ a : Fin r, alpha a) ≤
        ∑ a : Fin r, lambda a * alpha a := by
    calc
      eta * (∑ a : Fin r, alpha a)
          = ∑ a : Fin r, eta * alpha a := by
              rw [Finset.mul_sum]
      _ ≤ ∑ a : Fin r, lambda a * alpha a := by
            exact Finset.sum_le_sum
              (fun a _ => mul_le_mul_of_nonneg_right (hhead a)
                (halpha_nonneg a))
  have htailDefUpper :
      (∑ c : Fin q, mu c * (1 - beta c)) ≤
        eta * (∑ c : Fin q, (1 - beta c)) := by
    calc
      (∑ c : Fin q, mu c * (1 - beta c))
          ≤ ∑ c : Fin q, eta * (1 - beta c) := by
              exact Finset.sum_le_sum
                (fun c _ => mul_le_mul_of_nonneg_right (htail c)
                  (sub_nonneg.mpr (hbeta_le_one c)))
      _ = eta * (∑ c : Fin q, (1 - beta c)) := by
            rw [Finset.mul_sum]
  have hdef_le_head :
      (∑ c : Fin q, mu c * (1 - beta c)) ≤
        ∑ a : Fin r, lambda a * alpha a := by
    calc
      (∑ c : Fin q, mu c * (1 - beta c))
          ≤ eta * (∑ c : Fin q, (1 - beta c)) := htailDefUpper
      _ = eta * (∑ a : Fin r, alpha a) := by rw [← hbalance]
      _ ≤ ∑ a : Fin r, lambda a * alpha a := hheadLower
  have htail_decomp :
      (∑ c : Fin q, mu c) =
        (∑ c : Fin q, mu c * beta c) +
          ∑ c : Fin q, mu c * (1 - beta c) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  calc
    (∑ c : Fin q, mu c)
        = (∑ c : Fin q, mu c * beta c) +
            ∑ c : Fin q, mu c * (1 - beta c) := htail_decomp
    _ ≤ (∑ c : Fin q, mu c * beta c) +
          ∑ a : Fin r, lambda a * alpha a := by
          exact add_le_add (le_refl _) hdef_le_head
    _ = (∑ a : Fin r, lambda a * alpha a) +
          ∑ c : Fin q, mu c * beta c := by ring

/-- A coordinate of an exact Euclidean orthonormal frame carries total squared
mass at most one.  This is Bessel's inequality against a standard coordinate
vector. -/
theorem orthonormal_sum_coord_sq_le_one {n q : ℕ}
    (x : Fin q → EuclideanSpace ℝ (Fin n))
    (hx : Orthonormal ℝ x) (j : Fin n) :
    (∑ c : Fin q,
        ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2) ≤ 1 := by
  classical
  let e : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun k : Fin n => if k = j then (1 : ℝ) else 0)
  have hb :
      (∑ c : Fin q, ‖inner ℝ (x c) e‖ ^ 2) ≤ ‖e‖ ^ 2 := by
    simpa using
      (hx.sum_inner_products_le
        (x := e) (s := (Finset.univ : Finset (Fin q))))
  have hinner :
      ∀ c : Fin q, inner ℝ (x c) e =
        (x c : EuclideanSpace ℝ (Fin n)) j := by
    intro c
    rw [PiLp.inner_apply]
    simp [e, real_inner_eq_re_inner, RCLike.inner_apply, Finset.mem_univ]
  have hright : ‖e‖ ^ 2 = 1 := by
    simp [e, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
      Finset.mem_univ]
  calc
    (∑ c : Fin q,
        ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2)
        = ∑ c : Fin q, ‖inner ℝ (x c) e‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro c _
            rw [hinner c]
            simp [Real.norm_eq_abs, sq_abs]
    _ ≤ ‖e‖ ^ 2 := hb
    _ = 1 := hright

/-- The coordinate masses of a `q`-element exact Euclidean orthonormal frame
sum to `q`. -/
theorem orthonormal_sum_coord_sq_eq_card {n q : ℕ}
    (x : Fin q → EuclideanSpace ℝ (Fin n))
    (hx : Orthonormal ℝ x) :
    (∑ j : Fin n,
        ∑ c : Fin q, ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2) =
      (q : ℝ) := by
  classical
  rw [orthonormal_iff_ite] at hx
  have hnorm :
      ∀ c : Fin q,
        (∑ j : Fin n,
          ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2) = 1 := by
    intro c
    have hcc := hx c c
    have hnorm_sq : ‖x c‖ ^ 2 = 1 := by
      simpa [pow_two] using hcc
    have hcoord :
        (∑ j : Fin n,
          ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2) =
          ‖x c‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hcoord, hnorm_sq]
  calc
    (∑ j : Fin n,
        ∑ c : Fin q, ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2)
        = ∑ c : Fin q,
            ∑ j : Fin n,
              ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2 := by
            rw [Finset.sum_comm]
    _ = ∑ c : Fin q, (1 : ℝ) := by
          exact Finset.sum_congr rfl (fun c _ => hnorm c)
    _ = (q : ℝ) := by simp

/-- Expanding the total action of a diagonal matrix on a Euclidean frame gives
the singular-square weights times the coordinate masses. -/
theorem sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_weighted_coord_sq
    {n q : ℕ}
    (sigma : Fin n → ℝ)
    (x : Fin q → EuclideanSpace ℝ (Fin n)) :
    (∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin n => if i = j then sigma i else 0)
            (fun j : Fin n => (x c : EuclideanSpace ℝ (Fin n)) j))) =
      ∑ j : Fin n,
        sigma j ^ 2 *
          ∑ c : Fin q, ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2 := by
  classical
  have hdiag :
      ∀ c : Fin q, ∀ i : Fin n,
        (∑ j : Fin n,
          (if i = j then sigma i else 0) *
            ((x c : EuclideanSpace ℝ (Fin n)) j)) =
          sigma i * ((x c : EuclideanSpace ℝ (Fin n)) i) := by
    intro c i
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  unfold vecNorm2Sq rectMatMulVec
  calc
    (∑ c : Fin q,
        ∑ i : Fin n,
          (∑ j : Fin n,
            (if i = j then sigma i else 0) *
              ((x c : EuclideanSpace ℝ (Fin n)) j)) ^ 2)
        =
          ∑ c : Fin q,
            ∑ i : Fin n,
              (sigma i *
                ((x c : EuclideanSpace ℝ (Fin n)) i)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro c _
            apply Finset.sum_congr rfl
            intro i _
            rw [hdiag c i]
    _ =
          ∑ i : Fin n,
            ∑ c : Fin q,
              sigma i ^ 2 *
                ((x c : EuclideanSpace ℝ (Fin n)) i) ^ 2 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro c _
            ring
    _ =
          ∑ i : Fin n,
            sigma i ^ 2 *
              ∑ c : Fin q,
                ((x c : EuclideanSpace ℝ (Fin n)) i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]

/-- Diagonal source-side tail-energy lower bound under a visible head-tail gap.

For an exact orthonormal `q`-frame in an `r+q` right domain, if every displayed
head diagonal square is at least `eta` and every displayed tail diagonal square
is at most `eta`, then the total squared action of the diagonal source matrix
on the frame is at least the displayed tail-energy sum.

This is exact-object diagonal Ky Fan infrastructure.  It does not instantiate
the gap from ordered singular values, transport through a nontrivial right
singular-vector table, or certify any computed singular-vector/diagonal
routine.  Sampling probabilities and laws remain exact mathematical inputs by
project convention. -/
theorem sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_gap
    {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) {eta : ℝ}
    (x : Fin q → EuclideanSpace ℝ (Fin (r + q)))
    (hx : Orthonormal ℝ x)
    (hhead : ∀ a : Fin r, eta ≤ sigma (Fin.castAdd q a) ^ 2)
    (htail : ∀ c : Fin q, sigma (Fin.natAdd r c) ^ 2 ≤ eta) :
    (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin (r + q) => if i = j then sigma i else 0)
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
  classical
  let alpha : Fin r → ℝ :=
    fun a => ∑ c : Fin q,
      ((x c : EuclideanSpace ℝ (Fin (r + q))) (Fin.castAdd q a)) ^ 2
  let beta : Fin q → ℝ :=
    fun c => ∑ d : Fin q,
      ((x d : EuclideanSpace ℝ (Fin (r + q))) (Fin.natAdd r c)) ^ 2
  have halpha_nonneg : ∀ a : Fin r, 0 ≤ alpha a := by
    intro a
    exact Finset.sum_nonneg (fun c _ => sq_nonneg _)
  have hbeta_le_one : ∀ c : Fin q, beta c ≤ 1 := by
    intro c
    simpa [beta] using
      orthonormal_sum_coord_sq_le_one x hx (Fin.natAdd r c)
  have hmass :=
    orthonormal_sum_coord_sq_eq_card x hx
  have hsplit :
      (∑ a : Fin r, alpha a) + (∑ c : Fin q, beta c) = (q : ℝ) := by
    have h := hmass
    rw [Fin.sum_univ_add] at h
    simpa [alpha, beta] using h
  have hbalance :
      (∑ a : Fin r, alpha a) =
        ∑ c : Fin q, (1 - beta c) := by
    calc
      (∑ a : Fin r, alpha a)
          = (q : ℝ) - ∑ c : Fin q, beta c := by linarith
      _ = ∑ c : Fin q, (1 - beta c) := by
            simp [Finset.sum_sub_distrib]
  have hweighted :=
    headTail_weighted_tail_sum_le_of_gap
      (fun a : Fin r => sigma (Fin.castAdd q a) ^ 2)
      (fun c : Fin q => sigma (Fin.natAdd r c) ^ 2)
      alpha beta halpha_nonneg hbeta_le_one hbalance hhead htail
  have henergy :
      (∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin (r + q) => if i = j then sigma i else 0)
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j))) =
        (∑ a : Fin r,
          sigma (Fin.castAdd q a) ^ 2 * alpha a) +
          ∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2 * beta c := by
    rw [sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_weighted_coord_sq]
    rw [Fin.sum_univ_add]
  rw [henergy]
  exact hweighted

/-- Ordered diagonal head-tail gap certificate, positive-head case.

If the displayed diagonal/singular-value squares are antitone in the coordinate
index and the head block is nonempty, then the last head square is a valid gap
parameter for LR.1dk: every head square lies above it and every tail square
lies below it. -/
theorem diagonal_headTail_square_gap_of_antitone_head_pos {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) (hr : 0 < r)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    ∃ eta : ℝ,
      (∀ a : Fin r, eta ≤ sigma (Fin.castAdd q a) ^ 2) ∧
        ∀ c : Fin q, sigma (Fin.natAdd r c) ^ 2 ≤ eta := by
  classical
  let lastHead : Fin r := rectTopLastIndex hr
  refine ⟨sigma (Fin.castAdd q lastHead) ^ 2, ?_, ?_⟩
  · intro a
    exact
      hmono (Fin.castAdd q a) (Fin.castAdd q lastHead)
        (by
          simpa [lastHead] using le_rectTopLastIndex hr a)
  · intro c
    exact
      hmono (Fin.castAdd q lastHead) (Fin.natAdd r c)
        (by
          have hlast_le_r : (lastHead : ℕ) ≤ r :=
            Nat.le_of_lt lastHead.isLt
          calc
            ((Fin.castAdd q lastHead : Fin (r + q)) : ℕ)
                = (lastHead : ℕ) := rfl
            _ ≤ r := hlast_le_r
            _ ≤ r + (c : ℕ) := Nat.le_add_right r (c : ℕ)
            _ = ((Fin.natAdd r c : Fin (r + q)) : ℕ) := rfl)

/-- Ordered diagonal source-side tail-energy lower bound, positive-head case.

This composes LR.1dk with the finite ordered-gap certificate above.  It removes
the abstract gap parameter when the displayed head count is positive and the
exact diagonal/singular-value-square table is antitone in coordinate order.
It remains exact-object diagonal infrastructure: the zero-head edge case,
right-basis transport, SVD/source-split construction, randomness, and computed
non-probability routine certificates are separate obligations. -/
theorem sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_antitone_head_pos
    {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) (hr : 0 < r)
    (x : Fin q → EuclideanSpace ℝ (Fin (r + q)))
    (hx : Orthonormal ℝ x)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin (r + q) => if i = j then sigma i else 0)
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
  rcases diagonal_headTail_square_gap_of_antitone_head_pos
      sigma hr hmono with
    ⟨eta, hhead, htail⟩
  exact
    sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_gap
      sigma x hx hhead htail

/-- A Euclidean orthonormal frame whose cardinality equals the ambient
coordinate dimension has coordinate-square mass one in each coordinate.

This is the zero-head companion to the LR.1dk coordinate-mass facts: when the
number of vectors equals the ambient coordinate dimension, the Bessel upper
bound is saturated coordinate by coordinate. -/
theorem orthonormal_sum_coord_sq_eq_one_of_card_eq {n q : ℕ}
    (hnq : n = q)
    (x : Fin q → EuclideanSpace ℝ (Fin n))
    (hx : Orthonormal ℝ x) (j : Fin n) :
    (∑ c : Fin q,
        ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2) = 1 := by
  classical
  subst n
  let alpha : Fin q → ℝ :=
    fun j => ∑ c : Fin q,
      ((x c : EuclideanSpace ℝ (Fin q)) j) ^ 2
  have hle : ∀ j : Fin q, alpha j ≤ 1 := by
    intro j
    simpa [alpha] using orthonormal_sum_coord_sq_le_one x hx j
  have hdef_nonneg : ∀ j : Fin q, 0 ≤ 1 - alpha j := by
    intro j
    linarith [hle j]
  have hsum_alpha : (∑ j : Fin q, alpha j) = (q : ℝ) := by
    simpa [alpha] using orthonormal_sum_coord_sq_eq_card x hx
  have hsum_def : (∑ j : Fin q, (1 - alpha j)) = 0 := by
    calc
      (∑ j : Fin q, (1 - alpha j))
          = (∑ _j : Fin q, (1 : ℝ)) - ∑ j : Fin q, alpha j := by
            rw [Finset.sum_sub_distrib]
      _ = (q : ℝ) - (q : ℝ) := by
            simp [hsum_alpha]
      _ = 0 := by ring
  have hdef_zero : 1 - alpha j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hdef_nonneg j)).mp hsum_def j (Finset.mem_univ j)
  have halpha : alpha j = 1 := by linarith
  simpa [alpha] using halpha

/-- A full Euclidean orthonormal `q`-frame has coordinate-square mass one in
each coordinate. -/
theorem orthonormal_sum_coord_sq_eq_one_of_full {q : ℕ}
    (x : Fin q → EuclideanSpace ℝ (Fin q))
    (hx : Orthonormal ℝ x) (j : Fin q) :
    (∑ c : Fin q,
        ((x c : EuclideanSpace ℝ (Fin q)) j) ^ 2) = 1 := by
  simpa using
    orthonormal_sum_coord_sq_eq_one_of_card_eq
      (n := q) (q := q) rfl x hx j

/-- Full-frame diagonal energy identity.

When an exact orthonormal `q`-frame fills the whole `q`-dimensional coordinate
space, the total squared action of a diagonal source matrix on the frame is
exactly the sum of its displayed diagonal squares. -/
theorem sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_sum_sq_of_orthonormal_full
    {q : ℕ}
    (sigma : Fin q → ℝ)
    (x : Fin q → EuclideanSpace ℝ (Fin q))
    (hx : Orthonormal ℝ x) :
    (∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin q => if i = j then sigma i else 0)
            (fun j : Fin q => (x c : EuclideanSpace ℝ (Fin q)) j))) =
      ∑ j : Fin q, sigma j ^ 2 := by
  classical
  rw [sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_weighted_coord_sq]
  apply Finset.sum_congr rfl
  intro j _
  rw [orthonormal_sum_coord_sq_eq_one_of_full x hx j]
  ring

/-- Zero-head diagonal source-side tail-energy lower bound.

With no displayed head coordinates, an exact orthonormal `q`-frame fills the
whole right coordinate space, so the LR.1dk diagonal source action equals the
tail diagonal-square sum.  This closes the `r = 0` companion to LR.1dl; the
right-basis transport and full Ky Fan/Eckart--Young foundations remain separate
obligations. -/
theorem sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_zero_head
    {q : ℕ}
    (sigma : Fin q → ℝ)
    (x : Fin q → EuclideanSpace ℝ (Fin q))
    (hx : Orthonormal ℝ x) :
    (∑ c : Fin q, sigma c ^ 2) ≤
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin q => if i = j then sigma i else 0)
            (fun j : Fin q =>
              (x c : EuclideanSpace ℝ (Fin q)) j)) := by
  have h :=
    sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_sum_sq_of_orthonormal_full
      sigma x hx
  simpa using (le_of_eq h.symm)

/-- Combined ordered diagonal source-side tail-energy lower bound.

The positive-head branch uses the ordered last-head gap certificate LR.1dl; the
zero-head branch uses the full-frame equality LR.1dm.  Thus the ordered
diagonal lower bound no longer exposes a separate `0 < r` side condition.  This
is still exact-object diagonal infrastructure: right-basis transport, the full
Rayleigh/Ky Fan theorem, Eckart--Young, randomness, and computed
non-probability routine certificates remain separate obligations. -/
theorem sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_antitone
    {r q : ℕ}
    (sigma : Fin (r + q) → ℝ)
    (x : Fin q → EuclideanSpace ℝ (Fin (r + q)))
    (hx : Orthonormal ℝ x)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin (r + q) => if i = j then sigma i else 0)
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hcoord :
        ∀ j : Fin (0 + q),
          (∑ c : Fin q,
            ((x c : EuclideanSpace ℝ (Fin (0 + q))) j) ^ 2) = 1 := by
        intro j
        exact
          orthonormal_sum_coord_sq_eq_one_of_card_eq
            (n := 0 + q) (q := q) (by simp) x hx j
    rw [sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_weighted_coord_sq]
    rw [Fin.sum_univ_add]
    simp [hcoord]
  · exact
      sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_antitone_head_pos
        sigma hr x hx hmono

/-- Kernel-to-residual min-max adapter for the Eckart--Young route.

If the exact source block has a vector-action lower bound
`sigma * ||x||₂ <= ||A x||₂` on every nonzero vector in an `r+1` dimensional
right domain, then every repository rank-at-most-`r` competitor has Frobenius
residual at least `sigma`.  This theorem uses the LR.1cy rank-nullity kernel
vector and the local Frobenius matrix-vector domination theorem; proving the
source lower-action hypothesis from ordered singular values is a later D4
step. -/
theorem rectRankAtMost_lowRankResidualFrob_ge_of_vector_lower_bound_succ
    {m r : ℕ}
    (A B : Fin m → Fin (r + 1) → ℝ) {sigma : ℝ}
    (hB : RectRankAtMost m (r + 1) r B)
    (hA :
      ∀ x : Fin (r + 1) → ℝ, x ≠ 0 →
        sigma * vecNorm2 x ≤ vecNorm2 (rectMatMulVec A x)) :
    sigma ≤ lowRankResidualFrob A B := by
  rcases rectRankAtMost_exists_rightKernelVector_succ hB with
    ⟨x, hxne, hBx⟩
  have hxnorm_ne : vecNorm2 x ≠ 0 := by
    intro hzero
    apply hxne
    ext j
    exact (vecNorm2_eq_zero_iff x).mp hzero j
  have hxnorm_pos : 0 < vecNorm2 x :=
    lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxnorm_ne)
  have hres_vec :
      rectMatMulVec (fun i j => A i j - B i j) x = rectMatMulVec A x :=
    rectMatMulVec_sub_eq_left_of_rightKernel A B x hBx
  have hlower :
      sigma * vecNorm2 x ≤ vecNorm2 (rectMatMulVec A x) :=
    hA x hxne
  have hupper0 :
      vecNorm2 (rectMatMulVec (fun i j => A i j - B i j) x) ≤
        frobNormRect (fun i j => A i j - B i j) * vecNorm2 x :=
    vecNorm2_rectMatMulVec_le_frobNormRect_mul
      (fun i j => A i j - B i j) x
  have hupper :
      vecNorm2 (rectMatMulVec A x) ≤
        lowRankResidualFrob A B * vecNorm2 x := by
    simpa [lowRankResidualFrob, hres_vec] using hupper0
  have hmul :
      sigma * vecNorm2 x ≤ lowRankResidualFrob A B * vecNorm2 x :=
    le_trans hlower hupper
  have hdiv :
      sigma ≤ (lowRankResidualFrob A B * vecNorm2 x) / vecNorm2 x :=
    (le_div_iff₀ hxnorm_pos).mpr hmul
  have hcancel :
      (lowRankResidualFrob A B * vecNorm2 x) / vecNorm2 x =
        lowRankResidualFrob A B := by
    field_simp [hxnorm_ne]
  simpa [hcancel] using hdiv

/-- A minimal rectangular norm-like interface for equation (9) theorem
surfaces.  This is deliberately weaker than a full unitarily invariant norm
API: it exposes only nonnegativity and the triangle step needed to turn an
exact head/tail residual certificate into a residual bound.  Concrete
unitarily invariant norm instances remain a separate foundation obligation. -/
structure RectNormLike (m n : ℕ) where
  norm : (Fin m → Fin n → ℝ) → ℝ
  norm_nonneg : ∀ A, 0 ≤ norm A
  sub_le_add : ∀ A B,
    norm (fun i j => A i j - B i j) ≤ norm A + norm B

/-- A rectangular norm-like functional with exact left and right orthogonal
invariance.  This is still certificate-shaped: it exposes the unitarily
invariant API needed by equation (9), while singular-value comparison and
Eckart--Young instantiation remain separate foundations. -/
structure UnitaryInvariantRectNormLike (m n : ℕ) extends RectNormLike m n where
  orthogonal_left : ∀ U A, IsOrthogonal m U →
    norm (matMulRectLeft U A) = norm A
  orthogonal_right : ∀ A V, IsOrthogonal n V →
    norm (matMulRectRight A V) = norm A

namespace UnitaryInvariantRectNormLike

/-- Left orthogonal invariance as a namespace theorem. -/
theorem norm_matMulRectLeft {m n : ℕ}
    (ξ : UnitaryInvariantRectNormLike m n)
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (hU : IsOrthogonal m U) :
    ξ.norm (matMulRectLeft U A) = ξ.norm A :=
  ξ.orthogonal_left U A hU

/-- Right orthogonal invariance as a namespace theorem. -/
theorem norm_matMulRectRight {m n : ℕ}
    (ξ : UnitaryInvariantRectNormLike m n)
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin n → ℝ)
    (hV : IsOrthogonal n V) :
    ξ.norm (matMulRectRight A V) = ξ.norm A :=
  ξ.orthogonal_right A V hV

end UnitaryInvariantRectNormLike

/-- Residual measured by a supplied rectangular norm-like functional. -/
noncomputable def lowRankResidualNorm {m n : ℕ}
    (ξ : RectNormLike m n)
    (A B : Fin m → Fin n → ℝ) : ℝ :=
  ξ.norm (fun i j => A i j - B i j)

/-- The rectangular Frobenius norm as a concrete `RectNormLike` instance.
This closes only the Frobenius instance of the norm-generic equation (9)
surface; it is not a general unitarily invariant norm API. -/
noncomputable def frobRectNormLike (m n : ℕ) : RectNormLike m n where
  norm := frobNormRect
  norm_nonneg := by
    intro A
    exact frobNormRect_nonneg A
  sub_le_add := by
    intro A B
    exact frobNormRect_sub_le A B

/-- The norm field of `frobRectNormLike` is exactly `frobNormRect`. -/
theorem frobRectNormLike_norm {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    (frobRectNormLike m n).norm A = frobNormRect A :=
  rfl

/-- The rectangular Frobenius norm as a concrete unitarily invariant
`RectNormLike` certificate. -/
noncomputable def frobUnitaryInvariantRectNormLike (m n : ℕ) :
    UnitaryInvariantRectNormLike m n where
  toRectNormLike := frobRectNormLike m n
  orthogonal_left := by
    intro U A hU
    exact frobNormRect_orthogonal_left U A hU
  orthogonal_right := by
    intro A V hV
    exact frobNormRect_orthogonal_right A V hV

/-- Forgetting the Frobenius unitarily invariant certificate recovers the
existing Frobenius `RectNormLike` instance. -/
theorem frobUnitaryInvariantRectNormLike_toRectNormLike {m n : ℕ} :
    (frobUnitaryInvariantRectNormLike m n).toRectNormLike =
      frobRectNormLike m n :=
  rfl

/-- The norm field of the Frobenius unitarily invariant certificate is exactly
the repository rectangular Frobenius norm. -/
theorem frobUnitaryInvariantRectNormLike_norm {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    (frobUnitaryInvariantRectNormLike m n).norm A = frobNormRect A :=
  rfl

/-- The norm-generic residual specializes definitionally to the Frobenius
residual under `frobRectNormLike`. -/
theorem lowRankResidualNorm_frobRectNormLike {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) :
    lowRankResidualNorm (frobRectNormLike m n) A B =
      lowRankResidualFrob A B :=
  rfl

/-- `frobRectNormLike` inherits left orthogonal invariance from the repository
rectangular Frobenius norm. -/
theorem frobRectNormLike_orthogonal_left {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (hU : IsOrthogonal m U) :
    (frobRectNormLike m n).norm (matMulRectLeft U A) =
      (frobRectNormLike m n).norm A := by
  exact frobNormRect_orthogonal_left U A hU

/-- `frobRectNormLike` inherits right orthogonal invariance from the repository
rectangular Frobenius norm. -/
theorem frobRectNormLike_orthogonal_right {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin n → ℝ)
    (hV : IsOrthogonal n V) :
    (frobRectNormLike m n).norm (matMulRectRight A V) =
      (frobRectNormLike m n).norm A := by
  exact frobNormRect_orthogonal_right A V hV

/-- A Frobenius-best rank-`k` approximation certificate.  This is intentionally
certificate-shaped: later SVD infrastructure can instantiate it, while
Algorithm 3 implementation-facing results separately account for computed bases
and projectors. -/
structure IsBestRankApproxFrob (m n k : ℕ)
    (A Ak : Fin m → Fin n → ℝ) : Prop where
  rank_le : RectRankAtMost m n k Ak
  optimal : ∀ B, RectRankAtMost m n k B →
    lowRankResidualFrob A Ak ≤ lowRankResidualFrob A B

/-- Best rank-`k` approximation certificate measured by a supplied norm-like
functional.  This is the norm-generic analogue of `IsBestRankApproxFrob`;
instantiating it from singular values/Eckart--Young for unitarily invariant
norms is still tracked separately. -/
structure IsBestRankApproxNorm (m n k : ℕ)
    (ξ : RectNormLike m n)
    (A Ak : Fin m → Fin n → ℝ) : Prop where
  rank_le : RectRankAtMost m n k Ak
  optimal : ∀ B, RectRankAtMost m n k B →
    lowRankResidualNorm ξ A Ak ≤ lowRankResidualNorm ξ A B

/-- Exact right-subspace projection approximation `A (V Vᵀ)`. -/
noncomputable def rightBasisProjectorApprox {m n q : ℕ}
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin q → ℝ) :
    Fin m → Fin n → ℝ :=
  preconditionColumns A (basisColumnProjector V)

/-- Exact left-subspace projection approximation `(U Uᵀ) A`. -/
noncomputable def leftBasisProjectorApprox {m n q : ℕ}
    (U : Fin m → Fin q → ℝ) (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  preconditionRows (basisColumnProjector U) A

/-- The exact right projected approximation factors through the displayed
right-basis dimension. -/
noncomputable def rightBasisProjectorApproxFactorization {m n q : ℕ}
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin q → ℝ) :
    RectRankFactorization m n q (rightBasisProjectorApprox A V) where
  left := fun i a => ∑ j : Fin n, A i j * V j a
  right := fun a j => V j a
  factorization := by
    intro i j
    unfold rightBasisProjectorApprox preconditionColumns basisColumnProjector
    calc
      (∑ k : Fin n, A i k * ∑ a : Fin q, V k a * V j a)
          = ∑ k : Fin n, ∑ a : Fin q, A i k * (V k a * V j a) := by
              simp_rw [Finset.mul_sum]
      _ = ∑ a : Fin q, ∑ k : Fin n, A i k * (V k a * V j a) := by
              rw [Finset.sum_comm]
      _ = ∑ a : Fin q, (∑ k : Fin n, A i k * V k a) * V j a := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro k _
              ring

/-- The exact right projected approximation has rank at most the number of
displayed basis columns. -/
theorem rightBasisProjectorApprox_rankAtMost {m n q : ℕ}
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin q → ℝ) :
    RectRankAtMost m n q (rightBasisProjectorApprox A V) :=
  ⟨rightBasisProjectorApproxFactorization A V⟩

/-- The exact left projected approximation factors through the displayed
left-basis dimension. -/
noncomputable def leftBasisProjectorApproxFactorization {m n q : ℕ}
    (U : Fin m → Fin q → ℝ) (A : Fin m → Fin n → ℝ) :
    RectRankFactorization m n q (leftBasisProjectorApprox U A) where
  left := U
  right := fun a j => ∑ i : Fin m, U i a * A i j
  factorization := by
    intro i j
    unfold leftBasisProjectorApprox preconditionRows basisColumnProjector
    calc
      (∑ k : Fin m, (∑ a : Fin q, U i a * U k a) * A k j)
          = ∑ k : Fin m, ∑ a : Fin q, (U i a * U k a) * A k j := by
              simp_rw [Finset.sum_mul]
      _ = ∑ a : Fin q, ∑ k : Fin m, (U i a * U k a) * A k j := by
              rw [Finset.sum_comm]
      _ = ∑ a : Fin q, U i a * (∑ k : Fin m, U k a * A k j) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring

/-- The exact left projected approximation has rank at most the number of
displayed basis columns. -/
theorem leftBasisProjectorApprox_rankAtMost {m n q : ℕ}
    (U : Fin m → Fin q → ℝ) (A : Fin m → Fin n → ℝ) :
    RectRankAtMost m n q (leftBasisProjectorApprox U A) :=
  ⟨leftBasisProjectorApproxFactorization U A⟩

/-- The optimality field of a best rank-`k` Frobenius approximation, exposed as
a reusable theorem for downstream low-rank structural arguments. -/
theorem IsBestRankApproxFrob.residual_le_of_rankAtMost {m n k : ℕ}
    {A Ak B : Fin m → Fin n → ℝ}
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hB : RectRankAtMost m n k B) :
    lowRankResidualFrob A Ak ≤ lowRankResidualFrob A B :=
  hbest.optimal B hB

/-- The optimality field of a norm-generic best rank-`k` certificate. -/
theorem IsBestRankApproxNorm.residual_le_of_rankAtMost {m n k : ℕ}
    {ξ : RectNormLike m n}
    {A Ak B : Fin m → Fin n → ℝ}
    (hbest : IsBestRankApproxNorm m n k ξ A Ak)
    (hB : RectRankAtMost m n k B) :
    lowRankResidualNorm ξ A Ak ≤ lowRankResidualNorm ξ A B :=
  hbest.optimal B hB

/-- A Frobenius-best rank certificate is the corresponding norm-generic
certificate for `frobRectNormLike`. -/
theorem IsBestRankApproxFrob.to_norm_frobRectNormLike {m n k : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (hbest : IsBestRankApproxFrob m n k A Ak) :
    IsBestRankApproxNorm m n k (frobRectNormLike m n) A Ak where
  rank_le := hbest.rank_le
  optimal := by
    intro B hB
    simpa [lowRankResidualNorm_frobRectNormLike]
      using hbest.optimal B hB

/-- An exact right basis-product approximation with exactly `k` displayed
basis vectors is a valid comparison candidate for a best rank-`k` Frobenius
approximation. -/
theorem IsBestRankApproxFrob.residual_le_rightBasisProjectorApprox {m n k : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (V : Fin n → Fin k → ℝ) :
    lowRankResidualFrob A Ak ≤ lowRankResidualFrob A (rightBasisProjectorApprox A V) :=
  hbest.residual_le_of_rankAtMost (rightBasisProjectorApprox_rankAtMost A V)

/-- An exact left basis-product approximation with exactly `k` displayed
basis vectors is a valid comparison candidate for a best rank-`k` Frobenius
approximation. -/
theorem IsBestRankApproxFrob.residual_le_leftBasisProjectorApprox {m n k : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (U : Fin m → Fin k → ℝ) :
    lowRankResidualFrob A Ak ≤ lowRankResidualFrob A (leftBasisProjectorApprox U A) :=
  hbest.residual_le_of_rankAtMost (leftBasisProjectorApprox_rankAtMost U A)

/-- Exact column sketch `A Z`, the column-space object appearing in the
source equation (9) as `P_{A Z}`. -/
noncomputable def columnSketch {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin m → Fin r → ℝ :=
  preconditionColumns A Z

/-- Exact head matrix generated by multiplying the sketch `A Z` by a displayed
coefficient table `W`.  The source equation (9) pseudoinverse route will later
instantiate `W` with a source-subspace coefficient such as a `V_k^T Z`
pseudoinverse expression. -/
noncomputable def columnSketchHead {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (W : Fin r → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => ∑ a : Fin r, columnSketch A Z i a * W a j

/-- Exact residual tail associated with the displayed sketch coefficient table
`W`: `A - (A Z) W`. -/
noncomputable def columnSketchTail {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (W : Fin r → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => A i j - columnSketchHead A Z W i j

/-- Certificate that a displayed head matrix lies in the exact column space of
the sketch `A Z`.  In the source equation (9) proof, this is the algebraic
obligation that the leading SVD part is reproduced by the sketch projector. -/
structure ColumnSketchHeadFactorization {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Head : Fin m → Fin n → ℝ) where
  coeff : Fin r → Fin n → ℝ
  factorization :
    ∀ i j, Head i j = ∑ a : Fin r, columnSketch A Z i a * coeff a j

/-- The canonical head `(A Z) W` factors through the sketch columns. -/
noncomputable def columnSketchHead_headFactorization {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (W : Fin r → Fin n → ℝ) :
    ColumnSketchHeadFactorization A Z (columnSketchHead A Z W) where
  coeff := W
  factorization := by
    intro i j
    rfl

/-- Exact selected right-Gram eigenvector sketch matrix.  Its columns are the
right-Gram eigenbasis vectors indexed by the selected finite set `s`. -/
noncomputable def rectRightGramBasisSketchMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin n → Fin s.card → ℝ :=
  fun j a => rectRightGramEigenbasis A j (s.orderEmbOfFin rfl a)

/-- Coefficient table for the selected right-Gram eigenvector sketch head. -/
noncomputable def rectRightGramBasisSketchCoeff {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin s.card → Fin n → ℝ :=
  fun a j => rectRightGramEigenbasis A j (s.orderEmbOfFin rfl a)

/-- The selected eigenvector sketch columns are exactly the selected projected
columns `A v_a`. -/
theorem columnSketch_rectRightGramBasisSketchMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (i : Fin m) (a : Fin s.card) :
    columnSketch A (rectRightGramBasisSketchMatrix A s) i a =
      rectRightGramProjectedColumn A i (s.orderEmbOfFin rfl a) := by
  rfl

/-- The selected right-Gram head is the column-sketch head generated by the
selected eigenvector sketch and coefficient table. -/
theorem rectRightGramBasisSketch_head_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (i : Fin m) (j : Fin n) :
    rectRightGramBasisSVDHead A s i j =
      columnSketchHead A (rectRightGramBasisSketchMatrix A s)
        (rectRightGramBasisSketchCoeff A s) i j := by
  classical
  unfold rectRightGramBasisSVDHead columnSketchHead
  let e : Fin s.card → Fin n := fun a => s.orderEmbOfFin rfl a
  let term : Fin n → ℝ :=
    fun a =>
      rectRightGramLeftSingularZeroSafe A i a *
        rectRightGramBasisSingularValue A a *
        rectRightGramEigenbasis A j a
  have hsum :
      s.sum term = ∑ a : Fin s.card, term (e a) := by
    have hsub :
        (∑ a : Fin s.card, term (e a)) = ∑ x : s, term x := by
      refine Fintype.sum_equiv (s.orderIsoOfFin rfl).toEquiv
        (fun a : Fin s.card => term (e a))
        (fun x : s => term x) ?_
      intro a
      simp [e]
    calc
      s.sum term = ∑ x : s, term x := by
            simpa using (Finset.sum_coe_sort s term).symm
      _ = ∑ a : Fin s.card, term (e a) := hsub.symm
  rw [show
      s.sum (fun a =>
          rectRightGramLeftSingularZeroSafe A i a *
            rectRightGramBasisSingularValue A a *
            rectRightGramEigenbasis A j a) = s.sum term by rfl]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro a _
  rw [columnSketch_rectRightGramBasisSketchMatrix A s i a]
  have hf := rectRightGramLeftSingularZeroSafe_factor_column A i (e a)
  rw [← hf]
  simp [rectRightGramBasisSketchCoeff, e]
  ring

/-- Column-sketch factorization of the selected right-Gram head through the
selected eigenvector sketch. -/
noncomputable def rectRightGramBasisSketchHeadFactorization {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    ColumnSketchHeadFactorization A (rectRightGramBasisSketchMatrix A s)
      (rectRightGramBasisSVDHead A s) where
  coeff := rectRightGramBasisSketchCoeff A s
  factorization := by
    intro i j
    exact rectRightGramBasisSketch_head_eq A s i j

/-- The selected right-Gram head lies in the exact selected-eigenvector sketch
column space. -/
noncomputable def rectRightGramBasisSVDHead_columnSketchHeadFactorization {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    ColumnSketchHeadFactorization A (rectRightGramBasisSketchMatrix A s)
      (rectRightGramBasisSVDHead A s) :=
  rectRightGramBasisSketchHeadFactorization A s

/-- The canonical head/tail pair induced by `W` splits `A`. -/
theorem columnSketchHeadTail_split {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (W : Fin r → Fin n → ℝ) :
    ∀ i j, A i j = columnSketchHead A Z W i j + columnSketchTail A Z W i j := by
  intro i j
  unfold columnSketchTail
  ring

/-- If a left multiplier reproduces the sketch columns, then it reproduces any
head matrix that factors through those columns. -/
theorem preconditionRows_reproduces_head_of_columnSketchHeadFactorization
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P : Fin m → Fin m → ℝ) (Head : Fin m → Fin n → ℝ)
    (hrepr :
      ∀ i a, preconditionRows P (columnSketch A Z) i a = columnSketch A Z i a)
    (hHead : ColumnSketchHeadFactorization A Z Head) :
    ∀ i j, preconditionRows P Head i j = Head i j := by
  intro i j
  calc
    preconditionRows P Head i j
        = ∑ k : Fin m, P i k * Head k j := by rfl
    _ = ∑ k : Fin m,
          P i k * (∑ a : Fin r, columnSketch A Z k a * hHead.coeff a j) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hHead.factorization k j]
    _ = ∑ k : Fin m, ∑ a : Fin r,
          P i k * (columnSketch A Z k a * hHead.coeff a j) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ a : Fin r, ∑ k : Fin m,
          P i k * (columnSketch A Z k a * hHead.coeff a j) := by
          rw [Finset.sum_comm]
    _ = ∑ a : Fin r,
          (∑ k : Fin m, P i k * columnSketch A Z k a) * hHead.coeff a j := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ∑ a : Fin r,
          preconditionRows P (columnSketch A Z) i a * hHead.coeff a j := by
          rfl
    _ = ∑ a : Fin r, columnSketch A Z i a * hHead.coeff a j := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hrepr i a]
    _ = Head i j := by
          rw [hHead.factorization i j]

/-- Certificate that a square left multiplier factors through the columns of a
displayed rectangular matrix.  For equation (9), this is the exact-object
surface needed to say that the analysis projector `P_{A Z}` maps through the
sketch column space before introducing pseudoinverse-specific foundations. -/
structure LeftFactorThrough {m r : ℕ}
    (P : Fin m → Fin m → ℝ) (B : Fin m → Fin r → ℝ) where
  coeff : Fin r → Fin m → ℝ
  factorization : ∀ i j, P i j = ∑ a : Fin r, B i a * coeff a j

/-- If a left multiplier factors through `r` displayed columns, then multiplying
any `m × n` matrix on the left by it gives a matrix of repository rank at most
`r`. -/
noncomputable def leftProductFactorizationOfLeftFactorThrough {m n r : ℕ}
    {P : Fin m → Fin m → ℝ} {B : Fin m → Fin r → ℝ}
    (hP : LeftFactorThrough P B) (A : Fin m → Fin n → ℝ) :
    RectRankFactorization m n r (preconditionRows P A) where
  left := B
  right := fun a j => ∑ k : Fin m, hP.coeff a k * A k j
  factorization := by
    intro i j
    unfold preconditionRows
    calc
      (∑ k : Fin m, P i k * A k j)
          = ∑ k : Fin m, (∑ a : Fin r, B i a * hP.coeff a k) * A k j := by
              apply Finset.sum_congr rfl
              intro k _
              rw [hP.factorization]
      _ = ∑ k : Fin m, ∑ a : Fin r, (B i a * hP.coeff a k) * A k j := by
              simp_rw [Finset.sum_mul]
      _ = ∑ a : Fin r, ∑ k : Fin m, (B i a * hP.coeff a k) * A k j := by
              rw [Finset.sum_comm]
      _ = ∑ a : Fin r, B i a * (∑ k : Fin m, hP.coeff a k * A k j) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring

/-- Rank-at-most wrapper for a left product whose multiplier factors through
`r` displayed columns. -/
theorem preconditionRows_rankAtMost_of_leftFactorThrough {m n r : ℕ}
    {P : Fin m → Fin m → ℝ} {B : Fin m → Fin r → ℝ}
    (hP : LeftFactorThrough P B) (A : Fin m → Fin n → ℝ) :
    RectRankAtMost m n r (preconditionRows P A) :=
  ⟨leftProductFactorizationOfLeftFactorThrough hP A⟩

/-- Exact equation (9) projector candidate: if `P_AZ` factors through the
column sketch `A Z`, then `P_AZ A` has repository rank at most the number of
sketch columns. -/
theorem sketchColumnProjectorApprox_rankAtMost {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z)) :
    RectRankAtMost m n r (preconditionRows P_AZ A) :=
  preconditionRows_rankAtMost_of_leftFactorThrough hP A

/-- Certificate-shaped exact residual surface for the source equation (9).
The terms `tail` and `coupling` stand for the exact analysis quantities
`||Σ_{k,⊥}||` and `||Σ_{k,⊥}(V_{k,⊥}ᵀ Z)(V_kᵀ Z)^+||` after choosing a
concrete norm route.  This structure records the inequality without pretending
that the repository has already built the rectangular SVD, pseudoinverse, or
unitarily invariant norm infrastructure needed to instantiate it. -/
structure Equation9ResidualCertificate {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (tail coupling : ℝ) : Prop where
  tail_nonneg : 0 ≤ tail
  coupling_nonneg : 0 ≤ coupling
  residual_bound :
    lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling

/-- Norm-generic exact residual surface for source equation (9).  The supplied
functional `ξ` may later be instantiated by a concrete unitarily invariant norm,
but this theorem surface only assumes the explicit norm-like fields in
`RectNormLike`. -/
structure Equation9ResidualNormCertificate {m n : ℕ}
    (ξ : RectNormLike m n)
    (A : Fin m → Fin n → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (tail coupling : ℝ) : Prop where
  tail_nonneg : 0 ≤ tail
  coupling_nonneg : 0 ≤ coupling
  residual_bound :
    lowRankResidualNorm ξ A (preconditionRows P_AZ A) ≤ tail + coupling

/-- Head/tail decomposition certificate for equation (9).

This exposes the exact algebra hidden in the source proof before the remaining
rectangular-SVD and pseudoinverse foundations are available: `A = Head + Tail`,
the head lies in the exact sketch column space, and the tail plus projected-tail
Frobenius norms are bounded by the displayed radii. -/
structure Equation9HeadTailSketchCertificate {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ)
    (tail coupling : ℝ) where
  split : ∀ i j, A i j = Head i j + Tail i j
  head_factor : ColumnSketchHeadFactorization A Z Head
  tail_nonneg : 0 ≤ tail
  coupling_nonneg : 0 ≤ coupling
  tail_bound : frobNormRect Tail ≤ tail
  coupling_bound : frobNormRect (preconditionRows P_AZ Tail) ≤ coupling

/-- Norm-generic head/tail decomposition certificate for equation (9).  It is
the same exact head-in-sketch algebra as `Equation9HeadTailSketchCertificate`,
but the two visible analytic bounds are measured by a supplied norm-like
functional. -/
structure Equation9HeadTailSketchNormCertificate {m n r : ℕ}
    (ξ : RectNormLike m n)
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ)
    (tail coupling : ℝ) where
  split : ∀ i j, A i j = Head i j + Tail i j
  head_factor : ColumnSketchHeadFactorization A Z Head
  tail_nonneg : 0 ≤ tail
  coupling_nonneg : 0 ≤ coupling
  tail_bound : ξ.norm Tail ≤ tail
  coupling_bound : ξ.norm (preconditionRows P_AZ Tail) ≤ coupling

/-- A Frobenius equation-(9) residual certificate is the norm-generic
certificate for `frobRectNormLike`. -/
theorem Equation9ResidualCertificate.to_norm_frobRectNormLike {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {P_AZ : Fin m → Fin m → ℝ}
    {tail coupling : ℝ}
    (h : Equation9ResidualCertificate A P_AZ tail coupling) :
    Equation9ResidualNormCertificate (frobRectNormLike m n)
      A P_AZ tail coupling where
  tail_nonneg := h.tail_nonneg
  coupling_nonneg := h.coupling_nonneg
  residual_bound := by
    simpa [lowRankResidualNorm_frobRectNormLike]
      using h.residual_bound

/-- A Frobenius head/tail sketch certificate is the norm-generic head/tail
certificate for `frobRectNormLike`. -/
def Equation9HeadTailSketchCertificate.to_norm_frobRectNormLike
    {m n r : ℕ}
    {A : Fin m → Fin n → ℝ} {Z : Fin n → Fin r → ℝ}
    {P_AZ : Fin m → Fin m → ℝ} {Head Tail : Fin m → Fin n → ℝ}
    {tail coupling : ℝ}
    (h : Equation9HeadTailSketchCertificate A Z P_AZ Head Tail tail coupling) :
    Equation9HeadTailSketchNormCertificate (frobRectNormLike m n)
      A Z P_AZ Head Tail tail coupling where
  split := h.split
  head_factor := h.head_factor
  tail_nonneg := h.tail_nonneg
  coupling_nonneg := h.coupling_nonneg
  tail_bound := by
    simpa [frobRectNormLike] using h.tail_bound
  coupling_bound := by
    simpa [frobRectNormLike] using h.coupling_bound

/-- A head/tail sketch certificate and sketch reproduction instantiate the
equation (9) residual certificate. -/
theorem Equation9HeadTailSketchCertificate.to_residualCertificate {m n r : ℕ}
    {A : Fin m → Fin n → ℝ} {Z : Fin n → Fin r → ℝ}
    {P_AZ : Fin m → Fin m → ℝ} {Head Tail : Fin m → Fin n → ℝ}
    {tail coupling : ℝ}
    (h : Equation9HeadTailSketchCertificate A Z P_AZ Head Tail tail coupling)
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a) :
    Equation9ResidualCertificate A P_AZ tail coupling where
  tail_nonneg := h.tail_nonneg
  coupling_nonneg := h.coupling_nonneg
  residual_bound := by
    have hHead :
        ∀ i j, preconditionRows P_AZ Head i j = Head i j :=
      preconditionRows_reproduces_head_of_columnSketchHeadFactorization
        A Z P_AZ Head hrepr h.head_factor
    have hPA :
        ∀ i j,
          preconditionRows P_AZ A i j =
            preconditionRows P_AZ Head i j + preconditionRows P_AZ Tail i j := by
      intro i j
      calc
        preconditionRows P_AZ A i j
            = ∑ k : Fin m, P_AZ i k * (Head k j + Tail k j) := by
                unfold preconditionRows
                apply Finset.sum_congr rfl
                intro k _
                rw [h.split k j]
        _ = ∑ k : Fin m,
              (P_AZ i k * Head k j + P_AZ i k * Tail k j) := by
                apply Finset.sum_congr rfl
                intro k _
                ring
        _ = (∑ k : Fin m, P_AZ i k * Head k j) +
              (∑ k : Fin m, P_AZ i k * Tail k j) := by
                rw [Finset.sum_add_distrib]
        _ = preconditionRows P_AZ Head i j + preconditionRows P_AZ Tail i j := by
                rfl
    have hres :
        (fun i j => A i j - preconditionRows P_AZ A i j) =
          (fun i j => Tail i j - preconditionRows P_AZ Tail i j) := by
      funext i
      funext j
      rw [h.split i j, hPA i j, hHead i j]
      ring
    unfold lowRankResidualFrob
    rw [hres]
    exact le_trans (frobNormRect_sub_le Tail (preconditionRows P_AZ Tail))
      (add_le_add h.tail_bound h.coupling_bound)

/-- A norm-generic head/tail sketch certificate and sketch reproduction
instantiate the norm-generic equation (9) residual certificate.  Only the
triangle field of `RectNormLike` is used here; unitarily invariant norm
invariance and singular-value comparisons are intentionally not hidden in this
adapter. -/
theorem Equation9HeadTailSketchNormCertificate.to_residualNormCertificate
    {m n r : ℕ}
    {ξ : RectNormLike m n}
    {A : Fin m → Fin n → ℝ} {Z : Fin n → Fin r → ℝ}
    {P_AZ : Fin m → Fin m → ℝ} {Head Tail : Fin m → Fin n → ℝ}
    {tail coupling : ℝ}
    (h : Equation9HeadTailSketchNormCertificate ξ A Z P_AZ Head Tail tail coupling)
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a) :
    Equation9ResidualNormCertificate ξ A P_AZ tail coupling where
  tail_nonneg := h.tail_nonneg
  coupling_nonneg := h.coupling_nonneg
  residual_bound := by
    have hHead :
        ∀ i j, preconditionRows P_AZ Head i j = Head i j :=
      preconditionRows_reproduces_head_of_columnSketchHeadFactorization
        A Z P_AZ Head hrepr h.head_factor
    have hPA :
        ∀ i j,
          preconditionRows P_AZ A i j =
            preconditionRows P_AZ Head i j + preconditionRows P_AZ Tail i j := by
      intro i j
      calc
        preconditionRows P_AZ A i j
            = ∑ k : Fin m, P_AZ i k * (Head k j + Tail k j) := by
                unfold preconditionRows
                apply Finset.sum_congr rfl
                intro k _
                rw [h.split k j]
        _ = ∑ k : Fin m,
              (P_AZ i k * Head k j + P_AZ i k * Tail k j) := by
                apply Finset.sum_congr rfl
                intro k _
                ring
        _ = (∑ k : Fin m, P_AZ i k * Head k j) +
              (∑ k : Fin m, P_AZ i k * Tail k j) := by
                rw [Finset.sum_add_distrib]
        _ = preconditionRows P_AZ Head i j + preconditionRows P_AZ Tail i j := by
                rfl
    have hres :
        (fun i j => A i j - preconditionRows P_AZ A i j) =
          (fun i j => Tail i j - preconditionRows P_AZ Tail i j) := by
      funext i
      funext j
      rw [h.split i j, hPA i j, hHead i j]
      ring
    unfold lowRankResidualNorm
    rw [hres]
    exact le_trans (ξ.sub_le_add Tail (preconditionRows P_AZ Tail))
      (add_le_add h.tail_bound h.coupling_bound)

/-- The canonical head/tail pair from a displayed coefficient table `W`
instantiates the head/tail sketch certificate once the two exact norm bounds
are supplied. -/
noncomputable def equation9HeadTailSketchCertificate_of_columnSketchHead
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ) (W : Fin r → Fin n → ℝ)
    (tail coupling : ℝ)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (columnSketchTail A Z W) ≤ tail)
    (hcoupling :
      frobNormRect (preconditionRows P_AZ (columnSketchTail A Z W)) ≤ coupling) :
    Equation9HeadTailSketchCertificate A Z P_AZ
      (columnSketchHead A Z W) (columnSketchTail A Z W) tail coupling where
  split := columnSketchHeadTail_split A Z W
  head_factor := columnSketchHead_headFactorization A Z W
  tail_nonneg := htail_nonneg
  coupling_nonneg := hcoupling_nonneg
  tail_bound := htail
  coupling_bound := hcoupling

/-- The right-hand side in an equation (9) residual certificate is nonnegative. -/
theorem Equation9ResidualCertificate.tail_add_coupling_nonneg {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {P_AZ : Fin m → Fin m → ℝ}
    {tail coupling : ℝ}
    (h : Equation9ResidualCertificate A P_AZ tail coupling) :
    0 ≤ tail + coupling :=
  add_nonneg h.tail_nonneg h.coupling_nonneg

/-- The right-hand side in a norm-generic equation (9) residual certificate is
nonnegative. -/
theorem Equation9ResidualNormCertificate.tail_add_coupling_nonneg {m n : ℕ}
    {ξ : RectNormLike m n}
    {A : Fin m → Fin n → ℝ} {P_AZ : Fin m → Fin m → ℝ}
    {tail coupling : ℝ}
    (h : Equation9ResidualNormCertificate ξ A P_AZ tail coupling) :
    0 ≤ tail + coupling :=
  add_nonneg h.tail_nonneg h.coupling_nonneg

/-- Exact equation (9) rank/residual surface: a supplied column-sketch projector
factorization and a supplied residual certificate imply that `P_AZ A` is a
rank-`r` candidate with the displayed equation (9) residual bound. -/
theorem equation9RankResidualSurface {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hEq9 : Equation9ResidualCertificate A P_AZ tail coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling :=
  ⟨sketchColumnProjectorApprox_rankAtMost A Z P_AZ hP, hEq9.residual_bound⟩

/-- Norm-generic equation (9) rank/residual surface.  This proves the algebraic
rank and residual wrapper for any supplied `RectNormLike`; proving that a
specific unitarily invariant norm supplies the required head/tail bounds is a
separate foundation. -/
theorem equation9RankResidualNormSurface {m n r : ℕ}
    (ξ : RectNormLike m n)
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hEq9 : Equation9ResidualNormCertificate ξ A P_AZ tail coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualNorm ξ A (preconditionRows P_AZ A) ≤ tail + coupling :=
  ⟨sketchColumnProjectorApprox_rankAtMost A Z P_AZ hP, hEq9.residual_bound⟩

/-- Rank/residual surface from the explicit head/tail sketch certificate. -/
theorem equation9HeadTailSketchRankResidualSurface {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling : ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchCertificate A Z P_AZ Head Tail tail coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling :=
  equation9RankResidualSurface A Z P_AZ tail coupling hP
    (hHT.to_residualCertificate hrepr)

/-- The arbitrary selected right-Gram head/tail split instantiates the
equation-(9) head/tail sketch certificate for the selected eigenvector sketch,
once the exact tail and projected-tail coupling bounds are supplied. -/
noncomputable def equation9HeadTailSketchCertificate_of_rectRightGramBasisSVDHead
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail : frobNormRect (rectRightGramBasisSVDTail A s) ≤ tail)
    (hcoupling :
      frobNormRect (preconditionRows P_AZ (rectRightGramBasisSVDTail A s)) ≤
        coupling) :
    Equation9HeadTailSketchCertificate A (rectRightGramBasisSketchMatrix A s)
      P_AZ (rectRightGramBasisSVDHead A s) (rectRightGramBasisSVDTail A s)
      tail coupling where
  split := rectRightGramBasisSVD_head_tail_entry A s
  head_factor := rectRightGramBasisSVDHead_columnSketchHeadFactorization A s
  tail_nonneg := htail_nonneg
  coupling_nonneg := hcoupling_nonneg
  tail_bound := htail
  coupling_bound := hcoupling

/-- Selected right-Gram equation-(9) rank/residual surface: if the exact
selected-sketch multiplier factors through and reproduces the selected sketch
columns, and if the selected tail and projected-tail coupling are bounded by
the displayed radii, then the exact projector candidate has rank at most
`|s|` and residual at most `tail + coupling`. -/
theorem equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hP :
      LeftFactorThrough P_AZ
        (columnSketch A (rectRightGramBasisSketchMatrix A s)))
    (hrepr :
      ∀ i a,
        preconditionRows P_AZ
            (columnSketch A (rectRightGramBasisSketchMatrix A s)) i a =
          columnSketch A (rectRightGramBasisSketchMatrix A s) i a)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail : frobNormRect (rectRightGramBasisSVDTail A s) ≤ tail)
    (hcoupling :
      frobNormRect (preconditionRows P_AZ (rectRightGramBasisSVDTail A s)) ≤
        coupling) :
    RectRankAtMost m n s.card (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling :=
  equation9HeadTailSketchRankResidualSurface A
    (rectRightGramBasisSketchMatrix A s) P_AZ
    (rectRightGramBasisSVDHead A s) (rectRightGramBasisSVDTail A s)
    tail coupling hP hrepr
    (equation9HeadTailSketchCertificate_of_rectRightGramBasisSVDHead
      A s P_AZ tail coupling htail_nonneg hcoupling_nonneg htail hcoupling)

/-- Selected right-Gram equation-(9) rank/residual surface with an explicit
paper-facing rank parameter `k`, obtained from the cardinality certificate
`s.card = k`. -/
theorem
    equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_card_eq
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hcard : s.card = k)
    (hP :
      LeftFactorThrough P_AZ
        (columnSketch A (rectRightGramBasisSketchMatrix A s)))
    (hrepr :
      ∀ i a,
        preconditionRows P_AZ
            (columnSketch A (rectRightGramBasisSketchMatrix A s)) i a =
          columnSketch A (rectRightGramBasisSketchMatrix A s) i a)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail : frobNormRect (rectRightGramBasisSVDTail A s) ≤ tail)
    (hcoupling :
      frobNormRect (preconditionRows P_AZ (rectRightGramBasisSVDTail A s)) ≤
        coupling) :
    RectRankAtMost m n k (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling := by
  have hsurface :=
    equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead
      A s P_AZ tail coupling hP hrepr htail_nonneg hcoupling_nonneg htail
      hcoupling
  exact ⟨rectRankAtMost_of_eq_rank hcard hsurface.1, hsurface.2⟩

/-- Selected right-Gram equation-(9) rank/residual surface for a selected-index
embedding `Fin k ↪ Fin n`.  The rank parameter is the displayed domain size
`k`; the selected set cardinality is proved by `rectRightGramSelectedIndexSet_card`. -/
theorem
    equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_embedding
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (e : Fin k ↪ Fin n)
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hP :
      LeftFactorThrough P_AZ
        (columnSketch A
          (rectRightGramBasisSketchMatrix A (rectRightGramSelectedIndexSet e))))
    (hrepr :
      ∀ i a,
        preconditionRows P_AZ
            (columnSketch A
              (rectRightGramBasisSketchMatrix A
                (rectRightGramSelectedIndexSet e))) i a =
          columnSketch A
            (rectRightGramBasisSketchMatrix A
              (rectRightGramSelectedIndexSet e)) i a)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect
          (rectRightGramBasisSVDTail A (rectRightGramSelectedIndexSet e)) ≤
        tail)
    (hcoupling :
      frobNormRect
          (preconditionRows P_AZ
            (rectRightGramBasisSVDTail A (rectRightGramSelectedIndexSet e))) ≤
        coupling) :
    RectRankAtMost m n k (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling :=
  equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_card_eq
    A (rectRightGramSelectedIndexSet e) P_AZ tail coupling
    (rectRightGramSelectedIndexSet_card e) hP hrepr htail_nonneg
    hcoupling_nonneg htail hcoupling

/-- Semantic ordered-top embedding handoff for the selected right-Gram
equation-(9) surface.  The certificate exposes exactly what remains to connect
mathlib's arbitrary basis-indexed right-Gram eigenvectors to the ordered
singular-value sequence: selected basis singular values must agree with the
first `k` ordered singular values.  Under that certificate, the selected square
and order facts are available together with the LR.1ch embedding rank/residual
surface. -/
theorem
    equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_orderedTopEmbedding
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (e : Fin k ↪ Fin n)
    (htop : RectRightGramOrderedTopEmbeddingCertificate A hk e)
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hP :
      LeftFactorThrough P_AZ
        (columnSketch A
          (rectRightGramBasisSketchMatrix A (rectRightGramSelectedIndexSet e))))
    (hrepr :
      ∀ i a,
        preconditionRows P_AZ
            (columnSketch A
              (rectRightGramBasisSketchMatrix A
                (rectRightGramSelectedIndexSet e))) i a =
          columnSketch A
            (rectRightGramBasisSketchMatrix A
              (rectRightGramSelectedIndexSet e)) i a)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect
          (rectRightGramBasisSVDTail A (rectRightGramSelectedIndexSet e)) ≤
        tail)
    (hcoupling :
      frobNormRect
          (preconditionRows P_AZ
            (rectRightGramBasisSVDTail A (rectRightGramSelectedIndexSet e))) ≤
        coupling) :
    (∀ a : Fin k,
      (rectRightGramBasisSingularValue A (e a)) ^ 2 =
        rectSingularValueSq A (rectTopIndex hk a)) ∧
      Antitone (fun a : Fin k => rectRightGramBasisSingularValue A (e a)) ∧
        RectRankAtMost m n k (preconditionRows P_AZ A) ∧
          lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling := by
  refine ⟨?_, ?_⟩
  · intro a
    exact rectRightGramOrderedTopEmbeddingCertificate_selected_sq_eq
      A hk e htop a
  · refine ⟨?_, ?_⟩
    · exact rectRightGramOrderedTopEmbeddingCertificate_selected_antitone
        A hk e htop
    · exact
        equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_embedding
          A e P_AZ tail coupling hP hrepr htail_nonneg hcoupling_nonneg
          htail hcoupling

/-- Constructed ordered-top embedding version of the selected right-Gram
equation-(9) surface.  The semantic ordered-top certificate is instantiated by
the mathlib reindexing equivalence used for the right-Gram eigenbasis. -/
theorem
    equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_constructedOrderedTopEmbedding
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hP :
      LeftFactorThrough P_AZ
        (columnSketch A
          (rectRightGramBasisSketchMatrix A
            (rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk)))))
    (hrepr :
      ∀ i a,
        preconditionRows P_AZ
            (columnSketch A
              (rectRightGramBasisSketchMatrix A
                (rectRightGramSelectedIndexSet
                  (rectRightGramOrderedTopEmbedding hk)))) i a =
          columnSketch A
            (rectRightGramBasisSketchMatrix A
              (rectRightGramSelectedIndexSet
                (rectRightGramOrderedTopEmbedding hk))) i a)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect
          (rectRightGramBasisSVDTail A
            (rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))) ≤
        tail)
    (hcoupling :
      frobNormRect
          (preconditionRows P_AZ
            (rectRightGramBasisSVDTail A
              (rectRightGramSelectedIndexSet
                (rectRightGramOrderedTopEmbedding hk)))) ≤
        coupling) :
    (∀ a : Fin k,
      (rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a)) ^ 2 =
        rectSingularValueSq A (rectTopIndex hk a)) ∧
      Antitone
        (fun a : Fin k =>
          rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk a)) ∧
        RectRankAtMost m n k (preconditionRows P_AZ A) ∧
          lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling :=
  equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_orderedTopEmbedding
    A hk (rectRightGramOrderedTopEmbedding hk)
    (rectRightGramOrderedTopEmbedding_certificate A hk)
    P_AZ tail coupling hP hrepr htail_nonneg hcoupling_nonneg
    htail hcoupling

/-- Norm-generic rank/residual surface from the explicit head/tail sketch
certificate. -/
theorem equation9HeadTailSketchNormRankResidualSurface {m n r : ℕ}
    (ξ : RectNormLike m n)
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling : ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchNormCertificate ξ A Z P_AZ Head Tail tail coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualNorm ξ A (preconditionRows P_AZ A) ≤ tail + coupling :=
  equation9RankResidualNormSurface ξ A Z P_AZ tail coupling hP
    (hHT.to_residualNormCertificate hrepr)

/-- Unitarily invariant norm rank/residual surface.  This is a typed wrapper
around the norm-generic theorem: the orthogonal-invariance fields are available
on `ξ` for later singular-value/source-SVD instantiations, while this theorem
uses only the `RectNormLike` part. -/
theorem equation9RankResidualUnitaryNormSurface {m n r : ℕ}
    (ξ : UnitaryInvariantRectNormLike m n)
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hEq9 :
      Equation9ResidualNormCertificate ξ.toRectNormLike A P_AZ tail coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualNorm ξ.toRectNormLike A (preconditionRows P_AZ A) ≤
        tail + coupling :=
  equation9RankResidualNormSurface ξ.toRectNormLike A Z P_AZ
    tail coupling hP hEq9

/-- Unitarily invariant norm rank/residual surface from an explicit head/tail
certificate. -/
theorem equation9HeadTailSketchUnitaryNormRankResidualSurface {m n r : ℕ}
    (ξ : UnitaryInvariantRectNormLike m n)
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling : ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchNormCertificate ξ.toRectNormLike A Z P_AZ
        Head Tail tail coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualNorm ξ.toRectNormLike A (preconditionRows P_AZ A) ≤
        tail + coupling :=
  equation9HeadTailSketchNormRankResidualSurface ξ.toRectNormLike
    A Z P_AZ Head Tail tail coupling hP hrepr hHT

/-- Relative-error surface for equation (9): if the supplied equation (9)
right-hand side is itself bounded by `rho` times the residual of a certified
best rank-`k` approximation, then the exact projector candidate has that
relative residual bound. -/
theorem equation9RelativeResidualSurface {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hEq9 : Equation9ResidualCertificate A P_AZ tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
        lowRankResidualFrob A (preconditionRows P_AZ A) ≤
          rho * lowRankResidualFrob A Ak :=
  ⟨hbest.rank_le,
    sketchColumnProjectorApprox_rankAtMost A Z P_AZ hP,
    le_trans hEq9.residual_bound hrelative⟩

/-- Norm-generic relative-error surface for equation (9), conditional on a
norm-generic best-rank certificate and a scalar comparison of the visible
head/tail radii. -/
theorem equation9RelativeResidualNormSurface {m n k r : ℕ}
    {ξ : RectNormLike m n}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxNorm m n k ξ A Ak)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hEq9 : Equation9ResidualNormCertificate ξ A P_AZ tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualNorm ξ A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
        lowRankResidualNorm ξ A (preconditionRows P_AZ A) ≤
          rho * lowRankResidualNorm ξ A Ak :=
  ⟨hbest.rank_le,
    sketchColumnProjectorApprox_rankAtMost A Z P_AZ hP,
    le_trans hEq9.residual_bound hrelative⟩

/-- Relative-error surface from the explicit head/tail sketch certificate. -/
theorem equation9HeadTailSketchRelativeResidualSurface {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchCertificate A Z P_AZ Head Tail tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
        lowRankResidualFrob A (preconditionRows P_AZ A) ≤
          rho * lowRankResidualFrob A Ak :=
  equation9RelativeResidualSurface Z P_AZ tail coupling rho hbest hP
    (hHT.to_residualCertificate hrepr) hrelative

/-- Norm-generic relative-error surface from the explicit head/tail sketch
certificate. -/
theorem equation9HeadTailSketchNormRelativeResidualSurface {m n k r : ℕ}
    {ξ : RectNormLike m n}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxNorm m n k ξ A Ak)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchNormCertificate ξ A Z P_AZ Head Tail tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualNorm ξ A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
        lowRankResidualNorm ξ A (preconditionRows P_AZ A) ≤
          rho * lowRankResidualNorm ξ A Ak :=
  equation9RelativeResidualNormSurface Z P_AZ tail coupling rho hbest hP
    (hHT.to_residualNormCertificate hrepr) hrelative

/-- Unitarily invariant norm relative-error surface for equation (9).  The
best-rank and residual certificates are still explicit; Eckart--Young and
singular-value construction remain separate foundations. -/
theorem equation9RelativeResidualUnitaryNormSurface {m n k r : ℕ}
    {ξ : UnitaryInvariantRectNormLike m n}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxNorm m n k ξ.toRectNormLike A Ak)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hEq9 :
      Equation9ResidualNormCertificate ξ.toRectNormLike A P_AZ tail coupling)
    (hrelative :
      tail + coupling ≤ rho * lowRankResidualNorm ξ.toRectNormLike A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
        lowRankResidualNorm ξ.toRectNormLike A (preconditionRows P_AZ A) ≤
          rho * lowRankResidualNorm ξ.toRectNormLike A Ak :=
  equation9RelativeResidualNormSurface Z P_AZ tail coupling rho
    hbest hP hEq9 hrelative

/-- Unitarily invariant norm relative-error surface from the explicit
head/tail sketch certificate. -/
theorem equation9HeadTailSketchUnitaryNormRelativeResidualSurface {m n k r : ℕ}
    {ξ : UnitaryInvariantRectNormLike m n}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxNorm m n k ξ.toRectNormLike A Ak)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchNormCertificate ξ.toRectNormLike A Z P_AZ
        Head Tail tail coupling)
    (hrelative :
      tail + coupling ≤ rho * lowRankResidualNorm ξ.toRectNormLike A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
        lowRankResidualNorm ξ.toRectNormLike A (preconditionRows P_AZ A) ≤
          rho * lowRankResidualNorm ξ.toRectNormLike A Ak :=
  equation9HeadTailSketchNormRelativeResidualSurface Z P_AZ Head Tail
    tail coupling rho hbest hP hrepr hHT hrelative

/-- Frobenius specialization of the norm-generic head/tail rank/residual
surface.  This makes the concrete `frobRectNormLike` instantiation explicit
while preserving the older Frobenius statement shape. -/
theorem equation9HeadTailSketchFrobNormRankResidualSurface {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling : ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchCertificate A Z P_AZ Head Tail tail coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling := by
  simpa [lowRankResidualNorm_frobRectNormLike]
    using
      equation9HeadTailSketchNormRankResidualSurface
        (frobRectNormLike m n) A Z P_AZ Head Tail tail coupling hP hrepr
        hHT.to_norm_frobRectNormLike

/-- Frobenius specialization of the norm-generic head/tail relative-residual
surface.  This is a D2 bridge theorem: it closes the concrete Frobenius
`RectNormLike` instantiation, not the still-open all-unitarily-invariant norm
or Eckart--Young foundations. -/
theorem equation9HeadTailSketchFrobNormRelativeResidualSurface {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchCertificate A Z P_AZ Head Tail tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
        lowRankResidualFrob A (preconditionRows P_AZ A) ≤
          rho * lowRankResidualFrob A Ak := by
  simpa [lowRankResidualNorm_frobRectNormLike]
    using
      equation9HeadTailSketchNormRelativeResidualSurface
        (Z := Z) (P_AZ := P_AZ) (Head := Head) (Tail := Tail)
        (tail := tail) (coupling := coupling) (rho := rho)
        (hbest := hbest.to_norm_frobRectNormLike)
        (hP := hP) (hrepr := hrepr)
        (hHT := hHT.to_norm_frobRectNormLike)
        (hrelative := by
          simpa [lowRankResidualNorm_frobRectNormLike] using hrelative)

/-- Exact left multiplier obtained by multiplying the column sketch `A Z` by a
displayed coefficient table `C`.  Later pseudoinverse infrastructure can
instantiate `C` with `(A Z)^+`; this definition itself is only exact algebra. -/
noncomputable def columnSketchLeftMultiplier {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) :
    Fin m → Fin m → ℝ :=
  fun i j => ∑ a : Fin r, columnSketch A Z i a * C a j

/-- Exact right multiplier `C (A Z)` appearing in the Moore-Penrose equations
for a coefficient table `C`.  The source proof eventually needs the full
four-equation pseudoinverse surface; this definition exposes the `C B` side
without constructing a pseudoinverse. -/
noncomputable def columnSketchRightMultiplier {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) :
    Fin r → Fin r → ℝ :=
  preconditionRows C (columnSketch A Z)

/-- Exact Gram matrix `Bᵀ B` for the column sketch `B = A Z`.  This is an
analysis object used to state the full-column-rank pseudoinverse route; no
floating-point cost is charged unless an implementation actually computes it. -/
noncomputable def columnSketchGram {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin r → Fin r → ℝ :=
  fun a b => ∑ i : Fin m, columnSketch A Z i a * columnSketch A Z i b

/-- The exact sketch Gram matrix `BᵀB` is symmetric. -/
theorem columnSketchGram_symmetric {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    IsSymmetricFiniteMatrix (columnSketchGram A Z) := by
  intro a b
  unfold columnSketchGram
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The quadratic form of a column-sketch Gram matrix is the squared norm of
the corresponding sketched column combination. -/
theorem finiteQuadraticForm_columnSketchGram_eq_sum_sq {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (x : Fin r → ℝ) :
    finiteQuadraticForm (columnSketchGram A Z) x =
      ∑ i : Fin m, (∑ a : Fin r, columnSketch A Z i a * x a) ^ 2 := by
  classical
  unfold finiteQuadraticForm finiteMatVec columnSketchGram
  calc
    ∑ a : Fin r,
        x a *
          ∑ b : Fin r,
            (∑ i : Fin m, columnSketch A Z i a * columnSketch A Z i b) *
              x b
        =
          ∑ a : Fin r, ∑ b : Fin r, ∑ i : Fin m,
            (columnSketch A Z i a * x a) *
              (columnSketch A Z i b * x b) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ =
          ∑ b : Fin r, ∑ a : Fin r, ∑ i : Fin m,
            (columnSketch A Z i a * x a) *
              (columnSketch A Z i b * x b) := by
            rw [Finset.sum_comm]
    _ =
          ∑ b : Fin r, ∑ i : Fin m, ∑ a : Fin r,
            (columnSketch A Z i a * x a) *
              (columnSketch A Z i b * x b) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m, ∑ b : Fin r, ∑ a : Fin r,
            (columnSketch A Z i a * x a) *
              (columnSketch A Z i b * x b) := by
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m, ∑ a : Fin r, ∑ b : Fin r,
            (columnSketch A Z i a * x a) *
              (columnSketch A Z i b * x b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m,
            (∑ a : Fin r, columnSketch A Z i a * x a) *
              (∑ b : Fin r, columnSketch A Z i b * x b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
    _ =
          ∑ i : Fin m, (∑ a : Fin r, columnSketch A Z i a * x a) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- Every exact column-sketch Gram matrix is positive semidefinite. -/
theorem columnSketchGram_finitePSD {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    finitePSD (columnSketchGram A Z) := by
  intro x
  rw [finiteQuadraticForm_columnSketchGram_eq_sum_sq A Z x]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- A positive-definite exact head Gram remains nonsingular after adding an
exact positive-semidefinite tail Gram. -/
theorem matrix_det_ne_zero_of_posDef_add_posSemidef {r : ℕ}
    (Head Tail : Fin r → Fin r → ℝ)
    (hHead : Matrix.PosDef (Head : Matrix (Fin r) (Fin r) ℝ))
    (hTail : Matrix.PosSemidef (Tail : Matrix (Fin r) (Fin r) ℝ)) :
    Matrix.det ((fun a b => Head a b + Tail a b) :
      Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
  have hsum :
      Matrix.PosDef
        ((Head : Matrix (Fin r) (Fin r) ℝ) +
          (Tail : Matrix (Fin r) (Fin r) ℝ)) :=
    hHead.add_posSemidef hTail
  have hdet :
      0 <
        Matrix.det
          ((Head : Matrix (Fin r) (Fin r) ℝ) +
            (Tail : Matrix (Fin r) (Fin r) ℝ)) :=
    Matrix.PosDef.det_pos hsum
  exact ne_of_gt (by simpa using hdet)

/-- Exact coefficient table `G^{-1} Bᵀ` for the column sketch `B = A Z` and a
supplied inverse candidate `Ginv` for `G = BᵀB`. -/
noncomputable def columnSketchGramInverseCoefficient {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ) :
    Fin r → Fin m → ℝ :=
  fun a i => ∑ b : Fin r, Ginv a b * columnSketch A Z i b

/-- The concrete exact Gram-inverse projector candidate
`P = (A Z) ((A Z)ᵀ(A Z))^{-1}(A Z)ᵀ`.  This is an analysis object unless an
implementation-facing theorem supplies floating-point certificates for the
Gram, inverse, products, and storage. -/
noncomputable def columnSketchGramInverseProjector {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin m → Fin m → ℝ :=
  columnSketchLeftMultiplier A Z
    (columnSketchGramInverseCoefficient A Z
      (nonsingInv r (columnSketchGram A Z)))

/-- Concrete computed-object certificate for the low-rank column-sketch
Gram-inverse projector when the exact analysis projector is stored by rounded
multiply-one copies before it is applied to `A`.

This charges only the non-probability storage/copy of the already supplied
projector entries.  It is not a floating-point routine for forming the sketch
Gram, inverting it, or multiplying out the projector; those routine
instantiations remain separate implementation-facing obligations. -/
noncomputable def columnSketchGramInverseProjectorStoredMulOne
    (fp : FPModel) {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    ComputedPreconditioner fp (columnSketchGramInverseProjector A Z) :=
  ComputedPreconditioner.ofComputedMatrix
    (ComputedMatrix.flMulOne fp (columnSketchGramInverseProjector A Z))

@[simp] theorem columnSketchGramInverseProjectorStoredMulOne_matrix
    (fp : FPModel) {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    (columnSketchGramInverseProjectorStoredMulOne fp A Z).matrix =
      fun i k => fp.fl_mul (columnSketchGramInverseProjector A Z i k) 1 :=
  rfl

@[simp] theorem columnSketchGramInverseProjectorStoredMulOne_abs_error
    (fp : FPModel) {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    (columnSketchGramInverseProjectorStoredMulOne fp A Z).abs_error =
      fun i k => fp.u * |columnSketchGramInverseProjector A Z i k| :=
  rfl

/-- Entrywise storage/copy error for the concrete rounded multiply-one
realization of the low-rank column-sketch Gram-inverse projector. -/
theorem columnSketchGramInverseProjectorStoredMulOne_entry_error_bound
    (fp : FPModel) {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (i k : Fin m) :
    |(columnSketchGramInverseProjectorStoredMulOne fp A Z).matrix i k -
        columnSketchGramInverseProjector A Z i k| ≤
      fp.u * |columnSketchGramInverseProjector A Z i k| :=
  (columnSketchGramInverseProjectorStoredMulOne fp A Z).entry_abs_error_bound i k

/-- Implementation-facing entrywise error for applying the stored low-rank
Gram-inverse projector to the input matrix.

The algorithmic operations charged here are: rounded multiply-one storage of
every projector entry and the rounded length-`m` matrix product
`fl(P_hat A)`.  Sampling probabilities and laws are exact by convention, and
the exact projector itself remains the analysis reference. -/
theorem fl_columnSketchGramInverseProjectorStoredMulOne_preconditionRows_entry_error_bound
    (fp : FPModel) {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (hm : gammaValid fp m) (i : Fin m) (j : Fin n) :
    |fl_preconditionRowsWithComputedLeft fp
        (columnSketchGramInverseProjectorStoredMulOne fp A Z) A i j -
      preconditionRows (columnSketchGramInverseProjector A Z) A i j| ≤
      gamma fp m *
          ∑ k : Fin m,
            |fp.fl_mul (columnSketchGramInverseProjector A Z i k) 1| *
              |A k j| +
        ∑ k : Fin m,
          (fp.u * |columnSketchGramInverseProjector A Z i k|) * |A k j| := by
  simpa [columnSketchGramInverseProjectorStoredMulOne,
    flPreconditionRowsWithComputedLeftEntryErrorBudget] using
    fl_preconditionRowsWithComputedLeft_entry_error_budget_bound
      fp (columnSketchGramInverseProjectorStoredMulOne fp A Z) A hm i j

/-- Certificate for the source full-column-rank route
`C = (BᵀB)^{-1}Bᵀ`.  The inverse and symmetry fields are explicit because this
file does not yet construct `G^{-1}` from rank/SVD facts. -/
structure ColumnSketchGramInverseCertificate {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ) : Prop where
  inverse : IsInverse r (columnSketchGram A Z) Ginv
  symmetric_inverse : IsSymmetricFiniteMatrix Ginv

/-- A nonzero determinant of the exact sketch Gram matrix supplies the concrete
repository `nonsingInv` Gram-inverse certificate.  This is still an exact-object
route: it reduces LR.1 to proving the determinant/nonzero-full-rank condition,
not to computing the inverse in floating point. -/
theorem columnSketchGramInverseCertificate_of_det_ne_zero
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchGramInverseCertificate A Z
      (nonsingInv r (columnSketchGram A Z)) where
  inverse :=
    isInverse_nonsingInv_of_det_ne_zero r (columnSketchGram A Z) hdet
  symmetric_inverse :=
    nonsingInv_symmetric_of_symmetric (columnSketchGram A Z)
      (columnSketchGram_symmetric A Z)

/-- Thin exact factorization certificate for the column sketch `B = A Z`.
The source SVD/QR route can instantiate this with `B = U R`, orthonormal
columns in `U`, and nonsingular square factor `R`. -/
structure ColumnSketchThinFactorCertificate {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (R : Fin r → Fin r → ℝ) : Prop where
  factorization :
    ∀ i a, columnSketch A Z i a = ∑ c : Fin r, U i c * R c a
  orthonormal_columns :
    ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b
  det_factor_ne_zero :
    Matrix.det (R : Matrix (Fin r) (Fin r) ℝ) ≠ 0

/-- Exact source-factor matrix `U Σ Vᵀ`.  This is a theorem-surface object for
the equation (9) SVD route; implementation-facing theorems must separately
certify any computed singular vectors, singular values, or products. -/
noncomputable def sourceSVDFactorMatrix {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => ∑ a : Fin r, U i a * (∑ b : Fin r, Sigma a b * V j b)

/-- A diagonal source factor expands to the usual supplied-SVD sum
`sum_k U_ik sigma_k V_jk`.

This is exact-object algebra.  It is used only to align supplied SVD-style
representations with the source-factor theorem surface; computed singular
vectors, singular values, and products remain non-probability FP/certificate
obligations. -/
theorem sourceSVDFactorMatrix_diagonal_eq_sum {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (sigma : Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (i : Fin m) (j : Fin n) :
    sourceSVDFactorMatrix U
        (fun a b : Fin r => if a = b then sigma a else 0) V i j =
      ∑ k : Fin r, U i k * (sigma k * V j k) := by
  unfold sourceSVDFactorMatrix
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- The exact source head `U Σ Vᵀ` factors through the displayed source rank
dimension.  This is an exact-object source-SVD rank certificate; constructing
or computing the source SVD data remains a separate obligation. -/
noncomputable def sourceSVDFactorMatrixRankFactorization {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) :
    RectRankFactorization m n r (sourceSVDFactorMatrix U Sigma V) where
  left := U
  right := fun a j => ∑ b : Fin r, Sigma a b * V j b
  factorization := by
    intro i j
    rfl

/-- The exact source head `U Σ Vᵀ` has rank at most the displayed source
dimension `r`. -/
theorem sourceSVDFactorMatrix_rankAtMost {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) :
    RectRankAtMost m n r (sourceSVDFactorMatrix U Sigma V) :=
  ⟨sourceSVDFactorMatrixRankFactorization U Sigma V⟩

/-- A rectangular left factor with exact orthonormal columns preserves the
squared Euclidean norm of a coefficient vector.  This is exact source-SVD
algebra; a computed left singular-vector table needs a separate certificate. -/
theorem vecNorm2Sq_leftOrthonormalFactor {m r : ℕ}
    (U : Fin m → Fin r → ℝ) (y : Fin r → ℝ)
    (hU :
      ∀ a b : Fin r, (∑ i : Fin m, U i a * U i b) = idMatrix r a b) :
    vecNorm2Sq (fun i : Fin m => ∑ a : Fin r, U i a * y a) =
      vecNorm2Sq y := by
  unfold vecNorm2Sq
  have expand : ∀ i : Fin m,
      (∑ a : Fin r, U i a * y a) ^ 2 =
        ∑ a : Fin r, ∑ b : Fin r,
          U i a * U i b * (y a * y b) := by
    intro i
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  have factor : ∀ b : Fin r,
      ∑ i : Fin m, U i a * U i b * (y a * y b) =
        (∑ i : Fin m, U i a * U i b) * (y a * y b) := by
    intro b
    rw [← Finset.sum_mul]
  simp_rw [factor, hU]
  simp [idMatrix, Finset.sum_ite_eq, Finset.mem_univ]
  ring

/-- A diagonal exact source block whose displayed diagonal entries are bounded
below by a nonnegative `sigma` expands every vector by at least `sigma` in
squared Euclidean norm.  Computed diagonal singular values require a separate
implementation-facing certificate. -/
theorem vecNorm2Sq_diagonal_lower_bound {r : ℕ}
    (Sigma : Fin r → Fin r → ℝ) (sigmaDiag : Fin r → ℝ) {sigma : ℝ}
    (hSigma : ∀ a b, Sigma a b = if a = b then sigmaDiag a else 0)
    (hsigma_nonneg : 0 ≤ sigma)
    (hdiag : ∀ a, sigma ≤ sigmaDiag a)
    (y : Fin r → ℝ) :
    sigma ^ 2 * vecNorm2Sq y ≤ vecNorm2Sq (matMulVec r Sigma y) := by
  have hcoord : ∀ a : Fin r,
      matMulVec r Sigma y a = sigmaDiag a * y a := by
    intro a
    unfold matMulVec
    calc
      (∑ b : Fin r, Sigma a b * y b)
          = ∑ b : Fin r, (if a = b then sigmaDiag a else 0) * y b := by
              apply Finset.sum_congr rfl
              intro b _
              rw [hSigma a b]
      _ = sigmaDiag a * y a := by
              simp [Finset.sum_ite_eq, Finset.mem_univ]
  have hnorm :
      vecNorm2Sq (matMulVec r Sigma y) =
        ∑ a : Fin r, sigmaDiag a ^ 2 * y a ^ 2 := by
    unfold vecNorm2Sq
    apply Finset.sum_congr rfl
    intro a _
    rw [hcoord a]
    ring
  calc
    sigma ^ 2 * vecNorm2Sq y
        = ∑ a : Fin r, sigma ^ 2 * y a ^ 2 := by
            unfold vecNorm2Sq
            rw [Finset.mul_sum]
    _ ≤ ∑ a : Fin r, sigmaDiag a ^ 2 * y a ^ 2 := by
            apply Finset.sum_le_sum
            intro a _
            have hsq : sigma ^ 2 ≤ sigmaDiag a ^ 2 := by
              nlinarith [hsigma_nonneg, hdiag a]
            exact mul_le_mul_of_nonneg_right hsq (sq_nonneg (y a))
    _ = vecNorm2Sq (matMulVec r Sigma y) := hnorm.symm

/-- Matrix-vector action of an exact source factor `U Sigma V^T`, written as
successive right-transpose, diagonal/source, and left-basis actions. -/
theorem rectMatMulVec_sourceSVDFactorMatrix {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (Sigma : Fin n → Fin n → ℝ)
    (V : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x =
      fun i : Fin m =>
        ∑ a : Fin n,
          U i a * matMulVec n Sigma (matMulVec n (matTranspose V) x) a := by
  ext i
  unfold rectMatMulVec sourceSVDFactorMatrix matMulVec matTranspose
  calc
    (∑ j : Fin n,
        (∑ a : Fin n, U i a * (∑ b : Fin n, Sigma a b * V j b)) * x j)
        =
          ∑ j : Fin n, ∑ a : Fin n,
            U i a * ((∑ b : Fin n, Sigma a b * V j b) * x j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            ring
    _ =
          ∑ a : Fin n, ∑ j : Fin n,
            U i a * ((∑ b : Fin n, Sigma a b * V j b) * x j) := by
            rw [Finset.sum_comm]
    _ =
          ∑ a : Fin n,
            U i a *
              (∑ j : Fin n, (∑ b : Fin n, Sigma a b * V j b) * x j) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
    _ =
          ∑ a : Fin n,
            U i a *
              (∑ b : Fin n, Sigma a b *
                ∑ j : Fin n, V j b * x j) := by
            apply Finset.sum_congr rfl
            intro a _
            congr 1
            calc
              (∑ j : Fin n, (∑ b : Fin n, Sigma a b * V j b) * x j)
                  =
                    ∑ j : Fin n, ∑ b : Fin n,
                      (Sigma a b * V j b) * x j := by
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [Finset.sum_mul]
                  _ =
                    ∑ b : Fin n, ∑ j : Fin n,
                      (Sigma a b * V j b) * x j := by
                      rw [Finset.sum_comm]
                  _ =
                    ∑ b : Fin n, Sigma a b *
                      ∑ j : Fin n, V j b * x j := by
                      apply Finset.sum_congr rfl
                      intro b _
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro j _
                      ring

/-- Exact right-orthogonal transport preserves Euclidean inner products after
multiplication by `V^T`. -/
theorem inner_matTranspose_mulVec_eq_of_isOrthogonal {n : ℕ}
    (V : Fin n → Fin n → ℝ) (hV : IsOrthogonal n V)
    (x y : Fin n → ℝ) :
    inner ℝ
        (WithLp.toLp 2 (matMulVec n (matTranspose V) x) :
          EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 (matMulVec n (matTranspose V) y) :
          EuclideanSpace ℝ (Fin n)) =
      inner ℝ
        (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n)) := by
  have hsum :
      (∑ i : Fin n,
          (∑ j : Fin n, V j i * y j) *
            (∑ k : Fin n, V k i * x k)) =
        ∑ j : Fin n, y j * x j := by
    calc
      (∑ i : Fin n,
          (∑ j : Fin n, V j i * y j) *
            (∑ k : Fin n, V k i * x k))
          =
            ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
              (V j i * V k i) * (y j * x k) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ =
            ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n,
              (V j i * V k i) * (y j * x k) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_comm]
      _ =
            ∑ j : Fin n, ∑ k : Fin n,
              (∑ i : Fin n, V j i * V k i) * (y j * x k) := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            rw [← Finset.sum_mul]
      _ = ∑ j : Fin n, y j * x j := by
            simp [hV.row_orthonormal, Finset.sum_ite_eq, Finset.mem_univ]
  simpa [PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply,
    matMulVec, matTranspose] using hsum

/-- Exact right-orthogonal transport sends an orthonormal Euclidean frame to
another orthonormal frame via multiplication by `V^T`. -/
theorem orthonormal_matTranspose_mulVec_of_isOrthogonal {n q : ℕ}
    (V : Fin n → Fin n → ℝ) (hV : IsOrthogonal n V)
    (x : Fin q → EuclideanSpace ℝ (Fin n))
    (hx : Orthonormal ℝ x) :
    Orthonormal ℝ
      (fun c : Fin q =>
        (WithLp.toLp 2
          (matMulVec n (matTranspose V)
            (fun j : Fin n =>
              (x c : EuclideanSpace ℝ (Fin n)) j)) :
          EuclideanSpace ℝ (Fin n))) := by
  rw [orthonormal_iff_ite] at hx ⊢
  intro c d
  have hinner :=
    inner_matTranspose_mulVec_eq_of_isOrthogonal V hV
      (fun j : Fin n => (x c : EuclideanSpace ℝ (Fin n)) j)
      (fun j : Fin n => (x d : EuclideanSpace ℝ (Fin n)) j)
  simpa using hinner.trans (hx c d)

/-- For an exact source factor `U diag(sigma) V^T`, exact left
column-orthonormality of `U` identifies the source action energy with the
diagonal action energy after right-basis transport by `V^T`. -/
theorem vecNorm2Sq_sourceSVDFactorMatrix_eq_diagonal_transpose_action {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (sigma : Fin n → ℝ)
    (V : Fin n → Fin n → ℝ)
    (hU :
      ∀ a b : Fin n, (∑ i : Fin m, U i a * U i b) = idMatrix n a b)
    (x : Fin n → ℝ) :
    vecNorm2Sq
        (rectMatMulVec
          (sourceSVDFactorMatrix U
            (fun i j : Fin n => if i = j then sigma i else 0) V) x) =
      vecNorm2Sq
        (rectMatMulVec
          (fun i j : Fin n => if i = j then sigma i else 0)
          (matMulVec n (matTranspose V) x)) := by
  let y : Fin n → ℝ := matMulVec n (matTranspose V) x
  let z : Fin n → ℝ :=
    matMulVec n (fun i j : Fin n => if i = j then sigma i else 0) y
  have hleft :
      vecNorm2Sq (fun i : Fin m => ∑ a : Fin n, U i a * z a) =
        vecNorm2Sq z :=
    vecNorm2Sq_leftOrthonormalFactor U z hU
  rw [rectMatMulVec_sourceSVDFactorMatrix U
    (fun i j : Fin n => if i = j then sigma i else 0) V x]
  simpa [y, z, matMulVec, rectMatMulVec] using hleft

/-- Exact source-factor transport for the ordered diagonal source-side
tail-energy theorem.  The right orthogonal table transports the probe frame,
the left column-orthonormal table preserves the squared source action, and
LR.1dn supplies the ordered diagonal lower bound.

This remains exact-object source-factor infrastructure only: it does not
construct an SVD/source split, prove Eckart--Young optimality, derive
randomness, or certify computed SVD/singular-vector/projector/Gram/sketch/
product routines.  Sampling probabilities and laws remain exact mathematical
inputs by convention. -/
theorem sum_vecNorm2Sq_sourceSVDFactorMatrix_ge_tail_sq_of_orthonormal_antitone
    {m r q : ℕ}
    (U : Fin m → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (V : Fin (r + q) → Fin (r + q) → ℝ)
    (x : Fin q → EuclideanSpace ℝ (Fin (r + q)))
    (hU :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, U i a * U i b) = idMatrix (r + q) a b)
    (hV : IsOrthogonal (r + q) V)
    (hx : Orthonormal ℝ x)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (sourceSVDFactorMatrix U
              (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
            (fun j : Fin (r + q) =>
      (x c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
  let y : Fin q → EuclideanSpace ℝ (Fin (r + q)) :=
    fun c : Fin q =>
      (WithLp.toLp 2
        (matMulVec (r + q) (matTranspose V)
          (fun j : Fin (r + q) =>
            (x c : EuclideanSpace ℝ (Fin (r + q))) j)) :
        EuclideanSpace ℝ (Fin (r + q)))
  have hy : Orthonormal ℝ y := by
    simpa [y] using
      orthonormal_matTranspose_mulVec_of_isOrthogonal V hV x hx
  have hdiag :=
    sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_antitone
      sigma y hy hmono
  have hsum_eq :
      (∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin (r + q) => if i = j then sigma i else 0)
            (fun j : Fin (r + q) =>
              (y c : EuclideanSpace ℝ (Fin (r + q))) j))) =
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (sourceSVDFactorMatrix U
              (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
    apply Finset.sum_congr rfl
    intro c _
    have h :=
      vecNorm2Sq_sourceSVDFactorMatrix_eq_diagonal_transpose_action
        U sigma V hU
        (fun j : Fin (r + q) =>
      (x c : EuclideanSpace ℝ (Fin (r + q))) j)
    simpa [y] using h.symm
  simpa [hsum_eq] using hdiag

/-- Exact q-dimensional Eckart--Young lower-bound bridge for supplied ordered
source-factor data, squared form.

For every exact rank-at-most-`r` competitor, LR.1dj selects an orthonormal
right-kernel probe family.  LR.1do lower-bounds the source action on that same
family by the displayed ordered tail-square sum, while LR.1dj upper-bounds it
by the competitor residual Frobenius square.

This is exact-object infrastructure only: rectangular SVD/source-split
construction, randomness, and computed non-probability SVD/projector/Gram/
sketch/product certificates remain separate obligations. -/
theorem rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_antitone
    {m r q : ℕ}
    (U : Fin m → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (V : Fin (r + q) → Fin (r + q) → ℝ)
    (hU :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, U i a * U i b) = idMatrix (r + q) a b)
    (hV : IsOrthogonal (r + q) V)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (B : Fin m → Fin (r + q) → ℝ)
    (hB : RectRankAtMost m (r + q) r B) :
    (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      (lowRankResidualFrob
        (sourceSVDFactorMatrix U
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
        B) ^ 2 := by
  rcases hB with ⟨fac⟩
  let A : Fin m → Fin (r + q) → ℝ :=
    sourceSVDFactorMatrix U
      (fun i j : Fin (r + q) => if i = j then sigma i else 0) V
  rcases rectRankFactorization_exists_orthonormalRightKernelFamily_energy_le
      (A := A) fac with
    ⟨x, hx, _hzero, henergy⟩
  let xAmb : Fin q → EuclideanSpace ℝ (Fin (r + q)) :=
    fun c : Fin q => (x c : EuclideanSpace ℝ (Fin (r + q)))
  have hxAmb : Orthonormal ℝ xAmb := by
    rw [orthonormal_iff_ite] at hx ⊢
    intro c d
    have h := hx c d
    simpa [xAmb, Submodule.coe_inner] using h
  have hsource :
      (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
        ∑ c : Fin q,
          vecNorm2Sq
            (rectMatMulVec A
              (fun j : Fin (r + q) =>
                (xAmb c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
    simpa [A, xAmb] using
      sum_vecNorm2Sq_sourceSVDFactorMatrix_ge_tail_sq_of_orthonormal_antitone
        U sigma V xAmb hU hV hxAmb hmono
  have hsq :
      (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
        frobNormSqRect (fun i j => A i j - B i j) :=
    le_trans hsource henergy
  rw [lowRankResidualFrob, frobNormRect_sq]
  exact hsq

/-- Exact source-factor transport for the head-tail gap version of the
ordered diagonal tail-energy theorem.

Unlike the antitone source-factor theorem, this statement only requires a
visible gap `eta`: every head square is at least `eta`, and every tail square
is at most `eta`.  This is the right exact-object shape for constructed
ordered top-`k` splits whose complement-tail enumeration is not itself sorted
by singular value.  It does not construct an SVD/source split, derive
randomness, or certify computed non-probability SVD/projector/Gram/sketch/
product routines. Sampling probabilities and laws remain exact mathematical
inputs by convention. -/
theorem sum_vecNorm2Sq_sourceSVDFactorMatrix_ge_tail_sq_of_orthonormal_gap
    {m r q : ℕ}
    (U : Fin m → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (V : Fin (r + q) → Fin (r + q) → ℝ)
    {eta : ℝ}
    (x : Fin q → EuclideanSpace ℝ (Fin (r + q)))
    (hU :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, U i a * U i b) = idMatrix (r + q) a b)
    (hV : IsOrthogonal (r + q) V)
    (hx : Orthonormal ℝ x)
    (hhead : ∀ a : Fin r, eta ≤ sigma (Fin.castAdd q a) ^ 2)
    (htail : ∀ c : Fin q, sigma (Fin.natAdd r c) ^ 2 ≤ eta) :
    (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (sourceSVDFactorMatrix U
              (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
  let y : Fin q → EuclideanSpace ℝ (Fin (r + q)) :=
    fun c : Fin q =>
      (WithLp.toLp 2
        (matMulVec (r + q) (matTranspose V)
          (fun j : Fin (r + q) =>
            (x c : EuclideanSpace ℝ (Fin (r + q))) j)) :
        EuclideanSpace ℝ (Fin (r + q)))
  have hy : Orthonormal ℝ y := by
    simpa [y] using
      orthonormal_matTranspose_mulVec_of_isOrthogonal V hV x hx
  have hdiag :=
    sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_gap
      sigma y hy hhead htail
  have hsum_eq :
      (∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin (r + q) => if i = j then sigma i else 0)
            (fun j : Fin (r + q) =>
              (y c : EuclideanSpace ℝ (Fin (r + q))) j))) =
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (sourceSVDFactorMatrix U
              (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
    apply Finset.sum_congr rfl
    intro c _
    have h :=
      vecNorm2Sq_sourceSVDFactorMatrix_eq_diagonal_transpose_action
        U sigma V hU
        (fun j : Fin (r + q) =>
          (x c : EuclideanSpace ℝ (Fin (r + q))) j)
    simpa [y] using h.symm
  simpa [hsum_eq] using hdiag

/-- Exact q-dimensional Eckart--Young lower-bound bridge for supplied
source-factor data under a visible head-tail gap, squared form.

This is the gap-based companion to
`rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_antitone`.
It is exact-object lower-bound infrastructure only; the gap must still be
instantiated by a source theorem, and computed non-probability routines remain
separate obligations. -/
theorem rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_gap
    {m r q : ℕ}
    (U : Fin m → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (V : Fin (r + q) → Fin (r + q) → ℝ)
    {eta : ℝ}
    (hU :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, U i a * U i b) = idMatrix (r + q) a b)
    (hV : IsOrthogonal (r + q) V)
    (hhead : ∀ a : Fin r, eta ≤ sigma (Fin.castAdd q a) ^ 2)
    (htail : ∀ c : Fin q, sigma (Fin.natAdd r c) ^ 2 ≤ eta)
    (B : Fin m → Fin (r + q) → ℝ)
    (hB : RectRankAtMost m (r + q) r B) :
    (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      (lowRankResidualFrob
        (sourceSVDFactorMatrix U
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
        B) ^ 2 := by
  rcases hB with ⟨fac⟩
  let A : Fin m → Fin (r + q) → ℝ :=
    sourceSVDFactorMatrix U
      (fun i j : Fin (r + q) => if i = j then sigma i else 0) V
  rcases rectRankFactorization_exists_orthonormalRightKernelFamily_energy_le
      (A := A) fac with
    ⟨x, hx, _hzero, henergy⟩
  let xAmb : Fin q → EuclideanSpace ℝ (Fin (r + q)) :=
    fun c : Fin q => (x c : EuclideanSpace ℝ (Fin (r + q)))
  have hxAmb : Orthonormal ℝ xAmb := by
    rw [orthonormal_iff_ite] at hx ⊢
    intro c d
    have h := hx c d
    simpa [xAmb, Submodule.coe_inner] using h
  have hsource :
      (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
        ∑ c : Fin q,
          vecNorm2Sq
            (rectMatMulVec A
              (fun j : Fin (r + q) =>
                (xAmb c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
    simpa [A, xAmb] using
      sum_vecNorm2Sq_sourceSVDFactorMatrix_ge_tail_sq_of_orthonormal_gap
        U sigma V xAmb hU hV hxAmb hhead htail
  have hsq :
      (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
        frobNormSqRect (fun i j => A i j - B i j) :=
    le_trans hsource henergy
  rw [lowRankResidualFrob, frobNormRect_sq]
  exact hsq

/-- Square-root norm form of
`rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_gap`. -/
theorem sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_gap
    {m r q : ℕ}
    (U : Fin m → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (V : Fin (r + q) → Fin (r + q) → ℝ)
    {eta : ℝ}
    (hU :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, U i a * U i b) = idMatrix (r + q) a b)
    (hV : IsOrthogonal (r + q) V)
    (hhead : ∀ a : Fin r, eta ≤ sigma (Fin.castAdd q a) ^ 2)
    (htail : ∀ c : Fin q, sigma (Fin.natAdd r c) ^ 2 ≤ eta)
    (B : Fin m → Fin (r + q) → ℝ)
    (hB : RectRankAtMost m (r + q) r B) :
    Real.sqrt (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      lowRankResidualFrob
        (sourceSVDFactorMatrix U
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
        B := by
  let A : Fin m → Fin (r + q) → ℝ :=
    sourceSVDFactorMatrix U
      (fun i j : Fin (r + q) => if i = j then sigma i else 0) V
  have hsq :=
    rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_gap
      U sigma V hU hV hhead htail B hB
  calc
    Real.sqrt (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2)
        ≤ Real.sqrt ((lowRankResidualFrob A B) ^ 2) :=
          Real.sqrt_le_sqrt (by simpa [A] using hsq)
    _ = lowRankResidualFrob A B := by
          rw [Real.sqrt_sq_eq_abs]
          exact abs_of_nonneg (frobNormRect_nonneg _)

/-- Square-root norm form of
`rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_antitone`. -/
theorem sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_antitone
    {m r q : ℕ}
    (U : Fin m → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (V : Fin (r + q) → Fin (r + q) → ℝ)
    (hU :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, U i a * U i b) = idMatrix (r + q) a b)
    (hV : IsOrthogonal (r + q) V)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (B : Fin m → Fin (r + q) → ℝ)
    (hB : RectRankAtMost m (r + q) r B) :
    Real.sqrt (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      lowRankResidualFrob
        (sourceSVDFactorMatrix U
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
        B := by
  let A : Fin m → Fin (r + q) → ℝ :=
    sourceSVDFactorMatrix U
      (fun i j : Fin (r + q) => if i = j then sigma i else 0) V
  have hsq :=
    rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_antitone
      U sigma V hU hV hmono B hB
  calc
    Real.sqrt (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2)
        ≤ Real.sqrt ((lowRankResidualFrob A B) ^ 2) :=
          Real.sqrt_le_sqrt (by simpa [A] using hsq)
    _ = lowRankResidualFrob A B := by
          rw [Real.sqrt_sq_eq_abs]
          exact abs_of_nonneg (frobNormRect_nonneg _)

/-- Diagonal source-block vector-action lower bound.  If `U` has exact
orthonormal columns, `V` is exact square orthogonal, and the diagonal entries of
`Sigma` are all at least a nonnegative `sigma`, then the exact source factor
`U Sigma V^T` supplies the vector-action hypothesis needed by LR.1cz.

This is exact-object spectral infrastructure only; it does not certify computed
SVD/singular-vector/diagonal routines, and sampling probabilities/laws remain
exact mathematical inputs by convention. -/
theorem sourceSVDFactorMatrix_diagonal_vector_action_lower_bound {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (Sigma : Fin n → Fin n → ℝ)
    (sigmaDiag : Fin n → ℝ) (V : Fin n → Fin n → ℝ) {sigma : ℝ}
    (hU :
      ∀ a b : Fin n, (∑ i : Fin m, U i a * U i b) = idMatrix n a b)
    (hV : IsOrthogonal n V)
    (hSigma : ∀ a b, Sigma a b = if a = b then sigmaDiag a else 0)
    (hsigma_nonneg : 0 ≤ sigma)
    (hdiag : ∀ a, sigma ≤ sigmaDiag a)
    (x : Fin n → ℝ) :
    sigma * vecNorm2 x ≤
      vecNorm2 (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x) := by
  let y : Fin n → ℝ := matMulVec n (matTranspose V) x
  let z : Fin n → ℝ := matMulVec n Sigma y
  have hleft :
      vecNorm2Sq (fun i : Fin m => ∑ a : Fin n, U i a * z a) =
        vecNorm2Sq z :=
    vecNorm2Sq_leftOrthonormalFactor U z hU
  have hdiag_lower :
      sigma ^ 2 * vecNorm2Sq y ≤ vecNorm2Sq z := by
    simpa [z] using
      vecNorm2Sq_diagonal_lower_bound Sigma sigmaDiag hSigma
        hsigma_nonneg hdiag y
  have hy_norm : vecNorm2Sq y = vecNorm2Sq x := by
    simpa [y] using
      vecNorm2Sq_orthogonal (matTranspose V) x hV.transpose
  have hsq_source :
      vecNorm2Sq (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x) =
        vecNorm2Sq z := by
    rw [rectMatMulVec_sourceSVDFactorMatrix U Sigma V x]
    simpa [z] using hleft
  have hsq :
      sigma ^ 2 * vecNorm2Sq x ≤
        vecNorm2Sq (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x) := by
    calc
      sigma ^ 2 * vecNorm2Sq x
          = sigma ^ 2 * vecNorm2Sq y := by rw [hy_norm]
      _ ≤ vecNorm2Sq z := hdiag_lower
      _ = vecNorm2Sq (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x) :=
          hsq_source.symm
  have hsq_norm :
      (sigma * vecNorm2 x) ^ 2 ≤
        (vecNorm2 (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x)) ^ 2 := by
    calc
      (sigma * vecNorm2 x) ^ 2
          = sigma ^ 2 * vecNorm2Sq x := by
              rw [mul_pow, vecNorm2_sq]
      _ ≤ vecNorm2Sq (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x) := hsq
      _ =
          (vecNorm2 (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x)) ^ 2 := by
          rw [vecNorm2_sq]
  have hleft_nonneg : 0 ≤ sigma * vecNorm2 x :=
    mul_nonneg hsigma_nonneg (vecNorm2_nonneg x)
  have hright_nonneg :
      0 ≤ vecNorm2 (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x) :=
    vecNorm2_nonneg _
  have habs := (sq_le_sq).mp hsq_norm
  simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs

/-- Supplied exact square SVD-style diagonal data instantiate the generic
diagonal source-block vector-action lower bound.  Every displayed singular
entry is assumed to be at least the nonnegative lower radius `sigma`.

This is exact-object spectral infrastructure only; it does not construct or
certify computed singular vectors, singular values, or source products. -/
theorem squareSVD_diagonal_vector_action_lower_bound {n : ℕ}
    (Ufull Vfull : Fin n → Fin n → ℝ) (sigmaVals : Fin n → ℝ)
    {sigma : ℝ}
    (hU : IsOrthogonal n Ufull)
    (hV : IsOrthogonal n Vfull)
    (hsigma_nonneg : 0 ≤ sigma)
    (hdiag : ∀ a : Fin n, sigma ≤ sigmaVals a)
    (x : Fin n → ℝ) :
    sigma * vecNorm2 x ≤
      vecNorm2
        (rectMatMulVec
          (sourceSVDFactorMatrix Ufull
            (fun a b => if a = b then sigmaVals a else 0) Vfull) x) :=
  sourceSVDFactorMatrix_diagonal_vector_action_lower_bound
    Ufull (fun a b => if a = b then sigmaVals a else 0) sigmaVals Vfull
    (by
      intro a b
      exact hU.col_orthonormal a b)
    hV
    (by
      intro a b
      rfl)
    hsigma_nonneg hdiag x

/-- Supplied exact thin-rectangular SVD-style diagonal data instantiate the
generic diagonal source-block vector-action lower bound.  The left table is
rectangular and is supplied by an exact column-orthonormality certificate; the
right table remains square orthogonal.

This is exact-object spectral infrastructure only; computed non-probability
SVD/singular-vector/product routines remain separate obligations. -/
theorem rectangularThinSVD_diagonal_vector_action_lower_bound {m n : ℕ}
    (Ufull : Fin m → Fin n → ℝ) (Vfull : Fin n → Fin n → ℝ)
    (sigmaVals : Fin n → ℝ) {sigma : ℝ}
    (hUcols :
      ∀ a b : Fin n,
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal n Vfull)
    (hsigma_nonneg : 0 ≤ sigma)
    (hdiag : ∀ a : Fin n, sigma ≤ sigmaVals a)
    (x : Fin n → ℝ) :
    sigma * vecNorm2 x ≤
      vecNorm2
        (rectMatMulVec
          (sourceSVDFactorMatrix Ufull
            (fun a b => if a = b then sigmaVals a else 0) Vfull) x) :=
  sourceSVDFactorMatrix_diagonal_vector_action_lower_bound
    Ufull (fun a b => if a = b then sigmaVals a else 0) sigmaVals Vfull
    (by
      intro a b
      simpa [idMatrix] using hUcols a b)
    hV
    (by
      intro a b
      rfl)
    hsigma_nonneg hdiag x

/-- Square supplied-SVD residual lower bound on an `(r+1)` source block.  The
diagonal lower-action theorem supplies the vector hypothesis in the LR.1cz
rank-nullity/min-max adapter. -/
theorem rectRankAtMost_lowRankResidualFrob_ge_of_squareSVD_diagonal_succ
    {r : ℕ}
    (Ufull Vfull : Fin (r + 1) → Fin (r + 1) → ℝ)
    (sigmaVals : Fin (r + 1) → ℝ) {sigma : ℝ}
    (hU : IsOrthogonal (r + 1) Ufull)
    (hV : IsOrthogonal (r + 1) Vfull)
    (hsigma_nonneg : 0 ≤ sigma)
    (hdiag : ∀ a : Fin (r + 1), sigma ≤ sigmaVals a)
    (B : Fin (r + 1) → Fin (r + 1) → ℝ)
    (hB : RectRankAtMost (r + 1) (r + 1) r B) :
    sigma ≤
      lowRankResidualFrob
        (sourceSVDFactorMatrix Ufull
          (fun a b => if a = b then sigmaVals a else 0) Vfull) B :=
  rectRankAtMost_lowRankResidualFrob_ge_of_vector_lower_bound_succ
    (sourceSVDFactorMatrix Ufull
      (fun a b => if a = b then sigmaVals a else 0) Vfull)
    B hB
    (by
      intro x _hx
      exact
        squareSVD_diagonal_vector_action_lower_bound Ufull Vfull
          sigmaVals hU hV hsigma_nonneg hdiag x)

/-- Thin-rectangular supplied-SVD residual lower bound on an `(r+1)` source
block.  This exact-object wrapper charges no floating-point probability
construction and does not certify computed singular-vector routines. -/
theorem rectRankAtMost_lowRankResidualFrob_ge_of_rectangularThinSVD_diagonal_succ
    {m r : ℕ}
    (Ufull : Fin m → Fin (r + 1) → ℝ)
    (Vfull : Fin (r + 1) → Fin (r + 1) → ℝ)
    (sigmaVals : Fin (r + 1) → ℝ) {sigma : ℝ}
    (hUcols :
      ∀ a b : Fin (r + 1),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + 1) Vfull)
    (hsigma_nonneg : 0 ≤ sigma)
    (hdiag : ∀ a : Fin (r + 1), sigma ≤ sigmaVals a)
    (B : Fin m → Fin (r + 1) → ℝ)
    (hB : RectRankAtMost m (r + 1) r B) :
    sigma ≤
      lowRankResidualFrob
        (sourceSVDFactorMatrix Ufull
          (fun a b => if a = b then sigmaVals a else 0) Vfull) B :=
  rectRankAtMost_lowRankResidualFrob_ge_of_vector_lower_bound_succ
    (sourceSVDFactorMatrix Ufull
      (fun a b => if a = b then sigmaVals a else 0) Vfull)
    B hB
    (by
      intro x _hx
      exact
        rectangularThinSVD_diagonal_vector_action_lower_bound Ufull Vfull
          sigmaVals hUcols hV hsigma_nonneg hdiag x)

/-- The constructed ordered top-`r+1` right-Gram head block instantiates the
one-block min-max residual lower bound.  If the last selected ordered singular
value is positive, every displayed selected diagonal entry dominates it, so any
rank-at-most-`r` competitor on those displayed coordinates has Frobenius
residual at least that last selected value.

This is exact-object spectral infrastructure only.  It uses the exact
right-Gram singular data as analysis objects and does not certify a computed
SVD/singular-vector/projector/Gram/sketch/product routine. -/
theorem rectRankAtMost_lowRankResidualFrob_ge_of_rectRightGramOrderedHeadDiagonal_succ
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : r + 1 ≤ n)
    (hlast :
      0 < rectSingularValue A
        (rectTopIndex hk (rectTopLastIndex (Nat.succ_pos r))))
    (B : Fin m → Fin (r + 1) → ℝ)
    (hB : RectRankAtMost m (r + 1) r B) :
    rectSingularValue A
        (rectTopIndex hk (rectTopLastIndex (Nat.succ_pos r))) ≤
      lowRankResidualFrob
        (sourceSVDFactorMatrix
          (rectRightGramOrderedHeadLeft A hk)
          (rectRightGramOrderedHeadSingularDiagonal A hk)
          (idMatrix (r + 1))) B := by
  classical
  let sigma :=
    rectSingularValue A
      (rectTopIndex hk (rectTopLastIndex (Nat.succ_pos r)))
  let sigmaVals : Fin (r + 1) → ℝ :=
    fun a => rectRightGramBasisSingularValue A
      (rectRightGramOrderedTopEmbedding hk a)
  have hUcols :
      ∀ a b : Fin (r + 1),
        (∑ i : Fin m,
          rectRightGramOrderedHeadLeft A hk i a *
            rectRightGramOrderedHeadLeft A hk i b) =
          if a = b then 1 else 0 := by
    intro a b
    simpa [idMatrix] using
      rectRightGramOrderedHeadLeft_col_orthonormal_of_last_pos
        A hk (Nat.succ_pos r) hlast a b
  have hsigma_nonneg : 0 ≤ sigma := by
    exact rectSingularValue_nonneg A _
  have hdiag : ∀ a : Fin (r + 1), sigma ≤ sigmaVals a := by
    intro a
    change sigma ≤
      rectRightGramBasisSingularValue A (rectRightGramOrderedTopEmbedding hk a)
    rw [(rectRightGramOrderedTopEmbedding_certificate A hk).singularValue_eq a]
    simpa [sigma] using
      rectSingularValue_antitone A
        (rectTopIndex_le_last hk (Nat.succ_pos r) a)
  have hthin :=
    rectRankAtMost_lowRankResidualFrob_ge_of_rectangularThinSVD_diagonal_succ
      (rectRightGramOrderedHeadLeft A hk)
      (idMatrix (r + 1))
      sigmaVals
      hUcols
      (IsOrthogonal.id (r + 1))
      hsigma_nonneg
      hdiag
      B hB
  simpa [sigma, sigmaVals, rectRightGramOrderedHeadSingularDiagonal] using hthin

/-- Expanding the ordered top-`k` source factor gives the displayed selected
right-Gram SVD terms in the constructed embedding order. -/
theorem sourceSVDFactorMatrix_rectRightGramOrderedHead_entry
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (i : Fin m) (j : Fin n) :
    sourceSVDFactorMatrix
        (rectRightGramOrderedHeadLeft A hk)
        (rectRightGramOrderedHeadSingularDiagonal A hk)
        (rectRightGramOrderedHeadRight A hk) i j =
      ∑ a : Fin k,
        rectRightGramLeftSingularZeroSafe A i
            (rectRightGramOrderedTopEmbedding hk a) *
          rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk a) *
          rectRightGramEigenbasis A j
            (rectRightGramOrderedTopEmbedding hk a) := by
  unfold sourceSVDFactorMatrix rectRightGramOrderedHeadLeft
    rectRightGramOrderedHeadSingularDiagonal rectRightGramOrderedHeadRight
  apply Finset.sum_congr rfl
  intro a _
  simp [Finset.mem_univ]
  ring

/-- The selected right-Gram head induced by the constructed ordered top-`k`
embedding is exactly the ordered source factor `U_ord Sigma_ord V_ord^T`.
This closes the exact ordered source-head factorization step, not the
complementary tail factor or Eckart--Young optimality. -/
theorem rectRightGramBasisSVDHead_orderedTopEmbedding_eq_sourceSVDFactorMatrix
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (i : Fin m) (j : Fin n) :
    rectRightGramBasisSVDHead A
        (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))
        i j =
      sourceSVDFactorMatrix
        (rectRightGramOrderedHeadLeft A hk)
        (rectRightGramOrderedHeadSingularDiagonal A hk)
        (rectRightGramOrderedHeadRight A hk) i j := by
  classical
  rw [sourceSVDFactorMatrix_rectRightGramOrderedHead_entry]
  unfold rectRightGramBasisSVDHead rectRightGramSelectedIndexSet
  rw [Finset.sum_map]

/-- Expanding the complement-tail source factor gives the displayed
basis-indexed SVD terms in the complement enumeration order. -/
theorem sourceSVDFactorMatrix_rectRightGramBasisSVDTail_entry
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (i : Fin m) (j : Fin n) :
    sourceSVDFactorMatrix
        (rectRightGramBasisSVDTailLeft A s)
        (rectRightGramBasisSVDTailSingularDiagonal A s)
        (rectRightGramBasisSVDTailRight A s) i j =
      ∑ a : Fin ((sᶜ).card),
        rectRightGramLeftSingularZeroSafe A i
            ((sᶜ).orderEmbOfFin rfl a) *
          rectRightGramBasisSingularValue A
            ((sᶜ).orderEmbOfFin rfl a) *
          rectRightGramEigenbasis A j
            ((sᶜ).orderEmbOfFin rfl a) := by
  unfold sourceSVDFactorMatrix rectRightGramBasisSVDTailLeft
    rectRightGramBasisSVDTailSingularDiagonal rectRightGramBasisSVDTailRight
  apply Finset.sum_congr rfl
  intro a _
  simp [Finset.mem_univ]
  ring

/-- The complementary right-Gram tail for any selected finite index set is
exactly the source factor `U_tail Sigma_tail V_tail^T` obtained by enumerating
the complement.  This is exact analysis-object algebra; it does not assert that
the zero-safe tail-left table is an orthonormal SVD tail basis. -/
theorem rectRightGramBasisSVDTail_eq_sourceSVDFactorMatrix
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (i : Fin m) (j : Fin n) :
    rectRightGramBasisSVDTail A s i j =
      sourceSVDFactorMatrix
        (rectRightGramBasisSVDTailLeft A s)
        (rectRightGramBasisSVDTailSingularDiagonal A s)
        (rectRightGramBasisSVDTailRight A s) i j := by
  classical
  rw [sourceSVDFactorMatrix_rectRightGramBasisSVDTail_entry]
  unfold rectRightGramBasisSVDTail
  let e : Fin ((sᶜ).card) → Fin n := fun a => (sᶜ).orderEmbOfFin rfl a
  let term : Fin n → ℝ :=
    fun a =>
      rectRightGramLeftSingularZeroSafe A i a *
        rectRightGramBasisSingularValue A a *
        rectRightGramEigenbasis A j a
  have hsum :
      (sᶜ).sum term = ∑ a : Fin ((sᶜ).card), term (e a) := by
    have hsub :
        (∑ a : Fin ((sᶜ).card), term (e a)) =
          ∑ x : {x // x ∈ (sᶜ)}, term x := by
      refine Fintype.sum_equiv ((sᶜ).orderIsoOfFin rfl).toEquiv
        (fun a : Fin ((sᶜ).card) => term (e a))
        (fun x : {x // x ∈ (sᶜ)} => term x) ?_
      intro a
      simp [e]
    calc
      (sᶜ).sum term = ∑ x : {x // x ∈ (sᶜ)}, term x := by
            simpa using (Finset.sum_coe_sort (sᶜ) term).symm
      _ = ∑ a : Fin ((sᶜ).card), term (e a) := hsub.symm
  rw [show
      (sᶜ).sum (fun a =>
          rectRightGramLeftSingularZeroSafe A i a *
            rectRightGramBasisSingularValue A a *
            rectRightGramEigenbasis A j a) = (sᶜ).sum term by rfl]
  rw [hsum]

/-- A replacement complement-tail left table gives the same source factor as
the zero-safe table if it agrees with the zero-safe table on every nonzero
complement singular direction.  On zero singular directions, the diagonal tail
singular-value block erases the left column. -/
theorem sourceSVDFactorMatrix_rectRightGramBasisSVDTail_replacement_left_entry
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (Utail : Fin m → Fin ((sᶜ).card) → ℝ)
    (hUtail :
      ∀ i a,
        rectRightGramBasisSingularValue A
            ((sᶜ).orderEmbOfFin rfl a) ≠ 0 →
          Utail i a =
            rectRightGramLeftSingularZeroSafe A i
              ((sᶜ).orderEmbOfFin rfl a))
    (i : Fin m) (j : Fin n) :
    sourceSVDFactorMatrix
        Utail
        (rectRightGramBasisSVDTailSingularDiagonal A s)
        (rectRightGramBasisSVDTailRight A s) i j =
      ∑ a : Fin ((sᶜ).card),
        rectRightGramLeftSingularZeroSafe A i
            ((sᶜ).orderEmbOfFin rfl a) *
          rectRightGramBasisSingularValue A
            ((sᶜ).orderEmbOfFin rfl a) *
          rectRightGramEigenbasis A j
            ((sᶜ).orderEmbOfFin rfl a) := by
  unfold sourceSVDFactorMatrix rectRightGramBasisSVDTailSingularDiagonal
    rectRightGramBasisSVDTailRight
  apply Finset.sum_congr rfl
  intro a _
  by_cases hτ :
      rectRightGramBasisSingularValue A
        ((sᶜ).orderEmbOfFin rfl a) = 0
  · simp [hτ]
  · rw [hUtail i a hτ]
    simp
    ring

/-- Replacement-left version of the complement-tail source factorization.  This
is the exact adapter needed by a nullspace-completed tail-left construction:
the replacement table may differ from the zero-safe table only on diagonal-zero
tail singular directions. -/
theorem rectRightGramBasisSVDTail_eq_sourceSVDFactorMatrix_replacement_left
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (Utail : Fin m → Fin ((sᶜ).card) → ℝ)
    (hUtail :
      ∀ i a,
        rectRightGramBasisSingularValue A
            ((sᶜ).orderEmbOfFin rfl a) ≠ 0 →
          Utail i a =
            rectRightGramLeftSingularZeroSafe A i
              ((sᶜ).orderEmbOfFin rfl a))
    (i : Fin m) (j : Fin n) :
    rectRightGramBasisSVDTail A s i j =
      sourceSVDFactorMatrix
        Utail
        (rectRightGramBasisSVDTailSingularDiagonal A s)
        (rectRightGramBasisSVDTailRight A s) i j := by
  calc
    rectRightGramBasisSVDTail A s i j =
        sourceSVDFactorMatrix
          (rectRightGramBasisSVDTailLeft A s)
          (rectRightGramBasisSVDTailSingularDiagonal A s)
          (rectRightGramBasisSVDTailRight A s) i j :=
        rectRightGramBasisSVDTail_eq_sourceSVDFactorMatrix A s i j
    _ =
        ∑ a : Fin ((sᶜ).card),
          rectRightGramLeftSingularZeroSafe A i
              ((sᶜ).orderEmbOfFin rfl a) *
            rectRightGramBasisSingularValue A
              ((sᶜ).orderEmbOfFin rfl a) *
            rectRightGramEigenbasis A j
              ((sᶜ).orderEmbOfFin rfl a) :=
        sourceSVDFactorMatrix_rectRightGramBasisSVDTail_entry A s i j
    _ =
        sourceSVDFactorMatrix
          Utail
          (rectRightGramBasisSVDTailSingularDiagonal A s)
          (rectRightGramBasisSVDTailRight A s) i j :=
        (sourceSVDFactorMatrix_rectRightGramBasisSVDTail_replacement_left_entry
          A s Utail hUtail i j).symm

/-- The ordered top-`k` complementary right-Gram tail is exactly the ordered
complement source factor. -/
theorem rectRightGramBasisSVDTail_orderedTopEmbedding_eq_sourceSVDFactorMatrix
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (i : Fin m) (j : Fin n) :
    rectRightGramBasisSVDTail A
        (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))
        i j =
      sourceSVDFactorMatrix
        (rectRightGramOrderedTailLeft A hk)
        (rectRightGramOrderedTailSingularDiagonal A hk)
        (rectRightGramOrderedTailRight A hk) i j := by
  simpa [rectRightGramOrderedTailLeft, rectRightGramOrderedTailRight,
    rectRightGramOrderedTailSingularDiagonal] using
    rectRightGramBasisSVDTail_eq_sourceSVDFactorMatrix A
      (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)) i j

/-- The constructed ordered right-Gram source head plus the ordered complement
source tail reconstructs `A` entrywise.  This closes only the exact source-split
algebra; orthonormal tail-left completion and Eckart--Young optimality remain
separate D3 obligations. -/
theorem rectRightGramOrdered_source_head_add_tail
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (i : Fin m) (j : Fin n) :
    sourceSVDFactorMatrix
        (rectRightGramOrderedHeadLeft A hk)
        (rectRightGramOrderedHeadSingularDiagonal A hk)
        (rectRightGramOrderedHeadRight A hk) i j +
      sourceSVDFactorMatrix
        (rectRightGramOrderedTailLeft A hk)
        (rectRightGramOrderedTailSingularDiagonal A hk)
        (rectRightGramOrderedTailRight A hk) i j =
      A i j := by
  rw [← rectRightGramBasisSVDHead_orderedTopEmbedding_eq_sourceSVDFactorMatrix
      A hk i j,
    ← rectRightGramBasisSVDTail_orderedTopEmbedding_eq_sourceSVDFactorMatrix
      A hk i j]
  exact
    rectRightGramBasisSVD_head_add_tail A
      (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)) i j

/-- Ordered source split with a replacement complement-tail left table.  The
replacement table must agree with the constructed zero-safe tail-left table on
nonzero complement singular directions; zero complement directions are erased
by the diagonal tail singular-value block. -/
theorem rectRightGramOrdered_source_head_add_tail_replacement_left
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (Utail :
      Fin m →
        Fin (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ)
    (hUtail :
      ∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c)
    (i : Fin m) (j : Fin n) :
    sourceSVDFactorMatrix
        (rectRightGramOrderedHeadLeft A hk)
        (rectRightGramOrderedHeadSingularDiagonal A hk)
        (rectRightGramOrderedHeadRight A hk) i j +
      sourceSVDFactorMatrix
        Utail
        (rectRightGramOrderedTailSingularDiagonal A hk)
        (rectRightGramOrderedTailRight A hk) i j =
      A i j := by
  rw [← rectRightGramBasisSVDHead_orderedTopEmbedding_eq_sourceSVDFactorMatrix
      A hk i j]
  change
    rectRightGramBasisSVDHead A
          (rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk)) i j +
      sourceSVDFactorMatrix
        Utail
        (rectRightGramBasisSVDTailSingularDiagonal A
          (rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk)))
        (rectRightGramBasisSVDTailRight A
          (rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))) i j =
      A i j
  rw [← rectRightGramBasisSVDTail_eq_sourceSVDFactorMatrix_replacement_left
    A (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))
    Utail ?_ i j]
  exact
    rectRightGramBasisSVD_head_add_tail A
      (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)) i j
  intro i c hτ
  simpa [rectRightGramOrderedTailLeft] using hUtail i c hτ

/-- For an exact source split `A = U Sigma V^T + Tail`, the Frobenius residual
of the displayed source head is exactly the Frobenius norm of the tail.  This is
an exact analysis-object identity; a computed SVD/head/tail routine must supply
its own perturbation certificate before using it implementation-facing. -/
theorem lowRankResidualFrob_sourceSVDFactorMatrix_eq_tail {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j) :
    lowRankResidualFrob A (sourceSVDFactorMatrix U Sigma V) =
      frobNormRect Tail := by
  unfold lowRankResidualFrob
  apply congrArg frobNormRect
  funext i j
  rw [hA i j]
  ring

/-- Norm-generic version of
`lowRankResidualFrob_sourceSVDFactorMatrix_eq_tail`. -/
theorem lowRankResidualNorm_sourceSVDFactorMatrix_eq_tail {m n r : ℕ}
    (ξ : RectNormLike m n)
    (A Tail : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j) :
    lowRankResidualNorm ξ A (sourceSVDFactorMatrix U Sigma V) =
      ξ.norm Tail := by
  unfold lowRankResidualNorm
  apply congrArg ξ.norm
  funext i j
  rw [hA i j]
  ring

/-- If a source split has the supplied Eckart--Young/tail-optimality inequality,
then the displayed source head is a Frobenius best rank-`r` approximation.
The rank side is proved by `sourceSVDFactorMatrix_rankAtMost`; the optimality
inequality remains an explicit source-SVD/Eckart--Young obligation. -/
theorem sourceSVDFactorMatrix_isBestRankApproxFrob_of_tail_optimal {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hopt : ∀ B, RectRankAtMost m n r B →
      frobNormRect Tail ≤ lowRankResidualFrob A B) :
    IsBestRankApproxFrob m n r A (sourceSVDFactorMatrix U Sigma V) where
  rank_le := sourceSVDFactorMatrix_rankAtMost U Sigma V
  optimal := by
    intro B hB
    rw [lowRankResidualFrob_sourceSVDFactorMatrix_eq_tail A Tail U Sigma V hA]
    exact hopt B hB

/-- Norm-generic best-rank certificate from an exact source split and a supplied
tail-optimality inequality for the chosen norm. -/
theorem sourceSVDFactorMatrix_isBestRankApproxNorm_of_tail_optimal {m n r : ℕ}
    (ξ : RectNormLike m n)
    (A Tail : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hopt : ∀ B, RectRankAtMost m n r B →
      ξ.norm Tail ≤ lowRankResidualNorm ξ A B) :
    IsBestRankApproxNorm m n r ξ A (sourceSVDFactorMatrix U Sigma V) where
  rank_le := sourceSVDFactorMatrix_rankAtMost U Sigma V
  optimal := by
    intro B hB
    rw [lowRankResidualNorm_sourceSVDFactorMatrix_eq_tail ξ A Tail U Sigma V hA]
    exact hopt B hB

/-- Exact source cross factor `Vᵀ Z`.  The sampling law for `Z` remains an
exact mathematical input; computing this product is a separate non-probability
FP obligation. -/
noncomputable def rightSketchCrossGram {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin r → Fin r → ℝ :=
  fun a b => ∑ j : Fin n, V j a * Z j b

/-- Exact source sketch right factor `Σ (Vᵀ Z)`. -/
noncomputable def sourceSVDSketchRightFactor {n r : ℕ}
    (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin r → Fin r → ℝ :=
  fun a b => ∑ c : Fin r, Sigma a c * rightSketchCrossGram V Z c b

/-- A displayed diagonal source singular-value block is nonsingular when all
displayed diagonal entries are nonzero.  This is exact source-SVD algebra; a
computed singular-value routine must separately certify its rounded diagonal
entries and any perturbation radius. -/
theorem matrix_det_ne_zero_of_eq_diagonal_nonzero
    {r : ℕ}
    (Sigma : Fin r → Fin r → ℝ) (sigma : Fin r → ℝ)
    (hSigma : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hdiag : ∀ a, sigma a ≠ 0) :
    Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
  have hmat :
      (Sigma : Matrix (Fin r) (Fin r) ℝ) = Matrix.diagonal sigma := by
    ext a b
    rw [hSigma a b]
    simp [Matrix.diagonal_apply]
  rw [hmat, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (by
    intro a _
    exact hdiag a)

/-- Positive displayed diagonal singular values give the determinant
hypothesis consumed by the exact source determinant route. -/
theorem matrix_det_ne_zero_of_eq_diagonal_pos
    {r : ℕ}
    (Sigma : Fin r → Fin r → ℝ) (sigma : Fin r → ℝ)
    (hSigma : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hpos : ∀ a, 0 < sigma a) :
    Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  matrix_det_ne_zero_of_eq_diagonal_nonzero Sigma sigma hSigma
    (by
      intro a
      exact ne_of_gt (hpos a))

/-- Exact source-tail left orthogonality, `U^T Tail = 0`, stated entrywise.
This is an analysis-side SVD split certificate; if an implementation computes
the source basis or tail, those are non-probability computed quantities. -/
def sourceTailLeftOrthogonal {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Tail : Fin m → Fin n → ℝ) : Prop :=
  ∀ a j, ∑ i : Fin m, U i a * Tail i j = 0

/-- A supplied tail SVD-style factorization gives the left source-tail
orthogonality field once the head and tail left bases are cross-orthogonal.
This is exact analysis-side algebra; computed bases or tail factors remain
implementation-facing non-probability obligations. -/
theorem sourceTailLeftOrthogonal_of_tail_factor_left_cross_zero {m n r q : ℕ}
    (U : Fin m → Fin r → ℝ) (Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vtail : Fin n → Fin q → ℝ)
    (hTail : ∀ i j,
      Tail i j = sourceSVDFactorMatrix Utail SigmaTail Vtail i j)
    (hcross : ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0) :
    sourceTailLeftOrthogonal U Tail := by
  intro a j
  calc
    ∑ i : Fin m, U i a * Tail i j =
        ∑ i : Fin m, U i a *
          sourceSVDFactorMatrix Utail SigmaTail Vtail i j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hTail i j]
    _ = ∑ c : Fin q, (∑ b : Fin q, SigmaTail c b * Vtail j b) *
          (∑ i : Fin m, U i a * Utail i c) := by
          unfold sourceSVDFactorMatrix
          calc
            ∑ i : Fin m, U i a *
                (∑ c : Fin q, Utail i c *
                  (∑ b : Fin q, SigmaTail c b * Vtail j b)) =
                ∑ i : Fin m, ∑ c : Fin q,
                  U i a * (Utail i c *
                    (∑ b : Fin q, SigmaTail c b * Vtail j b)) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Finset.mul_sum]
            _ = ∑ c : Fin q, ∑ i : Fin m,
                  U i a * (Utail i c *
                    (∑ b : Fin q, SigmaTail c b * Vtail j b)) := by
                  rw [Finset.sum_comm]
            _ = ∑ c : Fin q, (∑ b : Fin q, SigmaTail c b * Vtail j b) *
                  (∑ i : Fin m, U i a * Utail i c) := by
                  apply Finset.sum_congr rfl
                  intro c _
                  calc
                    ∑ i : Fin m, U i a * (Utail i c *
                        (∑ b : Fin q, SigmaTail c b * Vtail j b)) =
                        ∑ i : Fin m,
                          (∑ b : Fin q, SigmaTail c b * Vtail j b) *
                            (U i a * Utail i c) := by
                          apply Finset.sum_congr rfl
                          intro i _
                          ring
                    _ = (∑ b : Fin q, SigmaTail c b * Vtail j b) *
                        (∑ i : Fin m, U i a * Utail i c) := by
                          rw [Finset.mul_sum]
    _ = 0 := by
          simp [hcross]

/-- First-class exact source-SVD head/tail certificate for the diagonal
equation-(9) route.

This packages the exact analysis-side data that LR.1bm/LR.1bn previously
threaded as separate hypotheses: a source split, a tail factorization, exact
left/right orthogonality and completeness fields, and a diagonal nonsingular
head block. It is deliberately not a rectangular SVD existence theorem and it
does not certify computed singular vectors, singular values, bases, projectors,
Grams, inverses, or products. Those remain implementation-facing
non-probability obligations. Sampling probabilities and laws remain exact
mathematical inputs by project convention. -/
structure DiagonalSourceSVDTailCertificate (m n r q : ℕ)
    (A Tail : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (SigmaHead : Fin r → Fin r → ℝ)
    (sigmaHead : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ) : Prop where
  split :
    ∀ i j, A i j = sourceSVDFactorMatrix U SigmaHead V i j + Tail i j
  tail_factor :
    ∀ i j, Tail i j = sourceSVDFactorMatrix Utail SigmaTail Vperp i j
  Utail_orthonormal :
    ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b
  left_cross :
    ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0
  U_orthonormal :
    ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b
  head_diagonal :
    ∀ a b, SigmaHead a b = if a = b then sigmaHead a else 0
  head_nonzero :
    ∀ a, sigmaHead a ≠ 0
  Vperp_orthonormal :
    ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c
  right_cross_tail :
    ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0
  right_cross_head :
    ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0
  V_orthonormal :
    ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c
  right_complete :
    ∀ j k,
      (∑ c : Fin q, Vperp j c * Vperp k c) +
        (∑ b : Fin r, V j b * V k b) =
      idMatrix n j k

namespace DiagonalSourceSVDTailCertificate

/-- The exact certificate supplies the source-tail left-orthogonality field
consumed by the head-plus-tail sketch-Gram split. -/
theorem sourceTailLeftOrthogonal {m n r q : ℕ}
    {A Tail : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      DiagonalSourceSVDTailCertificate m n r q A Tail U SigmaHead
        sigmaHead V Utail SigmaTail Vperp) :
    sourceTailLeftOrthogonal U Tail :=
  sourceTailLeftOrthogonal_of_tail_factor_left_cross_zero
    U Tail Utail SigmaTail Vperp cert.tail_factor cert.left_cross

/-- A supplied tail-optimality inequality turns the exact diagonal source
certificate into the Frobenius best-rank certificate used by the relative
equation-(9) surfaces. The actual Eckart--Young/singular-value proof of this
inequality remains a separate foundation obligation. -/
theorem isBestRankApproxFrob_of_tail_optimal {m n r q : ℕ}
    {A Tail : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      DiagonalSourceSVDTailCertificate m n r q A Tail U SigmaHead
        sigmaHead V Utail SigmaTail Vperp)
    (hopt : ∀ B, RectRankAtMost m n r B →
      frobNormRect Tail ≤ lowRankResidualFrob A B) :
    IsBestRankApproxFrob m n r A (sourceSVDFactorMatrix U SigmaHead V) :=
  sourceSVDFactorMatrix_isBestRankApproxFrob_of_tail_optimal
    A Tail U SigmaHead V cert.split hopt

end DiagonalSourceSVDTailCertificate

/-- Sketching the exact source head `U Sigma V^T` gives
`U (Sigma (V^T Z))`. -/
theorem columnSketch_sourceSVDFactorMatrix
    {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ) :
    ∀ i a,
      columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a =
        ∑ c : Fin r, U i c * sourceSVDSketchRightFactor Sigma V Z c a := by
  intro i a
  unfold columnSketch preconditionColumns sourceSVDFactorMatrix
    sourceSVDSketchRightFactor rightSketchCrossGram
  calc
    (∑ k : Fin n,
        (∑ c : Fin r, U i c * (∑ d : Fin r, Sigma c d * V k d)) *
          Z k a)
        =
          ∑ k : Fin n, ∑ c : Fin r,
            (U i c * (∑ d : Fin r, Sigma c d * V k d)) * Z k a := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ =
          ∑ c : Fin r, ∑ k : Fin n,
            (U i c * (∑ d : Fin r, Sigma c d * V k d)) * Z k a := by
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ k : Fin n,
                (∑ d : Fin r, Sigma c d * V k d) * Z k a) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ k : Fin n, ∑ d : Fin r,
                (Sigma c d * V k d) * Z k a) := by
            apply Finset.sum_congr rfl
            intro c _
            apply congrArg (fun x => U i c * x)
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ d : Fin r, ∑ k : Fin n,
                (Sigma c d * V k d) * Z k a) := by
            apply Finset.sum_congr rfl
            intro c _
            congr 1
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ d : Fin r,
                Sigma c d * ∑ k : Fin n, V k d * Z k a) := by
            apply Finset.sum_congr rfl
            intro c _
            congr 1
            apply Finset.sum_congr rfl
            intro d _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring

/-- The source head sketch is left-orthogonal to the sketched tail when
`U^T Tail = 0`.  This is the cross-term cancellation needed before proving the
head-plus-tail sketch-Gram determinant route. -/
theorem columnSketch_sourceSVDFactorMatrix_tail_leftOrthogonal
    {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (Tail : Fin m → Fin n → ℝ)
    (hUT : sourceTailLeftOrthogonal U Tail) :
    ∀ a b,
      ∑ i : Fin m,
        columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
          columnSketch Tail Z i b = 0 := by
  intro a b
  have hHead := columnSketch_sourceSVDFactorMatrix U Sigma V Z
  calc
    ∑ i : Fin m,
        columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
          columnSketch Tail Z i b
        =
          ∑ i : Fin m,
            (∑ c : Fin r,
              U i c * sourceSVDSketchRightFactor Sigma V Z c a) *
              (∑ j : Fin n, Tail i j * Z j b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hHead i a]
            rfl
    _ =
          ∑ i : Fin m, ∑ c : Fin r, ∑ j : Fin n,
            (U i c * sourceSVDSketchRightFactor Sigma V Z c a) *
              (Tail i j * Z j b) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
    _ =
          ∑ c : Fin r, ∑ j : Fin n, ∑ i : Fin m,
            (U i c * sourceSVDSketchRightFactor Sigma V Z c a) *
              (Tail i j * Z j b) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r, ∑ j : Fin n,
            (sourceSVDSketchRightFactor Sigma V Z c a * Z j b) *
              (∑ i : Fin m, U i c * Tail i j) := by
            apply Finset.sum_congr rfl
            intro c _
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = 0 := by
            apply Finset.sum_eq_zero
            intro c _
            apply Finset.sum_eq_zero
            intro j _
            rw [hUT c j]
            ring

/-- The sketched tail is left-orthogonal to the source head sketch when
`U^T Tail = 0`; this is the transposed cross-term cancellation. -/
theorem columnSketch_tail_sourceSVDFactorMatrix_leftOrthogonal
    {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (Tail : Fin m → Fin n → ℝ)
    (hUT : sourceTailLeftOrthogonal U Tail) :
    ∀ a b,
      ∑ i : Fin m,
        columnSketch Tail Z i a *
          columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b = 0 := by
  intro a b
  have hcross :=
    columnSketch_sourceSVDFactorMatrix_tail_leftOrthogonal
      U Sigma V Z Tail hUT b a
  calc
    ∑ i : Fin m,
        columnSketch Tail Z i a *
          columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b
        =
          ∑ i : Fin m,
            columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b *
              columnSketch Tail Z i a := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = 0 := hcross

/-- Under the exact source split `A = U Sigma V^T + Tail` and the SVD
orthogonality field `U^T Tail = 0`, the sketch Gram of `A Z` decomposes as the
sum of the source-head sketch Gram and the tail sketch Gram.  This is the first
determinant-route dependency for the head-plus-tail equation (9) proof. -/
theorem columnSketchGram_sourceHeadTail_leftOrthogonal
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hUT : sourceTailLeftOrthogonal U Tail) :
    ∀ a b,
      columnSketchGram A Z a b =
        columnSketchGram (sourceSVDFactorMatrix U Sigma V) Z a b +
          columnSketchGram Tail Z a b := by
  intro a b
  have hAZ :
      ∀ i a,
        columnSketch A Z i a =
          columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a +
            columnSketch Tail Z i a := by
    intro i a
    unfold columnSketch preconditionColumns
    calc
      ∑ j : Fin n, A i j * Z j a
          =
            ∑ j : Fin n,
              (sourceSVDFactorMatrix U Sigma V i j + Tail i j) * Z j a := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hA i j]
      _ =
            ∑ j : Fin n, sourceSVDFactorMatrix U Sigma V i j * Z j a +
              ∑ j : Fin n, Tail i j * Z j a := by
              simp_rw [add_mul]
              rw [Finset.sum_add_distrib]
  have hcross₁ :=
    columnSketch_sourceSVDFactorMatrix_tail_leftOrthogonal
      U Sigma V Z Tail hUT a b
  have hcross₂ :=
    columnSketch_tail_sourceSVDFactorMatrix_leftOrthogonal
      U Sigma V Z Tail hUT a b
  unfold columnSketchGram
  calc
    ∑ i : Fin m, columnSketch A Z i a * columnSketch A Z i b
        =
          ∑ i : Fin m,
            (columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a +
              columnSketch Tail Z i a) *
            (columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b +
              columnSketch Tail Z i b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hAZ i a, hAZ i b]
    _ =
          ∑ i : Fin m,
            (columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
              columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b +
            columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
              columnSketch Tail Z i b +
            columnSketch Tail Z i a *
              columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b +
            columnSketch Tail Z i a * columnSketch Tail Z i b) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ =
          (∑ i : Fin m,
            columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
              columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b) +
          (∑ i : Fin m,
            columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
              columnSketch Tail Z i b) +
          (∑ i : Fin m,
            columnSketch Tail Z i a *
              columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b) +
          (∑ i : Fin m,
            columnSketch Tail Z i a * columnSketch Tail Z i b) := by
            simp_rw [Finset.sum_add_distrib]
    _ =
          (∑ i : Fin m,
            columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
              columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b) +
          (∑ i : Fin m,
            columnSketch Tail Z i a * columnSketch Tail Z i b) := by
            rw [hcross₁, hcross₂]
            ring

/-- If the exact source-head sketch Gram is positive definite, then the
head-plus-tail sketch Gram is nonsingular under the orthogonal source split.
The tail-Gram PSD part is supplied by `columnSketchGram_finitePSD`; the
remaining source-facing work is to derive the positive definiteness of the
source-head sketch Gram from the full-rank source data. -/
theorem columnSketchGram_sourceHeadTail_det_ne_zero_of_head_posDef
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hUT : sourceTailLeftOrthogonal U Tail)
    (hHead :
      Matrix.PosDef
        (columnSketchGram (sourceSVDFactorMatrix U Sigma V) Z :
          Matrix (Fin r) (Fin r) ℝ)) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
  have hsplit :=
    columnSketchGram_sourceHeadTail_leftOrthogonal
      A Tail Z U Sigma V hA hUT
  have hTailPSD :
      finitePSD (columnSketchGram Tail Z) :=
    columnSketchGram_finitePSD Tail Z
  have hTailMatPSD :
      Matrix.PosSemidef
        (columnSketchGram Tail Z : Matrix (Fin r) (Fin r) ℝ) :=
    finitePSD.to_matrix_posSemidef
      (columnSketchGram Tail Z)
      (columnSketchGram_symmetric Tail Z)
      hTailPSD
  have hdet :=
    matrix_det_ne_zero_of_posDef_add_posSemidef
      (columnSketchGram (sourceSVDFactorMatrix U Sigma V) Z)
      (columnSketchGram Tail Z)
      hHead hTailMatPSD
  have hmat :
      (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) =
        ((fun a b =>
          columnSketchGram (sourceSVDFactorMatrix U Sigma V) Z a b +
            columnSketchGram Tail Z a b) :
          Matrix (Fin r) (Fin r) ℝ) := by
    ext a b
    exact hsplit a b
  rw [hmat]
  exact hdet

/-- Exact source coefficient table `(VᵀZ)^{-1}Vᵀ` for the source equation
(9) route.  This is an analysis object: if an implementation computes the
cross product, inverse, or coefficient table, those are non-probability
computed quantities and require separate FP/inexact-arithmetic certificates. -/
noncomputable def sourceSketchCoefficient {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin r → Fin n → ℝ :=
  fun a j =>
    ∑ b : Fin r, nonsingInv r (rightSketchCrossGram V Z) a b * V j b

/-- The exact coefficient table `(VᵀZ)^{-1}Vᵀ` reproduces `Vᵀ` after
left multiplication by `VᵀZ`, provided the source cross factor is nonsingular. -/
theorem rightSketchCrossGram_sourceSketchCoefficient
    {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ∀ a j,
      (∑ b : Fin r,
        rightSketchCrossGram V Z a b * sourceSketchCoefficient V Z b j) =
        V j a := by
  intro a j
  have hright :=
    (isInverse_nonsingInv_of_det_ne_zero r (rightSketchCrossGram V Z) hVZ).2
  unfold sourceSketchCoefficient
  calc
    (∑ b : Fin r,
        rightSketchCrossGram V Z a b *
          (∑ c : Fin r,
            nonsingInv r (rightSketchCrossGram V Z) b c * V j c))
        =
          ∑ b : Fin r, ∑ c : Fin r,
            rightSketchCrossGram V Z a b *
              (nonsingInv r (rightSketchCrossGram V Z) b c * V j c) := by
            simp_rw [Finset.mul_sum]
    _ =
          ∑ c : Fin r, ∑ b : Fin r,
            rightSketchCrossGram V Z a b *
              (nonsingInv r (rightSketchCrossGram V Z) b c * V j c) := by
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r,
            (∑ b : Fin r,
              rightSketchCrossGram V Z a b *
                nonsingInv r (rightSketchCrossGram V Z) b c) * V j c := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro b _
            ring
    _ = ∑ c : Fin r, idMatrix r a c * V j c := by
            apply Finset.sum_congr rfl
            intro c _
            rw [hright a c]
            rfl
    _ = V j a := by
            simp [idMatrix, Finset.mem_univ]

/-- Multiplying the exact source sketch right factor `Σ(VᵀZ)` by the source
coefficient table `(VᵀZ)^{-1}Vᵀ` recovers `ΣVᵀ`. -/
theorem sourceSVDSketchRightFactor_sourceSketchCoefficient
    {n r : ℕ}
    (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ∀ a j,
      (∑ b : Fin r,
        sourceSVDSketchRightFactor Sigma V Z a b *
          sourceSketchCoefficient V Z b j) =
        ∑ c : Fin r, Sigma a c * V j c := by
  intro a j
  have hMW := rightSketchCrossGram_sourceSketchCoefficient V Z hVZ
  unfold sourceSVDSketchRightFactor
  calc
    (∑ b : Fin r,
        (∑ c : Fin r, Sigma a c * rightSketchCrossGram V Z c b) *
          sourceSketchCoefficient V Z b j)
        =
          ∑ b : Fin r, ∑ c : Fin r,
            (Sigma a c * rightSketchCrossGram V Z c b) *
              sourceSketchCoefficient V Z b j := by
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_mul]
    _ =
          ∑ c : Fin r, ∑ b : Fin r,
            (Sigma a c * rightSketchCrossGram V Z c b) *
              sourceSketchCoefficient V Z b j := by
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r,
            Sigma a c *
              (∑ b : Fin r,
                rightSketchCrossGram V Z c b *
                  sourceSketchCoefficient V Z b j) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
    _ = ∑ c : Fin r, Sigma a c * V j c := by
            apply Finset.sum_congr rfl
            intro c _
            rw [hMW c j]

/-- The exact source coefficient table reproduces the source SVD head from its
own column sketch. -/
theorem columnSketchHead_sourceSVDFactorMatrix_sourceSketchCoefficient
    {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ∀ i j,
      columnSketchHead (sourceSVDFactorMatrix U Sigma V) Z
          (sourceSketchCoefficient V Z) i j =
        sourceSVDFactorMatrix U Sigma V i j := by
  intro i j
  have hSketch :
      ∀ i a,
        columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a =
          ∑ c : Fin r, U i c * sourceSVDSketchRightFactor Sigma V Z c a := by
    intro i a
    unfold columnSketch preconditionColumns sourceSVDFactorMatrix
      sourceSVDSketchRightFactor rightSketchCrossGram
    calc
      (∑ k : Fin n,
          (∑ c : Fin r, U i c * (∑ d : Fin r, Sigma c d * V k d)) *
            Z k a)
          =
            ∑ k : Fin n, ∑ c : Fin r,
              (U i c * (∑ d : Fin r, Sigma c d * V k d)) * Z k a := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_mul]
      _ =
            ∑ c : Fin r, ∑ k : Fin n,
              (U i c * (∑ d : Fin r, Sigma c d * V k d)) * Z k a := by
              rw [Finset.sum_comm]
      _ =
            ∑ c : Fin r,
              U i c *
                (∑ k : Fin n, (∑ d : Fin r, Sigma c d * V k d) * Z k a) := by
              apply Finset.sum_congr rfl
              intro c _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ =
            ∑ c : Fin r,
              U i c *
                (∑ k : Fin n, ∑ d : Fin r, (Sigma c d * V k d) * Z k a) := by
              apply Finset.sum_congr rfl
              intro c _
              congr 1
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_mul]
      _ =
            ∑ c : Fin r,
              U i c *
                (∑ d : Fin r, ∑ k : Fin n, (Sigma c d * V k d) * Z k a) := by
              apply Finset.sum_congr rfl
              intro c _
              congr 1
              rw [Finset.sum_comm]
      _ =
            ∑ c : Fin r,
              U i c *
                (∑ d : Fin r, Sigma c d *
                  (∑ k : Fin n, V k d * Z k a)) := by
              apply Finset.sum_congr rfl
              intro c _
              congr 1
              apply Finset.sum_congr rfl
              intro d _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
  have hCoeff :=
    sourceSVDSketchRightFactor_sourceSketchCoefficient Sigma V Z hVZ
  unfold columnSketchHead sourceSVDFactorMatrix
  calc
    (∑ a : Fin r,
        columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
          sourceSketchCoefficient V Z a j)
        =
          ∑ a : Fin r,
            (∑ c : Fin r, U i c * sourceSVDSketchRightFactor Sigma V Z c a) *
              sourceSketchCoefficient V Z a j := by
            apply Finset.sum_congr rfl
            intro a _
            rw [hSketch i a]
    _ =
          ∑ a : Fin r, ∑ c : Fin r,
            (U i c * sourceSVDSketchRightFactor Sigma V Z c a) *
              sourceSketchCoefficient V Z a j := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_mul]
    _ =
          ∑ c : Fin r, ∑ a : Fin r,
            (U i c * sourceSVDSketchRightFactor Sigma V Z c a) *
              sourceSketchCoefficient V Z a j := by
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ a : Fin r,
                sourceSVDSketchRightFactor Sigma V Z c a *
                  sourceSketchCoefficient V Z a j) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
    _ =
          ∑ c : Fin r, U i c *
            (∑ d : Fin r, Sigma c d * V j d) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [hCoeff c j]

/-- Linearity of the exact column sketch through an explicitly supplied
head/tail split. -/
theorem columnSketch_eq_add_of_eq_add
    {m n r : ℕ}
    (A B C : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = B i j + C i j) :
    ∀ i a, columnSketch A Z i a = columnSketch B Z i a + columnSketch C Z i a := by
  intro i a
  unfold columnSketch preconditionColumns
  calc
    (∑ k : Fin n, A i k * Z k a)
        = ∑ k : Fin n, (B i k + C i k) * Z k a := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hA i k]
    _ = ∑ k : Fin n, (B i k * Z k a + C i k * Z k a) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ =
          (∑ k : Fin n, B i k * Z k a) +
            ∑ k : Fin n, C i k * Z k a := by
            rw [Finset.sum_add_distrib]

/-- Linearity of the exact coefficient-generated sketch head through a supplied
head/tail split of the underlying sketch. -/
theorem columnSketchHead_eq_add_of_columnSketch_eq_add
    {m n r : ℕ}
    (A B C : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (W : Fin r → Fin n → ℝ)
    (hAZ :
      ∀ i a, columnSketch A Z i a = columnSketch B Z i a + columnSketch C Z i a) :
    ∀ i j,
      columnSketchHead A Z W i j =
        columnSketchHead B Z W i j + columnSketchHead C Z W i j := by
  intro i j
  unfold columnSketchHead
  calc
    (∑ a : Fin r, columnSketch A Z i a * W a j)
        =
          ∑ a : Fin r,
            (columnSketch B Z i a + columnSketch C Z i a) * W a j := by
            apply Finset.sum_congr rfl
            intro a _
            rw [hAZ i a]
    _ =
          ∑ a : Fin r,
            (columnSketch B Z i a * W a j +
              columnSketch C Z i a * W a j) := by
            apply Finset.sum_congr rfl
            intro a _
            ring
    _ =
          (∑ a : Fin r, columnSketch B Z i a * W a j) +
            ∑ a : Fin r, columnSketch C Z i a * W a j := by
            rw [Finset.sum_add_distrib]

/-- For a source head/tail split `A = UΣVᵀ + T`, the source coefficient table
rewrites the displayed sketch head as the exact source head plus the sketched
tail contribution. -/
theorem columnSketchHead_sourceHeadTail_sourceSketchCoefficient
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j) :
    ∀ i j,
      columnSketchHead A Z (sourceSketchCoefficient V Z) i j =
        sourceSVDFactorMatrix U Sigma V i j +
          columnSketchHead Tail Z (sourceSketchCoefficient V Z) i j := by
  intro i j
  have hAZ :=
    columnSketch_eq_add_of_eq_add A (sourceSVDFactorMatrix U Sigma V) Tail Z hA
  have hAdd :=
    columnSketchHead_eq_add_of_columnSketch_eq_add
      A (sourceSVDFactorMatrix U Sigma V) Tail Z
      (sourceSketchCoefficient V Z) hAZ
  have hHead :=
    columnSketchHead_sourceSVDFactorMatrix_sourceSketchCoefficient
      U Sigma V Z hVZ
  calc
    columnSketchHead A Z (sourceSketchCoefficient V Z) i j
        =
          columnSketchHead (sourceSVDFactorMatrix U Sigma V) Z
              (sourceSketchCoefficient V Z) i j +
            columnSketchHead Tail Z (sourceSketchCoefficient V Z) i j := by
            rw [hAdd i j]
    _ =
          sourceSVDFactorMatrix U Sigma V i j +
            columnSketchHead Tail Z (sourceSketchCoefficient V Z) i j := by
            rw [hHead i j]

/-- Explicit source residual tail induced by the paper's coefficient table:
`T - (T Z)(VᵀZ)^{-1}Vᵀ`. -/
noncomputable def sourceSketchResidualTail {m n r : ℕ}
    (Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    Tail i j - columnSketchHead Tail Z (sourceSketchCoefficient V Z) i j

/-- Squared Frobenius norm is preserved by left multiplication with a
rectangular matrix whose columns are exactly orthonormal.  This is the
rectangular-tail analogue of square orthogonal invariance used in the source
equation (9) route. -/
theorem frobNormSqRect_leftOrthonormalFactor
    {m q n : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix q a b) :
    frobNormSqRect (fun i j => ∑ a : Fin q, U i a * C a j) =
      frobNormSqRect C := by
  unfold frobNormSqRect
  calc
    (∑ i : Fin m, ∑ j : Fin n, (∑ a : Fin q, U i a * C a j) ^ 2)
        =
          ∑ j : Fin n, ∑ i : Fin m, (∑ a : Fin q, U i a * C a j) ^ 2 := by
            rw [Finset.sum_comm]
    _ =
          ∑ j : Fin n, ∑ a : Fin q, C a j ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            calc
              (∑ i : Fin m, (∑ a : Fin q, U i a * C a j) ^ 2)
                  =
                    ∑ i : Fin m, ∑ a : Fin q, ∑ b : Fin q,
                      (U i a * C a j) * (U i b * C b j) := by
                      apply Finset.sum_congr rfl
                      intro i _
                      rw [sq, Finset.sum_mul]
                      apply Finset.sum_congr rfl
                      intro a _
                      rw [Finset.mul_sum]
              _ =
                    ∑ a : Fin q, ∑ b : Fin q, ∑ i : Fin m,
                      (U i a * C a j) * (U i b * C b j) := by
                      rw [Finset.sum_comm]
                      apply Finset.sum_congr rfl
                      intro a _
                      rw [Finset.sum_comm]
              _ =
                    ∑ a : Fin q, ∑ b : Fin q,
                      (∑ i : Fin m, U i a * U i b) * (C a j * C b j) := by
                      apply Finset.sum_congr rfl
                      intro a _
                      apply Finset.sum_congr rfl
                      intro b _
                      calc
                        (∑ i : Fin m, (U i a * C a j) * (U i b * C b j))
                            =
                              ∑ i : Fin m,
                                (U i a * U i b) * (C a j * C b j) := by
                                apply Finset.sum_congr rfl
                                intro i _
                                ring
                        _ =
                              (∑ i : Fin m, U i a * U i b) *
                                (C a j * C b j) := by
                                rw [Finset.sum_mul]
              _ =
                    ∑ a : Fin q, ∑ b : Fin q,
                      idMatrix q a b * (C a j * C b j) := by
                      apply Finset.sum_congr rfl
                      intro a _
                      apply Finset.sum_congr rfl
                      intro b _
                      rw [hU a b]
              _ = ∑ a : Fin q, C a j ^ 2 := by
                      apply Finset.sum_congr rfl
                      intro a _
                      simp [idMatrix, Finset.mem_univ]
                      ring
    _ =
          ∑ a : Fin q, ∑ j : Fin n, C a j ^ 2 := by
            rw [Finset.sum_comm]

/-- Frobenius norm is preserved by left multiplication with a rectangular
matrix whose columns are exactly orthonormal. -/
theorem frobNormRect_leftOrthonormalFactor
    {m q n : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix q a b) :
    frobNormRect (fun i j => ∑ a : Fin q, U i a * C a j) =
      frobNormRect C := by
  unfold frobNormRect
  rw [frobNormSqRect_leftOrthonormalFactor U C hU]

/-- Exact source-SVD-style factors with orthonormal left and right column
tables preserve the squared Frobenius norm of the displayed middle block.
This is a local SVD-norm identity on the Eckart--Young route; it assumes the
exact singular-vector tables and does not construct or compute them. -/
theorem frobNormSqRect_sourceSVDFactorMatrix_orthonormal
    {m n q : ℕ}
    (U : Fin m → Fin q → ℝ) (Sigma : Fin q → Fin q → ℝ)
    (V : Fin n → Fin q → ℝ)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix q a b)
    (hV : ∀ a b, ∑ j : Fin n, V j a * V j b = idMatrix q a b) :
    frobNormSqRect (sourceSVDFactorMatrix U Sigma V) =
      frobNormSq Sigma := by
  have hleft :
      frobNormSqRect (sourceSVDFactorMatrix U Sigma V) =
        frobNormSqRect (fun a j => ∑ b : Fin q, Sigma a b * V j b) := by
    simpa [sourceSVDFactorMatrix] using
      (frobNormSqRect_leftOrthonormalFactor U
        (fun a j => ∑ b : Fin q, Sigma a b * V j b) hU)
  have hright :
      frobNormSqRect (fun a j => ∑ b : Fin q, Sigma a b * V j b) =
        frobNormSqRect Sigma := by
    have h :=
      finiteFrobNormSq_rectRightOrthonormal
        (m := q) (n := q) (κ := Fin n)
        Sigma (fun b j => V j b) hV
    simpa [finiteFrobNormSq_fin] using h
  calc
    frobNormSqRect (sourceSVDFactorMatrix U Sigma V)
        = frobNormSqRect (fun a j => ∑ b : Fin q, Sigma a b * V j b) :=
          hleft
    _ = frobNormSqRect Sigma := hright
    _ = frobNormSq Sigma := frobNormSqRect_eq_frobNormSq Sigma

/-- Norm form of `frobNormSqRect_sourceSVDFactorMatrix_orthonormal`. -/
theorem frobNormRect_sourceSVDFactorMatrix_orthonormal
    {m n q : ℕ}
    (U : Fin m → Fin q → ℝ) (Sigma : Fin q → Fin q → ℝ)
    (V : Fin n → Fin q → ℝ)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix q a b)
    (hV : ∀ a b, ∑ j : Fin n, V j a * V j b = idMatrix q a b) :
    frobNormRect (sourceSVDFactorMatrix U Sigma V) =
      frobNorm Sigma := by
  unfold frobNormRect
  rw [frobNormSqRect_sourceSVDFactorMatrix_orthonormal U Sigma V hU hV]
  rw [frobNorm_eq_sqrt_frobNormSq]

/-- If the source tail factors as `Tail = Utail * TailCoord`, then the exact
source residual tail factors through the same left basis. -/
theorem sourceSketchResidualTail_leftFactor
    {m q n r : ℕ}
    (Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ) (TailCoord : Fin q → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hTail :
      ∀ i j, Tail i j = ∑ a : Fin q, Utail i a * TailCoord a j) :
    ∀ i j,
      sourceSketchResidualTail Tail Z V i j =
        ∑ a : Fin q, Utail i a *
          sourceSketchResidualTail TailCoord Z V a j := by
  intro i j
  have hSketch :
      ∀ i b,
        columnSketch Tail Z i b =
          ∑ a : Fin q, Utail i a * columnSketch TailCoord Z a b := by
    intro i b
    unfold columnSketch preconditionColumns
    calc
      (∑ k : Fin n, Tail i k * Z k b)
          =
            ∑ k : Fin n,
              (∑ a : Fin q, Utail i a * TailCoord a k) * Z k b := by
              apply Finset.sum_congr rfl
              intro k _
              rw [hTail i k]
      _ =
            ∑ k : Fin n, ∑ a : Fin q,
              (Utail i a * TailCoord a k) * Z k b := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_mul]
      _ =
            ∑ a : Fin q, ∑ k : Fin n,
              (Utail i a * TailCoord a k) * Z k b := by
              rw [Finset.sum_comm]
      _ =
            ∑ a : Fin q, Utail i a *
              (∑ k : Fin n, TailCoord a k * Z k b) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
  have hHead :
      columnSketchHead Tail Z (sourceSketchCoefficient V Z) i j =
        ∑ a : Fin q, Utail i a *
          columnSketchHead TailCoord Z (sourceSketchCoefficient V Z) a j := by
    unfold columnSketchHead
    calc
      (∑ b : Fin r, columnSketch Tail Z i b *
          sourceSketchCoefficient V Z b j)
          =
            ∑ b : Fin r,
              (∑ a : Fin q, Utail i a * columnSketch TailCoord Z a b) *
                sourceSketchCoefficient V Z b j := by
              apply Finset.sum_congr rfl
              intro b _
              rw [hSketch i b]
      _ =
            ∑ b : Fin r, ∑ a : Fin q,
              (Utail i a * columnSketch TailCoord Z a b) *
                sourceSketchCoefficient V Z b j := by
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.sum_mul]
      _ =
            ∑ a : Fin q, ∑ b : Fin r,
              (Utail i a * columnSketch TailCoord Z a b) *
                sourceSketchCoefficient V Z b j := by
              rw [Finset.sum_comm]
      _ =
            ∑ a : Fin q, Utail i a *
              (∑ b : Fin r,
                columnSketch TailCoord Z a b *
                  sourceSketchCoefficient V Z b j) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro b _
              ring
  unfold sourceSketchResidualTail
  calc
    Tail i j - columnSketchHead Tail Z (sourceSketchCoefficient V Z) i j
        =
          (∑ a : Fin q, Utail i a * TailCoord a j) -
            ∑ a : Fin q, Utail i a *
              columnSketchHead TailCoord Z (sourceSketchCoefficient V Z) a j := by
            rw [hTail i j, hHead]
    _ =
          ∑ a : Fin q, Utail i a *
            (TailCoord a j -
              columnSketchHead TailCoord Z (sourceSketchCoefficient V Z) a j) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro a _
            ring

/-- The source residual-tail Frobenius norm reduces exactly to the coordinate
tail residual whenever the tail left factor has orthonormal columns. -/
theorem frobNormSqRect_sourceSketchResidualTail_leftOrthonormalFactor
    {m q n r : ℕ}
    (Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ) (TailCoord : Fin q → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hTail :
      ∀ i j, Tail i j = ∑ a : Fin q, Utail i a * TailCoord a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b) :
    frobNormSqRect (sourceSketchResidualTail Tail Z V) =
      frobNormSqRect (sourceSketchResidualTail TailCoord Z V) := by
  have hres :=
    sourceSketchResidualTail_leftFactor Tail Utail TailCoord Z V hTail
  calc
    frobNormSqRect (sourceSketchResidualTail Tail Z V)
        =
          frobNormSqRect
            (fun i j => ∑ a : Fin q, Utail i a *
              sourceSketchResidualTail TailCoord Z V a j) := by
            congr 1
            funext i j
            exact hres i j
    _ =
          frobNormSqRect (sourceSketchResidualTail TailCoord Z V) :=
            frobNormSqRect_leftOrthonormalFactor Utail
              (sourceSketchResidualTail TailCoord Z V) hUtail

/-- Norm form of the source residual-tail reduction through an orthonormal
left tail basis. -/
theorem frobNormRect_sourceSketchResidualTail_leftOrthonormalFactor
    {m q n r : ℕ}
    (Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ) (TailCoord : Fin q → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hTail :
      ∀ i j, Tail i j = ∑ a : Fin q, Utail i a * TailCoord a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b) :
    frobNormRect (sourceSketchResidualTail Tail Z V) =
      frobNormRect (sourceSketchResidualTail TailCoord Z V) := by
  unfold frobNormRect
  rw [frobNormSqRect_sourceSketchResidualTail_leftOrthonormalFactor
    Tail Utail TailCoord Z V hTail hUtail]

/-- Transposed row representation of an exact right tail basis `Vperp`.
This is an exact analysis object; computed right bases in an implementation
need separate non-probability FP certificates. -/
def sourceRightBasisTranspose {n q : ℕ}
    (Vperp : Fin n → Fin q → ℝ) : Fin q → Fin n → ℝ :=
  fun a j => Vperp j a

/-- Rectangular cross factor `Vperpᵀ Z` for the source tail coordinates. -/
noncomputable def rightSketchCrossGramRect {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin q → Fin r → ℝ :=
  fun a b => ∑ j : Fin n, Vperp j a * Z j b

/-- Floating-point rectangular cross factor computed as the matrix product
`fl((Vperpᵀ) Z)`.  This is a concrete non-probability computation; the
sampling law defining `Z` remains an exact mathematical input. -/
noncomputable def flRightSketchCrossGramRect (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin q → Fin r → ℝ :=
  fl_matMul fp q n r (sourceRightBasisTranspose Vperp) Z

/-- Dot-product budget for computing one entry of `Vperpᵀ Z` by
`flRightSketchCrossGramRect`. -/
noncomputable def rightSketchCrossGramRectDotBudget (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin q → Fin r → ℝ :=
  fun a b => gamma fp n * ∑ j : Fin n, |Vperp j a| * |Z j b|

/-- Entrywise floating-point dot-product error for the computed rectangular
cross factor `fl((Vperpᵀ)Z)`. -/
theorem rightSketchCrossGramRect_flMatMul_entry_abs_error_le
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (Z : Fin n → Fin r → ℝ)
    (hγ : gammaValid fp n) :
    ∀ a b,
      |rightSketchCrossGramRect Vperp Z a b -
          flRightSketchCrossGramRect fp Vperp Z a b| ≤
        rightSketchCrossGramRectDotBudget fp Vperp Z a b := by
  intro a b
  have hdot :=
    matMul_error_bound fp q n r (sourceRightBasisTranspose Vperp) Z hγ a b
  simpa [rightSketchCrossGramRect, flRightSketchCrossGramRect,
    rightSketchCrossGramRectDotBudget, sourceRightBasisTranspose,
    abs_sub_comm] using hdot

/-- Summed left-component certificate induced by the concrete floating-point
cross-gram computation. -/
theorem rightSketchCrossGramRect_flMatMul_component_left_error_le
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (Z : Fin n → Fin r → ℝ)
    (Y : Fin r → Fin r → ℝ)
    (hγ : gammaValid fp n) :
    ∀ a c,
      ∑ b : Fin r,
          |rightSketchCrossGramRect Vperp Z a b -
              flRightSketchCrossGramRect fp Vperp Z a b| *
            |Y b c| ≤
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b * |Y b c| := by
  intro a c
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_right
    (rightSketchCrossGramRect_flMatMul_entry_abs_error_le fp Vperp Z hγ a b)
    (abs_nonneg _)

/-- Floating-point square cross Gram computed as `fl((Vᵀ)Z)`.  This is the
computed non-probability input that an inverse routine would consume when
forming an approximation to `(Vᵀ Z)^{-1}`. -/
noncomputable def flRightSketchCrossGram (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin r → Fin r → ℝ :=
  flRightSketchCrossGramRect fp V Z

/-- Dot-product budget for the computed square cross Gram `fl((Vᵀ)Z)`. -/
noncomputable def rightSketchCrossGramDotBudget (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin r → Fin r → ℝ :=
  rightSketchCrossGramRectDotBudget fp V Z

/-- Entrywise floating-point dot-product error for the computed square cross
Gram `fl((Vᵀ)Z)`. -/
theorem rightSketchCrossGram_flMatMul_entry_abs_error_le
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hγ : gammaValid fp n) :
    ∀ a b,
      |rightSketchCrossGram V Z a b -
          flRightSketchCrossGram fp V Z a b| ≤
        rightSketchCrossGramDotBudget fp V Z a b := by
  intro a b
  simpa [rightSketchCrossGram, rightSketchCrossGramRect,
    flRightSketchCrossGram, rightSketchCrossGramDotBudget] using
    rightSketchCrossGramRect_flMatMul_entry_abs_error_le fp V Z hγ a b

/-- Uniform-budget Frobenius certificate for the computed square cross Gram
`fl((Vᵀ)Z)`.  This is an inverse-routine input certificate, not yet an inverse
routine perturbation theorem. -/
theorem frobNorm_rightSketchCrossGram_sub_flMatMul_le_of_dotBudget_le
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    {omega : ℝ}
    (hγ : gammaValid fp n)
    (homega : 0 ≤ omega)
    (hBudget :
      ∀ a b, rightSketchCrossGramDotBudget fp V Z a b ≤ omega) :
    frobNorm
        (fun a b => rightSketchCrossGram V Z a b -
          flRightSketchCrossGram fp V Z a b) ≤
      Real.sqrt ((r : ℝ) * (r : ℝ)) * omega := by
  rw [← frobNormRect_eq_frobNorm]
  exact
    frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
      (fun a b => rightSketchCrossGram V Z a b -
        flRightSketchCrossGram fp V Z a b)
      homega
      (fun a b =>
        le_trans
          (rightSketchCrossGram_flMatMul_entry_abs_error_le fp V Z hγ a b)
          (hBudget a b))

/-- Sketching the transposed right tail basis gives the rectangular cross
factor `Vperpᵀ Z`. -/
theorem columnSketch_sourceRightBasisTranspose
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (Z : Fin n → Fin r → ℝ) :
    ∀ a b,
      columnSketch (sourceRightBasisTranspose Vperp) Z a b =
        rightSketchCrossGramRect Vperp Z a b := by
  intro a b
  rfl

/-- The exact sketch head of `Vperpᵀ` with the source coefficient table is
`(Vperpᵀ Z)(Vᵀ Z)^{-1}Vᵀ`. -/
theorem columnSketchHead_sourceRightBasisTranspose
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    ∀ a j,
      columnSketchHead (sourceRightBasisTranspose Vperp) Z
          (sourceSketchCoefficient V Z) a j =
        ∑ b : Fin r,
          rightSketchCrossGramRect Vperp Z a b *
            sourceSketchCoefficient V Z b j := by
  intro a j
  unfold columnSketchHead
  apply Finset.sum_congr rfl
  intro b _
  rw [columnSketch_sourceRightBasisTranspose Vperp Z a b]

/-- Coordinate residual identity for the right tail basis:
`Vperpᵀ - (Vperpᵀ Z)(Vᵀ Z)^{-1}Vᵀ`. -/
theorem sourceSketchResidualTail_sourceRightBasisTranspose
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    ∀ a j,
      sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V a j =
        Vperp j a -
          ∑ b : Fin r,
            rightSketchCrossGramRect Vperp Z a b *
              sourceSketchCoefficient V Z b j := by
  intro a j
  unfold sourceSketchResidualTail
  rw [columnSketchHead_sourceRightBasisTranspose Vperp Z V a j]
  rfl

/-- If the coordinate tail is `Sigma * R`, then the source residual tail is
`Sigma` times the residual of `R`. -/
theorem sourceSketchResidualTail_leftSquareFactor
    {q n r : ℕ}
    (Sigma : Fin q → Fin q → ℝ) (R : Fin q → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    ∀ a j,
      sourceSketchResidualTail (matMulRectLeft Sigma R) Z V a j =
        matMulRectLeft Sigma (sourceSketchResidualTail R Z V) a j := by
  intro a j
  simpa [matMulRectLeft] using
    (sourceSketchResidualTail_leftFactor
      (matMulRectLeft Sigma R) Sigma R Z V (by intro i k; rfl) a j)

/-- Frobenius submultiplicative bound for the preceding coordinate-tail
factorization.  This is a non-sharp but explicit foundation step toward the
equation (9) source-tail bound; the sharp spectral/unitarily invariant version
remains a separate obligation. -/
theorem frobNormRect_sourceSketchResidualTail_leftSquareFactor_le
    {q n r : ℕ}
    (Sigma : Fin q → Fin q → ℝ) (R : Fin q → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    frobNormRect (sourceSketchResidualTail (matMulRectLeft Sigma R) Z V) ≤
      frobNorm Sigma * frobNormRect (sourceSketchResidualTail R Z V) := by
  have hfact :
      sourceSketchResidualTail (matMulRectLeft Sigma R) Z V =
        matMulRectLeft Sigma (sourceSketchResidualTail R Z V) := by
    funext a j
    exact sourceSketchResidualTail_leftSquareFactor Sigma R Z V a j
  rw [hfact]
  exact frobNormRect_matMulRectLeft_le Sigma (sourceSketchResidualTail R Z V)

/-- Explicit `Sigma_perp Vperpᵀ` coordinate residual factorization:
`Sigma_perp (Vperpᵀ - (Vperpᵀ Z)(Vᵀ Z)^{-1}Vᵀ)`. -/
theorem sourceSketchResidualTail_sigmaRightBasisTranspose_explicit
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ) (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    ∀ a j,
      sourceSketchResidualTail
          (matMulRectLeft Sigma (sourceRightBasisTranspose Vperp)) Z V a j =
        ∑ c : Fin q, Sigma a c *
          (Vperp j c -
            ∑ b : Fin r,
              rightSketchCrossGramRect Vperp Z c b *
                sourceSketchCoefficient V Z b j) := by
  intro a j
  rw [sourceSketchResidualTail_leftSquareFactor Sigma
    (sourceRightBasisTranspose Vperp) Z V a j]
  unfold matMulRectLeft
  apply Finset.sum_congr rfl
  intro c _
  rw [sourceSketchResidualTail_sourceRightBasisTranspose Vperp Z V c j]

/-- Frobenius bound for the explicit `Sigma_perp Vperpᵀ` coordinate residual
factorization. -/
theorem frobNormRect_sourceSketchResidualTail_sigmaRightBasisTranspose_le
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ) (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    frobNormRect
        (sourceSketchResidualTail
          (matMulRectLeft Sigma (sourceRightBasisTranspose Vperp)) Z V) ≤
      frobNorm Sigma *
        frobNormRect (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V) :=
  frobNormRect_sourceSketchResidualTail_leftSquareFactor_le
    Sigma (sourceRightBasisTranspose Vperp) Z V

/-- Exact factor `(Vperpᵀ Z)(Vᵀ Z)^{-1}` used after right-multiplying the
coordinate residual by the head right basis. -/
noncomputable def rightSketchCrossGramRectInvFactor {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    Fin q → Fin r → ℝ :=
  fun a c =>
    ∑ b : Fin r,
      rightSketchCrossGramRect Vperp Z a b *
        nonsingInv r (rightSketchCrossGram V Z) b c

/-- The exact source coefficient table annihilates the right-tail basis when
the head and tail right bases are exactly orthogonal. -/
theorem sourceSketchCoefficient_mul_rightTailBasis_of_cross_zero
    {n q r : ℕ}
    (V : Fin n → Fin r → ℝ) (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (hcross : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0) :
    ∀ b c,
      (∑ j : Fin n, sourceSketchCoefficient V Z b j * Vperp j c) = 0 := by
  intro b c
  unfold sourceSketchCoefficient
  calc
    (∑ j : Fin n,
        (∑ d : Fin r,
          nonsingInv r (rightSketchCrossGram V Z) b d * V j d) *
          Vperp j c)
        =
          ∑ j : Fin n, ∑ d : Fin r,
            (nonsingInv r (rightSketchCrossGram V Z) b d * V j d) *
              Vperp j c := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ =
          ∑ d : Fin r, ∑ j : Fin n,
            (nonsingInv r (rightSketchCrossGram V Z) b d * V j d) *
              Vperp j c := by
            rw [Finset.sum_comm]
    _ =
          ∑ d : Fin r,
            nonsingInv r (rightSketchCrossGram V Z) b d *
              (∑ j : Fin n, V j d * Vperp j c) := by
            apply Finset.sum_congr rfl
            intro d _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ =
          ∑ d : Fin r,
            nonsingInv r (rightSketchCrossGram V Z) b d * 0 := by
            apply Finset.sum_congr rfl
            intro d _
            rw [hcross d c]
    _ = 0 := by simp

/-- Multiplying the exact source coefficient table by the head right basis
recovers the displayed inverse factor, provided the head right basis has
orthonormal columns. -/
theorem sourceSketchCoefficient_mul_headRightBasis_of_orthonormal
    {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c) :
    ∀ b c,
      (∑ j : Fin n, sourceSketchCoefficient V Z b j * V j c) =
        nonsingInv r (rightSketchCrossGram V Z) b c := by
  intro b c
  unfold sourceSketchCoefficient
  calc
    (∑ j : Fin n,
        (∑ d : Fin r,
          nonsingInv r (rightSketchCrossGram V Z) b d * V j d) *
          V j c)
        =
          ∑ j : Fin n, ∑ d : Fin r,
            (nonsingInv r (rightSketchCrossGram V Z) b d * V j d) *
              V j c := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ =
          ∑ d : Fin r, ∑ j : Fin n,
            (nonsingInv r (rightSketchCrossGram V Z) b d * V j d) *
              V j c := by
            rw [Finset.sum_comm]
    _ =
          ∑ d : Fin r,
            nonsingInv r (rightSketchCrossGram V Z) b d *
              (∑ j : Fin n, V j d * V j c) := by
            apply Finset.sum_congr rfl
            intro d _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ =
          ∑ d : Fin r,
            nonsingInv r (rightSketchCrossGram V Z) b d * idMatrix r d c := by
            apply Finset.sum_congr rfl
            intro d _
            rw [hV d c]
    _ = nonsingInv r (rightSketchCrossGram V Z) b c := by
            simp [idMatrix, Finset.mem_univ]

/-- Right-multiplying the exact right-tail residual by `Vperp` gives the
identity block under exact right-tail orthonormality and head/tail
orthogonality. -/
theorem sourceRightResidual_mul_rightTailBasis_eq_id
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcross : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0) :
    ∀ a c,
      (∑ j : Fin n,
        sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V a j *
          Vperp j c) =
        idMatrix q a c := by
  intro a c
  have hWperp :=
    sourceSketchCoefficient_mul_rightTailBasis_of_cross_zero V Vperp Z hcross
  have htail :
      (∑ j : Fin n,
        (∑ b : Fin r,
          rightSketchCrossGramRect Vperp Z a b *
            sourceSketchCoefficient V Z b j) *
          Vperp j c) = 0 := by
    calc
      (∑ j : Fin n,
        (∑ b : Fin r,
          rightSketchCrossGramRect Vperp Z a b *
            sourceSketchCoefficient V Z b j) *
          Vperp j c)
          =
            ∑ b : Fin r, ∑ j : Fin n,
              (rightSketchCrossGramRect Vperp Z a b *
                sourceSketchCoefficient V Z b j) *
                Vperp j c := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.sum_mul]
      _ =
            ∑ b : Fin r,
              rightSketchCrossGramRect Vperp Z a b *
                (∑ j : Fin n, sourceSketchCoefficient V Z b j * Vperp j c) := by
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ =
            ∑ b : Fin r,
              rightSketchCrossGramRect Vperp Z a b * 0 := by
              apply Finset.sum_congr rfl
              intro b _
              rw [hWperp b c]
      _ = 0 := by simp
  calc
    (∑ j : Fin n,
        sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V a j *
          Vperp j c)
        =
          ∑ j : Fin n,
            (Vperp j a -
              ∑ b : Fin r,
                rightSketchCrossGramRect Vperp Z a b *
                  sourceSketchCoefficient V Z b j) *
              Vperp j c := by
            apply Finset.sum_congr rfl
            intro j _
            rw [sourceSketchResidualTail_sourceRightBasisTranspose Vperp Z V a j]
    _ =
          (∑ j : Fin n, Vperp j a * Vperp j c) -
            ∑ j : Fin n,
              (∑ b : Fin r,
                rightSketchCrossGramRect Vperp Z a b *
                  sourceSketchCoefficient V Z b j) *
                Vperp j c := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = idMatrix q a c := by
            rw [hVperp a c, htail, sub_zero]

/-- Right-multiplying the exact right-tail residual by the head right basis
gives the negative `(Vperpᵀ Z)(Vᵀ Z)^{-1}` block. -/
theorem sourceRightResidual_mul_headRightBasis_eq_neg_invFactor
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hcross : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c) :
    ∀ a c,
      (∑ j : Fin n,
        sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V a j *
          V j c) =
        - rightSketchCrossGramRectInvFactor Vperp Z V a c := by
  intro a c
  have hWV :=
    sourceSketchCoefficient_mul_headRightBasis_of_orthonormal V Z hV
  have htail :
      (∑ j : Fin n,
        (∑ b : Fin r,
          rightSketchCrossGramRect Vperp Z a b *
            sourceSketchCoefficient V Z b j) *
          V j c) =
        rightSketchCrossGramRectInvFactor Vperp Z V a c := by
    unfold rightSketchCrossGramRectInvFactor
    calc
      (∑ j : Fin n,
        (∑ b : Fin r,
          rightSketchCrossGramRect Vperp Z a b *
            sourceSketchCoefficient V Z b j) *
          V j c)
          =
            ∑ b : Fin r, ∑ j : Fin n,
              (rightSketchCrossGramRect Vperp Z a b *
                sourceSketchCoefficient V Z b j) *
                V j c := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.sum_mul]
      _ =
            ∑ b : Fin r,
              rightSketchCrossGramRect Vperp Z a b *
                (∑ j : Fin n, sourceSketchCoefficient V Z b j * V j c) := by
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ =
            ∑ b : Fin r,
              rightSketchCrossGramRect Vperp Z a b *
                nonsingInv r (rightSketchCrossGram V Z) b c := by
              apply Finset.sum_congr rfl
              intro b _
              rw [hWV b c]
  calc
    (∑ j : Fin n,
        sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V a j *
          V j c)
        =
          ∑ j : Fin n,
            (Vperp j a -
              ∑ b : Fin r,
                rightSketchCrossGramRect Vperp Z a b *
                  sourceSketchCoefficient V Z b j) *
              V j c := by
            apply Finset.sum_congr rfl
            intro j _
            rw [sourceSketchResidualTail_sourceRightBasisTranspose Vperp Z V a j]
    _ =
          (∑ j : Fin n, Vperp j a * V j c) -
            ∑ j : Fin n,
              (∑ b : Fin r,
                rightSketchCrossGramRect Vperp Z a b *
                  sourceSketchCoefficient V Z b j) *
                V j c := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = - rightSketchCrossGramRectInvFactor Vperp Z V a c := by
            rw [hcross a c, htail]
            ring

/-- Concatenate the exact right-tail and right-head bases as a single
sum-indexed right-basis block.  The left summand is `Vperp`; the right summand
is `V`. -/
noncomputable def rightBasisBlock {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (V : Fin n → Fin r → ℝ) :
    Fin n → (Fin q ⊕ Fin r) → ℝ :=
  fun j bc =>
    match bc with
    | Sum.inl c => Vperp j c
    | Sum.inr b => V j b

/-- Row orthonormality of the concatenated right-basis block from the explicit
tail/head row-completeness identity. -/
theorem rightBasisBlock_row_orthonormal_of_sum
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (V : Fin n → Fin r → ℝ)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k) :
    ∀ j k,
      ∑ bc : Fin q ⊕ Fin r,
        rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V k bc =
      idMatrix n j k := by
  intro j k
  unfold rightBasisBlock
  rw [Fintype.sum_sum_type]
  simpa using hcomplete j k

/-- Component right-basis orthonormality fields assemble the column
orthonormality certificate for the concatenated block `[Vperp,V]`.  This is an
exact source-SVD bridge: constructing or computing the component bases remains
a separate non-probability obligation. -/
theorem rightBasisBlock_col_orthonormal_of_component_orthonormal_fields
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (V : Fin n → Fin r → ℝ)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c) :
    ∀ bc bd : Fin q ⊕ Fin r,
      (∑ j : Fin n,
        rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V j bd) =
        if bc = bd then 1 else 0 := by
  intro bc bd
  cases bc with
  | inl a =>
      cases bd with
      | inl c =>
          simpa [rightBasisBlock, idMatrix] using hVperp a c
      | inr c =>
          simpa [rightBasisBlock] using hcrossHead a c
  | inr b =>
      cases bd with
      | inl c =>
          simpa [rightBasisBlock] using hcrossTail b c
      | inr c =>
          simpa [rightBasisBlock, idMatrix] using hV b c

/-- Component right-basis fields plus the row-completeness identity assemble
both orthonormality certificates for the concatenated block `[Vperp,V]`. -/
theorem rightBasisBlock_col_row_orthonormal_of_component_fields
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (V : Fin n → Fin r → ℝ)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k) :
    (∀ bc bd : Fin q ⊕ Fin r,
      (∑ j : Fin n,
        rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V j bd) =
        if bc = bd then 1 else 0) ∧
      (∀ j k,
        (∑ bc : Fin q ⊕ Fin r,
          rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V k bc) =
          idMatrix n j k) := by
  constructor
  · exact
      rightBasisBlock_col_orthonormal_of_component_orthonormal_fields
        Vperp V hVperp hcrossTail hcrossHead hV
  · exact rightBasisBlock_row_orthonormal_of_sum Vperp V hcomplete

/-- Column orthonormality of the concatenated right-basis block
`[Vperp,V]` implies all component right-basis fields used by the source-tail
residual block algebra.  This is an exact source-SVD block certificate; a
computed basis routine must separately certify its rounded basis columns. -/
theorem rightBasisBlock_component_orthonormal_fields_of_col_orthonormal
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (V : Fin n → Fin r → ℝ)
    (hcols :
      ∀ bc bd : Fin q ⊕ Fin r,
        (∑ j : Fin n,
          rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V j bd) =
          if bc = bd then 1 else 0) :
    (∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c) ∧
      (∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0) ∧
      (∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0) ∧
      (∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c) := by
  constructor
  · intro a c
    have h := hcols (Sum.inl a) (Sum.inl c)
    simpa [rightBasisBlock, idMatrix] using h
  constructor
  · intro b c
    have h := hcols (Sum.inr b) (Sum.inl c)
    simpa [rightBasisBlock] using h
  constructor
  · intro a c
    have h := hcols (Sum.inl a) (Sum.inr c)
    simpa [rightBasisBlock] using h
  · intro b c
    have h := hcols (Sum.inr b) (Sum.inr c)
    simpa [rightBasisBlock, idMatrix] using h

/-- Row orthonormality of the concatenated right-basis block is exactly the
tail-plus-head row-completeness identity consumed by the source-tail Frobenius
block identity. -/
theorem rightBasisBlock_complete_sum_of_row_orthonormal
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (V : Fin n → Fin r → ℝ)
    (hrows :
      ∀ j k,
        (∑ bc : Fin q ⊕ Fin r,
          rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V k bc) =
          idMatrix n j k) :
    ∀ j k,
      (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k := by
  intro j k
  have h := hrows j k
  simpa [rightBasisBlock, Fintype.sum_sum_type] using h

/-- A selected right-Gram head index is orthogonal to every complement-tail
right index. -/
theorem rectRightGramSelectedIndexSet_head_tail_cross_zero
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (e : Fin k ↪ Fin n)
    (a : Fin k)
    (c : Fin (((rectRightGramSelectedIndexSet e)ᶜ).card)) :
    ∑ j : Fin n,
        rectRightGramEigenbasis A j (e a) *
          rectRightGramEigenbasis A j
            (((rectRightGramSelectedIndexSet e)ᶜ).orderEmbOfFin rfl c) =
      0 := by
  classical
  let s : Finset (Fin n) := rectRightGramSelectedIndexSet e
  have hmem : e a ∈ s := by
    simp [s, rectRightGramSelectedIndexSet]
  have htail_mem :
      (sᶜ).orderEmbOfFin rfl c ∈ sᶜ :=
    Finset.orderEmbOfFin_mem (sᶜ) rfl c
  have htail_not : (sᶜ).orderEmbOfFin rfl c ∉ s :=
    Finset.mem_compl.mp htail_mem
  have hne : e a ≠ (sᶜ).orderEmbOfFin rfl c := by
    intro h
    exact htail_not (by simpa [h] using hmem)
  change
    ∑ j : Fin n,
        rectRightGramEigenbasis A j (e a) *
          rectRightGramEigenbasis A j ((sᶜ).orderEmbOfFin rfl c) =
      0
  calc
    ∑ j : Fin n,
        rectRightGramEigenbasis A j (e a) *
          rectRightGramEigenbasis A j ((sᶜ).orderEmbOfFin rfl c)
        =
      idMatrix n (e a) ((sᶜ).orderEmbOfFin rfl c) := by
        simpa using
          rectRightGramEigenbasis_col_orthonormal A
            (e a) ((sᶜ).orderEmbOfFin rfl c)
    _ = 0 := by
        simp [idMatrix, hne]

/-- The complement-tail right index is orthogonal to every selected right-Gram
head index. -/
theorem rectRightGramSelectedIndexSet_tail_head_cross_zero
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (e : Fin k ↪ Fin n)
    (c : Fin (((rectRightGramSelectedIndexSet e)ᶜ).card))
    (a : Fin k) :
    ∑ j : Fin n,
        rectRightGramEigenbasis A j
            (((rectRightGramSelectedIndexSet e)ᶜ).orderEmbOfFin rfl c) *
          rectRightGramEigenbasis A j (e a) =
      0 := by
  simpa [mul_comm] using
    rectRightGramSelectedIndexSet_head_tail_cross_zero A e a c

/-- The selected head plus complement-tail right tables are row-complete because
they partition the exact right-Gram eigenbasis. -/
theorem rectRightGramSelectedIndexSet_tail_head_row_complete
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (e : Fin k ↪ Fin n)
    (j l : Fin n) :
    (∑ c : Fin (((rectRightGramSelectedIndexSet e)ᶜ).card),
        rectRightGramEigenbasis A j
            (((rectRightGramSelectedIndexSet e)ᶜ).orderEmbOfFin rfl c) *
          rectRightGramEigenbasis A l
            (((rectRightGramSelectedIndexSet e)ᶜ).orderEmbOfFin rfl c)) +
      (∑ a : Fin k,
        rectRightGramEigenbasis A j (e a) *
          rectRightGramEigenbasis A l (e a)) =
      idMatrix n j l := by
  classical
  let s : Finset (Fin n) := rectRightGramSelectedIndexSet e
  let term : Fin n → ℝ :=
    fun a => rectRightGramEigenbasis A j a * rectRightGramEigenbasis A l a
  change
    (∑ c : Fin ((sᶜ).card), term ((sᶜ).orderEmbOfFin rfl c)) +
      (∑ a : Fin k, term (e a)) =
      idMatrix n j l
  have htail :
      (sᶜ).sum term =
        ∑ c : Fin ((sᶜ).card), term ((sᶜ).orderEmbOfFin rfl c) :=
    rectRightGramComplement_sum_orderEmbOfFin s term
  have hhead :
      s.sum term = ∑ a : Fin k, term (e a) := by
    simpa [s] using rectRightGramSelectedIndexSet_sum e term
  rw [← htail, ← hhead]
  have hpartition :
      (sᶜ).sum term + s.sum term = ∑ a : Fin n, term a := by
    have h :
        s.sum term + (sᶜ).sum term = ∑ a : Fin n, term a := by
      rw [← Finset.sum_union disjoint_compl_right]
      rw [Finset.union_compl]
    simpa [add_comm] using h
  rw [hpartition]
  exact rectRightGramEigenbasis_row_orthonormal A j l

/-- The constructed ordered right-tail/head block has exact column
orthonormality. -/
theorem rectRightGramOrderedRightBasisBlock_col_orthonormal
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    ∀ bc bd :
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ⊕ Fin k,
      (∑ j : Fin n,
        rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) j bc *
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) j bd) =
        if bc = bd then 1 else 0 := by
  exact
    rightBasisBlock_col_orthonormal_of_component_orthonormal_fields
      (rectRightGramOrderedTailRight A hk)
      (rectRightGramOrderedHeadRight A hk)
      (rectRightGramOrderedTailRight_col_orthonormal A hk)
      (by
        intro b c
        simpa [rectRightGramOrderedTailRight, rectRightGramOrderedHeadRight,
          rectRightGramBasisSVDTailRight] using
          rectRightGramSelectedIndexSet_head_tail_cross_zero A
            (rectRightGramOrderedTopEmbedding hk) b c)
      (by
        intro c b
        simpa [rectRightGramOrderedTailRight, rectRightGramOrderedHeadRight,
          rectRightGramBasisSVDTailRight] using
          rectRightGramSelectedIndexSet_tail_head_cross_zero A
            (rectRightGramOrderedTopEmbedding hk) c b)
      (rectRightGramOrderedHeadRight_col_orthonormal A hk)

/-- The constructed ordered right-tail/head block has exact row
orthonormality, equivalently row completeness. -/
theorem rectRightGramOrderedRightBasisBlock_row_orthonormal
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    ∀ j l,
      (∑ bc :
        Fin (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ⊕ Fin k,
        rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) j bc *
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) l bc) =
        idMatrix n j l := by
  exact
    rightBasisBlock_row_orthonormal_of_sum
      (rectRightGramOrderedTailRight A hk)
      (rectRightGramOrderedHeadRight A hk)
      (by
        intro j l
        simpa [rectRightGramOrderedTailRight, rectRightGramOrderedHeadRight,
          rectRightGramBasisSVDTailRight] using
          rectRightGramSelectedIndexSet_tail_head_row_complete A
            (rectRightGramOrderedTopEmbedding hk) j l)

/-- The constructed ordered right-tail/head block packages exact column
orthonormality and row completeness together. -/
theorem rectRightGramOrderedRightBasisBlock_col_row_orthonormal
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    (∀ bc bd :
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ⊕ Fin k,
      (∑ j : Fin n,
        rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) j bc *
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) j bd) =
        if bc = bd then 1 else 0) ∧
      (∀ j l,
        (∑ bc :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ⊕ Fin k,
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) j bc *
            rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) l bc) =
          idMatrix n j l) := by
  exact
    ⟨rectRightGramOrderedRightBasisBlock_col_orthonormal A hk,
      rectRightGramOrderedRightBasisBlock_row_orthonormal A hk⟩

/-- The right-tail residual block `[I, -M]` that appears after multiplying
`R_perp = Vperpᵀ - (Vperpᵀ Z)(VᵀZ)^{-1}Vᵀ` by the full right-basis block. -/
noncomputable def sourceRightResidualBlock {q r : ℕ}
    (M : Fin q → Fin r → ℝ) : Fin q → (Fin q ⊕ Fin r) → ℝ :=
  fun a bc =>
    match bc with
    | Sum.inl c => idMatrix q a c
    | Sum.inr c => -M a c

/-- The singular-value-weighted right-tail residual block
`[Sigma, -Sigma M]`. -/
noncomputable def sigmaRightResidualBlock {q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ) (M : Fin q → Fin r → ℝ) :
    Fin q → (Fin q ⊕ Fin r) → ℝ :=
  fun a bc =>
    match bc with
    | Sum.inl c => Sigma a c
    | Sum.inr c => -matMulRectLeft Sigma M a c

/-- The squared Frobenius norm of `[Sigma, -Sigma M]` splits into the source
tail squared norm and the squared norm of the inverse-cross term. -/
theorem finiteFrobNormSq_sigmaRightResidualBlock
    {q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ) (M : Fin q → Fin r → ℝ) :
    finiteFrobNormSq (sigmaRightResidualBlock Sigma M) =
      frobNormSq Sigma + frobNormSqRect (matMulRectLeft Sigma M) := by
  unfold finiteFrobNormSq sigmaRightResidualBlock frobNormSq frobNormSqRect
  calc
    (∑ a : Fin q,
        ∑ bc : Fin q ⊕ Fin r,
          (match bc with
          | Sum.inl c => Sigma a c
          | Sum.inr c => -matMulRectLeft Sigma M a c) ^ 2)
        =
          ∑ a : Fin q,
            ((∑ c : Fin q, Sigma a c ^ 2) +
              (∑ c : Fin r, (-matMulRectLeft Sigma M a c) ^ 2)) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Fintype.sum_sum_type]
    _ =
          (∑ a : Fin q, ∑ c : Fin q, Sigma a c ^ 2) +
            (∑ a : Fin q, ∑ c : Fin r,
              matMulRectLeft Sigma M a c ^ 2) := by
            rw [Finset.sum_add_distrib]
            congr 1
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro c _
            ring

/-- Multiplying the exact right-tail residual by the concatenated right-basis
block gives `[I, -M]`, where `M=(Vperpᵀ Z)(VᵀZ)^{-1}`. -/
theorem sourceRightResidual_rightBasisBlock_eq_block
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c) :
    ∀ a bc,
      (∑ j : Fin n,
        sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V a j *
          rightBasisBlock Vperp V j bc) =
        sourceRightResidualBlock
          (rightSketchCrossGramRectInvFactor Vperp Z V) a bc := by
  intro a bc
  cases bc with
  | inl c =>
      simpa [rightBasisBlock, sourceRightResidualBlock] using
        sourceRightResidual_mul_rightTailBasis_eq_id
          Vperp Z V hVperp hcrossTail a c
  | inr c =>
      simpa [rightBasisBlock, sourceRightResidualBlock] using
        sourceRightResidual_mul_headRightBasis_eq_neg_invFactor
          Vperp Z V hcrossHead hV a c

/-- The singular-value-weighted right-tail residual, multiplied by the
concatenated right-basis block, is `[Sigma, -Sigma M]`. -/
theorem sourceRightResidual_sigma_rightBasisBlock_eq_block
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c) :
    ∀ a bc,
      (∑ j : Fin n,
        matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V) a j *
          rightBasisBlock Vperp V j bc) =
        sigmaRightResidualBlock Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V) a bc := by
  intro a bc
  have hblock :=
    sourceRightResidual_rightBasisBlock_eq_block
      Vperp Z V hVperp hcrossTail hcrossHead hV
  calc
    (∑ j : Fin n,
        matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V) a j *
          rightBasisBlock Vperp V j bc)
        =
          ∑ c : Fin q, Sigma a c *
            (∑ j : Fin n,
              sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V c j *
                rightBasisBlock Vperp V j bc) := by
            unfold matMulRectLeft
            calc
              (∑ j : Fin n,
                  (∑ c : Fin q,
                    Sigma a c *
                      sourceSketchResidualTail
                        (sourceRightBasisTranspose Vperp) Z V c j) *
                    rightBasisBlock Vperp V j bc)
                  =
                    ∑ j : Fin n, ∑ c : Fin q,
                      (Sigma a c *
                        sourceSketchResidualTail
                          (sourceRightBasisTranspose Vperp) Z V c j) *
                        rightBasisBlock Vperp V j bc := by
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [Finset.sum_mul]
              _ =
                    ∑ c : Fin q, ∑ j : Fin n,
                      (Sigma a c *
                        sourceSketchResidualTail
                          (sourceRightBasisTranspose Vperp) Z V c j) *
                        rightBasisBlock Vperp V j bc := by
                      rw [Finset.sum_comm]
              _ =
                    ∑ c : Fin q, Sigma a c *
                      (∑ j : Fin n,
                        sourceSketchResidualTail
                          (sourceRightBasisTranspose Vperp) Z V c j *
                          rightBasisBlock Vperp V j bc) := by
                      apply Finset.sum_congr rfl
                      intro c _
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro j _
                      ring
    _ =
          ∑ c : Fin q, Sigma a c *
            sourceRightResidualBlock
              (rightSketchCrossGramRectInvFactor Vperp Z V) c bc := by
            apply Finset.sum_congr rfl
            intro c _
            rw [hblock c bc]
    _ =
        sigmaRightResidualBlock Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V) a bc := by
            cases bc with
            | inl d =>
                simp [sourceRightResidualBlock, sigmaRightResidualBlock,
                  idMatrix, Finset.mem_univ]
            | inr d =>
                unfold sourceRightResidualBlock sigmaRightResidualBlock
                unfold matMulRectLeft
                change
                  (∑ c : Fin q,
                    Sigma a c *
                      (-(rightSketchCrossGramRectInvFactor Vperp Z V c d))) =
                    -(∑ c : Fin q,
                      Sigma a c *
                        rightSketchCrossGramRectInvFactor Vperp Z V c d)
                rw [← Finset.sum_neg_distrib]
                apply Finset.sum_congr rfl
                intro c _
                ring

/-- Squared Frobenius identity for the singular-value-weighted coordinate
right-tail residual after the exact right-basis block is supplied as complete.

This is the exact-object Frobenius/right-orthogonal invariance step following
LR.1w.  It still leaves the sharp spectral/unitarily invariant bound on
`Sigma * (Vperpᵀ Z)(VᵀZ)^{-1}` as the next analytic obligation. -/
theorem frobNormSqRect_sigma_sourceRightResidual_eq_block
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k) :
    frobNormSqRect
        (matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V)) =
      frobNormSq Sigma +
        frobNormSqRect
          (matMulRectLeft Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V)) := by
  let R := sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V
  let Q := rightBasisBlock Vperp V
  let M := rightSketchCrossGramRectInvFactor Vperp Z V
  have hQ :
      ∀ j k,
        ∑ bc : Fin q ⊕ Fin r, Q j bc * Q k bc = idMatrix n j k := by
    intro j k
    exact rightBasisBlock_row_orthonormal_of_sum Vperp V hcomplete j k
  have hinv :
      finiteFrobNormSq
          (fun a bc => ∑ j : Fin n, matMulRectLeft Sigma R a j * Q j bc) =
        frobNormSqRect (matMulRectLeft Sigma R) :=
    finiteFrobNormSq_rectRightOrthonormal (matMulRectLeft Sigma R) Q hQ
  have hprod :
      finiteFrobNormSq
          (fun a bc => ∑ j : Fin n, matMulRectLeft Sigma R a j * Q j bc) =
        finiteFrobNormSq (sigmaRightResidualBlock Sigma M) := by
    unfold finiteFrobNormSq
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro bc _
    have hentry :
        (fun a bc => ∑ j : Fin n, matMulRectLeft Sigma R a j * Q j bc) a bc =
          sigmaRightResidualBlock Sigma M a bc := by
      change
        (∑ j : Fin n,
          matMulRectLeft Sigma
            (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V) a j *
            rightBasisBlock Vperp V j bc) =
          sigmaRightResidualBlock Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V) a bc
      exact sourceRightResidual_sigma_rightBasisBlock_eq_block
        Sigma Vperp Z V hVperp hcrossTail hcrossHead hV a bc
    rw [hentry]
  calc
    frobNormSqRect
        (matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V))
        =
          finiteFrobNormSq
            (fun a bc => ∑ j : Fin n, matMulRectLeft Sigma R a j * Q j bc) := by
            rw [hinv]
    _ = finiteFrobNormSq (sigmaRightResidualBlock Sigma M) := hprod
    _ = frobNormSq Sigma +
          frobNormSqRect
            (matMulRectLeft Sigma
              (rightSketchCrossGramRectInvFactor Vperp Z V)) := by
            exact finiteFrobNormSq_sigmaRightResidualBlock Sigma M

/-- Norm form of the singular-value-weighted right-tail residual block
identity. -/
theorem frobNormRect_sigma_sourceRightResidual_eq_sqrt_block
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k) :
    frobNormRect
        (matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V)) =
      Real.sqrt
        (frobNormSq Sigma +
          frobNormSqRect
            (matMulRectLeft Sigma
              (rightSketchCrossGramRectInvFactor Vperp Z V))) := by
  unfold frobNormRect
  rw [frobNormSqRect_sigma_sourceRightResidual_eq_block
    Sigma Vperp Z V hVperp hcrossTail hcrossHead hV hcomplete]

/-- Source-facing Frobenius tail bound from the CACM equation-(9) cross-term
certificate.  The bound on
`Sigma * (Vperpᵀ Z)(VᵀZ)^{-1}` is a structural exact-object hypothesis of the
paper statement; it is not derived from probability construction or from the
full-rank condition alone. -/
theorem frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm Sigma) :
    frobNormRect
        (matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V)) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma := by
  let M := rightSketchCrossGramRectInvFactor Vperp Z V
  let Cross := matMulRectLeft Sigma M
  have hSigma_nonneg : 0 ≤ frobNorm Sigma := frobNorm_nonneg Sigma
  have hCross_nonneg : 0 ≤ frobNormRect Cross := frobNormRect_nonneg Cross
  have hepsSigma_nonneg : 0 ≤ eps * frobNorm Sigma :=
    mul_nonneg heps hSigma_nonneg
  have hCross_sq :
      frobNormRect Cross ^ 2 ≤ (eps * frobNorm Sigma) ^ 2 := by
    have habs :
        |frobNormRect Cross| ≤ |eps * frobNorm Sigma| := by
      simpa [Cross, M, abs_of_nonneg hCross_nonneg,
        abs_of_nonneg hepsSigma_nonneg] using hcrossTerm
    exact (sq_le_sq).mpr habs
  have hCross_sq' :
      frobNormRect Cross ^ 2 ≤ eps ^ 2 * frobNorm Sigma ^ 2 := by
    calc
      frobNormRect Cross ^ 2 ≤ (eps * frobNorm Sigma) ^ 2 := hCross_sq
      _ = eps ^ 2 * frobNorm Sigma ^ 2 := by ring
  have hradicand :
      frobNormSq Sigma + frobNormSqRect Cross ≤
        (1 + eps ^ 2) * frobNorm Sigma ^ 2 := by
    rw [← frobNorm_sq Sigma, ← frobNormRect_sq Cross]
    nlinarith [hCross_sq']
  calc
    frobNormRect
        (matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V))
        =
          Real.sqrt (frobNormSq Sigma + frobNormSqRect Cross) := by
            simpa [M, Cross] using
              frobNormRect_sigma_sourceRightResidual_eq_sqrt_block
                Sigma Vperp Z V hVperp hcrossTail hcrossHead hV hcomplete
    _ ≤ Real.sqrt ((1 + eps ^ 2) * frobNorm Sigma ^ 2) :=
          Real.sqrt_le_sqrt hradicand
    _ = Real.sqrt (1 + eps ^ 2) * frobNorm Sigma := by
          have hfactor : 0 ≤ 1 + eps ^ 2 := by
            nlinarith [sq_nonneg eps]
          rw [Real.sqrt_mul hfactor (frobNorm Sigma ^ 2),
            Real.sqrt_sq_eq_abs, abs_of_nonneg hSigma_nonneg]

/-- Source-facing Frobenius tail bound from a single exact orthonormality
certificate for the concatenated right-basis block `[Vperp,V]`.  The theorem
derives the component right-basis hypotheses and row-completeness internally,
then applies the source cross-term certificate. -/
theorem frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq_of_rightBasisBlock_orthonormal
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hcols :
      ∀ bc bd : Fin q ⊕ Fin r,
        (∑ j : Fin n,
          rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V j bd) =
          if bc = bd then 1 else 0)
    (hrows :
      ∀ j k,
        (∑ bc : Fin q ⊕ Fin r,
          rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V k bc) =
          idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm Sigma) :
    frobNormRect
        (matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V)) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma := by
  have hfields :=
    rightBasisBlock_component_orthonormal_fields_of_col_orthonormal
      Vperp V hcols
  have hcomplete :=
    rightBasisBlock_complete_sum_of_row_orthonormal Vperp V hrows
  exact
    frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq
      Sigma Vperp Z V heps hfields.1 hfields.2.1 hfields.2.2.1
      hfields.2.2.2 hcomplete hcrossTerm

/-- Source-facing Frobenius tail bound through the assembled block certificate:
separate SVD-style component right-basis fields and row-completeness first
assemble exact column/row orthonormality of `[Vperp,V]`, then feed the
block-certificate theorem. -/
theorem frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq_of_component_block_assembly
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm Sigma) :
    frobNormRect
        (matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V)) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma := by
  have hblock :=
    rightBasisBlock_col_row_orthonormal_of_component_fields
      Vperp V hVperp hcrossTail hcrossHead hV hcomplete
  exact
    frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq_of_rightBasisBlock_orthonormal
      Sigma Vperp Z V heps hblock.1 hblock.2 hcrossTerm

/-- Ambient source-tail Frobenius certificate obtained by composing the
left-orthonormal tail reduction with the exact coordinate
`Sigma_perp Vperpᵀ` residual factorization and the source cross-term
certificate.

This theorem is still an exact-object result.  It assumes the source tail has
already been represented as `Utail * Sigma * Vperpᵀ`, with `Utail` exactly
left-orthonormal, and it assumes the CACM equation-(9) Frobenius cross-term
bound as a visible certificate.  Computed SVD/basis/projector/Gram/inverse and
product routines require separate non-probability FP certificates. -/
theorem frobNormRect_sourceSketchResidualTail_sourceSVDTail_le_sqrt_one_add_eps_sq
    {m n q r : ℕ}
    (Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm Sigma) :
    frobNormRect (sourceSketchResidualTail Tail Z V) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma := by
  let TailCoord := matMulRectLeft Sigma (sourceRightBasisTranspose Vperp)
  have hleft :
      frobNormRect (sourceSketchResidualTail Tail Z V) =
        frobNormRect (sourceSketchResidualTail TailCoord Z V) :=
    frobNormRect_sourceSketchResidualTail_leftOrthonormalFactor
      Tail Utail TailCoord Z V hTail hUtail
  have hcoord :
      sourceSketchResidualTail TailCoord Z V =
        matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V) := by
    funext a j
    exact sourceSketchResidualTail_leftSquareFactor
      Sigma (sourceRightBasisTranspose Vperp) Z V a j
  have hsource :
      frobNormRect
          (matMulRectLeft Sigma
            (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V)) ≤
        Real.sqrt (1 + eps ^ 2) * frobNorm Sigma :=
    frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq
      Sigma Vperp Z V heps hVperp hcrossTail hcrossHead hV hcomplete hcrossTerm
  calc
    frobNormRect (sourceSketchResidualTail Tail Z V)
        = frobNormRect (sourceSketchResidualTail TailCoord Z V) := hleft
    _ =
        frobNormRect
          (matMulRectLeft Sigma
            (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V)) := by
          rw [hcoord]
    _ ≤ Real.sqrt (1 + eps ^ 2) * frobNorm Sigma := hsource

/-- The canonical `columnSketchTail A Z W` becomes the source residual tail
`T - (T Z)(VᵀZ)^{-1}Vᵀ` when `W=(VᵀZ)^{-1}Vᵀ` and
`A = UΣVᵀ + T`. -/
theorem columnSketchTail_sourceHeadTail_sourceSketchCoefficient
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j) :
    ∀ i j,
      columnSketchTail A Z (sourceSketchCoefficient V Z) i j =
        sourceSketchResidualTail Tail Z V i j := by
  intro i j
  have hHead :=
    columnSketchHead_sourceHeadTail_sourceSketchCoefficient
      A Tail U Sigma V Z hVZ hA
  unfold columnSketchTail sourceSketchResidualTail
  rw [hA i j, hHead i j]
  ring

/-- Source-head/tail instantiation of the equation (9) head/tail certificate
using the explicit coefficient table `(VᵀZ)^{-1}Vᵀ`.  The theorem leaves the
two analytic Frobenius bounds as visible obligations. -/
noncomputable def equation9HeadTailSketchCertificate_of_sourceHeadTail_sourceSketchCoefficient
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (tail coupling : ℝ)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows P_AZ (sourceSketchResidualTail Tail Z V)) ≤ coupling) :
    Equation9HeadTailSketchCertificate A Z P_AZ
      (columnSketchHead A Z (sourceSketchCoefficient V Z))
      (sourceSketchResidualTail Tail Z V) tail coupling where
  split := by
    intro i j
    have hHead :=
      columnSketchHead_sourceHeadTail_sourceSketchCoefficient
        A Tail U Sigma V Z hVZ hA
    unfold sourceSketchResidualTail
    rw [hA i j, hHead i j]
    ring
  head_factor :=
    columnSketchHead_headFactorization A Z (sourceSketchCoefficient V Z)
  tail_nonneg := htail_nonneg
  coupling_nonneg := hcoupling_nonneg
  tail_bound := htail
  coupling_bound := hcoupling

/-- Generic rank/residual surface for the source-head/tail coefficient route.
The projector is supplied by exact certificates; this result does not assume a
concrete Gram inverse for the full head-plus-tail sketch. -/
theorem equation9RankResidualSurface_of_sourceHeadTail_sourceSketchCoefficient
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (tail coupling : ℝ)
    (hleft : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a =
        columnSketch A Z i a)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows P_AZ (sourceSketchResidualTail Tail Z V)) ≤ coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling :=
  equation9HeadTailSketchRankResidualSurface
    A Z P_AZ
    (columnSketchHead A Z (sourceSketchCoefficient V Z))
    (sourceSketchResidualTail Tail Z V) tail coupling
    hleft hrepr
    (equation9HeadTailSketchCertificate_of_sourceHeadTail_sourceSketchCoefficient
      A Tail Z P_AZ U Sigma V tail coupling hVZ hA
      htail_nonneg hcoupling_nonneg htail hcoupling)

/-- Relative residual surface for the source-head/tail coefficient route,
conditional on a certified best-rank approximation and a scalar comparison of
the two visible source-tail radii. -/
theorem equation9RelativeResidualSurface_of_sourceHeadTail_sourceSketchCoefficient
    {m n k r : ℕ}
    {A Ak Tail : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hleft : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a =
        columnSketch A Z i a)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows P_AZ (sourceSketchResidualTail Tail Z V)) ≤ coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤
        rho * lowRankResidualFrob A Ak :=
  equation9HeadTailSketchRelativeResidualSurface
    Z P_AZ
    (columnSketchHead A Z (sourceSketchCoefficient V Z))
    (sourceSketchResidualTail Tail Z V) tail coupling rho
    hbest hleft hrepr
    (equation9HeadTailSketchCertificate_of_sourceHeadTail_sourceSketchCoefficient
      A Tail Z P_AZ U Sigma V tail coupling hVZ hA
      htail_nonneg hcoupling_nonneg htail hcoupling)
    hrelative

/-- If `A = U Σ Vᵀ`, then the exact column sketch factors as
`A Z = U (Σ Vᵀ Z)`. -/
theorem columnSketch_eq_sourceSVDFactorization {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j) :
    ∀ i a,
      columnSketch A Z i a =
        ∑ c : Fin r, U i c * sourceSVDSketchRightFactor Sigma V Z c a := by
  intro i a
  unfold columnSketch preconditionColumns sourceSVDSketchRightFactor rightSketchCrossGram
  calc
    (∑ k : Fin n, A i k * Z k a)
        =
          ∑ k : Fin n,
            (∑ c : Fin r, U i c * (∑ d : Fin r, Sigma c d * V k d)) *
              Z k a := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hA i k]
            rfl
    _ =
          ∑ k : Fin n, ∑ c : Fin r,
            (U i c * (∑ d : Fin r, Sigma c d * V k d)) * Z k a := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ =
          ∑ c : Fin r, ∑ k : Fin n,
            (U i c * (∑ d : Fin r, Sigma c d * V k d)) * Z k a := by
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ k : Fin n, (∑ d : Fin r, Sigma c d * V k d) * Z k a) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ k : Fin n, ∑ d : Fin r, (Sigma c d * V k d) * Z k a) := by
            apply Finset.sum_congr rfl
            intro c _
            congr 1
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ d : Fin r, ∑ k : Fin n, (Sigma c d * V k d) * Z k a) := by
            apply Finset.sum_congr rfl
            intro c _
            congr 1
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ d : Fin r, Sigma c d * (∑ k : Fin n, V k d * Z k a)) := by
            apply Finset.sum_congr rfl
            intro c _
            congr 1
            apply Finset.sum_congr rfl
            intro d _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring

/-- The determinant of the exact right factor `Σ(VᵀZ)` is nonzero whenever
both exact source determinants are nonzero. -/
theorem sourceSVDSketchRightFactor_det_ne_zero_of_det_ne_zero {n r : ℕ}
    (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det
      (sourceSVDSketchRightFactor Sigma V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
  let SM : Matrix (Fin r) (Fin r) ℝ := Sigma
  let VM : Matrix (Fin r) (Fin r) ℝ := rightSketchCrossGram V Z
  have hmat :
      (sourceSVDSketchRightFactor Sigma V Z : Matrix (Fin r) (Fin r) ℝ) =
        SM * VM := by
    ext a b
    simp [sourceSVDSketchRightFactor, rightSketchCrossGram, SM, VM,
      Matrix.mul_apply]
  have hdet :
      Matrix.det
          (sourceSVDSketchRightFactor Sigma V Z : Matrix (Fin r) (Fin r) ℝ) =
        Matrix.det SM * Matrix.det VM := by
    calc
      Matrix.det
          (sourceSVDSketchRightFactor Sigma V Z : Matrix (Fin r) (Fin r) ℝ)
          = Matrix.det (SM * VM) := by rw [hmat]
      _ = Matrix.det SM * Matrix.det VM := by rw [Matrix.det_mul]
  intro hzero
  have hprod : Matrix.det SM * Matrix.det VM = 0 := by
    simpa [hdet] using hzero
  rcases mul_eq_zero.mp hprod with hleft | hright
  · exact hSigma hleft
  · exact hVZ hright

/-- Diagonal-singular-block version of
`sourceSVDSketchRightFactor_det_ne_zero_of_det_ne_zero`.  The exact displayed
diagonal entries supply the `det(Σ) ≠ 0` hypothesis consumed by the source
right-factor determinant route. -/
theorem sourceSVDSketchRightFactor_det_ne_zero_of_diagonal_nonzero {n r : ℕ}
    (Sigma : Fin r → Fin r → ℝ) (sigma : Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det
      (sourceSVDSketchRightFactor Sigma V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  sourceSVDSketchRightFactor_det_ne_zero_of_det_ne_zero Sigma V Z
    (matrix_det_ne_zero_of_eq_diagonal_nonzero
      Sigma sigma hSigmaDiag hSigmaNonzero)
    hVZ

/-- Positive displayed diagonal singular values are a sufficient source for
the source right-factor determinant route. -/
theorem sourceSVDSketchRightFactor_det_ne_zero_of_diagonal_pos {n r : ℕ}
    (Sigma : Fin r → Fin r → ℝ) (sigma : Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaPos : ∀ a, 0 < sigma a)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det
      (sourceSVDSketchRightFactor Sigma V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  sourceSVDSketchRightFactor_det_ne_zero_of_det_ne_zero Sigma V Z
    (matrix_det_ne_zero_of_eq_diagonal_pos
      Sigma sigma hSigmaDiag hSigmaPos)
    hVZ

/-- Source-SVD-shaped exact thin-factor certificate for `A Z`: if
`A = U Σ Vᵀ`, `U` has orthonormal columns, and `det(Σ(VᵀZ))` is nonzero, then
`A Z = U (Σ VᵀZ)` is a valid thin factorization for LR.1k. -/
theorem columnSketchThinFactorCertificate_of_sourceSVD
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hdet :
      Matrix.det
        (sourceSVDSketchRightFactor Sigma V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchThinFactorCertificate A Z U
      (sourceSVDSketchRightFactor Sigma V Z) where
  factorization :=
    columnSketch_eq_sourceSVDFactorization A Z U Sigma V hA
  orthonormal_columns := hU
  det_factor_ne_zero := hdet

/-- Source-SVD-shaped exact thin-factor certificate using the separate source
determinant hypotheses `det(Σ) ≠ 0` and `det(VᵀZ) ≠ 0`. -/
theorem columnSketchThinFactorCertificate_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchThinFactorCertificate A Z U
      (sourceSVDSketchRightFactor Sigma V Z) :=
  columnSketchThinFactorCertificate_of_sourceSVD A Z U Sigma V hA hU
    (sourceSVDSketchRightFactor_det_ne_zero_of_det_ne_zero Sigma V Z hSigma hVZ)

/-- Source-SVD-shaped exact thin-factor certificate using a displayed exact
diagonal singular-value block instead of a raw `det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchThinFactorCertificate_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchThinFactorCertificate A Z U
      (sourceSVDSketchRightFactor Sigma V Z) :=
  columnSketchThinFactorCertificate_of_sourceSVD A Z U Sigma V hA hU
    (sourceSVDSketchRightFactor_det_ne_zero_of_diagonal_nonzero
      Sigma sigma V Z hSigmaDiag hSigmaNonzero hVZ)

/-- Under a thin factorization `B=U R` with orthonormal columns in `U`, the
exact sketch Gram matrix is entrywise `RᵀR`. -/
theorem columnSketchGram_eq_factorGram_of_thinFactorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (R : Fin r → Fin r → ℝ)
    (hthin : ColumnSketchThinFactorCertificate A Z U R) :
    ∀ a b,
      columnSketchGram A Z a b = ∑ c : Fin r, R c a * R c b := by
  intro a b
  unfold columnSketchGram
  calc
    (∑ i : Fin m, columnSketch A Z i a * columnSketch A Z i b)
        = ∑ i : Fin m,
            (∑ c : Fin r, U i c * R c a) *
              (∑ d : Fin r, U i d * R d b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hthin.factorization i a, hthin.factorization i b]
    _ = ∑ i : Fin m, ∑ c : Fin r, ∑ d : Fin r,
            (U i c * R c a) * (U i d * R d b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
    _ = ∑ c : Fin r, ∑ d : Fin r, ∑ i : Fin m,
            (U i c * R c a) * (U i d * R d b) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.sum_comm]
    _ = ∑ c : Fin r, ∑ d : Fin r,
            (∑ i : Fin m, U i c * U i d) * (R c a * R d b) := by
            apply Finset.sum_congr rfl
            intro c _
            apply Finset.sum_congr rfl
            intro d _
            calc
              (∑ i : Fin m, (U i c * R c a) * (U i d * R d b))
                  = ∑ i : Fin m, (U i c * U i d) * (R c a * R d b) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  ring
              _ = (∑ i : Fin m, U i c * U i d) * (R c a * R d b) := by
                  rw [Finset.sum_mul]
    _ = ∑ c : Fin r, ∑ d : Fin r,
            idMatrix r c d * (R c a * R d b) := by
            apply Finset.sum_congr rfl
            intro c _
            apply Finset.sum_congr rfl
            intro d _
            rw [hthin.orthonormal_columns c d]
    _ = ∑ c : Fin r, R c a * R c b := by
            apply Finset.sum_congr rfl
            intro c _
            simp [idMatrix, Finset.mem_univ]

/-- A thin factorization `B=U R` with orthonormal columns and nonsingular `R`
implies the exact sketch Gram determinant is nonzero. -/
theorem columnSketchGram_det_ne_zero_of_thinFactorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (R : Fin r → Fin r → ℝ)
    (hthin : ColumnSketchThinFactorCertificate A Z U R) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
  have hentry :=
    columnSketchGram_eq_factorGram_of_thinFactorCertificate A Z U R hthin
  let RM : Matrix (Fin r) (Fin r) ℝ := R
  have hmat :
      (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) =
        RM.transpose * RM := by
    ext a b
    rw [hentry a b]
    simp [RM, Matrix.mul_apply]
  have hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) =
        Matrix.det RM * Matrix.det RM := by
    calc
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ)
          = Matrix.det (RM.transpose * RM) := by
              rw [hmat]
      _ = Matrix.det RM.transpose * Matrix.det RM := by
              rw [Matrix.det_mul]
      _ = Matrix.det RM * Matrix.det RM := by
              rw [Matrix.det_transpose]
  intro hzero
  have hprod : Matrix.det RM * Matrix.det RM = 0 := by
    simpa [hdet] using hzero
  rcases mul_eq_zero.mp hprod with hleft | hright
  · exact hthin.det_factor_ne_zero hleft
  · exact hthin.det_factor_ne_zero hright

/-- A nonsingular square real factor has a positive-definite normal Gram
`RᵀR`.  This is the positive-definiteness version of the determinant bridge
used in the equation (9) source-head route. -/
theorem matrix_transpose_mul_self_posDef_of_det_ne_zero {r : ℕ}
    (R : Matrix (Fin r) (Fin r) ℝ)
    (hdet : Matrix.det R ≠ 0) :
    Matrix.PosDef (R.transpose * R) := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa using Matrix.isHermitian_conjTranspose_mul_self R
  · intro x hx
    have hRx : Matrix.mulVec R x ≠ 0 := by
      intro hzero
      exact hx (Matrix.eq_zero_of_mulVec_eq_zero hdet hzero)
    have hquad :
        star x ⬝ᵥ Matrix.mulVec (R.transpose * R) x =
          Matrix.mulVec R x ⬝ᵥ Matrix.mulVec R x := by
      calc
        star x ⬝ᵥ Matrix.mulVec (R.transpose * R) x
            = star x ⬝ᵥ Matrix.mulVec R.transpose (Matrix.mulVec R x) := by
                rw [← Matrix.mulVec_mulVec]
        _ = Matrix.vecMul (star x) R.transpose ⬝ᵥ Matrix.mulVec R x := by
                rw [Matrix.dotProduct_mulVec]
        _ = Matrix.mulVec R (star x) ⬝ᵥ Matrix.mulVec R x := by
                rw [Matrix.vecMul_transpose]
        _ = Matrix.mulVec R x ⬝ᵥ Matrix.mulVec R x := by
                simp
    have hnonneg : 0 ≤ Matrix.mulVec R x ⬝ᵥ Matrix.mulVec R x := by
      unfold dotProduct
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((Matrix.mulVec R x) i)
    have hne : Matrix.mulVec R x ⬝ᵥ Matrix.mulVec R x ≠ 0 := by
      intro hzero
      exact hRx (dotProduct_self_eq_zero.mp hzero)
    exact hquad.symm ▸ lt_of_le_of_ne hnonneg hne.symm

/-- A thin factorization `B=U R` with orthonormal columns and nonsingular `R`
upgrades the exact sketch Gram from merely nonsingular to positive definite. -/
theorem columnSketchGram_posDef_of_thinFactorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (R : Fin r → Fin r → ℝ)
    (hthin : ColumnSketchThinFactorCertificate A Z U R) :
    Matrix.PosDef (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) := by
  have hentry :=
    columnSketchGram_eq_factorGram_of_thinFactorCertificate A Z U R hthin
  let RM : Matrix (Fin r) (Fin r) ℝ := R
  have hmat :
      (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) =
        RM.transpose * RM := by
    ext a b
    rw [hentry a b]
    simp [RM, Matrix.mul_apply]
  rw [hmat]
  exact matrix_transpose_mul_self_posDef_of_det_ne_zero RM
    (by simpa [RM] using hthin.det_factor_ne_zero)

/-- A thin factorization certificate supplies the concrete repository
`nonsingInv` Gram-inverse certificate. -/
theorem columnSketchGramInverseCertificate_of_thinFactorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (R : Fin r → Fin r → ℝ)
    (hthin : ColumnSketchThinFactorCertificate A Z U R) :
    ColumnSketchGramInverseCertificate A Z
      (nonsingInv r (columnSketchGram A Z)) :=
  columnSketchGramInverseCertificate_of_det_ne_zero A Z
    (columnSketchGram_det_ne_zero_of_thinFactorCertificate A Z U R hthin)

/-- For `C = G^{-1}Bᵀ`, the exact right multiplier `C B` is the identity when
`Ginv` is a left inverse of the sketch Gram matrix `G = BᵀB`. -/
theorem columnSketchRightMultiplier_eq_id_of_gramInverseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ)
    (hG : ColumnSketchGramInverseCertificate A Z Ginv) :
    ∀ a b,
      columnSketchRightMultiplier A Z
          (columnSketchGramInverseCoefficient A Z Ginv) a b =
        idMatrix r a b := by
  intro a b
  have hleft := hG.inverse.1 a b
  unfold columnSketchGram at hleft
  unfold columnSketchRightMultiplier columnSketchGramInverseCoefficient
    preconditionRows
  calc
    (∑ k : Fin m,
        (∑ c : Fin r, Ginv a c * columnSketch A Z k c) *
          columnSketch A Z k b)
        = ∑ c : Fin r, Ginv a c *
            (∑ k : Fin m, columnSketch A Z k c * columnSketch A Z k b) := by
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = idMatrix r a b := by
            simpa [idMatrix] using hleft

/-- The coefficient-side Moore-Penrose equation `C B C = C` for the exact
Gram-inverse coefficient table. -/
theorem columnSketchGramInverseCoefficient_reproducesCoeff
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ)
    (hG : ColumnSketchGramInverseCertificate A Z Ginv) :
    ∀ a i,
      preconditionRows
          (columnSketchRightMultiplier A Z
            (columnSketchGramInverseCoefficient A Z Ginv))
          (columnSketchGramInverseCoefficient A Z Ginv) a i =
        columnSketchGramInverseCoefficient A Z Ginv a i := by
  intro a i
  have hCB :=
    columnSketchRightMultiplier_eq_id_of_gramInverseCertificate A Z Ginv hG
  unfold preconditionRows
  calc
    (∑ b : Fin r,
        columnSketchRightMultiplier A Z
            (columnSketchGramInverseCoefficient A Z Ginv) a b *
          columnSketchGramInverseCoefficient A Z Ginv b i)
        = ∑ b : Fin r,
            idMatrix r a b *
              columnSketchGramInverseCoefficient A Z Ginv b i := by
            apply Finset.sum_congr rfl
            intro b _
            rw [hCB a b]
    _ = columnSketchGramInverseCoefficient A Z Ginv a i := by
            simp [idMatrix, Finset.mem_univ]

/-- The exact multiplier `P = B G^{-1} Bᵀ` is symmetric when `G^{-1}` is
symmetric. -/
theorem columnSketchLeftMultiplier_symmetric_of_gramInverseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ)
    (hG : ColumnSketchGramInverseCertificate A Z Ginv) :
    IsSymmetricFiniteMatrix
      (columnSketchLeftMultiplier A Z
        (columnSketchGramInverseCoefficient A Z Ginv)) := by
  intro i j
  unfold columnSketchLeftMultiplier columnSketchGramInverseCoefficient
  calc
    (∑ a : Fin r,
        columnSketch A Z i a *
          (∑ b : Fin r, Ginv a b * columnSketch A Z j b))
        = ∑ a : Fin r, ∑ b : Fin r,
            columnSketch A Z i a * (Ginv a b * columnSketch A Z j b) := by
            simp_rw [Finset.mul_sum]
    _ = ∑ b : Fin r, ∑ a : Fin r,
            columnSketch A Z i a * (Ginv a b * columnSketch A Z j b) := by
            rw [Finset.sum_comm]
    _ = ∑ b : Fin r, ∑ a : Fin r,
            columnSketch A Z j b * (Ginv b a * columnSketch A Z i a) := by
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro a _
            rw [hG.symmetric_inverse a b]
            ring
    _ = ∑ b : Fin r,
            columnSketch A Z j b *
              (∑ a : Fin r, Ginv b a * columnSketch A Z i a) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.mul_sum]

/-- The exact right multiplier `C B` for `C=G^{-1}Bᵀ` is symmetric because it
is the identity under the Gram-inverse certificate. -/
theorem columnSketchRightMultiplier_symmetric_of_gramInverseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ)
    (hG : ColumnSketchGramInverseCertificate A Z Ginv) :
    IsSymmetricFiniteMatrix
      (columnSketchRightMultiplier A Z
        (columnSketchGramInverseCoefficient A Z Ginv)) := by
  intro a b
  have hCB :=
    columnSketchRightMultiplier_eq_id_of_gramInverseCertificate A Z Ginv hG
  rw [hCB a b, hCB b a]
  simp [idMatrix, eq_comm]

/-- The explicit multiplier `(A Z) C` factors through the exact column sketch
with coefficient table `C`. -/
noncomputable def columnSketchLeftMultiplier_leftFactorThrough {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) :
    LeftFactorThrough (columnSketchLeftMultiplier A Z C) (columnSketch A Z) where
  coeff := C
  factorization := by
    intro i j
    rfl

/-- The explicit coefficient multiplier `(A Z) C` gives a rank-at-most-`r`
projected approximation `(A Z) C A`. -/
theorem columnSketchLeftMultiplier_rankAtMost {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) :
    RectRankAtMost m n r
      (preconditionRows (columnSketchLeftMultiplier A Z C) A) :=
  sketchColumnProjectorApprox_rankAtMost A Z (columnSketchLeftMultiplier A Z C)
    (columnSketchLeftMultiplier_leftFactorThrough A Z C)

/-- Equation (9) rank/residual surface specialized to an explicit coefficient
multiplier `(A Z) C`. -/
theorem columnSketchLeftMultiplier_equation9RankResidualSurface {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) (tail coupling : ℝ)
    (hEq9 :
      Equation9ResidualCertificate A (columnSketchLeftMultiplier A Z C) tail coupling) :
    RectRankAtMost m n r
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) ∧
      lowRankResidualFrob A
          (preconditionRows (columnSketchLeftMultiplier A Z C) A) ≤
        tail + coupling :=
  equation9RankResidualSurface A Z (columnSketchLeftMultiplier A Z C) tail coupling
    (columnSketchLeftMultiplier_leftFactorThrough A Z C) hEq9

/-- Relative equation (9) surface specialized to an explicit coefficient
multiplier `(A Z) C`. -/
theorem columnSketchLeftMultiplier_equation9RelativeResidualSurface {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (C : Fin r → Fin m → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hEq9 :
      Equation9ResidualCertificate A (columnSketchLeftMultiplier A Z C) tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) ∧
        lowRankResidualFrob A
            (preconditionRows (columnSketchLeftMultiplier A Z C) A) ≤
          rho * lowRankResidualFrob A Ak :=
  equation9RelativeResidualSurface Z (columnSketchLeftMultiplier A Z C)
    tail coupling rho hbest
    (columnSketchLeftMultiplier_leftFactorThrough A Z C) hEq9 hrelative

/-- Exact generalized-inverse certificate for the column sketch `B = A Z` and
coefficient table `C`: the multiplier `P_C = B C` reproduces the sketch,
equivalently `B C B = B`.  This is the algebraic condition a future
pseudoinverse construction must supply before the source projector `P_{A Z}`
can be used as an actual projector. -/
structure ColumnSketchGeneralizedInverse {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) : Prop where
  reproducesSketch :
    ∀ i a,
      preconditionRows (columnSketchLeftMultiplier A Z C) (columnSketch A Z) i a =
        columnSketch A Z i a

/-- A generalized-inverse coefficient table makes the exact multiplier
`P_C = (A Z) C` reproduce the column sketch. -/
theorem columnSketchLeftMultiplier_reproducesSketch_of_generalizedInverse
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchGeneralizedInverse A Z C) :
    ∀ i a,
      preconditionRows (columnSketchLeftMultiplier A Z C) (columnSketch A Z) i a =
        columnSketch A Z i a :=
  hC.reproducesSketch

/-- The exact generalized-inverse equation `B C B = B` for the Gram-inverse
coefficient table. -/
theorem columnSketchGramInverseCoefficient_generalizedInverse
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ)
    (hG : ColumnSketchGramInverseCertificate A Z Ginv) :
    ColumnSketchGeneralizedInverse A Z
      (columnSketchGramInverseCoefficient A Z Ginv) where
  reproducesSketch := by
    intro i a
    have hCB :=
      columnSketchRightMultiplier_eq_id_of_gramInverseCertificate A Z Ginv hG
    unfold preconditionRows columnSketchLeftMultiplier
    calc
      (∑ k : Fin m,
          (∑ b : Fin r,
              columnSketch A Z i b *
                columnSketchGramInverseCoefficient A Z Ginv b k) *
            columnSketch A Z k a)
          = ∑ k : Fin m, ∑ b : Fin r,
              (columnSketch A Z i b *
                  columnSketchGramInverseCoefficient A Z Ginv b k) *
                columnSketch A Z k a := by
              simp_rw [Finset.sum_mul]
      _ = ∑ b : Fin r, ∑ k : Fin m,
              (columnSketch A Z i b *
                  columnSketchGramInverseCoefficient A Z Ginv b k) *
                columnSketch A Z k a := by
              rw [Finset.sum_comm]
      _ = ∑ b : Fin r,
              columnSketch A Z i b *
                (∑ k : Fin m,
                  columnSketchGramInverseCoefficient A Z Ginv b k *
                    columnSketch A Z k a) := by
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = ∑ b : Fin r,
              columnSketch A Z i b *
                columnSketchRightMultiplier A Z
                  (columnSketchGramInverseCoefficient A Z Ginv) b a := by
              rfl
      _ = ∑ b : Fin r, columnSketch A Z i b * idMatrix r b a := by
              apply Finset.sum_congr rfl
              intro b _
              rw [hCB b a]
      _ = columnSketch A Z i a := by
              simp [idMatrix, Finset.sum_ite_eq', Finset.mem_univ]

/-- A generalized-inverse coefficient table makes `P_C = (A Z) C` idempotent:
`P_C^2 = P_C`.  This is the exact projector algebra that will be needed once a
pseudoinverse or full-rank construction instantiates the certificate. -/
theorem columnSketchLeftMultiplier_idempotent_of_generalizedInverse {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchGeneralizedInverse A Z C) :
    ∀ i j,
      preconditionRows (columnSketchLeftMultiplier A Z C)
          (columnSketchLeftMultiplier A Z C) i j =
        columnSketchLeftMultiplier A Z C i j := by
  intro i j
  unfold preconditionRows columnSketchLeftMultiplier
  calc
    (∑ k : Fin m,
        (∑ a : Fin r, columnSketch A Z i a * C a k) *
          (∑ b : Fin r, columnSketch A Z k b * C b j))
        = ∑ k : Fin m, ∑ b : Fin r,
            ((∑ a : Fin r, columnSketch A Z i a * C a k) *
                columnSketch A Z k b) * C b j := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro b _
              ring
    _ = ∑ b : Fin r, ∑ k : Fin m,
            ((∑ a : Fin r, columnSketch A Z i a * C a k) *
                columnSketch A Z k b) * C b j := by
              rw [Finset.sum_comm]
    _ = ∑ b : Fin r,
            (∑ k : Fin m,
              (∑ a : Fin r, columnSketch A Z i a * C a k) *
                columnSketch A Z k b) * C b j := by
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.sum_mul]
    _ = ∑ b : Fin r, columnSketch A Z i b * C b j := by
              apply Finset.sum_congr rfl
              intro b _
              have hb := hC.reproducesSketch i b
              unfold preconditionRows columnSketchLeftMultiplier at hb
              rw [hb]

/-- Packaged exact projector surface for the coefficient multiplier
`P_C = (A Z) C`: it factors through the sketch, reproduces the sketch columns,
is idempotent, and gives a rank-at-most-`r` approximation `P_C A`.  Orthogonal
projector and pseudoinverse instantiations remain separate obligations. -/
theorem columnSketchLeftMultiplier_projectorSurface_of_generalizedInverse {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchGeneralizedInverse A Z C) :
    Nonempty (LeftFactorThrough (columnSketchLeftMultiplier A Z C) (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows (columnSketchLeftMultiplier A Z C) (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows (columnSketchLeftMultiplier A Z C)
            (columnSketchLeftMultiplier A Z C) i j =
          columnSketchLeftMultiplier A Z C i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) :=
  ⟨⟨columnSketchLeftMultiplier_leftFactorThrough A Z C⟩,
    columnSketchLeftMultiplier_reproducesSketch_of_generalizedInverse A Z C hC,
    columnSketchLeftMultiplier_idempotent_of_generalizedInverse A Z C hC,
    columnSketchLeftMultiplier_rankAtMost A Z C⟩

/-- Exact orthogonal-projector certificate for the column sketch.  It combines
the generalized-inverse condition `B C B = B`, which gives reproduction and
idempotence for `P_C = B C`, with symmetry of the displayed multiplier.  This
is still a certificate surface: future pseudoinverse/full-rank infrastructure
must instantiate these fields for the particular `C = (A Z)^+`. -/
structure ColumnSketchOrthogonalProjectorCertificate {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) : Prop where
  generalizedInverse : ColumnSketchGeneralizedInverse A Z C
  symmetric :
    IsSymmetricFiniteMatrix (columnSketchLeftMultiplier A Z C)

/-- The symmetry field of an exact column-sketch orthogonal-projector
certificate. -/
theorem columnSketchLeftMultiplier_symmetric_of_orthogonalProjectorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchOrthogonalProjectorCertificate A Z C) :
    IsSymmetricFiniteMatrix (columnSketchLeftMultiplier A Z C) :=
  hC.symmetric

/-- An exact column-sketch orthogonal-projector certificate makes
`P_C = (A Z) C` idempotent. -/
theorem columnSketchLeftMultiplier_idempotent_of_orthogonalProjectorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchOrthogonalProjectorCertificate A Z C) :
    ∀ i j,
      preconditionRows (columnSketchLeftMultiplier A Z C)
          (columnSketchLeftMultiplier A Z C) i j =
        columnSketchLeftMultiplier A Z C i j :=
  columnSketchLeftMultiplier_idempotent_of_generalizedInverse A Z C
    hC.generalizedInverse

/-- Packaged exact symmetric-idempotent projector surface for
`P_C = (A Z) C`: the multiplier is symmetric, reproduces the sketch, is
idempotent, factors through the sketch, and gives a rank-at-most-`r`
approximation `P_C A`. -/
theorem columnSketchLeftMultiplier_orthogonalProjectorSurface {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchOrthogonalProjectorCertificate A Z C) :
    IsSymmetricFiniteMatrix (columnSketchLeftMultiplier A Z C) ∧
      Nonempty (LeftFactorThrough (columnSketchLeftMultiplier A Z C) (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows (columnSketchLeftMultiplier A Z C) (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows (columnSketchLeftMultiplier A Z C)
            (columnSketchLeftMultiplier A Z C) i j =
          columnSketchLeftMultiplier A Z C i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) :=
  ⟨hC.symmetric,
    (columnSketchLeftMultiplier_projectorSurface_of_generalizedInverse A Z C
      hC.generalizedInverse).1,
    (columnSketchLeftMultiplier_projectorSurface_of_generalizedInverse A Z C
      hC.generalizedInverse).2.1,
    (columnSketchLeftMultiplier_projectorSurface_of_generalizedInverse A Z C
      hC.generalizedInverse).2.2.1,
    (columnSketchLeftMultiplier_projectorSurface_of_generalizedInverse A Z C
      hC.generalizedInverse).2.2.2⟩

/-- A symmetric idempotent row multiplier is Frobenius-nonexpansive on
rectangular matrices.  This is the row-wise orthogonal-projector contraction
needed for the CACM equation-(9) coupling term. -/
theorem frobNormSqRect_preconditionRows_le_of_symmetric_idempotent {m n : ℕ}
    (P : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (hSym : IsSymmetricFiniteMatrix P)
    (hIdem : ∀ i j, preconditionRows P P i j = P i j) :
    frobNormSqRect (preconditionRows P A) ≤ frobNormSqRect A := by
  have hIdemFinite : ∀ i j, finiteMatMul P P i j = P i j := by
    intro i j
    simpa [finiteMatMul, preconditionRows] using hIdem i j
  unfold frobNormSqRect
  rw [Finset.sum_comm]
  rw [Finset.sum_comm (f := fun i j => A i j ^ 2)]
  apply Finset.sum_le_sum
  intro j _
  have hcol :=
    finiteVecNorm2Sq_finiteMatVec_le_of_symmetric_idempotent
      P hSym hIdemFinite (fun i : Fin m => A i j)
  simpa [finiteVecNorm2Sq, finiteMatVec, preconditionRows] using hcol

/-- Norm form of row Frobenius nonexpansiveness for a symmetric idempotent
multiplier. -/
theorem frobNormRect_preconditionRows_le_of_symmetric_idempotent {m n : ℕ}
    (P : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (hSym : IsSymmetricFiniteMatrix P)
    (hIdem : ∀ i j, preconditionRows P P i j = P i j) :
    frobNormRect (preconditionRows P A) ≤ frobNormRect A := by
  unfold frobNormRect
  exact Real.sqrt_le_sqrt
    (frobNormSqRect_preconditionRows_le_of_symmetric_idempotent
      P A hSym hIdem)

/-- Exact column-sketch orthogonal-projector certificates make the displayed
multiplier `(A Z) C` Frobenius-nonexpansive on every rectangular tail matrix.
This closes the projector-contractivity part of the equation-(9) coupling
term, while construction of the certificate remains a separate exact or
floating-point obligation. -/
theorem frobNormRect_preconditionRows_columnSketchLeftMultiplier_le_of_orthogonalProjectorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) (Tail : Fin m → Fin n → ℝ)
    (hC : ColumnSketchOrthogonalProjectorCertificate A Z C) :
    frobNormRect (preconditionRows (columnSketchLeftMultiplier A Z C) Tail) ≤
      frobNormRect Tail :=
  frobNormRect_preconditionRows_le_of_symmetric_idempotent
    (columnSketchLeftMultiplier A Z C) Tail
    (columnSketchLeftMultiplier_symmetric_of_orthogonalProjectorCertificate
      A Z C hC)
    (columnSketchLeftMultiplier_idempotent_of_orthogonalProjectorCertificate
      A Z C hC)

/-- Coupling-tail certificate obtained by applying an exact orthogonal
column-sketch projector to the ambient source-tail residual bound.  The sampling
law remains exact by project convention; the theorem is exact-object and still
requires separate certificates for any computed projector, basis, SVD, inverse,
or product routine used to instantiate its hypotheses. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_orthogonalProjector_le_sqrt_one_add_eps_sq
    {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hC : ColumnSketchOrthogonalProjectorCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm Sigma) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma := by
  have hprojector :
      frobNormRect
          (preconditionRows (columnSketchLeftMultiplier A Z C)
            (sourceSketchResidualTail Tail Z V)) ≤
        frobNormRect (sourceSketchResidualTail Tail Z V) :=
    frobNormRect_preconditionRows_columnSketchLeftMultiplier_le_of_orthogonalProjectorCertificate
      A Z C (sourceSketchResidualTail Tail Z V) hC
  have htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤
        Real.sqrt (1 + eps ^ 2) * frobNorm Sigma :=
    frobNormRect_sourceSketchResidualTail_sourceSVDTail_le_sqrt_one_add_eps_sq
      Tail Utail Sigma Vperp Z V heps hTail hUtail hVperp hcrossTail
      hcrossHead hV hcomplete hcrossTerm
  exact le_trans hprojector htail

/-- Certificate-shaped Moore-Penrose surface for a column sketch `B = A Z` and
a coefficient table `C`.  The fields are the four usual exact equations:
`B C B = B`, `C B C = C`, symmetry of `B C`, and symmetry of `C B`.

This is still not a construction or an existence theorem for `(A Z)^+`; it is
the exact certificate a future pseudoinverse/full-rank theorem or computed
routine may instantiate. -/
structure ColumnSketchMoorePenroseCertificate {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) : Prop where
  sketch_reproduction :
    ∀ i a,
      preconditionRows (columnSketchLeftMultiplier A Z C) (columnSketch A Z) i a =
        columnSketch A Z i a
  coefficient_reproduction :
    ∀ a i,
      preconditionRows (columnSketchRightMultiplier A Z C) C a i = C a i
  left_symmetric :
    IsSymmetricFiniteMatrix (columnSketchLeftMultiplier A Z C)
  right_symmetric :
    IsSymmetricFiniteMatrix (columnSketchRightMultiplier A Z C)

/-- The `B C B = B` Moore-Penrose field is exactly the generalized-inverse
certificate already used by the equation (9) projector surface. -/
theorem ColumnSketchMoorePenroseCertificate.to_generalizedInverse {m n r : ℕ}
    {A : Fin m → Fin n → ℝ} {Z : Fin n → Fin r → ℝ}
    {C : Fin r → Fin m → ℝ}
    (hC : ColumnSketchMoorePenroseCertificate A Z C) :
    ColumnSketchGeneralizedInverse A Z C where
  reproducesSketch := hC.sketch_reproduction

/-- A Moore-Penrose certificate supplies the exact symmetric generalized-inverse
projector certificate for `P_C = (A Z) C`. -/
theorem ColumnSketchMoorePenroseCertificate.to_orthogonalProjectorCertificate
    {m n r : ℕ}
    {A : Fin m → Fin n → ℝ} {Z : Fin n → Fin r → ℝ}
    {C : Fin r → Fin m → ℝ}
    (hC : ColumnSketchMoorePenroseCertificate A Z C) :
    ColumnSketchOrthogonalProjectorCertificate A Z C where
  generalizedInverse := hC.to_generalizedInverse
  symmetric := hC.left_symmetric

/-- Moore-Penrose-certificate version of the coupling-tail source-SVD
certificate.  This is the form consumed by the later source-coefficient
equation-(9) rank/residual surfaces. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq
    {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm Sigma) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_orthogonalProjector_le_sqrt_one_add_eps_sq
    A Tail Utail Sigma Vperp Z V C heps hC.to_orthogonalProjectorCertificate
    hTail hUtail hVperp hcrossTail hcrossHead hV hcomplete hcrossTerm

/-- The right-acting spectral certificate for the CACM source cross term.  If
the transpose action of
`(V_perp^T Z)(V_k^T Z)^{-1}` has operator-2 radius `eps`, then the Frobenius
cross term consumed by LR.1y/LR.1z/LR.1aa follows.

This is still exact-object: the operator certificate is supplied for the exact
rectangular cross factor.  Proving equivalence with an ordinary spectral-norm
certificate for the non-transposed factor remains a separate transpose-norm
foundation. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_transpose_rectOpNorm2Le
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hOp :
      rectOpNorm2Le
        (finiteTranspose (rightSketchCrossGramRectInvFactor Vperp Z V))
        eps) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      eps * frobNorm Sigma :=
  frobNormRect_matMulRectLeft_le_of_transpose_rectOpNorm2Le
    Sigma (rightSketchCrossGramRectInvFactor Vperp Z V) heps hOp

/-- Moore-Penrose projected source-tail certificate driven by a right-acting
operator-2 bound on the exact rectangular cross factor instead of a supplied
Frobenius cross-term certificate. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq_of_transpose_rectOpNorm2Le
    {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hOp :
      rectOpNorm2Le
        (finiteTranspose (rightSketchCrossGramRectInvFactor Vperp Z V))
        eps) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq
    A Tail Utail Sigma Vperp Z V C heps hC hTail hUtail hVperp hcrossTail
    hcrossHead hV hcomplete
    (frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_transpose_rectOpNorm2Le
      Sigma Vperp Z V heps hOp)

/-- Ordinary rectangular operator-2 certificate for the CACM source cross term.
This is the non-transposed form of the LR.1ab handoff: if the exact factor
`(V_perp^T Z)(V_k^T Z)^{-1}` has operator-2 radius `eps`, then the Frobenius
cross term consumed by LR.1y/LR.1z/LR.1aa follows. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_rectOpNorm2Le
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hOp :
      rectOpNorm2Le
        (rightSketchCrossGramRectInvFactor Vperp Z V)
        eps) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      eps * frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_transpose_rectOpNorm2Le
    Sigma Vperp Z V heps
    (rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (rightSketchCrossGramRectInvFactor Vperp Z V) heps hOp)

/-- Moore-Penrose projected source-tail certificate driven by an ordinary
operator-2 bound on the exact rectangular cross factor. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq_of_rectOpNorm2Le
    {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hOp :
      rectOpNorm2Le
        (rightSketchCrossGramRectInvFactor Vperp Z V)
        eps) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq
    A Tail Utail Sigma Vperp Z V C heps hC hTail hUtail hVperp hcrossTail
    hcrossHead hV hcomplete
    (frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_rectOpNorm2Le
      Sigma Vperp Z V heps hOp)

/-- Computed-cross-factor perturbation certificate for the source cross term.

If an implementation supplies a computed non-probability cross factor `Mhat`
with an ordinary rectangular operator certificate and a Frobenius perturbation
radius to the exact analysis factor `M`, then the exact Frobenius cross term
has the enlarged radius `eps + tau`.  This is the local D5 transfer used when
cross products, inverses, and products are computed approximately while the
sampling law itself remains exact by convention. -/
theorem frobNormRect_sigma_exactFactor_le_of_computed_rectOpNorm2Le_of_frobNormRect_error
    {q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (M Mhat : Fin q → Fin r → ℝ)
    {eps tau : ℝ}
    (heps : 0 ≤ eps)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hErr : frobNormRect (fun a b => M a b - Mhat a b) ≤ tau) :
    frobNormRect (matMulRectLeft Sigma M) ≤
      (eps + tau) * frobNorm Sigma := by
  let E : Fin q → Fin r → ℝ := fun a b => M a b - Mhat a b
  have hsplit :
      matMulRectLeft Sigma M =
        fun a b => matMulRectLeft Sigma Mhat a b + matMulRectLeft Sigma E a b := by
    ext a b
    unfold matMulRectLeft E
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  have hMhatCross :
      frobNormRect (matMulRectLeft Sigma Mhat) ≤ eps * frobNorm Sigma :=
    frobNormRect_matMulRectLeft_le_of_transpose_rectOpNorm2Le
      Sigma Mhat heps
      (rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Mhat heps hMhat)
  have hE :
      frobNormRect (matMulRectLeft Sigma E) ≤ frobNorm Sigma * tau := by
    calc
      frobNormRect (matMulRectLeft Sigma E)
          ≤ frobNorm Sigma * frobNormRect E :=
            frobNormRect_matMulRectLeft_le Sigma E
      _ ≤ frobNorm Sigma * tau :=
            mul_le_mul_of_nonneg_left (by simpa [E] using hErr)
              (frobNorm_nonneg Sigma)
  calc
    frobNormRect (matMulRectLeft Sigma M)
        =
          frobNormRect
            (fun a b =>
              matMulRectLeft Sigma Mhat a b + matMulRectLeft Sigma E a b) := by
          rw [hsplit]
    _ ≤
        frobNormRect (matMulRectLeft Sigma Mhat) +
          frobNormRect (matMulRectLeft Sigma E) :=
        frobNormRect_add_le (matMulRectLeft Sigma Mhat) (matMulRectLeft Sigma E)
    _ ≤ eps * frobNorm Sigma + frobNorm Sigma * tau :=
        add_le_add hMhatCross hE
    _ = (eps + tau) * frobNorm Sigma := by ring

/-- CACM equation-(9) cross-term transfer from a computed non-probability cross
factor.  The exact factor is still
`(V_perp^T Z)(V_k^T Z)^{-1}`, but the implementation-facing hypotheses are an
operator certificate for the computed `Mhat` and a Frobenius perturbation
certificate comparing `Mhat` with that exact factor. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_frobNormRect_error
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps tau : ℝ}
    (heps : 0 ≤ eps)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hErr :
      frobNormRect
          (fun a b => rightSketchCrossGramRectInvFactor Vperp Z V a b -
            Mhat a b) ≤ tau) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + tau) * frobNorm Sigma :=
  frobNormRect_sigma_exactFactor_le_of_computed_rectOpNorm2Le_of_frobNormRect_error
    Sigma (rightSketchCrossGramRectInvFactor Vperp Z V) Mhat heps hMhat hErr

/-- Moore-Penrose projected source-tail certificate driven by a computed
non-probability cross factor.

The sampling law for `Z` remains exact.  The extra radius `tau` is reserved for
the computed cross-product/inverse/product data summarized by `Mhat`; concrete
floating-point routines must instantiate the displayed Frobenius perturbation
certificate. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_tau_sq_of_computed_rectOpNorm2Le
    {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps tau : ℝ}
    (heps : 0 ≤ eps)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hErr :
      frobNormRect
          (fun a b => rightSketchCrossGramRectInvFactor Vperp Z V a b -
            Mhat a b) ≤ tau) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt (1 + (eps + tau) ^ 2) * frobNorm Sigma := by
  have htau : 0 ≤ tau :=
    le_trans
      (frobNormRect_nonneg
        (fun a b => rightSketchCrossGramRectInvFactor Vperp Z V a b - Mhat a b))
      hErr
  have hrad : 0 ≤ eps + tau := add_nonneg heps htau
  exact
    frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq
      A Tail Utail Sigma Vperp Z V C hrad hC hTail hUtail hVperp hcrossTail
      hcrossHead hV hcomplete
      (frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_frobNormRect_error
        Sigma Vperp Z V Mhat heps hMhat hErr)

/-- Entrywise-error instantiation of the computed-cross-factor certificate.

If a concrete routine bounds every entry of the exact CACM cross factor minus
the computed factor `Mhat` by `eta`, then the Frobenius perturbation radius in
LR.1ad may be chosen as `sqrt(q*r) * eta`. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_entry_abs_error
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps eta : ℝ}
    (heps : 0 ≤ eps) (heta : 0 ≤ eta)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hEntry :
      ∀ a b,
        |rightSketchCrossGramRectInvFactor Vperp Z V a b - Mhat a b| ≤ eta) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * eta) * frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_frobNormRect_error
    Sigma Vperp Z V Mhat heps hMhat
    (frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
      (fun a b => rightSketchCrossGramRectInvFactor Vperp Z V a b - Mhat a b)
      heta hEntry)

/-- Projected Moore-Penrose source-tail certificate from an entrywise computed
cross-factor error budget. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_entry_sq_of_computed_rectOpNorm2Le
    {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps eta : ℝ}
    (heps : 0 ≤ eps) (heta : 0 ≤ eta)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hEntry :
      ∀ a b,
        |rightSketchCrossGramRectInvFactor Vperp Z V a b - Mhat a b| ≤ eta) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt (1 + (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * eta) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_tau_sq_of_computed_rectOpNorm2Le
    A Tail Utail Sigma Vperp Z V C Mhat heps hC hTail hUtail hVperp hcrossTail
    hcrossHead hV hcomplete hMhat
    (frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
      (fun a b => rightSketchCrossGramRectInvFactor Vperp Z V a b - Mhat a b)
      heta hEntry)

/-- Entrywise cross-factor error from component certificates for the computed
rectangular cross product and computed inverse factor.

Here `Xhat` is the computed version of `Vperpᵀ Z`, `Yhat` is the computed
version of `(Vᵀ Z)^{-1}`, and `Mhat` is the rounded product `Xhat * Yhat`.
The three radii separately charge the left input, right input, and final
product rounding. -/
theorem rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_component_sums
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Xhat : Fin q → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {alpha beta rho : ℝ}
    (hLeft :
      ∀ a c,
        ∑ b : Fin r,
          |rightSketchCrossGramRect Vperp Z a b - Xhat a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hRight :
      ∀ a c,
        ∑ b : Fin r,
          |Xhat a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ beta)
    (hRound :
      ∀ a c, |(∑ b : Fin r, Xhat a b * Yhat b c) - Mhat a c| ≤ rho) :
    ∀ a c,
      |rightSketchCrossGramRectInvFactor Vperp Z V a c - Mhat a c| ≤
        alpha + beta + rho := by
  intro a c
  unfold rightSketchCrossGramRectInvFactor
  exact
    rectMatMul_entry_abs_sub_computed_le_of_component_sums
      (rightSketchCrossGramRect Vperp Z) Xhat
      (nonsingInv r (rightSketchCrossGram V Z)) Yhat Mhat
      hLeft hRight hRound a c

/-- Cross-term certificate when the computed cross factor is assembled from
componentwise-certified computed cross-gram, inverse, and product data. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_component_error
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Xhat : Fin q → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps alpha beta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hrho : 0 ≤ rho)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hLeft :
      ∀ a c,
        ∑ b : Fin r,
          |rightSketchCrossGramRect Vperp Z a b - Xhat a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hRight :
      ∀ a c,
        ∑ b : Fin r,
          |Xhat a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ beta)
    (hRound :
      ∀ a c, |(∑ b : Fin r, Xhat a b * Yhat b c) - Mhat a c| ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + beta + rho)) *
        frobNorm Sigma := by
  have heta : 0 ≤ alpha + beta + rho := by linarith
  exact
    frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_entry_abs_error
      Sigma Vperp Z V Mhat heps heta hMhat
      (rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_component_sums
        Vperp Z V Xhat Yhat Mhat hLeft hRight hRound)

/-- Projected Moore-Penrose source-tail certificate when the computed cross
factor is assembled from componentwise-certified computed cross-gram, inverse,
and product data. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_component_sq_of_computed_rectOpNorm2Le
    {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Xhat : Fin q → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps alpha beta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hrho : 0 ≤ rho)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hLeft :
      ∀ a c,
        ∑ b : Fin r,
          |rightSketchCrossGramRect Vperp Z a b - Xhat a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hRight :
      ∀ a c,
        ∑ b : Fin r,
          |Xhat a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ beta)
    (hRound :
      ∀ a c, |(∑ b : Fin r, Xhat a b * Yhat b c) - Mhat a c| ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + beta + rho)) ^ 2) *
        frobNorm Sigma := by
  have heta : 0 ≤ alpha + beta + rho := by linarith
  exact
    frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_entry_sq_of_computed_rectOpNorm2Le
      A Tail Utail Sigma Vperp Z V C Mhat heps heta hC hTail hUtail hVperp
      hcrossTail hcrossHead hV hcomplete hMhat
      (rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_component_sums
        Vperp Z V Xhat Yhat Mhat hLeft hRight hRound)

/-- Entrywise cross-factor error when the rectangular cross Gram is computed by
the concrete floating-point matrix product `fl((Vperpᵀ)Z)`, while the inverse
factor and final product remain certificate-facing computed quantities. -/
theorem rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_flMatMul_crossGram_component_sums
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {alpha beta rho : ℝ}
    (hγ : gammaValid fp n)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hRight :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ beta)
    (hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            Mhat a c| ≤ rho) :
    ∀ a c,
      |rightSketchCrossGramRectInvFactor Vperp Z V a c - Mhat a c| ≤
        alpha + beta + rho := by
  have hLeft :
      ∀ a c,
        ∑ b : Fin r,
          |rightSketchCrossGramRect Vperp Z a b -
              flRightSketchCrossGramRect fp Vperp Z a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha := by
    intro a c
    exact le_trans
      (rightSketchCrossGramRect_flMatMul_component_left_error_le
        fp Vperp Z (nonsingInv r (rightSketchCrossGram V Z)) hγ a c)
      (hLeftBudget a c)
  exact
    rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_component_sums
      Vperp Z V (flRightSketchCrossGramRect fp Vperp Z) Yhat Mhat
      hLeft hRight hRound

/-- Adapter from an entrywise computed-inverse certificate to the `beta`
component sum used by the computed cross-factor theorem.

This theorem does not claim that any particular inverse routine has produced
`Yhat`. It says that once such a routine supplies the visible entrywise
certificate for the exact analysis inverse, the remaining LR.1af/LR.1ag right
component budget follows from a row absolute-sum budget on the computed left
factor. Sampling probabilities and laws remain exact mathematical inputs. -/
theorem rightSketchCrossGramRectInvFactor_inverse_component_sum_le_of_entry_abs_error
    {n q r : ℕ}
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Xhat : Fin q → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eta chi : ℝ}
    (heta : 0 ≤ eta)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs : ∀ a, ∑ b : Fin r, |Xhat a b| ≤ chi) :
    ∀ a c,
      ∑ b : Fin r,
        |Xhat a b| *
          |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤
        chi * eta := by
  intro a c
  calc
    ∑ b : Fin r,
        |Xhat a b| *
          |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c|
        ≤ ∑ b : Fin r, |Xhat a b| * eta := by
          apply Finset.sum_le_sum
          intro b _
          exact mul_le_mul_of_nonneg_left (hInvEntry b c) (abs_nonneg _)
    _ = (∑ b : Fin r, |Xhat a b|) * eta := by
          rw [Finset.sum_mul]
    _ ≤ chi * eta :=
          mul_le_mul_of_nonneg_right (hXRowAbs a) heta

/-- Concrete-left-factor version of
`rightSketchCrossGramRectInvFactor_inverse_component_sum_le_of_entry_abs_error`
for `Xhat = fl((Vperpᵀ)Z)`. The inverse routine is still represented only by
the entrywise certificate for `Yhat`; the theorem does not charge probability
construction. -/
theorem rightSketchCrossGramRectInvFactor_flMatMul_inverse_component_sum_le_of_entry_abs_error
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eta chi : ℝ}
    (heta : 0 ≤ eta)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi) :
    ∀ a c,
      ∑ b : Fin r,
        |flRightSketchCrossGramRect fp Vperp Z a b| *
          |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤
        chi * eta :=
  rightSketchCrossGramRectInvFactor_inverse_component_sum_le_of_entry_abs_error
    Z V (flRightSketchCrossGramRect fp Vperp Z) Yhat
    heta hInvEntry hXRowAbs

/-- Entrywise cross-factor error when the rectangular cross Gram is computed by
`fl((Vperpᵀ)Z)`, the inverse factor has a supplied entrywise perturbation
certificate, and the final product has a supplied rounding certificate. -/
theorem rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_flMatMul_crossGram_inverse_entry_abs_error
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {alpha chi eta rho : ℝ}
    (hγ : gammaValid fp n)
    (heta : 0 ≤ eta)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            Mhat a c| ≤ rho) :
    ∀ a c,
      |rightSketchCrossGramRectInvFactor Vperp Z V a c - Mhat a c| ≤
        alpha + chi * eta + rho :=
  rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_flMatMul_crossGram_component_sums
    fp Vperp Z V Yhat Mhat hγ hLeftBudget
    (rightSketchCrossGramRectInvFactor_flMatMul_inverse_component_sum_le_of_entry_abs_error
      fp Vperp Z V Yhat heta hInvEntry hXRowAbs)
    hRound

/-- Cross-term certificate with a concrete floating-point computation of the
rectangular cross Gram `Vperpᵀ Z`.  The inverse factor `Yhat`, product `Mhat`,
and operator certificate for `Mhat` remain explicit non-probability
implementation certificates. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_flMatMul_crossGram_component_error
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps alpha beta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hrho : 0 ≤ rho)
    (hγ : gammaValid fp n)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hRight :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ beta)
    (hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            Mhat a c| ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + beta + rho)) *
        frobNorm Sigma := by
  have hLeft :
      ∀ a c,
        ∑ b : Fin r,
          |rightSketchCrossGramRect Vperp Z a b -
              flRightSketchCrossGramRect fp Vperp Z a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha := by
    intro a c
    exact le_trans
      (rightSketchCrossGramRect_flMatMul_component_left_error_le
        fp Vperp Z (nonsingInv r (rightSketchCrossGram V Z)) hγ a c)
      (hLeftBudget a c)
  exact
    frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_component_error
      Sigma Vperp Z V (flRightSketchCrossGramRect fp Vperp Z) Yhat Mhat
      heps halpha hbeta hrho hMhat hLeft hRight hRound

/-- Cross-term certificate with a concrete `fl_matMul` rectangular cross Gram
and an entrywise computed-inverse perturbation certificate.

The displayed `chi * eta` term is the computed-inverse contribution: `eta`
bounds every entry of the exact inverse minus `Yhat`, while `chi` bounds the
row absolute sums of the computed rectangular factor. No floating-point error
is charged to sampling probabilities or sampling laws. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_flMatMul_crossGram_inverse_entry_error
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps alpha chi eta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγ : gammaValid fp n)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            Mhat a c| ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma := by
  have hbeta : 0 ≤ chi * eta := mul_nonneg hchi heta
  exact
    frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_flMatMul_crossGram_component_error
      fp Sigma Vperp Z V Yhat Mhat heps halpha hbeta hrho hγ hMhat
      hLeftBudget
      (rightSketchCrossGramRectInvFactor_flMatMul_inverse_component_sum_le_of_entry_abs_error
        fp Vperp Z V Yhat heta hInvEntry hXRowAbs)
      hRound

/-- Projected Moore-Penrose source-tail certificate with a concrete
floating-point computation of the rectangular cross Gram `Vperpᵀ Z`; inverse,
product, projector, and operator certificates remain explicit. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_component_sq_of_computed_rectOpNorm2Le
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps alpha beta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hrho : 0 ≤ rho)
    (hγ : gammaValid fp n)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hRight :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ beta)
    (hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            Mhat a c| ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + beta + rho)) ^ 2) *
        frobNorm Sigma := by
  have hLeft :
      ∀ a c,
        ∑ b : Fin r,
          |rightSketchCrossGramRect Vperp Z a b -
              flRightSketchCrossGramRect fp Vperp Z a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha := by
    intro a c
    exact le_trans
      (rightSketchCrossGramRect_flMatMul_component_left_error_le
        fp Vperp Z (nonsingInv r (rightSketchCrossGram V Z)) hγ a c)
      (hLeftBudget a c)
  exact
    frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_component_sq_of_computed_rectOpNorm2Le
      A Tail Utail Sigma Vperp Z V C
      (flRightSketchCrossGramRect fp Vperp Z) Yhat Mhat
      heps halpha hbeta hrho hC hTail hUtail hVperp
      hcrossTail hcrossHead hV hcomplete hMhat hLeft hRight hRound

/-- Projected Moore-Penrose source-tail certificate with concrete `fl_matMul`
rectangular cross Gram and an entrywise computed-inverse perturbation
certificate. The inverse routine itself remains a ledger obligation until a
concrete algorithm proves `hInvEntry`. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_inverse_entry_sq_of_computed_rectOpNorm2Le
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps alpha chi eta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγ : gammaValid fp n)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            Mhat a c| ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma := by
  have hbeta : 0 ≤ chi * eta := mul_nonneg hchi heta
  exact
    frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_component_sq_of_computed_rectOpNorm2Le
      fp A Tail Utail Sigma Vperp Z V C Yhat Mhat heps halpha hbeta hrho hγ hC
      hTail hUtail hVperp hcrossTail hcrossHead hV hcomplete hMhat
      hLeftBudget
      (rightSketchCrossGramRectInvFactor_flMatMul_inverse_component_sum_le_of_entry_abs_error
        fp Vperp Z V Yhat heta hInvEntry hXRowAbs)
      hRound

/-- Floating-point product used to assemble the computed equation-(9) cross
factor from a computed rectangular cross Gram `Xhat` and computed inverse
factor `Yhat`.  Sampling probabilities remain exact mathematical inputs; this
is only the non-probability matrix-product computation. -/
noncomputable def flRightSketchCrossGramRectInvFactorProduct
    (fp : FPModel) {q r : ℕ}
    (Xhat : Fin q → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ) :
    Fin q → Fin r → ℝ :=
  fl_matMul fp q r r Xhat Yhat

/-- Entrywise dot-product budget for the final rounded product
`fl(Xhat * Yhat)`. -/
noncomputable def rightSketchCrossGramRectInvFactorProductDotBudget
    (fp : FPModel) {q r : ℕ}
    (Xhat : Fin q → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ) :
    Fin q → Fin r → ℝ :=
  fun a c => gamma fp r * ∑ b : Fin r, |Xhat a b| * |Yhat b c|

/-- Entrywise floating-point error for the final rounded product
`fl(Xhat * Yhat)`. -/
theorem rightSketchCrossGramRectInvFactorProduct_flMatMul_entry_abs_error_le
    (fp : FPModel) {q r : ℕ}
    (Xhat : Fin q → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (hγ : gammaValid fp r) :
    ∀ a c,
      |(∑ b : Fin r, Xhat a b * Yhat b c) -
          flRightSketchCrossGramRectInvFactorProduct fp Xhat Yhat a c| ≤
        rightSketchCrossGramRectInvFactorProductDotBudget fp Xhat Yhat a c := by
  intro a c
  have hdot := matMul_error_bound fp q r r Xhat Yhat hγ a c
  simpa [flRightSketchCrossGramRectInvFactorProduct,
    rightSketchCrossGramRectInvFactorProductDotBudget, abs_sub_comm] using hdot

/-- Entrywise computed cross-factor error with concrete `fl_matMul` routines
for both `Vperpᵀ Z` and the final product `Xhat * Yhat`.

The only remaining inverse-side obligation is the entrywise certificate for
`Yhat`; the final product radius `rho` is now supplied by the displayed
matrix-product dot-budget. -/
theorem rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_flMatMul_crossGram_inverse_entry_abs_error_flMatMul_product
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {alpha chi eta rho : ℝ}
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (heta : 0 ≤ eta)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    ∀ a c,
      |rightSketchCrossGramRectInvFactor Vperp Z V a c -
          flRightSketchCrossGramRectInvFactorProduct fp
            (flRightSketchCrossGramRect fp Vperp Z) Yhat a c| ≤
        alpha + chi * eta + rho := by
  have hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            flRightSketchCrossGramRectInvFactorProduct fp
              (flRightSketchCrossGramRect fp Vperp Z) Yhat a c| ≤ rho := by
    intro a c
    exact le_trans
      (rightSketchCrossGramRectInvFactorProduct_flMatMul_entry_abs_error_le
        fp (flRightSketchCrossGramRect fp Vperp Z) Yhat hγr a c)
      (hProductBudget a c)
  exact
    rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_flMatMul_crossGram_inverse_entry_abs_error
      fp Vperp Z V Yhat
      (flRightSketchCrossGramRectInvFactorProduct fp
        (flRightSketchCrossGramRect fp Vperp Z) Yhat)
      hγn heta hLeftBudget hInvEntry hXRowAbs hRound

/-- Cross-term certificate with concrete `fl_matMul` routines for the
rectangular cross Gram and the final product, plus an entrywise inverse-factor
certificate. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_flMatMul_crossGram_inverse_entry_flMatMul_product
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps alpha chi eta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hMhat :
      rectOpNorm2Le
        (flRightSketchCrossGramRectInvFactorProduct fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat)
        eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma := by
  have hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            flRightSketchCrossGramRectInvFactorProduct fp
              (flRightSketchCrossGramRect fp Vperp Z) Yhat a c| ≤ rho := by
    intro a c
    exact le_trans
      (rightSketchCrossGramRectInvFactorProduct_flMatMul_entry_abs_error_le
        fp (flRightSketchCrossGramRect fp Vperp Z) Yhat hγr a c)
      (hProductBudget a c)
  exact
    frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_flMatMul_crossGram_inverse_entry_error
      fp Sigma Vperp Z V Yhat
      (flRightSketchCrossGramRectInvFactorProduct fp
        (flRightSketchCrossGramRect fp Vperp Z) Yhat)
      heps halpha hchi heta hrho hγn hMhat hLeftBudget hInvEntry hXRowAbs
      hRound

/-- Projected Moore-Penrose source-tail certificate with concrete `fl_matMul`
rectangular cross Gram and final product, plus an entrywise computed-inverse
certificate. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_inverse_entry_flMatMul_product_sq_of_computed_rectOpNorm2Le
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps alpha chi eta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hMhat :
      rectOpNorm2Le
        (flRightSketchCrossGramRectInvFactorProduct fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat)
        eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma := by
  have hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            flRightSketchCrossGramRectInvFactorProduct fp
              (flRightSketchCrossGramRect fp Vperp Z) Yhat a c| ≤ rho := by
    intro a c
    exact le_trans
      (rightSketchCrossGramRectInvFactorProduct_flMatMul_entry_abs_error_le
        fp (flRightSketchCrossGramRect fp Vperp Z) Yhat hγr a c)
      (hProductBudget a c)
  exact
    frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_inverse_entry_sq_of_computed_rectOpNorm2Le
      fp A Tail Utail Sigma Vperp Z V C Yhat
      (flRightSketchCrossGramRectInvFactorProduct fp
        (flRightSketchCrossGramRect fp Vperp Z) Yhat)
      heps halpha hchi heta hrho hγn hC hTail hUtail hVperp
      hcrossTail hcrossHead hV hcomplete hMhat hLeftBudget hInvEntry hXRowAbs
      hRound

/-- A visible Frobenius bound for the concrete computed product supplies the
ordinary rectangular operator certificate required by the computed cross-factor
theorems.  This is a deterministic certificate handoff for the non-probability
quantity `Mhat = fl(fl((Vperpᵀ)Z) * Yhat)`. -/
theorem rectOpNorm2Le_flRightSketchCrossGramRectInvFactorProduct_of_frobNormRect_le
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps : ℝ}
    (hFrob :
      frobNormRect
          (flRightSketchCrossGramRectInvFactorProduct fp
            (flRightSketchCrossGramRect fp Vperp Z) Yhat) ≤ eps) :
    rectOpNorm2Le
      (flRightSketchCrossGramRectInvFactorProduct fp
        (flRightSketchCrossGramRect fp Vperp Z) Yhat)
      eps :=
  rectOpNorm2Le_of_frobNormRect_le
    (flRightSketchCrossGramRectInvFactorProduct fp
      (flRightSketchCrossGramRect fp Vperp Z) Yhat)
    hFrob

/-- Cross-term certificate with concrete `fl_matMul` routines and a visible
Frobenius certificate for the computed product instead of an abstract operator
certificate. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_frobNormRect_flMatMul_crossGram_inverse_entry_flMatMul_product
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps alpha chi eta rho : ℝ}
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hMhatFrob :
      frobNormRect
          (flRightSketchCrossGramRectInvFactorProduct fp
            (flRightSketchCrossGramRect fp Vperp Z) Yhat) ≤ eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma := by
  let Mhat :=
    flRightSketchCrossGramRectInvFactorProduct fp
      (flRightSketchCrossGramRect fp Vperp Z) Yhat
  have heps : 0 ≤ eps :=
    le_trans (frobNormRect_nonneg Mhat) hMhatFrob
  have hMhat : rectOpNorm2Le Mhat eps := by
    simpa [Mhat] using
      rectOpNorm2Le_flRightSketchCrossGramRectInvFactorProduct_of_frobNormRect_le
        fp Vperp Z Yhat hMhatFrob
  exact
    frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_flMatMul_crossGram_inverse_entry_flMatMul_product
      fp Sigma Vperp Z V Yhat heps halpha hchi heta hrho hγn hγr hMhat
      hLeftBudget hInvEntry hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate with concrete `fl_matMul`
rectangular cross Gram and final product, an entrywise computed-inverse
certificate, and a visible Frobenius certificate for the computed product. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_frobNormRect_flMatMul_crossGram_inverse_entry_flMatMul_product_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps alpha chi eta rho : ℝ}
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hMhatFrob :
      frobNormRect
          (flRightSketchCrossGramRectInvFactorProduct fp
            (flRightSketchCrossGramRect fp Vperp Z) Yhat) ≤ eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma := by
  let Mhat :=
    flRightSketchCrossGramRectInvFactorProduct fp
      (flRightSketchCrossGramRect fp Vperp Z) Yhat
  have heps : 0 ≤ eps :=
    le_trans (frobNormRect_nonneg Mhat) hMhatFrob
  have hMhat : rectOpNorm2Le Mhat eps := by
    simpa [Mhat] using
      rectOpNorm2Le_flRightSketchCrossGramRectInvFactorProduct_of_frobNormRect_le
        fp Vperp Z Yhat hMhatFrob
  exact
    frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_inverse_entry_flMatMul_product_sq_of_computed_rectOpNorm2Le
      fp A Tail Utail Sigma Vperp Z V C Yhat heps halpha hchi heta hrho hγn hγr
      hC hTail hUtail hVperp hcrossTail hcrossHead hV hcomplete hMhat
      hLeftBudget hInvEntry hXRowAbs hProductBudget

/-- Entry magnitude of the concrete rounded product from a visible absolute
product sum and the `fl_matMul` dot-product error budget.  This is a
non-probability certificate source for the computed product itself. -/
theorem rightSketchCrossGramRectInvFactorProduct_entry_abs_le_of_product_sum_budget
    (fp : FPModel) {q r : ℕ}
    (Xhat : Fin q → Fin r → ℝ) (Yhat : Fin r → Fin r → ℝ)
    {kappa rho : ℝ}
    (hγ : gammaValid fp r)
    (hProductAbs :
      ∀ a c, ∑ b : Fin r, |Xhat a b| * |Yhat b c| ≤ kappa)
    (hProductBudget :
      ∀ a c, rightSketchCrossGramRectInvFactorProductDotBudget fp Xhat Yhat a c ≤
        rho) :
    ∀ a c,
      |flRightSketchCrossGramRectInvFactorProduct fp Xhat Yhat a c| ≤
        kappa + rho := by
  intro a c
  let exactDot : ℝ := ∑ b : Fin r, Xhat a b * Yhat b c
  let Mhat : Fin q → Fin r → ℝ :=
    flRightSketchCrossGramRectInvFactorProduct fp Xhat Yhat
  have hRound : |exactDot - Mhat a c| ≤ rho := by
    exact le_trans
      (by
        simpa [exactDot, Mhat] using
          rightSketchCrossGramRectInvFactorProduct_flMatMul_entry_abs_error_le
            fp Xhat Yhat hγ a c)
      (hProductBudget a c)
  have hDotAbs :
      |exactDot| ≤ ∑ b : Fin r, |Xhat a b| * |Yhat b c| := by
    unfold exactDot
    calc
      |∑ b : Fin r, Xhat a b * Yhat b c|
          ≤ ∑ b : Fin r, |Xhat a b * Yhat b c| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ b : Fin r, |Xhat a b| * |Yhat b c| := by
            apply Finset.sum_congr rfl
            intro b _
            exact abs_mul (Xhat a b) (Yhat b c)
  have hTri : |Mhat a c| ≤ |exactDot| + |exactDot - Mhat a c| := by
    calc
      |Mhat a c| = |Mhat a c - 0| := by ring_nf
      _ ≤ |Mhat a c - exactDot| + |exactDot - 0| :=
          abs_sub_le (Mhat a c) exactDot 0
      _ = |exactDot - Mhat a c| + |exactDot| := by
          rw [abs_sub_comm, sub_zero]
      _ = |exactDot| + |exactDot - Mhat a c| := by rw [add_comm]
  calc
    |flRightSketchCrossGramRectInvFactorProduct fp Xhat Yhat a c|
        = |Mhat a c| := by rfl
    _ ≤ |exactDot| + |exactDot - Mhat a c| := hTri
    _ ≤ kappa + rho :=
        add_le_add (le_trans hDotAbs (hProductAbs a c)) hRound

/-- Uniform absolute-product sums give a Frobenius certificate for the concrete
rounded product `fl_matMul Xhat Yhat`. -/
theorem frobNormRect_flRightSketchCrossGramRectInvFactorProduct_le_sqrt_mul_product_sum_budget
    (fp : FPModel) {q r : ℕ}
    (Xhat : Fin q → Fin r → ℝ) (Yhat : Fin r → Fin r → ℝ)
    {kappa rho : ℝ}
    (hkappa : 0 ≤ kappa) (hrho : 0 ≤ rho)
    (hγ : gammaValid fp r)
    (hProductAbs :
      ∀ a c, ∑ b : Fin r, |Xhat a b| * |Yhat b c| ≤ kappa)
    (hProductBudget :
      ∀ a c, rightSketchCrossGramRectInvFactorProductDotBudget fp Xhat Yhat a c ≤
        rho) :
    frobNormRect
        (flRightSketchCrossGramRectInvFactorProduct fp Xhat Yhat) ≤
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) :=
  frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
    (flRightSketchCrossGramRectInvFactorProduct fp Xhat Yhat)
    (add_nonneg hkappa hrho)
    (rightSketchCrossGramRectInvFactorProduct_entry_abs_le_of_product_sum_budget
      fp Xhat Yhat hγ hProductAbs hProductBudget)

/-- Product absolute-sum budgets can supply the computed-product operator
certificate by first producing a Frobenius certificate and then using the
deterministic Frobenius-to-operator handoff. -/
theorem rectOpNorm2Le_flRightSketchCrossGramRectInvFactorProduct_of_product_sum_budget
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps kappa rho : ℝ}
    (hkappa : 0 ≤ kappa) (hrho : 0 ≤ rho)
    (hγr : gammaValid fp r)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| * |Yhat b c| ≤ kappa)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho)
    (hRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ eps) :
    rectOpNorm2Le
      (flRightSketchCrossGramRectInvFactorProduct fp
        (flRightSketchCrossGramRect fp Vperp Z) Yhat)
      eps :=
  rectOpNorm2Le_flRightSketchCrossGramRectInvFactorProduct_of_frobNormRect_le
    fp Vperp Z Yhat
    (le_trans
      (frobNormRect_flRightSketchCrossGramRectInvFactorProduct_le_sqrt_mul_product_sum_budget
        fp (flRightSketchCrossGramRect fp Vperp Z) Yhat hkappa hrho hγr
        hProductAbs hProductBudget)
      hRadius)

/-- Cross-term certificate where the computed product's operator hypothesis is
instantiated from a visible absolute-product-sum budget for `fl(Xhat Yhat)`. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps kappa alpha chi eta rho : ℝ}
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| * |Yhat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_frobNormRect_flMatMul_crossGram_inverse_entry_flMatMul_product
    fp Sigma Vperp Z V Yhat halpha hchi heta hrho hγn hγr
    (le_trans
      (frobNormRect_flRightSketchCrossGramRectInvFactorProduct_le_sqrt_mul_product_sum_budget
        fp (flRightSketchCrossGramRect fp Vperp Z) Yhat hkappa hrho hγr
        hProductAbs hProductBudget)
      hProductFrobRadius)
    hLeftBudget hInvEntry hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate where the computed product's
Frobenius/operator certificate is supplied by an absolute-product-sum budget. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps kappa alpha chi eta rho : ℝ}
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| * |Yhat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_frobNormRect_flMatMul_crossGram_inverse_entry_flMatMul_product_sq
    fp A Tail Utail Sigma Vperp Z V C Yhat halpha hchi heta hrho hγn hγr
    hC hTail hUtail hVperp hcrossTail hcrossHead hV hcomplete
    (le_trans
      (frobNormRect_flRightSketchCrossGramRectInvFactorProduct_le_sqrt_mul_product_sum_budget
        fp (flRightSketchCrossGramRect fp Vperp Z) Yhat hkappa hrho hγr
        hProductAbs hProductBudget)
      hProductFrobRadius)
    hLeftBudget hInvEntry hXRowAbs hProductBudget

/-- A perturbed-inverse certificate supplies an entrywise error certificate for
the repository nonsingular inverse.  This is a deterministic Higham §13.1
adapter: the concrete inversion routine is represented by the displayed
perturbed inverse equation for `Yhat`. -/
theorem nonsingInv_entry_abs_sub_computed_inverse_le_of_perturbed_inverse_component_budget
    {r : ℕ}
    (A Yhat DeltaA : Fin r → Fin r → ℝ)
    {epsInv eta : ℝ}
    (hepsInv : 0 ≤ epsInv)
    (hdet : Matrix.det (A : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hDelta :
      ∀ i j, |DeltaA i j| ≤ epsInv * |A i j|)
    (hYhat :
      ∀ i j,
        ∑ k : Fin r, (A i k + DeltaA i k) * Yhat k j =
          if i = j then 1 else 0)
    (hBudget :
      ∀ i j,
        epsInv *
            ∑ k₁ : Fin r,
              |nonsingInv r A i k₁| *
                (∑ k₂ : Fin r, |A k₁ k₂| * |Yhat k₂ j|) ≤ eta) :
    ∀ i j, |nonsingInv r A i j - Yhat i j| ≤ eta := by
  intro i j
  have hInv : IsInverse r A (nonsingInv r A) :=
    isInverse_nonsingInv_of_det_ne_zero r A hdet
  exact le_trans
    (ideal_forward_error r A (nonsingInv r A) Yhat DeltaA epsInv hepsInv
      hDelta hInv.1 hInv.2 hYhat i j)
    (hBudget i j)

/-- Specialization of the perturbed-inverse adapter to the square cross Gram
`V_kᵀ Z` used in equation (9). -/
theorem rightSketchCrossGram_inverse_entry_abs_error_le_of_perturbed_inverse_component_budget
    {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (Yhat DeltaA : Fin r → Fin r → ℝ)
    {epsInv eta : ℝ}
    (hepsInv : 0 ≤ epsInv)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hDelta :
      ∀ b c,
        |DeltaA b c| ≤ epsInv * |rightSketchCrossGram V Z b c|)
    (hYhat :
      ∀ b c,
        ∑ k : Fin r,
          (rightSketchCrossGram V Z b k + DeltaA b k) * Yhat k c =
          if b = c then 1 else 0)
    (hBudget :
      ∀ b c,
        epsInv *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  |rightSketchCrossGram V Z k₁ k₂| * |Yhat k₂ c|) ≤ eta) :
    ∀ b c,
      |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta :=
  nonsingInv_entry_abs_sub_computed_inverse_le_of_perturbed_inverse_component_budget
    (rightSketchCrossGram V Z) Yhat DeltaA hepsInv hdet hDelta hYhat hBudget

/-- Cross-term certificate where the inverse entrywise radius is supplied by a
perturbed-inverse certificate and the computed-product operator certificate is
supplied by product absolute sums. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_perturbed_inverse_product_sum_budget
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat DeltaA : Fin r → Fin r → ℝ)
    {epsM epsInv kappa alpha chi eta rho : ℝ}
    (hepsInv : 0 ≤ epsInv)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hDelta :
      ∀ b c,
        |DeltaA b c| ≤ epsInv * |rightSketchCrossGram V Z b c|)
    (hYhat :
      ∀ b c,
        ∑ k : Fin r,
          (rightSketchCrossGram V Z b k + DeltaA b k) * Yhat k c =
          if b = c then 1 else 0)
    (hInvBudget :
      ∀ b c,
        epsInv *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  |rightSketchCrossGram V Z k₁ k₂| * |Yhat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| * |Yhat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product
    fp Sigma Vperp Z V Yhat hkappa halpha hchi heta hrho hγn hγr
    hProductAbs hProductFrobRadius hLeftBudget
    (rightSketchCrossGram_inverse_entry_abs_error_le_of_perturbed_inverse_component_budget
      V Z Yhat DeltaA hepsInv hdet hDelta hYhat hInvBudget)
    hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate where the inverse entrywise
radius is supplied by a perturbed-inverse certificate and the product operator
certificate is supplied by product absolute sums. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_perturbed_inverse_product_sum_budget_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Yhat DeltaA : Fin r → Fin r → ℝ)
    {epsM epsInv kappa alpha chi eta rho : ℝ}
    (hepsInv : 0 ≤ epsInv)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hDelta :
      ∀ b c,
        |DeltaA b c| ≤ epsInv * |rightSketchCrossGram V Z b c|)
    (hYhat :
      ∀ b c,
        ∑ k : Fin r,
          (rightSketchCrossGram V Z b k + DeltaA b k) * Yhat k c =
          if b = c then 1 else 0)
    (hInvBudget :
      ∀ b c,
        epsInv *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  |rightSketchCrossGram V Z k₁ k₂| * |Yhat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| * |Yhat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product_sq
    fp A Tail Utail Sigma Vperp Z V C Yhat hkappa halpha hchi heta hrho hγn hγr
    hC hTail hUtail hVperp hcrossTail hcrossHead hV hcomplete hProductAbs
    hProductFrobRadius hLeftBudget
  (rightSketchCrossGram_inverse_entry_abs_error_le_of_perturbed_inverse_component_budget
      V Z Yhat DeltaA hepsInv hdet hDelta hYhat hInvBudget)
    hXRowAbs hProductBudget

/-- Method-A LU inversion supplies the entrywise inverse certificate for the
square cross Gram `V_kᵀ Z` used in equation (9). -/
theorem rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_budget
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {eta : ℝ}
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hLU :
      LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat (gamma fp r))
    (hγr : gammaValid fp r)
    (hBudget :
      ∀ b c,
        (3 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta) :
    ∀ b c,
      |nonsingInv r (rightSketchCrossGram V Z) b c -
          methodAComputedInverse fp r L_hat U_hat b c| ≤ eta :=
  methodA_computed_inverse_entry_abs_sub_nonsingInv_le_of_lu_budget
    r fp (rightSketchCrossGram V Z) L_hat U_hat hdet
    hL_diag hU_diag hLU hγr hBudget

/-- Transfer an LU backward-error certificate from a computed square cross Gram
to the exact square cross Gram `VᵀZ`, when the input perturbation is measured
against the same `|L_hat||U_hat|` weights used by the LU certificate. -/
theorem rightSketchCrossGram_LUBackwardError_of_input_abs_error_le_absLUProduct
    {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ahat L_hat U_hat : Fin r → Fin r → ℝ)
    {epsLU mu : ℝ}
    (hLU : LUBackwardError r Ahat L_hat U_hat epsLU)
    (hInput :
      ∀ b c : Fin r,
        |Ahat b c - rightSketchCrossGram V Z b c| ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|) :
    LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat (epsLU + mu) :=
  LUBackwardError.of_input_abs_error_le_absLUProduct r
    (rightSketchCrossGram V Z) Ahat L_hat U_hat epsLU mu hLU hInput

/-- Concrete input-transfer certificate when the LU factors are generated from
the rounded square cross Gram `flRightSketchCrossGram fp V Z`. -/
theorem rightSketchCrossGram_LUBackwardError_of_flRightSketchCrossGram_input_budget
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsLU mu : ℝ}
    (hγn : gammaValid fp n)
    (hLU :
      LUBackwardError r (flRightSketchCrossGram fp V Z) L_hat U_hat epsLU)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|) :
    LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat (epsLU + mu) :=
  rightSketchCrossGram_LUBackwardError_of_input_abs_error_le_absLUProduct
    V Z (flRightSketchCrossGram fp V Z) L_hat U_hat hLU
    (fun b c =>
      le_trans
        (by
          rw [abs_sub_comm]
          exact rightSketchCrossGram_flMatMul_entry_abs_error_le fp V Z hγn b c)
        (hInputBudget b c))

/-- Method-A LU inversion with an exposed LU factorization coefficient supplies
the entrywise inverse certificate for the square cross Gram `V_kᵀ Z`. -/
theorem rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_factor_budget
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsLU eta : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hLU : LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat epsLU)
    (hγr : gammaValid fp r)
    (hBudget :
      ∀ b c,
        (epsLU + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta) :
    ∀ b c,
      |nonsingInv r (rightSketchCrossGram V Z) b c -
          methodAComputedInverse fp r L_hat U_hat b c| ≤ eta :=
  methodA_computed_inverse_entry_abs_sub_nonsingInv_le_of_lu_factor_budget
    r fp (rightSketchCrossGram V Z) L_hat U_hat hepsLU hdet
    hL_diag hU_diag hLU hγr hBudget

/-- Method-A inverse-entry certificate when the LU factors are certified for
the rounded square cross Gram `flRightSketchCrossGram fp V Z`; the exact
`VᵀZ` theorem receives the added input coefficient `mu`. -/
theorem rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_fl_lu_input_budget
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsLU mu eta : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hmu : 0 ≤ mu)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hLU :
      LUBackwardError r (flRightSketchCrossGram fp V Z) L_hat U_hat epsLU)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hBudget :
      ∀ b c,
        ((epsLU + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta) :
    ∀ b c,
      |nonsingInv r (rightSketchCrossGram V Z) b c -
          methodAComputedInverse fp r L_hat U_hat b c| ≤ eta :=
  rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_factor_budget
    fp V Z L_hat U_hat (add_nonneg hepsLU hmu) hdet hL_diag hU_diag
    (rightSketchCrossGram_LUBackwardError_of_flRightSketchCrossGram_input_budget
      fp V Z L_hat U_hat hγn hLU hInputBudget)
    hγr hBudget

/-- Doolittle-generated LU factors for the rounded square cross Gram satisfy
the standard LU backward-error certificate used by the Method-A inverse layer. -/
theorem rightSketchCrossGram_LUBackwardError_of_DoolittleLU_flRightSketchCrossGram
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    (hγr : gammaValid fp r)
    (hD :
      DoolittleLU r (flRightSketchCrossGram fp V Z) L_hat U_hat fp) :
    LUBackwardError r (flRightSketchCrossGram fp V Z) L_hat U_hat (gamma fp r) :=
  DoolittleLU.to_LUBackwardError r fp
    (flRightSketchCrossGram fp V Z) L_hat U_hat hγr hD

/-- Method-A inverse-entry certificate when the LU factors are generated by the
Doolittle recurrence from the rounded square cross Gram.  The sampling law stays
exact; the theorem charges the rounded square-cross-Gram input through `mu` and
the Doolittle factorization through `gamma fp r`. -/
theorem rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittle_fl_input_budget
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {mu eta : ℝ}
    (hmu : 0 ≤ mu)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleLU r (flRightSketchCrossGram fp V Z) L_hat U_hat fp)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta) :
    ∀ b c,
      |nonsingInv r (rightSketchCrossGram V Z) b c -
          methodAComputedInverse fp r L_hat U_hat b c| ≤ eta :=
  rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_fl_lu_input_budget
    fp V Z L_hat U_hat (gamma_nonneg fp hγr) hmu hγn hγr hdet
    hL_diag hU_diag
    (rightSketchCrossGram_LUBackwardError_of_DoolittleLU_flRightSketchCrossGram
      fp V Z L_hat U_hat hγr hD)
    hInputBudget hBudget

/-- Cross-term certificate where Method-A uses Doolittle-generated LU factors
for the rounded square cross Gram. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_methodA_doolittle_fl_input_product_sum_budget
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM mu kappa alpha chi eta rho : ℝ}
    (hmu : 0 ≤ mu)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleLU r (flRightSketchCrossGram fp V Z) L_hat U_hat fp)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hInvBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product
    fp Sigma Vperp Z V (methodAComputedInverse fp r L_hat U_hat)
    hkappa halpha hchi heta hrho hγn hγr hProductAbs hProductFrobRadius
    hLeftBudget
    (rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittle_fl_input_budget
      fp V Z L_hat U_hat hmu hγn hγr hdet hL_diag hU_diag hD
      hInputBudget hInvBudget)
    hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate where Method-A uses
Doolittle-generated LU factors for the rounded square cross Gram. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_doolittle_fl_input_product_sum_budget_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM mu kappa alpha chi eta rho : ℝ}
    (hmu : 0 ≤ mu)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleLU r (flRightSketchCrossGram fp V Z) L_hat U_hat fp)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hInvBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product_sq
    fp A Tail Utail Sigma Vperp Z V C
    (methodAComputedInverse fp r L_hat U_hat)
    hkappa halpha hchi heta hrho hγn hγr hC hTail hUtail hVperp hcrossTail
    hcrossHead hV hcomplete hProductAbs hProductFrobRadius hLeftBudget
    (rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittle_fl_input_budget
      fp V Z L_hat U_hat hmu hγn hγr hdet hL_diag hU_diag hD
      hInputBudget hInvBudget)
    hXRowAbs hProductBudget

/-- Dense-loop Doolittle factors for the rounded square cross Gram satisfy the
standard LU backward-error certificate once the visible compression budgets in
`DoolittleDenseLoopCertificate` are supplied. -/
theorem rightSketchCrossGram_LUBackwardError_of_DoolittleDenseLoopCertificate_flRightSketchCrossGram
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    (hγr : gammaValid fp r)
    (hD :
      DoolittleDenseLoopCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp) :
    LUBackwardError r (flRightSketchCrossGram fp V Z) L_hat U_hat (gamma fp r) :=
  hD.to_LUBackwardError hγr

/-- Method-A inverse-entry certificate when the LU factors are generated by a
dense-Doolittle loop certificate for the rounded square cross Gram. -/
theorem rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittleDenseLoop_fl_input_budget
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {mu eta : ℝ}
    (hmu : 0 ≤ mu)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleDenseLoopCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta) :
    ∀ b c,
      |nonsingInv r (rightSketchCrossGram V Z) b c -
          methodAComputedInverse fp r L_hat U_hat b c| ≤ eta :=
  rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittle_fl_input_budget
    fp V Z L_hat U_hat hmu hγn hγr hdet hL_diag hU_diag
    (hD.to_DoolittleLU (gamma_nonneg fp hγr)) hInputBudget hBudget

/-- Cross-term certificate where Method-A uses a dense-Doolittle loop
certificate for the rounded square cross Gram. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_methodA_doolittleDenseLoop_fl_input_product_sum_budget
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM mu kappa alpha chi eta rho : ℝ}
    (hmu : 0 ≤ mu)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleDenseLoopCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hInvBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_methodA_doolittle_fl_input_product_sum_budget
    fp Sigma Vperp Z V L_hat U_hat hmu hkappa halpha hchi heta hrho
    hγn hγr hdet hL_diag hU_diag
    (hD.to_DoolittleLU (gamma_nonneg fp hγr)) hInputBudget hInvBudget
    hProductAbs hProductFrobRadius hLeftBudget hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate where Method-A uses a
dense-Doolittle loop certificate for the rounded square cross Gram. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_doolittleDenseLoop_fl_input_product_sum_budget_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM mu kappa alpha chi eta rho : ℝ}
    (hmu : 0 ≤ mu)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleDenseLoopCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hInvBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_doolittle_fl_input_product_sum_budget_sq
    fp A Tail Utail Sigma Vperp Z V C L_hat U_hat hmu hkappa halpha hchi heta
    hrho hγn hγr hC hTail hUtail hVperp hcrossTail hcrossHead hV
    hcomplete hdet hL_diag hU_diag
    (hD.to_DoolittleLU (gamma_nonneg fp hγr)) hInputBudget hInvBudget
    hProductAbs hProductFrobRadius hLeftBudget hXRowAbs hProductBudget

/-- Absolute dense-Doolittle residual budgets plus dominance inequalities
produce the rounded square-cross-Gram LU backward-error certificate. -/
theorem rightSketchCrossGram_LUBackwardError_of_DoolittleDenseLoopAbsBudgetCertificate_flRightSketchCrossGram
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {BU BL : Fin r → Fin r → ℝ}
    (hγr : gammaValid fp r)
    (hD :
      DoolittleDenseLoopAbsBudgetCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp BU BL) :
    LUBackwardError r (flRightSketchCrossGram fp V Z) L_hat U_hat (gamma fp r) :=
  hD.to_LUBackwardError hγr

/-- Method-A inverse-entry certificate when a dense-Doolittle implementation
first proves absolute residual budgets and then proves their dominance by the
relative compression budgets required by the dense-loop certificate. -/
theorem rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittleDenseLoopAbsBudget_fl_input_budget
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {BU BL : Fin r → Fin r → ℝ}
    {mu eta : ℝ}
    (hmu : 0 ≤ mu)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleDenseLoopAbsBudgetCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp BU BL)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta) :
    ∀ b c,
      |nonsingInv r (rightSketchCrossGram V Z) b c -
          methodAComputedInverse fp r L_hat U_hat b c| ≤ eta :=
  rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittleDenseLoop_fl_input_budget
    fp V Z L_hat U_hat hmu hγn hγr hdet hL_diag hU_diag
    hD.to_denseLoopCertificate hInputBudget hBudget

/-- Cross-term certificate where Method-A uses dense-Doolittle factors supplied
through absolute residual budgets plus dominance inequalities. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_methodA_doolittleDenseLoopAbsBudget_fl_input_product_sum_budget
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {BU BL : Fin r → Fin r → ℝ}
    {epsM mu kappa alpha chi eta rho : ℝ}
    (hmu : 0 ≤ mu)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleDenseLoopAbsBudgetCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp BU BL)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hInvBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_methodA_doolittleDenseLoop_fl_input_product_sum_budget
    fp Sigma Vperp Z V L_hat U_hat hmu hkappa halpha hchi heta hrho
    hγn hγr hdet hL_diag hU_diag hD.to_denseLoopCertificate
    hInputBudget hInvBudget hProductAbs hProductFrobRadius hLeftBudget
    hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate where Method-A uses
dense-Doolittle factors supplied through absolute residual budgets plus
dominance inequalities. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_doolittleDenseLoopAbsBudget_fl_input_product_sum_budget_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {BU BL : Fin r → Fin r → ℝ}
    {epsM mu kappa alpha chi eta rho : ℝ}
    (hmu : 0 ≤ mu)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleDenseLoopAbsBudgetCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp BU BL)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hInvBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_doolittleDenseLoop_fl_input_product_sum_budget_sq
    fp A Tail Utail Sigma Vperp Z V C L_hat U_hat hmu hkappa halpha hchi heta
    hrho hγn hγr hC hTail hUtail hVperp hcrossTail hcrossHead hV
    hcomplete hdet hL_diag hU_diag hD.to_denseLoopCertificate
    hInputBudget hInvBudget hProductAbs hProductFrobRadius hLeftBudget
    hXRowAbs hProductBudget

/-- Cross-term certificate where the inverse entrywise radius is supplied by
Method-A LU inversion, and the computed-product operator certificate is supplied
by product absolute sums. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_methodA_inverse_product_sum_budget
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM kappa alpha chi eta rho : ℝ}
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hLU :
      LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat (gamma fp r))
    (hInvBudget :
      ∀ b c,
        (3 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product
    fp Sigma Vperp Z V (methodAComputedInverse fp r L_hat U_hat)
    hkappa halpha hchi heta hrho hγn hγr hProductAbs hProductFrobRadius
    hLeftBudget
    (rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_budget
      fp V Z L_hat U_hat hdet hL_diag hU_diag hLU hγr hInvBudget)
    hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate where the inverse entrywise
radius is supplied by Method-A LU inversion and the product operator certificate
is supplied by product absolute sums. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_inverse_product_sum_budget_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM kappa alpha chi eta rho : ℝ}
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hLU :
      LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat (gamma fp r))
    (hInvBudget :
      ∀ b c,
        (3 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product_sq
    fp A Tail Utail Sigma Vperp Z V C
    (methodAComputedInverse fp r L_hat U_hat)
    hkappa halpha hchi heta hrho hγn hγr hC hTail hUtail hVperp hcrossTail
    hcrossHead hV hcomplete hProductAbs hProductFrobRadius hLeftBudget
    (rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_budget
      fp V Z L_hat U_hat hdet hL_diag hU_diag hLU hγr hInvBudget)
    hXRowAbs hProductBudget

/-- Cross-term certificate where the inverse entrywise radius is supplied by
Method-A LU inversion with an exposed LU factorization coefficient. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_methodA_lu_factor_product_sum_budget
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM epsLU kappa alpha chi eta rho : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hLU : LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat epsLU)
    (hInvBudget :
      ∀ b c,
        (epsLU + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product
    fp Sigma Vperp Z V (methodAComputedInverse fp r L_hat U_hat)
    hkappa halpha hchi heta hrho hγn hγr hProductAbs hProductFrobRadius
    hLeftBudget
    (rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_factor_budget
      fp V Z L_hat U_hat hepsLU hdet hL_diag hU_diag hLU hγr hInvBudget)
    hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate where Method-A LU inversion
uses an exposed LU factorization coefficient. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_lu_factor_product_sum_budget_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM epsLU kappa alpha chi eta rho : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hLU : LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat epsLU)
    (hInvBudget :
      ∀ b c,
        (epsLU + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product_sq
    fp A Tail Utail Sigma Vperp Z V C
    (methodAComputedInverse fp r L_hat U_hat)
    hkappa halpha hchi heta hrho hγn hγr hC hTail hUtail hVperp hcrossTail
    hcrossHead hV hcomplete hProductAbs hProductFrobRadius hLeftBudget
    (rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_factor_budget
      fp V Z L_hat U_hat hepsLU hdet hL_diag hU_diag hLU hγr hInvBudget)
    hXRowAbs hProductBudget

/-- The exact Gram-inverse coefficient table `C = G^{-1}Bᵀ`, with
`G = BᵀB`, satisfies the four Moore-Penrose certificate equations under the
explicit Gram-inverse certificate. -/
theorem columnSketchGramInverseCoefficient_moorePenroseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ)
    (hG : ColumnSketchGramInverseCertificate A Z Ginv) :
    ColumnSketchMoorePenroseCertificate A Z
      (columnSketchGramInverseCoefficient A Z Ginv) where
  sketch_reproduction :=
    (columnSketchGramInverseCoefficient_generalizedInverse A Z Ginv hG).reproducesSketch
  coefficient_reproduction :=
    columnSketchGramInverseCoefficient_reproducesCoeff A Z Ginv hG
  left_symmetric :=
    columnSketchLeftMultiplier_symmetric_of_gramInverseCertificate A Z Ginv hG
  right_symmetric :=
    columnSketchRightMultiplier_symmetric_of_gramInverseCertificate A Z Ginv hG

/-- Determinant-facing Moore-Penrose route for the concrete coefficient table
`C = nonsingInv(BᵀB) Bᵀ`. -/
theorem columnSketchGramInverseCoefficient_moorePenroseCertificate_of_det_ne_zero
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchMoorePenroseCertificate A Z
      (columnSketchGramInverseCoefficient A Z
        (nonsingInv r (columnSketchGram A Z))) :=
  columnSketchGramInverseCoefficient_moorePenroseCertificate A Z
    (nonsingInv r (columnSketchGram A Z))
    (columnSketchGramInverseCertificate_of_det_ne_zero A Z hdet)

/-- Thin-factor-facing Moore-Penrose route for the concrete coefficient table
`C = nonsingInv(BᵀB) Bᵀ`. -/
theorem columnSketchGramInverseCoefficient_moorePenroseCertificate_of_thinFactorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (R : Fin r → Fin r → ℝ)
    (hthin : ColumnSketchThinFactorCertificate A Z U R) :
    ColumnSketchMoorePenroseCertificate A Z
      (columnSketchGramInverseCoefficient A Z
        (nonsingInv r (columnSketchGram A Z))) :=
  columnSketchGramInverseCoefficient_moorePenroseCertificate A Z
    (nonsingInv r (columnSketchGram A Z))
    (columnSketchGramInverseCertificate_of_thinFactorCertificate A Z U R hthin)


/-- The coefficient-side Moore-Penrose equation `C B C = C`, exposed for later
pseudoinverse algebra and computed-routine certificates. -/
theorem columnSketchRightMultiplier_reproducesCoeff_of_moorePenroseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchMoorePenroseCertificate A Z C) :
    ∀ a i,
      preconditionRows (columnSketchRightMultiplier A Z C) C a i = C a i :=
  hC.coefficient_reproduction

/-- The right Moore-Penrose symmetry equation for `C (A Z)`. -/
theorem columnSketchRightMultiplier_symmetric_of_moorePenroseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchMoorePenroseCertificate A Z C) :
    IsSymmetricFiniteMatrix (columnSketchRightMultiplier A Z C) :=
  hC.right_symmetric

/-- Packaged equation (9) projector surface obtained from a supplied
Moore-Penrose certificate.  This connects the four pseudoinverse equations to
the existing symmetric-idempotent rank surface, while leaving construction of
`C = (A Z)^+` and all computed non-probability routines as separate
obligations. -/
theorem columnSketchLeftMultiplier_orthogonalProjectorSurface_of_moorePenroseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchMoorePenroseCertificate A Z C) :
    IsSymmetricFiniteMatrix (columnSketchLeftMultiplier A Z C) ∧
      Nonempty (LeftFactorThrough (columnSketchLeftMultiplier A Z C) (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows (columnSketchLeftMultiplier A Z C) (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows (columnSketchLeftMultiplier A Z C)
            (columnSketchLeftMultiplier A Z C) i j =
          columnSketchLeftMultiplier A Z C i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) :=
  columnSketchLeftMultiplier_orthogonalProjectorSurface A Z C
    hC.to_orthogonalProjectorCertificate

/-- Packaged equation (9) projector surface for the concrete exact
Gram-inverse coefficient table `C = (BᵀB)^{-1}Bᵀ`, assuming the displayed
Gram-inverse certificate. -/
theorem columnSketchLeftMultiplier_orthogonalProjectorSurface_of_gramInverseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ)
    (hG : ColumnSketchGramInverseCertificate A Z Ginv) :
    IsSymmetricFiniteMatrix
        (columnSketchLeftMultiplier A Z
          (columnSketchGramInverseCoefficient A Z Ginv)) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z Ginv))
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z Ginv))
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z Ginv))
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z Ginv)) i j =
          columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z Ginv) i j) ∧
      RectRankAtMost m n r
        (preconditionRows
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z Ginv)) A) :=
  columnSketchLeftMultiplier_orthogonalProjectorSurface_of_moorePenroseCertificate
    A Z (columnSketchGramInverseCoefficient A Z Ginv)
    (columnSketchGramInverseCoefficient_moorePenroseCertificate A Z Ginv hG)

/-- Determinant-facing equation (9) projector surface for the concrete exact
Gram-inverse coefficient table `C = nonsingInv(BᵀB)Bᵀ`. -/
theorem columnSketchLeftMultiplier_orthogonalProjectorSurface_of_det_ne_zero
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    IsSymmetricFiniteMatrix
        (columnSketchLeftMultiplier A Z
          (columnSketchGramInverseCoefficient A Z
            (nonsingInv r (columnSketchGram A Z)))) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))))
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z)))) i j =
          columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))) i j) ∧
      RectRankAtMost m n r
        (preconditionRows
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z)))) A) :=
  columnSketchLeftMultiplier_orthogonalProjectorSurface_of_gramInverseCertificate
    A Z (nonsingInv r (columnSketchGram A Z))
    (columnSketchGramInverseCertificate_of_det_ne_zero A Z hdet)

/-- Thin-factor-facing equation (9) projector surface for the concrete exact
Gram-inverse coefficient table `C = nonsingInv(BᵀB)Bᵀ`. -/
theorem columnSketchLeftMultiplier_orthogonalProjectorSurface_of_thinFactorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (R : Fin r → Fin r → ℝ)
    (hthin : ColumnSketchThinFactorCertificate A Z U R) :
    IsSymmetricFiniteMatrix
        (columnSketchLeftMultiplier A Z
          (columnSketchGramInverseCoefficient A Z
            (nonsingInv r (columnSketchGram A Z)))) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))))
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z)))) i j =
          columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))) i j) ∧
      RectRankAtMost m n r
        (preconditionRows
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z)))) A) :=
  columnSketchLeftMultiplier_orthogonalProjectorSurface_of_gramInverseCertificate
    A Z (nonsingInv r (columnSketchGram A Z))
    (columnSketchGramInverseCertificate_of_thinFactorCertificate A Z U R hthin)

/-- Source-SVD-facing nonzero Gram determinant route.  The exact hypotheses
`det(Σ) ≠ 0` and `det(VᵀZ) ≠ 0` instantiate the thin-factor bridge with
`R = Σ(VᵀZ)`. -/
theorem columnSketchGram_det_ne_zero_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  columnSketchGram_det_ne_zero_of_thinFactorCertificate A Z U
    (sourceSVDSketchRightFactor Sigma V Z)
    (columnSketchThinFactorCertificate_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ)

/-- Source-SVD-facing nonzero Gram determinant route with an exact diagonal
source singular block replacing the raw `det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchGram_det_ne_zero_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  columnSketchGram_det_ne_zero_of_thinFactorCertificate A Z U
    (sourceSVDSketchRightFactor Sigma V Z)
    (columnSketchThinFactorCertificate_of_sourceSVD_diagonal_det_factors
      A Z U Sigma sigma V hA hU hSigmaDiag hSigmaNonzero hVZ)

/-- Source-SVD-facing positive-definite Gram route.  The exact hypotheses
`det(Σ) ≠ 0` and `det(VᵀZ) ≠ 0` instantiate the thin-factor bridge and prove
the source-head sketch Gram is positive definite. -/
theorem columnSketchGram_posDef_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.PosDef (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) :=
  columnSketchGram_posDef_of_thinFactorCertificate A Z U
    (sourceSVDSketchRightFactor Sigma V Z)
    (columnSketchThinFactorCertificate_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ)

/-- Source-SVD-facing positive-definite Gram route with an exact diagonal
source singular block replacing the raw `det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchGram_posDef_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.PosDef (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) :=
  columnSketchGram_posDef_of_thinFactorCertificate A Z U
    (sourceSVDSketchRightFactor Sigma V Z)
    (columnSketchThinFactorCertificate_of_sourceSVD_diagonal_det_factors
      A Z U Sigma sigma V hA hU hSigmaDiag hSigmaNonzero hVZ)

/-- Equation (9) determinant route for an orthogonal source head-plus-tail
split.  The source-head positive-definite certificate required by
`columnSketchGram_sourceHeadTail_det_ne_zero_of_head_posDef` is generated from
the exact thin source factors `U`, `Σ`, and `VᵀZ`. -/
theorem columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hUT : sourceTailLeftOrthogonal U Tail)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  columnSketchGram_sourceHeadTail_det_ne_zero_of_head_posDef
    A Tail Z U Sigma V hA hUT
    (columnSketchGram_posDef_of_sourceSVD_det_factors
      (sourceSVDFactorMatrix U Sigma V) Z U Sigma V
      (by intro i j; rfl) hU hSigma hVZ)

/-- Equation (9) determinant route for an orthogonal source head-plus-tail
split, with an exact diagonal singular-value block replacing the raw
`det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hUT : sourceTailLeftOrthogonal U Tail)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  columnSketchGram_sourceHeadTail_det_ne_zero_of_head_posDef
    A Tail Z U Sigma V hA hUT
    (columnSketchGram_posDef_of_sourceSVD_diagonal_det_factors
      (sourceSVDFactorMatrix U Sigma V) Z U Sigma sigma V
      (by intro i j; rfl) hU hSigmaDiag hSigmaNonzero hVZ)

/-- Source-tail-factor version of the equation (9) determinant route.  Instead
of assuming the field `U^T Tail = 0` directly, it derives it from a supplied
exact tail factorization and exact left-basis cross-orthogonality.  Computed
SVD/tail factors remain implementation-facing non-probability obligations. -/
theorem columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_det_factors_tail_factor_left_cross_zero
    {m n r q : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vtail : Fin n → Fin q → ℝ)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hTail :
      ∀ i j, Tail i j = sourceSVDFactorMatrix Utail SigmaTail Vtail i j)
    (hcross : ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_det_factors
    A Tail Z U Sigma V hA
    (sourceTailLeftOrthogonal_of_tail_factor_left_cross_zero
      U Tail Utail SigmaTail Vtail hTail hcross)
    hU hSigma hVZ

/-- Diagonal-singular-block version of the tail-factor determinant route.  The
visible diagonal entries of the exact source singular block replace the raw
`det(Sigma) != 0` hypothesis. -/
theorem columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_diagonal_tail_factor_left_cross_zero
    {m n r q : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vtail : Fin n → Fin q → ℝ)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hTail :
      ∀ i j, Tail i j = sourceSVDFactorMatrix Utail SigmaTail Vtail i j)
    (hcross : ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_det_factors_tail_factor_left_cross_zero
    A Tail Z U Sigma V Utail SigmaTail Vtail hA hTail hcross hU
    (matrix_det_ne_zero_of_eq_diagonal_nonzero
      Sigma sigma hSigmaDiag hSigmaNonzero)
    hVZ

/-- Source-SVD-facing concrete `nonsingInv` Gram-inverse certificate. -/
theorem columnSketchGramInverseCertificate_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchGramInverseCertificate A Z
      (nonsingInv r (columnSketchGram A Z)) :=
  columnSketchGramInverseCertificate_of_det_ne_zero A Z
    (columnSketchGram_det_ne_zero_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ)

/-- Source-SVD-facing exact Gram-inverse certificate with an exact diagonal
source singular block replacing the raw `det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchGramInverseCertificate_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchGramInverseCertificate A Z
      (nonsingInv r (columnSketchGram A Z)) :=
  columnSketchGramInverseCertificate_of_det_ne_zero A Z
    (columnSketchGram_det_ne_zero_of_sourceSVD_diagonal_det_factors
      A Z U Sigma sigma V hA hU hSigmaDiag hSigmaNonzero hVZ)

/-- Source-SVD-facing Moore-Penrose certificate for
`C = nonsingInv((A Z)ᵀ(A Z))(A Z)ᵀ`. -/
theorem columnSketchGramInverseCoefficient_moorePenroseCertificate_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchMoorePenroseCertificate A Z
      (columnSketchGramInverseCoefficient A Z
        (nonsingInv r (columnSketchGram A Z))) :=
  columnSketchGramInverseCoefficient_moorePenroseCertificate A Z
    (nonsingInv r (columnSketchGram A Z))
    (columnSketchGramInverseCertificate_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ)

/-- Source-SVD-facing Moore-Penrose certificate with an exact diagonal
source singular block replacing the raw `det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchGramInverseCoefficient_moorePenroseCertificate_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchMoorePenroseCertificate A Z
      (columnSketchGramInverseCoefficient A Z
        (nonsingInv r (columnSketchGram A Z))) :=
  columnSketchGramInverseCoefficient_moorePenroseCertificate A Z
    (nonsingInv r (columnSketchGram A Z))
    (columnSketchGramInverseCertificate_of_sourceSVD_diagonal_det_factors
      A Z U Sigma sigma V hA hU hSigmaDiag hSigmaNonzero hVZ)

/-- Source-SVD-facing equation (9) projector surface for the concrete exact
Gram-inverse coefficient table.  This still does not prove the equation (9)
residual inequality; it only closes the source determinant-to-projector
algebra. -/
theorem columnSketchLeftMultiplier_orthogonalProjectorSurface_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    IsSymmetricFiniteMatrix
        (columnSketchLeftMultiplier A Z
          (columnSketchGramInverseCoefficient A Z
            (nonsingInv r (columnSketchGram A Z)))) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))))
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z)))) i j =
          columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))) i j) ∧
      RectRankAtMost m n r
        (preconditionRows
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z)))) A) :=
  columnSketchLeftMultiplier_orthogonalProjectorSurface_of_det_ne_zero A Z
    (columnSketchGram_det_ne_zero_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ)

/-- Source-SVD-facing equation (9) projector surface for the concrete exact
Gram-inverse coefficient table, with an exact diagonal singular-value block
replacing the raw `det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchLeftMultiplier_orthogonalProjectorSurface_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    IsSymmetricFiniteMatrix
        (columnSketchLeftMultiplier A Z
          (columnSketchGramInverseCoefficient A Z
            (nonsingInv r (columnSketchGram A Z)))) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))))
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z)))) i j =
          columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))) i j) ∧
      RectRankAtMost m n r
        (preconditionRows
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z)))) A) :=
  columnSketchLeftMultiplier_orthogonalProjectorSurface_of_det_ne_zero A Z
    (columnSketchGram_det_ne_zero_of_sourceSVD_diagonal_det_factors
      A Z U Sigma sigma V hA hU hSigmaDiag hSigmaNonzero hVZ)

/-- Named-projector version of the source-SVD-facing exact Gram-inverse
projector surface. -/
theorem columnSketchGramInverseProjector_orthogonalProjectorSurface_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) := by
  simpa [columnSketchGramInverseProjector] using
    columnSketchLeftMultiplier_orthogonalProjectorSurface_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ

/-- Named-projector version of the source-SVD-facing exact Gram-inverse
projector surface, with an exact diagonal singular-value block replacing the
raw `det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchGramInverseProjector_orthogonalProjectorSurface_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) := by
  simpa [columnSketchGramInverseProjector] using
    columnSketchLeftMultiplier_orthogonalProjectorSurface_of_sourceSVD_diagonal_det_factors
      A Z U Sigma sigma V hA hU hSigmaDiag hSigmaNonzero hVZ

/-- Source-SVD-facing head/tail residual surface for the concrete exact
Gram-inverse projector.  The source determinant hypotheses provide the
projector reproduction algebra; the supplied head/tail certificate supplies the
still-open equation (9) SVD residual bound. -/
theorem columnSketchGramInverseProjector_sourceSVD_headTailRankResidualSurface
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling : ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hHT :
      Equation9HeadTailSketchCertificate A Z
        (columnSketchGramInverseProjector A Z) Head Tail tail coupling) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          tail + coupling := by
  have hproj :=
    columnSketchGramInverseProjector_orthogonalProjectorSurface_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ
  have hEq9 :
      Equation9ResidualCertificate A (columnSketchGramInverseProjector A Z)
        tail coupling :=
    hHT.to_residualCertificate hproj.2.2.1
  exact
    ⟨hproj.1, hproj.2.1, hproj.2.2.1, hproj.2.2.2.1,
      hproj.2.2.2.2, hEq9.residual_bound⟩

/-- Source-SVD-facing relative residual surface for the concrete exact
Gram-inverse projector, still conditional on the explicit head/tail equation
(9) certificate and a scalar comparison to a certified best rank-`k`
approximation. -/
theorem columnSketchGramInverseProjector_sourceSVD_headTailRelativeResidualSurface
    {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hHT :
      Equation9HeadTailSketchCertificate A Z
        (columnSketchGramInverseProjector A Z) Head Tail tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A Ak := by
  have hproj :=
    columnSketchGramInverseProjector_orthogonalProjectorSurface_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ
  have hEq9 :
      Equation9ResidualCertificate A (columnSketchGramInverseProjector A Z)
        tail coupling :=
    hHT.to_residualCertificate hproj.2.2.1
  exact
    ⟨hbest.rank_le, hproj.1, hproj.2.1, hproj.2.2.1,
      hproj.2.2.2.1, hproj.2.2.2.2,
      le_trans hEq9.residual_bound hrelative⟩

/-- Source-SVD-facing residual surface where the head/tail certificate is
instantiated by an explicit sketch coefficient table `W`, so the only remaining
residual obligations are the two exact Frobenius norm bounds for
`A - (A Z) W` and its projected image. -/
theorem columnSketchGramInverseProjector_sourceSVD_columnSketchHeadRankResidualSurface
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (W : Fin r → Fin n → ℝ)
    (tail coupling : ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (columnSketchTail A Z W) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (columnSketchTail A Z W)) ≤ coupling) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          tail + coupling :=
  columnSketchGramInverseProjector_sourceSVD_headTailRankResidualSurface
    A Z U Sigma V (columnSketchHead A Z W) (columnSketchTail A Z W)
    tail coupling hA hU hSigma hVZ
    (equation9HeadTailSketchCertificate_of_columnSketchHead
      A Z (columnSketchGramInverseProjector A Z) W tail coupling
      htail_nonneg hcoupling_nonneg htail hcoupling)

/-- Relative residual version of the explicit-coefficient source-SVD
head/tail bridge. -/
theorem columnSketchGramInverseProjector_sourceSVD_columnSketchHeadRelativeResidualSurface
    {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (W : Fin r → Fin n → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (columnSketchTail A Z W) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (columnSketchTail A Z W)) ≤ coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A Ak :=
  columnSketchGramInverseProjector_sourceSVD_headTailRelativeResidualSurface
    Z U Sigma V (columnSketchHead A Z W) (columnSketchTail A Z W)
    tail coupling rho hbest hA hU hSigma hVZ
    (equation9HeadTailSketchCertificate_of_columnSketchHead
      A Z (columnSketchGramInverseProjector A Z) W tail coupling
      htail_nonneg hcoupling_nonneg htail hcoupling)
    hrelative

/-- Source-SVD-facing residual surface with an exact diagonal singular-value
block replacing the raw `det(Σ) ≠ 0` hypothesis.  The residual radii still come
from the supplied head/tail equation-(9) certificate; computed SVD, projector,
Gram, inverse, and product routines remain separate non-probability
implementation obligations. -/
theorem columnSketchGramInverseProjector_sourceSVD_diagonal_headTailRankResidualSurface
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling : ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hHT :
      Equation9HeadTailSketchCertificate A Z
        (columnSketchGramInverseProjector A Z) Head Tail tail coupling) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          tail + coupling :=
  columnSketchGramInverseProjector_sourceSVD_headTailRankResidualSurface
    A Z U Sigma V Head Tail tail coupling hA hU
    (matrix_det_ne_zero_of_eq_diagonal_nonzero
      Sigma sigma hSigmaDiag hSigmaNonzero)
    hVZ hHT

/-- Relative residual version of the diagonal source-SVD head/tail bridge. -/
theorem columnSketchGramInverseProjector_sourceSVD_diagonal_headTailRelativeResidualSurface
    {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hHT :
      Equation9HeadTailSketchCertificate A Z
        (columnSketchGramInverseProjector A Z) Head Tail tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A Ak :=
  columnSketchGramInverseProjector_sourceSVD_headTailRelativeResidualSurface
    Z U Sigma V Head Tail tail coupling rho hbest hA hU
    (matrix_det_ne_zero_of_eq_diagonal_nonzero
      Sigma sigma hSigmaDiag hSigmaNonzero)
    hVZ hHT hrelative

/-- Explicit-coefficient source-SVD residual surface with a displayed diagonal
singular-value block in place of the raw determinant hypothesis. -/
theorem columnSketchGramInverseProjector_sourceSVD_diagonal_columnSketchHeadRankResidualSurface
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (W : Fin r → Fin n → ℝ) (tail coupling : ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (columnSketchTail A Z W) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (columnSketchTail A Z W)) ≤ coupling) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          tail + coupling :=
  columnSketchGramInverseProjector_sourceSVD_diagonal_headTailRankResidualSurface
    A Z U Sigma sigma V (columnSketchHead A Z W) (columnSketchTail A Z W)
    tail coupling hA hU hSigmaDiag hSigmaNonzero hVZ
    (equation9HeadTailSketchCertificate_of_columnSketchHead
      A Z (columnSketchGramInverseProjector A Z) W tail coupling
      htail_nonneg hcoupling_nonneg htail hcoupling)

/-- Relative residual version of the explicit-coefficient diagonal source-SVD
head/tail bridge. -/
theorem columnSketchGramInverseProjector_sourceSVD_diagonal_columnSketchHeadRelativeResidualSurface
    {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (W : Fin r → Fin n → ℝ) (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (columnSketchTail A Z W) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (columnSketchTail A Z W)) ≤ coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A Ak :=
  columnSketchGramInverseProjector_sourceSVD_diagonal_headTailRelativeResidualSurface
    Z U Sigma sigma V (columnSketchHead A Z W) (columnSketchTail A Z W)
    tail coupling rho hbest hA hU hSigmaDiag hSigmaNonzero hVZ
    (equation9HeadTailSketchCertificate_of_columnSketchHead
      A Z (columnSketchGramInverseProjector A Z) W tail coupling
      htail_nonneg hcoupling_nonneg htail hcoupling)
    hrelative

/-- Source-coefficient residual surface for any exact Moore-Penrose certificate
for the full sketch `A Z`.  This combines the LR.1o source residual tail with a
supplied four-equation exact pseudoinverse/projector certificate. -/
theorem columnSketchLeftMultiplier_sourceHeadTail_sourceSketchCoefficientRankResidualSurface
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (C : Fin r → Fin m → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (tail coupling : ℝ)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤ coupling) :
    IsSymmetricFiniteMatrix (columnSketchLeftMultiplier A Z C) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchLeftMultiplier A Z C)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchLeftMultiplier A Z C)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchLeftMultiplier A Z C)
            (columnSketchLeftMultiplier A Z C) i j =
          columnSketchLeftMultiplier A Z C i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) ≤
          tail + coupling := by
  have hproj :=
    columnSketchLeftMultiplier_orthogonalProjectorSurface A Z C
      hC.to_orthogonalProjectorCertificate
  have hres :=
    equation9RankResidualSurface_of_sourceHeadTail_sourceSketchCoefficient
      A Tail Z (columnSketchLeftMultiplier A Z C) U Sigma V tail coupling
      (columnSketchLeftMultiplier_leftFactorThrough A Z C)
      hproj.2.2.1 hVZ hA htail_nonneg hcoupling_nonneg htail hcoupling
  exact
    ⟨hproj.1, hproj.2.1, hproj.2.2.1, hproj.2.2.2.1, hres.1, hres.2⟩

/-- Relative residual version of the source-coefficient route for any supplied
exact Moore-Penrose certificate for the full sketch `A Z`. -/
theorem columnSketchLeftMultiplier_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface
    {m n k r : ℕ}
    {A Ak Tail : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (C : Fin r → Fin m → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤ coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchLeftMultiplier A Z C) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchLeftMultiplier A Z C)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchLeftMultiplier A Z C)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchLeftMultiplier A Z C)
            (columnSketchLeftMultiplier A Z C) i j =
          columnSketchLeftMultiplier A Z C i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) ≤
          rho * lowRankResidualFrob A Ak := by
  have hproj :=
    columnSketchLeftMultiplier_orthogonalProjectorSurface A Z C
      hC.to_orthogonalProjectorCertificate
  have hres :=
    equation9RelativeResidualSurface_of_sourceHeadTail_sourceSketchCoefficient
      Z (columnSketchLeftMultiplier A Z C) U Sigma V tail coupling rho
      hbest (columnSketchLeftMultiplier_leftFactorThrough A Z C)
      hproj.2.2.1 hVZ hA htail_nonneg hcoupling_nonneg htail hcoupling
      hrelative
  exact
    ⟨hres.1, hproj.1, hproj.2.1, hproj.2.2.1, hproj.2.2.2.1,
      hres.2.1, hres.2.2⟩

/-- Source-coefficient residual surface for the concrete exact Gram-inverse
projector `P = (A Z)((A Z)^T(A Z))^{-1}(A Z)^T`, assuming the exact sketch Gram
determinant is nonzero.  This removes the supplied Moore-Penrose certificate
from the previous source-tail bridge while still leaving concrete
Gram/inverse/product computations as separate FP obligations. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRankResidualSurface_of_det_ne_zero
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (tail coupling : ℝ)
    (hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (sourceSketchResidualTail Tail Z V)) ≤ coupling) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          tail + coupling := by
  simpa [columnSketchGramInverseProjector] using
    columnSketchLeftMultiplier_sourceHeadTail_sourceSketchCoefficientRankResidualSurface
      A Tail Z
      (columnSketchGramInverseCoefficient A Z
        (nonsingInv r (columnSketchGram A Z)))
      U Sigma V tail coupling
      (columnSketchGramInverseCoefficient_moorePenroseCertificate_of_det_ne_zero
        A Z hdet)
      hVZ hA htail_nonneg hcoupling_nonneg htail hcoupling

/-- Relative residual version of the concrete exact Gram-inverse source-tail
bridge.  The source residual and projected residual radii are still explicit
analysis obligations; the projector side is now instantiated from
`det((A Z)^T(A Z)) != 0`. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface_of_det_ne_zero
    {m n k r : ℕ}
    {A Ak Tail : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (sourceSketchResidualTail Tail Z V)) ≤ coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A Ak := by
  simpa [columnSketchGramInverseProjector] using
    columnSketchLeftMultiplier_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface
      Z
      (columnSketchGramInverseCoefficient A Z
        (nonsingInv r (columnSketchGram A Z)))
      U Sigma V tail coupling rho hbest
      (columnSketchGramInverseCoefficient_moorePenroseCertificate_of_det_ne_zero
        A Z hdet)
      hVZ hA htail_nonneg hcoupling_nonneg htail hcoupling hrelative

/-- Source-head/tail residual surface for the concrete exact Gram-inverse
projector, with the full sketch-Gram determinant generated from an exact
diagonal source singular block and exact source-tail left orthogonality.

This is still an exact-object theorem.  It removes the raw
`det((A Z)^T(A Z)) != 0` hypothesis from the displayed source-head/tail route,
but it does not construct the rectangular SVD, prove the tail-radius
inequalities, or certify computed SVD/projector/Gram/inverse/product routines. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRankResidualSurface_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (tail coupling : ℝ)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hUT : sourceTailLeftOrthogonal U Tail)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (sourceSketchResidualTail Tail Z V)) ≤ coupling) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          tail + coupling :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRankResidualSurface_of_det_ne_zero
    A Tail Z U Sigma V tail coupling
    (columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_diagonal_det_factors
      A Tail Z U Sigma sigma V hA hUT hU hSigmaDiag hSigmaNonzero hVZ)
    hVZ hA htail_nonneg hcoupling_nonneg htail hcoupling

/-- Relative residual version of the diagonal source-head/tail concrete
Gram-inverse projector surface. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface_of_sourceSVD_diagonal_det_factors
    {m n k r : ℕ}
    {A Ak Tail : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hUT : sourceTailLeftOrthogonal U Tail)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (sourceSketchResidualTail Tail Z V)) ≤ coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A Ak :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface_of_det_ne_zero
    Z U Sigma V tail coupling rho hbest
    (columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_diagonal_det_factors
      A Tail Z U Sigma sigma V hA hUT hU hSigmaDiag hSigmaNonzero hVZ)
    hVZ hA htail_nonneg hcoupling_nonneg htail hcoupling hrelative

/-- Source-head/tail diagonal-source residual surface with the two visible
source-tail radii instantiated from the CACM cross-term certificate.

The source-head determinant and projector route uses the displayed diagonal
source singular block.  The ambient tail and projected-tail radii are both
generated from the exact tail factorization
`Tail = Utail * SigmaTail * Vperpᵀ`, exact source/tail orthogonality, and the
exact cross-term bound for
`SigmaTail * (Vperpᵀ Z)(Vᵀ Z)^{-1}`.  This remains exact-object mathematics:
rectangular SVD construction, singular-value ordering, Eckart--Young
optimality, randomness-derived cross-term certificates, and computed
non-probability SVD/projector/Gram/inverse/product routines remain separate
obligations.  Sampling probabilities and laws remain exact mathematical
inputs. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_sourceSVD_diagonal_crossTerm
    {m n r q : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (SigmaHead : Fin r → Fin r → ℝ)
    (sigmaHead : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U SigmaHead V i j + Tail i j)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft SigmaTail (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hLeftCross : ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, SigmaHead a b = if a = b then sigmaHead a else 0)
    (hSigmaNonzero : ∀ a, sigmaHead a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) := by
  let rad := Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail
  have hTailSource :
      ∀ i j, Tail i j = sourceSVDFactorMatrix Utail SigmaTail Vperp i j := by
    intro i j
    rw [hTail i j]
    rfl
  have hUT : sourceTailLeftOrthogonal U Tail :=
    sourceTailLeftOrthogonal_of_tail_factor_left_cross_zero
      U Tail Utail SigmaTail Vperp hTailSource hLeftCross
  have hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
    columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_diagonal_det_factors
      A Tail Z U SigmaHead sigmaHead V hA hUT hU hSigmaDiag hSigmaNonzero hVZ
  have hC :
      ColumnSketchMoorePenroseCertificate A Z
        (columnSketchGramInverseCoefficient A Z
          (nonsingInv r (columnSketchGram A Z))) :=
    columnSketchGramInverseCoefficient_moorePenroseCertificate_of_det_ne_zero A Z hdet
  have hrad_nonneg : 0 ≤ rad := by
    exact mul_nonneg (Real.sqrt_nonneg _) (frobNorm_nonneg SigmaTail)
  have htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ rad :=
    frobNormRect_sourceSketchResidualTail_sourceSVDTail_le_sqrt_one_add_eps_sq
      Tail Utail SigmaTail Vperp Z V heps hTail hUtail hVperp
      hcrossTail hcrossHead hV hcomplete hcrossTerm
  have hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (sourceSketchResidualTail Tail Z V)) ≤ rad := by
    simpa [columnSketchGramInverseProjector, rad] using
      frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq
        A Tail Utail SigmaTail Vperp Z V
        (columnSketchGramInverseCoefficient A Z
          (nonsingInv r (columnSketchGram A Z)))
        heps hC hTail hUtail hVperp hcrossTail hcrossHead hV hcomplete
        hcrossTerm
  have hres :=
    columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRankResidualSurface_of_sourceSVD_diagonal_det_factors
      A Tail Z U SigmaHead sigmaHead V rad rad hA hUT hU hSigmaDiag
      hSigmaNonzero hVZ hrad_nonneg hrad_nonneg htail hcoupling
  refine ⟨hres.1, hres.2.1, hres.2.2.1, hres.2.2.2.1,
    hres.2.2.2.2.1, ?_⟩
  simpa [rad, two_mul] using hres.2.2.2.2.2

/-- Relative-residual version of
`columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_sourceSVD_diagonal_crossTerm`.

The only extra assumption is the visible scalar comparison that the displayed
cross-term-generated radius is small relative to the supplied best-rank
certificate.  This is still not an Eckart--Young theorem: construction of the
best-rank certificate from singular values remains a separate foundation. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_sourceSVD_diagonal_crossTerm
    {m n k r q : ℕ}
    {A Ak Tail : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (SigmaHead : Fin r → Fin r → ℝ)
    (sigmaHead : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U SigmaHead V i j + Tail i j)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft SigmaTail (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hLeftCross : ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, SigmaHead a b = if a = b then sigmaHead a else 0)
    (hSigmaNonzero : ∀ a, sigmaHead a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail)
    (hrelative :
      2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) ≤
        rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A Ak := by
  let rad := Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail
  have hTailSource :
      ∀ i j, Tail i j = sourceSVDFactorMatrix Utail SigmaTail Vperp i j := by
    intro i j
    rw [hTail i j]
    rfl
  have hUT : sourceTailLeftOrthogonal U Tail :=
    sourceTailLeftOrthogonal_of_tail_factor_left_cross_zero
      U Tail Utail SigmaTail Vperp hTailSource hLeftCross
  have hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
    columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_diagonal_det_factors
      A Tail Z U SigmaHead sigmaHead V hA hUT hU hSigmaDiag hSigmaNonzero hVZ
  have hC :
      ColumnSketchMoorePenroseCertificate A Z
        (columnSketchGramInverseCoefficient A Z
          (nonsingInv r (columnSketchGram A Z))) :=
    columnSketchGramInverseCoefficient_moorePenroseCertificate_of_det_ne_zero A Z hdet
  have hrad_nonneg : 0 ≤ rad := by
    exact mul_nonneg (Real.sqrt_nonneg _) (frobNorm_nonneg SigmaTail)
  have htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ rad :=
    frobNormRect_sourceSketchResidualTail_sourceSVDTail_le_sqrt_one_add_eps_sq
      Tail Utail SigmaTail Vperp Z V heps hTail hUtail hVperp
      hcrossTail hcrossHead hV hcomplete hcrossTerm
  have hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (sourceSketchResidualTail Tail Z V)) ≤ rad := by
    simpa [columnSketchGramInverseProjector, rad] using
      frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq
        A Tail Utail SigmaTail Vperp Z V
        (columnSketchGramInverseCoefficient A Z
          (nonsingInv r (columnSketchGram A Z)))
        heps hC hTail hUtail hVperp hcrossTail hcrossHead hV hcomplete
        hcrossTerm
  have hrelative' : rad + rad ≤ rho * lowRankResidualFrob A Ak := by
    simpa [rad, two_mul] using hrelative
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface_of_sourceSVD_diagonal_det_factors
      Z U SigmaHead sigmaHead V rad rad rho hbest hA hUT hU hSigmaDiag
      hSigmaNonzero hVZ hrad_nonneg hrad_nonneg htail hcoupling hrelative'

/-- Source-head/tail scalar-rate relative surface with the source head itself
as the best-rank comparison.

This composes the LR.1bm scalar residual theorem with the existing
tail-optimality handoff for `IsBestRankApproxFrob`.  The true
Eckart--Young/singular-value proof is not hidden: it is exactly the supplied
`hopt` inequality.  Sampling probabilities and laws remain exact mathematical
inputs, and computed non-probability SVD/projector/Gram/inverse/product
routines still need separate certificates before this exact-object theorem can
be used implementation-facing. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_sourceSVD_diagonal_crossTerm_tailOptimal
    {m n r q : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (SigmaHead : Fin r → Fin r → ℝ)
    (sigmaHead : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U SigmaHead V i j + Tail i j)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft SigmaTail (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hLeftCross : ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, SigmaHead a b = if a = b then sigmaHead a else 0)
    (hSigmaNonzero : ∀ a, sigmaHead a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail)
    (hopt : ∀ B, RectRankAtMost m n r B →
      frobNormRect Tail ≤ lowRankResidualFrob A B)
    (hrelative :
      2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) ≤
        rho * frobNormRect Tail) :
    IsBestRankApproxFrob m n r A (sourceSVDFactorMatrix U SigmaHead V) ∧
      lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) =
        frobNormRect Tail ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) := by
  let rad := Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail
  have hbest :
      IsBestRankApproxFrob m n r A
        (sourceSVDFactorMatrix U SigmaHead V) :=
    sourceSVDFactorMatrix_isBestRankApproxFrob_of_tail_optimal
      A Tail U SigmaHead V hA hopt
  have htail_eq :
      lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) =
        frobNormRect Tail :=
    lowRankResidualFrob_sourceSVDFactorMatrix_eq_tail
      A Tail U SigmaHead V hA
  have hsurface :=
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_sourceSVD_diagonal_crossTerm
      A Tail Z U SigmaHead sigmaHead V Utail SigmaTail Vperp heps hA hTail
      hUtail hLeftCross hU hSigmaDiag hSigmaNonzero hVZ hVperp hcrossTail
      hcrossHead hV hcomplete hcrossTerm
  have hrelative' :
      2 * rad ≤
        rho * lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) := by
    simpa [rad, htail_eq] using hrelative
  refine ⟨hbest, htail_eq, hsurface.1, hsurface.2.1, hsurface.2.2.1,
    hsurface.2.2.2.1, hsurface.2.2.2.2.1, ?_⟩
  exact le_trans hsurface.2.2.2.2.2 hrelative'

/-- Certificate-shaped version of the diagonal source-SVD scalar tail-rate
rank surface.

The exact source-SVD head/tail data are supplied by
`DiagonalSourceSVDTailCertificate`; the only extra exact assumptions are the
sketch nonsingularity condition and the CACM cross-term radius. This closes a
source-split-certificate handoff, not rectangular SVD existence, Eckart--Young,
randomness-derived cross-term bounds, or computed non-probability routine
instantiations. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_diagonalSourceSVDTailCertificate
    {m n r q : ℕ}
    {A Tail : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      DiagonalSourceSVDTailCertificate m n r q A Tail U SigmaHead
        sigmaHead V Utail SigmaTail Vperp)
    (Z : Fin n → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) := by
  have hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft SigmaTail (sourceRightBasisTranspose Vperp) a j := by
    intro i j
    rw [cert.tail_factor i j]
    rfl
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_sourceSVD_diagonal_crossTerm
      A Tail Z U SigmaHead sigmaHead V Utail SigmaTail Vperp heps cert.split
      hTail cert.Utail_orthonormal cert.left_cross cert.U_orthonormal
      cert.head_diagonal cert.head_nonzero hVZ cert.Vperp_orthonormal
      cert.right_cross_tail cert.right_cross_head cert.V_orthonormal
      cert.right_complete hcrossTerm

/-- Certificate-shaped version of the tail-optimal diagonal source-SVD relative
scalar tail-rate surface.

The exact source-SVD split and orthogonality data are packaged in
`DiagonalSourceSVDTailCertificate`. The visible `hopt` inequality is still the
entire Eckart--Young/tail-optimality obligation; the theorem does not derive it
from singular values. The probability law is exact by convention, while
computed SVD/singular-vector/projector/Gram/inverse/product routines still
require separate FP/inexact-arithmetic certificates before this result is
implementation-facing. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_diagonalSourceSVDTailCertificate
    {m n r q : ℕ}
    {A Tail : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      DiagonalSourceSVDTailCertificate m n r q A Tail U SigmaHead
        sigmaHead V Utail SigmaTail Vperp)
    (Z : Fin n → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail)
    (hopt : ∀ B, RectRankAtMost m n r B →
      frobNormRect Tail ≤ lowRankResidualFrob A B)
    (hrelative :
      2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) ≤
        rho * frobNormRect Tail) :
    IsBestRankApproxFrob m n r A (sourceSVDFactorMatrix U SigmaHead V) ∧
      lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) =
        frobNormRect Tail ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) := by
  have hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft SigmaTail (sourceRightBasisTranspose Vperp) a j := by
    intro i j
    rw [cert.tail_factor i j]
    rfl
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_sourceSVD_diagonal_crossTerm_tailOptimal
      A Tail Z U SigmaHead sigmaHead V Utail SigmaTail Vperp heps cert.split
      hTail cert.Utail_orthonormal cert.left_cross cert.U_orthonormal
      cert.head_diagonal cert.head_nonzero hVZ cert.Vperp_orthonormal
      cert.right_cross_tail cert.right_cross_head cert.V_orthonormal
      cert.right_complete hcrossTerm hopt hrelative

/-- Concatenate the exact left-head and left-tail bases as a single
sum-indexed left-basis block.  The left summand is the source head basis `U`;
the right summand is the tail basis `Utail`. -/
noncomputable def leftBasisBlock {m r q : ℕ}
    (U : Fin m → Fin r → ℝ) (Utail : Fin m → Fin q → ℝ) :
    Fin m → (Fin r ⊕ Fin q) → ℝ :=
  fun i bc =>
    match bc with
    | Sum.inl a => U i a
    | Sum.inr c => Utail i c

/-- Column orthonormality of the concatenated left-basis block `[U,Utail]`
implies the component source-head orthonormality, head-tail cross
orthogonality, and tail orthonormality fields consumed by
`DiagonalSourceSVDTailCertificate`.  This is exact SVD-block algebra; computed
left singular-vector tables remain separate non-probability obligations. -/
theorem leftBasisBlock_component_orthonormal_fields_of_col_orthonormal
    {m r q : ℕ}
    (U : Fin m → Fin r → ℝ) (Utail : Fin m → Fin q → ℝ)
    (hcols :
      ∀ bc bd : Fin r ⊕ Fin q,
        (∑ i : Fin m,
          leftBasisBlock U Utail i bc * leftBasisBlock U Utail i bd) =
          if bc = bd then 1 else 0) :
    (∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b) ∧
      (∀ a c, ∑ i : Fin m, U i a * Utail i c = 0) ∧
      (∀ a c, ∑ i : Fin m, Utail i a * Utail i c = idMatrix q a c) := by
  constructor
  · intro a b
    have h := hcols (Sum.inl a) (Sum.inl b)
    simpa [leftBasisBlock, idMatrix] using h
  constructor
  · intro a c
    have h := hcols (Sum.inl a) (Sum.inr c)
    simpa [leftBasisBlock] using h
  · intro a c
    have h := hcols (Sum.inr a) (Sum.inr c)
    simpa [leftBasisBlock, idMatrix] using h

/-- Component left-basis fields assemble the column orthonormality certificate
for the concatenated block `[U,Utail]`.  This is exact source-SVD algebra:
constructing the tail-left completion or computing singular-vector tables
remains a separate non-probability obligation. -/
theorem leftBasisBlock_col_orthonormal_of_component_orthonormal_fields
    {m r q : ℕ}
    (U : Fin m → Fin r → ℝ) (Utail : Fin m → Fin q → ℝ)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hcross : ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0)
    (hUtail : ∀ a c, ∑ i : Fin m, Utail i a * Utail i c = idMatrix q a c) :
    ∀ bc bd : Fin r ⊕ Fin q,
      (∑ i : Fin m,
        leftBasisBlock U Utail i bc * leftBasisBlock U Utail i bd) =
        if bc = bd then 1 else 0 := by
  intro bc bd
  cases bc with
  | inl a =>
      cases bd with
      | inl b =>
          simpa [leftBasisBlock, idMatrix] using hU a b
      | inr c =>
          simpa [leftBasisBlock] using hcross a c
  | inr c =>
      cases bd with
      | inl a =>
          calc
            (∑ i : Fin m,
              leftBasisBlock U Utail i (Sum.inr c) *
                leftBasisBlock U Utail i (Sum.inl a))
                =
                  ∑ i : Fin m, U i a * Utail i c := by
                    apply Finset.sum_congr rfl
                    intro i _
                    simp [leftBasisBlock]
                    ring
            _ = 0 := hcross a c
      | inr d =>
          simpa [leftBasisBlock, idMatrix] using hUtail c d

/-- A sum-indexed column-orthonormal family in `ℝ^m` has no more columns than
ambient rows.  This bridges the repository's raw finite-sum convention to
mathlib's `Orthonormal`/`LinearIndependent` dimension theorem. -/
theorem colOrthonormal_fintype_card_le_rows {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (X : Fin m → ι → ℝ)
    (hX : ∀ a b : ι,
      (∑ i : Fin m, X i a * X i b) = if a = b then 1 else 0) :
    Fintype.card ι ≤ m := by
  let v : ι → EuclideanSpace ℝ (Fin m) :=
    fun a => WithLp.toLp 2 (fun i : Fin m => X i a)
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro a b
    have h := hX a b
    unfold v
    rw [PiLp.inner_apply]
    simpa [real_inner_eq_re_inner, RCLike.inner_apply, mul_comm] using h
  have hli : LinearIndependent ℝ v := hv.linearIndependent
  have hcard := hli.fintype_card_le_finrank
  simpa using hcard

/-- A concatenated left block `[U,Utail]` with column orthonormality forces the
visible dimension condition `r+q <= m`.  Thus any full left-block
nullspace-completion route for equation (9) must either expose this tall/thin
condition or use a different rectangular SVD surface. -/
theorem leftBasisBlock_col_orthonormal_card_le_rows {m r q : ℕ}
    (U : Fin m → Fin r → ℝ) (Utail : Fin m → Fin q → ℝ)
    (hcols :
      ∀ bc bd : Fin r ⊕ Fin q,
        (∑ i : Fin m,
          leftBasisBlock U Utail i bc * leftBasisBlock U Utail i bd) =
          if bc = bd then 1 else 0) :
    r + q ≤ m := by
  have h :=
    colOrthonormal_fintype_card_le_rows
      (X := fun i bc => leftBasisBlock U Utail i bc) hcols
  simpa using h

/-- A partially specified family of raw column-orthonormal columns in `ℝ^m`
can be extended to a full `m × m` column-orthonormal table while preserving the
specified columns.

This is the finite-dimensional orthonormal-completion bridge needed by the
zero-tail replacement route for equation (9).  It is exact-object
infrastructure: it constructs no floating-point routine and charges no
probability-law error. -/
theorem partialColOrthonormal_exists_fullColOrthonormal {m : ℕ}
    (X : Fin m → Fin m → ℝ) (s : Set (Fin m))
    (hX : ∀ a b : s,
      (∑ i : Fin m, X i a * X i b) = if a = b then 1 else 0) :
    ∃ Y : Fin m → Fin m → ℝ,
      (∀ a : Fin m, a ∈ s → ∀ i : Fin m, Y i a = X i a) ∧
        ∀ a b : Fin m,
          (∑ i : Fin m, Y i a * Y i b) = if a = b then 1 else 0 := by
  classical
  let v : Fin m → EuclideanSpace ℝ (Fin m) :=
    fun a => WithLp.toLp 2 (fun i : Fin m => X i a)
  have hv : Orthonormal ℝ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    intro a b
    have h := hX a b
    unfold v
    rw [PiLp.inner_apply]
    simpa [Set.restrict, real_inner_eq_re_inner, RCLike.inner_apply, mul_comm] using h
  have hcard :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = Fintype.card (Fin m) := by
    simp
  obtain ⟨b, hb⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq
      (v := v) (s := s) hcard
  refine ⟨fun i a => b a i, ?_, ?_⟩
  · intro a ha i
    have h := hb a ha
    change b a i = X i a
    simpa [v] using congrArg (fun z : EuclideanSpace ℝ (Fin m) => z i) h
  · intro a c
    have h := b.inner_eq_ite a c
    rw [PiLp.inner_apply] at h
    simpa [real_inner_eq_re_inner, RCLike.inner_apply, mul_comm] using h

/-- Embedded block-column version of
`partialColOrthonormal_exists_fullColOrthonormal`.

If the head columns and any chosen tail columns of `[U,Utail₀]` are already a
partial orthonormal family, and the block indices embed into a full `Fin m`
coordinate set, then the unspecified tail columns can be replaced so that the
whole block `[U,Utail]` is column-orthonormal.  The replacement preserves every
tail column included in the partial set.

This is exact-object nullspace-completion infrastructure for equation (9).  It
does not yet instantiate the ordered right-Gram zero-tail set, prove
Eckart--Young, derive randomness certificates, or certify any computed
non-probability routine. -/
theorem partialLeftBasisBlock_exists_replacement_tail
    {m r q : ℕ}
    (e : Fin r ⊕ Fin q ↪ Fin m)
    (U : Fin m → Fin r → ℝ) (Utail₀ : Fin m → Fin q → ℝ)
    (s : Set (Fin r ⊕ Fin q))
    (hhead : ∀ a : Fin r, Sum.inl a ∈ s)
    (hpartial : ∀ a b : s,
      (∑ i : Fin m,
        leftBasisBlock U Utail₀ i a * leftBasisBlock U Utail₀ i b) =
        if a = b then 1 else 0) :
    ∃ Utail : Fin m → Fin q → ℝ,
      (∀ c : Fin q, Sum.inr c ∈ s → ∀ i : Fin m, Utail i c = Utail₀ i c) ∧
        ∀ bc bd : Fin r ⊕ Fin q,
          (∑ i : Fin m,
            leftBasisBlock U Utail i bc * leftBasisBlock U Utail i bd) =
            if bc = bd then 1 else 0 := by
  classical
  let blockCol : Fin r ⊕ Fin q → Fin m → ℝ :=
    fun bc i => leftBasisBlock U Utail₀ i bc
  let X : Fin m → Fin m → ℝ :=
    fun i a =>
      if ha : a ∈ Set.range (fun bc : Fin r ⊕ Fin q => e bc) then
        blockCol (Classical.choose ha) i
      else
        0
  let sFull : Set (Fin m) :=
    Set.image (fun bc : Fin r ⊕ Fin q => e bc) s
  have hX : ∀ a b : sFull,
      (∑ i : Fin m, X i a * X i b) = if a = b then 1 else 0 := by
    intro a b
    rcases a.2 with ⟨bc, hbc, hbc_eq⟩
    rcases b.2 with ⟨bd, hbd, hbd_eq⟩
    have hmem_a : (a : Fin m) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
      ⟨bc, hbc_eq⟩
    have hmem_b : (b : Fin m) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
      ⟨bd, hbd_eq⟩
    have hchoose_a : Classical.choose hmem_a = bc :=
      e.injective (by
        calc
          e (Classical.choose hmem_a) = (a : Fin m) :=
            Classical.choose_spec hmem_a
          _ = e bc := hbc_eq.symm)
    have hchoose_b : Classical.choose hmem_b = bd :=
      e.injective (by
        calc
          e (Classical.choose hmem_b) = (b : Fin m) :=
            Classical.choose_spec hmem_b
          _ = e bd := hbd_eq.symm)
    have h := hpartial ⟨bc, hbc⟩ ⟨bd, hbd⟩
    have hsum :
        (∑ i : Fin m, X i a * X i b) =
          ∑ i : Fin m,
            leftBasisBlock U Utail₀ i bc * leftBasisBlock U Utail₀ i bd := by
      apply Finset.sum_congr rfl
      intro i _
      have hXa : X i a = leftBasisBlock U Utail₀ i bc := by
        dsimp [X, blockCol]
        rw [dif_pos hmem_a]
        simp [hchoose_a]
      have hXb : X i b = leftBasisBlock U Utail₀ i bd := by
        dsimp [X, blockCol]
        rw [dif_pos hmem_b]
        simp [hchoose_b]
      rw [hXa, hXb]
    have hite_s :
        (if (⟨bc, hbc⟩ : s) = (⟨bd, hbd⟩ : s) then (1 : ℝ) else 0) =
          if bc = bd then 1 else 0 := by
      by_cases hbdc : bc = bd
      · subst hbdc
        simp
      · have hne : (⟨bc, hbc⟩ : s) ≠ (⟨bd, hbd⟩ : s) := by
          intro hEq
          exact hbdc (Subtype.ext_iff.mp hEq)
        simp [hbdc, hne]
    have hite_full : (if a = b then (1 : ℝ) else 0) =
        if bc = bd then 1 else 0 := by
      by_cases hbdc : bc = bd
      · subst hbdc
        have hab : a = b := by
          apply Subtype.ext
          calc
            (a : Fin m) = e bc := hbc_eq.symm
            _ = (b : Fin m) := hbd_eq
        simp [hab]
      · have hne :
          a ≠ b := by
          intro hEq
          apply hbdc
          apply e.injective
          calc
            e bc = (a : Fin m) := hbc_eq
            _ = (b : Fin m) := congrArg Subtype.val hEq
            _ = e bd := hbd_eq.symm
        simp [hbdc, hne]
    calc
      (∑ i : Fin m, X i a * X i b)
          = ∑ i : Fin m,
              leftBasisBlock U Utail₀ i bc * leftBasisBlock U Utail₀ i bd := hsum
      _ = if (⟨bc, hbc⟩ : s) = (⟨bd, hbd⟩ : s) then 1 else 0 := h
      _ = if bc = bd then 1 else 0 := hite_s
      _ = if a = b then 1 else 0 := hite_full.symm
  obtain ⟨Y, hYspec, hYcols⟩ :=
    partialColOrthonormal_exists_fullColOrthonormal X sFull hX
  refine ⟨fun i c => Y i (e (Sum.inr c)), ?_, ?_⟩
  · intro c hc i
    have hmem : e (Sum.inr c) ∈ sFull := ⟨Sum.inr c, hc, rfl⟩
    have hrange : e (Sum.inr c) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
      ⟨Sum.inr c, rfl⟩
    have hchoose : Classical.choose hrange = Sum.inr c :=
      e.injective (Classical.choose_spec hrange)
    simpa [X, blockCol, leftBasisBlock, hrange, hchoose] using
      hYspec (e (Sum.inr c)) hmem i
  · intro bc bd
    have hrewrite_left :
        (fun i : Fin m => leftBasisBlock U (fun i c => Y i (e (Sum.inr c))) i bc) =
          fun i : Fin m => Y i (e bc) := by
      funext i
      cases bc with
      | inl a =>
          have hmem : e (Sum.inl a) ∈ sFull := ⟨Sum.inl a, hhead a, rfl⟩
          have hrange : e (Sum.inl a) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
            ⟨Sum.inl a, rfl⟩
          have hchoose : Classical.choose hrange = Sum.inl a :=
            e.injective (Classical.choose_spec hrange)
          have h := hYspec (e (Sum.inl a)) hmem i
          simpa [X, blockCol, leftBasisBlock, hrange, hchoose] using h.symm
      | inr _ =>
          rfl
    have hrewrite_right :
        (fun i : Fin m => leftBasisBlock U (fun i c => Y i (e (Sum.inr c))) i bd) =
          fun i : Fin m => Y i (e bd) := by
      funext i
      cases bd with
      | inl a =>
          have hmem : e (Sum.inl a) ∈ sFull := ⟨Sum.inl a, hhead a, rfl⟩
          have hrange : e (Sum.inl a) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
            ⟨Sum.inl a, rfl⟩
          have hchoose : Classical.choose hrange = Sum.inl a :=
            e.injective (Classical.choose_spec hrange)
          have h := hYspec (e (Sum.inl a)) hmem i
          simpa [X, blockCol, leftBasisBlock, hrange, hchoose] using h.symm
      | inr _ =>
          rfl
    have hcols := hYcols (e bc) (e bd)
    have hite : (if e bc = e bd then (1 : ℝ) else 0) =
        if bc = bd then 1 else 0 := by
      by_cases hbc : bc = bd
      · subst hbc
        simp
      · have hne : e bc ≠ e bd := fun h => hbc (e.injective h)
        simp [hbc, hne]
    calc
      (∑ i : Fin m,
        leftBasisBlock U (fun i c => Y i (e (Sum.inr c))) i bc *
          leftBasisBlock U (fun i c => Y i (e (Sum.inr c))) i bd)
          = ∑ i : Fin m, Y i (e bc) * Y i (e bd) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [congr_fun hrewrite_left i, congr_fun hrewrite_right i]
      _ = if e bc = e bd then 1 else 0 := hcols
      _ = if bc = bd then 1 else 0 := hite

/-- Block-form exact source-SVD certificate for the diagonal equation-(9)
route.

This is one layer closer to a genuine rectangular SVD than
`DiagonalSourceSVDTailCertificate`: it assumes the primitive block
decomposition
`A = U SigmaHead V^T + Utail SigmaTail Vperp^T`, column orthonormality of the
left block `[U,Utail]`, column and row orthonormality of the right block
`[Vperp,V]`, and a displayed diagonal nonsingular source-head singular block.
It still does not prove existence of those singular-vector blocks, singular
value ordering, Eckart--Young tail optimality, randomness-derived cross-term
bounds, or any computed SVD/projector/Gram/inverse/product routine. Sampling
probabilities and laws remain exact mathematical inputs by project convention. -/
structure BlockDiagonalSourceSVDTailCertificate (m n r q : ℕ)
    (A : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (SigmaHead : Fin r → Fin r → ℝ)
    (sigmaHead : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ) : Prop where
  split :
    ∀ i j,
      A i j =
        sourceSVDFactorMatrix U SigmaHead V i j +
          sourceSVDFactorMatrix Utail SigmaTail Vperp i j
  left_columns :
    ∀ bc bd : Fin r ⊕ Fin q,
      (∑ i : Fin m,
        leftBasisBlock U Utail i bc * leftBasisBlock U Utail i bd) =
        if bc = bd then 1 else 0
  head_diagonal :
    ∀ a b, SigmaHead a b = if a = b then sigmaHead a else 0
  head_nonzero :
    ∀ a, sigmaHead a ≠ 0
  right_columns :
    ∀ bc bd : Fin q ⊕ Fin r,
      (∑ j : Fin n,
        rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V j bd) =
        if bc = bd then 1 else 0
  right_rows :
    ∀ j k,
      (∑ bc : Fin q ⊕ Fin r,
        rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V k bc) =
        idMatrix n j k

namespace BlockDiagonalSourceSVDTailCertificate

/-- Any block source-SVD certificate with a full left block `[U,Utail]` exposes
the necessary dimension side condition `r+q <= m`.  This is a formal guard
against silently constructing `n` orthonormal left columns in too small an
ambient row space. -/
theorem left_column_count_le_row_dim {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp) :
    r + q ≤ m :=
  leftBasisBlock_col_orthonormal_card_le_rows U Utail cert.left_columns

/-- The block source-SVD certificate supplies the diagonal source-tail
certificate used by the scalar equation-(9) surface, with the tail set to
`Utail SigmaTail Vperp^T`. -/
theorem to_diagonalSourceSVDTailCertificate {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp) :
    DiagonalSourceSVDTailCertificate m n r q A
      (sourceSVDFactorMatrix Utail SigmaTail Vperp) U SigmaHead
        sigmaHead V Utail SigmaTail Vperp := by
  have hleft :=
    leftBasisBlock_component_orthonormal_fields_of_col_orthonormal
      U Utail cert.left_columns
  have hright :=
    rightBasisBlock_component_orthonormal_fields_of_col_orthonormal
      Vperp V cert.right_columns
  have hcomplete :=
    rightBasisBlock_complete_sum_of_row_orthonormal Vperp V cert.right_rows
  exact
    { split := by
        intro i j
        exact cert.split i j
      tail_factor := by
        intro i j
        rfl
      Utail_orthonormal := hleft.2.2
      left_cross := hleft.2.1
      U_orthonormal := hleft.1
      head_diagonal := cert.head_diagonal
      head_nonzero := cert.head_nonzero
      Vperp_orthonormal := hright.1
      right_cross_tail := hright.2.1
      right_cross_head := hright.2.2.1
      V_orthonormal := hright.2.2.2
      right_complete := hcomplete }

/-- The block source-SVD certificate supplies the source-tail left
orthogonality field, again without constructing the SVD itself. -/
theorem sourceTailLeftOrthogonal {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp) :
    sourceTailLeftOrthogonal U
      (sourceSVDFactorMatrix Utail SigmaTail Vperp) :=
  cert.to_diagonalSourceSVDTailCertificate.sourceTailLeftOrthogonal

/-- A supplied Frobenius tail-optimality inequality turns the block source-SVD
certificate into the exact best-rank source-head certificate.  The inequality
is exactly the remaining Eckart--Young obligation. -/
theorem isBestRankApproxFrob_of_tail_optimal {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp)
    (hopt : ∀ B, RectRankAtMost m n r B →
      frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp) ≤
        lowRankResidualFrob A B) :
    IsBestRankApproxFrob m n r A (sourceSVDFactorMatrix U SigmaHead V) :=
  cert.to_diagonalSourceSVDTailCertificate.isBestRankApproxFrob_of_tail_optimal
    hopt

/-- The exact source-tail factor in a block source-SVD certificate has
Frobenius norm equal to the displayed tail singular-value block.  This is
exact-object algebra; computed singular-vector or product routines remain
separate non-probability FP obligations. -/
theorem tail_frobNorm_eq_sigma {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp) :
    frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp) =
      frobNorm SigmaTail := by
  exact
    frobNormRect_sourceSVDFactorMatrix_orthonormal
      Utail SigmaTail Vperp
      cert.to_diagonalSourceSVDTailCertificate.Utail_orthonormal
      cert.to_diagonalSourceSVDTailCertificate.Vperp_orthonormal

/-- The source-head residual in a block source-SVD certificate is exactly the
Frobenius norm of the displayed tail singular-value block. -/
theorem tail_lowRankResidual_eq_sigma {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp) :
    lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) =
      frobNorm SigmaTail := by
  calc
    lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V)
        =
          frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp) :=
          lowRankResidualFrob_sourceSVDFactorMatrix_eq_tail
            A (sourceSVDFactorMatrix Utail SigmaTail Vperp)
            U SigmaHead V cert.split
    _ = frobNorm SigmaTail := cert.tail_frobNorm_eq_sigma

/-- The constructed ordered right-Gram source split feeds the block diagonal
source-SVD certificate once the remaining left-block columns and nonzero head
singular values are supplied.

This is the LR.1cq exact-object bridge from the constructed ordered
right-Gram split to the existing equation-(9) certificate surface.  It uses the
closed ordered source split and ordered right-basis block completeness.  It
does not construct the nullspace-completed tail-left basis, prove
Eckart--Young tail optimality, derive randomness certificates, or certify
computed SVD/projector/Gram/sketch routines. -/
theorem of_rectRightGramOrderedSourceSplit
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (hleft_columns :
      ∀ bc bd :
          Fin k ⊕
            Fin (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        (∑ i : Fin m,
          leftBasisBlock
              (rectRightGramOrderedHeadLeft A hk)
              (rectRightGramOrderedTailLeft A hk) i bc *
            leftBasisBlock
              (rectRightGramOrderedHeadLeft A hk)
              (rectRightGramOrderedTailLeft A hk) i bd) =
          if bc = bd then 1 else 0)
    (hhead_nonzero :
      ∀ a : Fin k,
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a) ≠ 0) :
    BlockDiagonalSourceSVDTailCertificate m n k
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      A
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedHeadSingularDiagonal A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk)
      (rectRightGramOrderedTailLeft A hk)
      (rectRightGramOrderedTailSingularDiagonal A hk)
      (rectRightGramOrderedTailRight A hk) := by
  classical
  have hright := rectRightGramOrderedRightBasisBlock_col_row_orthonormal A hk
  exact
    { split := by
        intro i j
        exact (rectRightGramOrdered_source_head_add_tail A hk i j).symm
      left_columns := hleft_columns
      head_diagonal := by
        intro a b
        simp [rectRightGramOrderedHeadSingularDiagonal]
      head_nonzero := hhead_nonzero
      right_columns := hright.1
      right_rows := hright.2 }

/-- Component-left version of the constructed ordered source-split certificate
constructor.  The head/tail left orthonormality and cross fields are kept
visible so a later nullspace-completion theorem can instantiate exactly those
remaining fields. -/
theorem of_rectRightGramOrderedSourceSplit_component_left
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (hU :
      ∀ a b : Fin k,
        ∑ i : Fin m,
          rectRightGramOrderedHeadLeft A hk i a *
            rectRightGramOrderedHeadLeft A hk i b =
          idMatrix k a b)
    (hcross :
      ∀ a :
          Fin k,
        ∀ c :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        ∑ i : Fin m,
          rectRightGramOrderedHeadLeft A hk i a *
            rectRightGramOrderedTailLeft A hk i c =
          0)
    (hUtail :
      ∀ c d :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        ∑ i : Fin m,
          rectRightGramOrderedTailLeft A hk i c *
            rectRightGramOrderedTailLeft A hk i d =
          idMatrix
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).card) c d)
    (hhead_nonzero :
      ∀ a : Fin k,
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a) ≠ 0) :
    BlockDiagonalSourceSVDTailCertificate m n k
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      A
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedHeadSingularDiagonal A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk)
      (rectRightGramOrderedTailLeft A hk)
      (rectRightGramOrderedTailSingularDiagonal A hk)
      (rectRightGramOrderedTailRight A hk) := by
  exact
    of_rectRightGramOrderedSourceSplit A hk
      (leftBasisBlock_col_orthonormal_of_component_orthonormal_fields
        (rectRightGramOrderedHeadLeft A hk)
        (rectRightGramOrderedTailLeft A hk)
        hU hcross hUtail)
      hhead_nonzero

/-- Positivity of the kth ordered singular value supplies the head
nonzero/orthonormal fields in the constructed ordered source-split certificate.
The only remaining left-side fields are the tail-left orthonormality and the
head/tail left cross-orthogonality, exactly isolating the nullspace-completion
obligation. -/
theorem of_rectRightGramOrderedSourceSplit_component_left_of_last_pos
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (hcross :
      ∀ a :
          Fin k,
        ∀ c :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        ∑ i : Fin m,
          rectRightGramOrderedHeadLeft A hk i a *
            rectRightGramOrderedTailLeft A hk i c =
          0)
    (hUtail :
      ∀ c d :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        ∑ i : Fin m,
          rectRightGramOrderedTailLeft A hk i c *
            rectRightGramOrderedTailLeft A hk i d =
          idMatrix
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).card) c d) :
    BlockDiagonalSourceSVDTailCertificate m n k
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      A
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedHeadSingularDiagonal A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk)
      (rectRightGramOrderedTailLeft A hk)
      (rectRightGramOrderedTailSingularDiagonal A hk)
      (rectRightGramOrderedTailRight A hk) := by
  exact
    of_rectRightGramOrderedSourceSplit_component_left A hk
      (fun a b =>
        rectRightGramOrderedHeadLeft_col_orthonormal_of_last_pos
          A hk hk0 hlast a b)
      hcross hUtail
      (rectRightGramOrderedTopEmbedding_selected_nonzero_of_last_pos
        A hk hk0 hlast)

/-- After the constructed ordered head-tail left cross field is proved, the
last-position positivity constructor only needs the tail-left orthonormality
certificate.  This isolates the remaining nullspace-completed tail-left
obligation for the constructed ordered block source-SVD route. -/
theorem of_rectRightGramOrderedSourceSplit_tail_left_of_last_pos
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (hUtail :
      ∀ c d :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        ∑ i : Fin m,
          rectRightGramOrderedTailLeft A hk i c *
            rectRightGramOrderedTailLeft A hk i d =
          idMatrix
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).card) c d) :
    BlockDiagonalSourceSVDTailCertificate m n k
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      A
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedHeadSingularDiagonal A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk)
      (rectRightGramOrderedTailLeft A hk)
      (rectRightGramOrderedTailSingularDiagonal A hk)
      (rectRightGramOrderedTailRight A hk) := by
  exact
    of_rectRightGramOrderedSourceSplit_component_left_of_last_pos A hk hk0 hlast
      (fun a c =>
        rectRightGramOrderedHeadTailLeft_cross_zero_of_last_pos
          A hk hk0 hlast a c)
      hUtail

/-- Positive-complement branch for the constructed ordered block source-SVD
certificate.  Kth head positivity supplies the head fields and left cross
field; strict positivity of every complement singular value supplies tail-left
orthonormality for the zero-safe tail table.  Zero complement singular values
still require a separate nullspace-completed tail-left construction. -/
theorem of_rectRightGramOrderedSourceSplit_all_tail_pos_of_last_pos
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (htail_pos :
      ∀ c :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        0 < rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)) :
    BlockDiagonalSourceSVDTailCertificate m n k
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      A
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedHeadSingularDiagonal A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk)
      (rectRightGramOrderedTailLeft A hk)
      (rectRightGramOrderedTailSingularDiagonal A hk)
      (rectRightGramOrderedTailRight A hk) := by
  exact
    of_rectRightGramOrderedSourceSplit_tail_left_of_last_pos A hk hk0 hlast
      (fun c d =>
        rectRightGramOrderedTailLeft_col_orthonormal_of_complement_pos
          A hk htail_pos c d)

/-- Replacement-tail-left constructor for the ordered block source-SVD
certificate.  A future nullspace-completed table can instantiate `Utail` here:
it must agree with the constructed zero-safe table on nonzero complement
singular directions, be orthonormal, and remain orthogonal to the constructed
head-left block. -/
theorem of_rectRightGramOrderedSourceSplit_replacement_tail_left_of_last_pos
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (Utail :
      Fin m →
        Fin (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ)
    (hUtail_agree :
      ∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c)
    (hcross :
      ∀ a :
          Fin k,
        ∀ c :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        ∑ i : Fin m,
          rectRightGramOrderedHeadLeft A hk i a *
            Utail i c =
          0)
    (hUtail_orthonormal :
      ∀ c d :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        ∑ i : Fin m,
          Utail i c * Utail i d =
          idMatrix
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).card) c d) :
    BlockDiagonalSourceSVDTailCertificate m n k
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      A
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedHeadSingularDiagonal A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk)
      Utail
      (rectRightGramOrderedTailSingularDiagonal A hk)
      (rectRightGramOrderedTailRight A hk) := by
  classical
  have hright := rectRightGramOrderedRightBasisBlock_col_row_orthonormal A hk
  exact
    { split := by
        intro i j
        exact
          (rectRightGramOrdered_source_head_add_tail_replacement_left
            A hk Utail hUtail_agree i j).symm
      left_columns :=
        leftBasisBlock_col_orthonormal_of_component_orthonormal_fields
          (rectRightGramOrderedHeadLeft A hk)
          Utail
          (fun a b =>
            rectRightGramOrderedHeadLeft_col_orthonormal_of_last_pos
              A hk hk0 hlast a b)
          hcross
          hUtail_orthonormal
      head_diagonal := by
        intro a b
        simp [rectRightGramOrderedHeadSingularDiagonal]
      head_nonzero :=
        rectRightGramOrderedTopEmbedding_selected_nonzero_of_last_pos
          A hk hk0 hlast
      right_columns := hright.1
      right_rows := hright.2 }

end BlockDiagonalSourceSVDTailCertificate

/-- Obstruction to using the raw constructed zero-safe tail-left table in a
block source-SVD certificate when a complement singular value is zero.  Any
valid block certificate would imply tail-left orthonormality, contradicting the
zero self-dot theorem above. -/
theorem
    not_BlockDiagonalSourceSVDTailCertificate_rectRightGramOrdered_zero_safe_tail_of_zero_complement_singularValue
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    {c :
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)}
    (hzero :
      rectRightGramBasisSingularValue A
        (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) = 0) :
    ¬ BlockDiagonalSourceSVDTailCertificate m n k
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      A
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedHeadSingularDiagonal A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk)
      (rectRightGramOrderedTailLeft A hk)
      (rectRightGramOrderedTailSingularDiagonal A hk)
      (rectRightGramOrderedTailRight A hk) := by
  intro cert
  exact
    (not_rectRightGramOrderedTailLeft_col_orthonormal_of_zero_complement_singularValue
      A hk hzero)
      cert.to_diagonalSourceSVDTailCertificate.Utail_orthonormal

/-- Tail-index type for the constructed ordered top-`k` complement.  This
abbreviation keeps the nullspace-completion statements readable while reducing
definitionally to the complement-cardinality `Fin` type used elsewhere. -/
abbrev rectRightGramOrderedTailIndex {n k : ℕ} (hk : k ≤ n) : Type :=
  Fin (((rectRightGramSelectedIndexSet
    (rectRightGramOrderedTopEmbedding hk))ᶜ).card)

/-- The constructed ordered top block together with its complement-tail index
type has ambient right cardinality `n`.  This exact arithmetic bridge is one of
the remaining reindexing dependencies for transporting the q-dimensional
Eckart--Young lower-bound theorem to the constructed ordered source split. -/
theorem rectRightGramOrderedTailIndex_card_add {n k : ℕ} (hk : k ≤ n) :
    k + Fintype.card (rectRightGramOrderedTailIndex hk) = n := by
  simpa [rectRightGramOrderedTailIndex, Fintype.card_fin] using
    rectRightGramSelectedIndexSet_card_add_compl_card
      (rectRightGramOrderedTopEmbedding hk)

/-- The canonical exact column map from the constructed ordered top-`k` block
and its complement-tail enumeration into the original right-coordinate domain.
This is reindexing infrastructure only; it computes no floating-point object. -/
noncomputable def rectRightGramOrderedHeadTailColumnMap {n k : ℕ}
    (hk : k ≤ n) :
    Fin k ⊕ rectRightGramOrderedTailIndex hk → Fin n
  | Sum.inl a => rectRightGramOrderedTopEmbedding hk a
  | Sum.inr c =>
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)

@[simp] theorem rectRightGramOrderedHeadTailColumnMap_inl {n k : ℕ}
    (hk : k ≤ n) (a : Fin k) :
    rectRightGramOrderedHeadTailColumnMap hk (Sum.inl a) =
      rectRightGramOrderedTopEmbedding hk a := rfl

@[simp] theorem rectRightGramOrderedHeadTailColumnMap_inr {n k : ℕ}
    (hk : k ≤ n) (c : rectRightGramOrderedTailIndex hk) :
    rectRightGramOrderedHeadTailColumnMap hk (Sum.inr c) =
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) := rfl

/-- The constructed head-plus-complement-tail column map is injective. -/
theorem rectRightGramOrderedHeadTailColumnMap_injective {n k : ℕ}
    (hk : k ≤ n) :
    Function.Injective (rectRightGramOrderedHeadTailColumnMap hk) := by
  classical
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          have hab : a = b :=
            (rectRightGramOrderedTopEmbedding hk).injective (by
              simpa [rectRightGramOrderedHeadTailColumnMap] using hxy)
          simp [hab]
      | inr c =>
          let s := rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)
          have hhead : rectRightGramOrderedTopEmbedding hk a ∈ s := by
            simp [s, rectRightGramSelectedIndexSet]
          have htail_mem : (sᶜ).orderEmbOfFin rfl c ∈ sᶜ :=
            Finset.orderEmbOfFin_mem (sᶜ) rfl c
          have htail_not : (sᶜ).orderEmbOfFin rfl c ∉ s :=
            Finset.mem_compl.mp htail_mem
          have hraw :
              rectRightGramOrderedTopEmbedding hk a =
                (sᶜ).orderEmbOfFin rfl c := by
            simpa [rectRightGramOrderedHeadTailColumnMap, s] using hxy
          exfalso
          exact htail_not (by simpa [hraw] using hhead)
  | inr c =>
      cases y with
      | inl a =>
          let s := rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)
          have hhead : rectRightGramOrderedTopEmbedding hk a ∈ s := by
            simp [s, rectRightGramSelectedIndexSet]
          have htail_mem : (sᶜ).orderEmbOfFin rfl c ∈ sᶜ :=
            Finset.orderEmbOfFin_mem (sᶜ) rfl c
          have htail_not : (sᶜ).orderEmbOfFin rfl c ∉ s :=
            Finset.mem_compl.mp htail_mem
          have hraw :
              (sᶜ).orderEmbOfFin rfl c =
                rectRightGramOrderedTopEmbedding hk a := by
            simpa [rectRightGramOrderedHeadTailColumnMap, s] using hxy
          exfalso
          exact htail_not (by simpa [← hraw] using hhead)
      | inr d =>
          let s := rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)
          have hraw :
              (sᶜ).orderEmbOfFin rfl c =
                (sᶜ).orderEmbOfFin rfl d := by
            simpa [rectRightGramOrderedHeadTailColumnMap, s] using hxy
          have hcd : c = d := ((sᶜ).orderEmbOfFin rfl).injective hraw
          simp [hcd]

/-- The constructed head-plus-complement-tail column map is surjective. -/
theorem rectRightGramOrderedHeadTailColumnMap_surjective {n k : ℕ}
    (hk : k ≤ n) :
    Function.Surjective (rectRightGramOrderedHeadTailColumnMap hk) := by
  classical
  intro j
  let s := rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)
  by_cases hj : j ∈ s
  · have hpre :
        ∃ a : Fin k, rectRightGramOrderedTopEmbedding hk a = j := by
      simpa [s, rectRightGramSelectedIndexSet] using hj
    rcases hpre with ⟨a, ha⟩
    exact ⟨Sum.inl a, by simpa [rectRightGramOrderedHeadTailColumnMap] using ha⟩
  · have hjc : j ∈ sᶜ := Finset.mem_compl.mpr hj
    let c : Fin ((sᶜ).card) := ((sᶜ).orderIsoOfFin rfl).symm ⟨j, hjc⟩
    have hc_sub : (sᶜ).orderIsoOfFin rfl c = ⟨j, hjc⟩ := by
      simp [c]
    have hc : (sᶜ).orderEmbOfFin rfl c = j := by
      change (((sᶜ).orderIsoOfFin rfl c : {x // x ∈ sᶜ}) : Fin n) = j
      exact congrArg Subtype.val hc_sub
    exact ⟨Sum.inr c, by
      simpa [rectRightGramOrderedHeadTailColumnMap, s] using hc⟩

/-- Exact equivalence from the constructed ordered head plus complement-tail
index sum to the original right-coordinate domain. -/
noncomputable def rectRightGramOrderedHeadTailColumnSumEquiv {n k : ℕ}
    (hk : k ≤ n) :
    Fin k ⊕ rectRightGramOrderedTailIndex hk ≃ Fin n :=
  Equiv.ofBijective (rectRightGramOrderedHeadTailColumnMap hk)
    ⟨rectRightGramOrderedHeadTailColumnMap_injective hk,
      rectRightGramOrderedHeadTailColumnMap_surjective hk⟩

@[simp] theorem rectRightGramOrderedHeadTailColumnSumEquiv_inl {n k : ℕ}
    (hk : k ≤ n) (a : Fin k) :
    rectRightGramOrderedHeadTailColumnSumEquiv hk (Sum.inl a) =
      rectRightGramOrderedTopEmbedding hk a := rfl

@[simp] theorem rectRightGramOrderedHeadTailColumnSumEquiv_inr {n k : ℕ}
    (hk : k ≤ n) (c : rectRightGramOrderedTailIndex hk) :
    rectRightGramOrderedHeadTailColumnSumEquiv hk (Sum.inr c) =
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) := rfl

/-- Exact `Fin (k+q) ≃ Fin n` version of the constructed ordered
head-plus-complement-tail column equivalence, where
`q = |{ordered top-k indices}ᶜ|`. -/
noncomputable def rectRightGramOrderedHeadTailColumnEquiv {n k : ℕ}
    (hk : k ≤ n) :
    Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ≃ Fin n :=
  finSumFinEquiv.symm.trans (rectRightGramOrderedHeadTailColumnSumEquiv hk)

@[simp] theorem rectRightGramOrderedHeadTailColumnEquiv_head {n k : ℕ}
    (hk : k ≤ n) (a : Fin k) :
    rectRightGramOrderedHeadTailColumnEquiv hk (finSumFinEquiv (Sum.inl a)) =
      rectRightGramOrderedTopEmbedding hk a := by
  simp [rectRightGramOrderedHeadTailColumnEquiv]

@[simp] theorem rectRightGramOrderedHeadTailColumnEquiv_tail {n k : ℕ}
    (hk : k ≤ n) (c : rectRightGramOrderedTailIndex hk) :
    rectRightGramOrderedHeadTailColumnEquiv hk (finSumFinEquiv (Sum.inr c)) =
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) := by
  simp [rectRightGramOrderedHeadTailColumnEquiv]

/-- Rank-at-most transport through the constructed ordered head-plus-tail
column equivalence. -/
theorem RectRankAtMost.reindexCols_rectRightGramOrderedHeadTailColumnEquiv
    {m n k r : ℕ} (hk : k ≤ n) {A : Fin m → Fin n → ℝ}
    (hA : RectRankAtMost m n r A) :
    RectRankAtMost m
      (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) r
      (rectReindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) A) :=
  RectRankAtMost.reindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) hA

/-- Rank-at-most transports back from the constructed ordered head-plus-tail
column equivalence. -/
theorem RectRankAtMost.of_reindexCols_rectRightGramOrderedHeadTailColumnEquiv
    {m n k r : ℕ} (hk : k ≤ n) {A : Fin m → Fin n → ℝ}
    (hA : RectRankAtMost m
      (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) r
      (rectReindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) A)) :
    RectRankAtMost m n r A :=
  RectRankAtMost.of_reindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) hA

/-- Frobenius residual invariance through the constructed ordered
head-plus-tail column equivalence. -/
theorem lowRankResidualFrob_rectRightGramOrderedHeadTailColumnEquiv
    {m n k : ℕ} (hk : k ≤ n) (A B : Fin m → Fin n → ℝ) :
    lowRankResidualFrob
        (rectReindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) A)
        (rectReindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) B) =
      lowRankResidualFrob A B :=
  lowRankResidualFrob_reindexCols
    (rectRightGramOrderedHeadTailColumnEquiv hk) A B

/-- Constructed ordered head-tail square gap.

For a nonempty constructed top-`k` block, the last selected top singular square
separates every selected head singular square from every complement-tail
singular square.  This is the exact-object gap certificate needed by the
source-factor LR.1dw bridge when the complement-tail enumeration is not itself
sorted.  It does not build the original-column reindexing/equivalence
transport, prove tail optimality, derive randomness, or certify computed
non-probability SVD/projector/Gram/sketch routines. -/
theorem rectRightGramOrdered_head_tail_square_gap
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k) :
    ∃ eta : ℝ,
      (∀ a : Fin k,
        eta ≤
          rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk a) ^ 2) ∧
      ∀ c : rectRightGramOrderedTailIndex hk,
        rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) ^ 2 ≤
          eta := by
  classical
  let last : Fin k := rectTopLastIndex hk0
  refine
    ⟨rectRightGramBasisSingularValue A
        (rectRightGramOrderedTopEmbedding hk last) ^ 2, ?_, ?_⟩
  · intro a
    have hlast_sq :
        rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk last) ^ 2 =
          rectSingularValueSq A (rectTopIndex hk last) :=
      rectRightGramOrderedTopEmbeddingCertificate_selected_sq_eq
        A hk (rectRightGramOrderedTopEmbedding hk)
        (rectRightGramOrderedTopEmbedding_certificate A hk) last
    have ha_sq :
        rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk a) ^ 2 =
          rectSingularValueSq A (rectTopIndex hk a) :=
      rectRightGramOrderedTopEmbeddingCertificate_selected_sq_eq
        A hk (rectRightGramOrderedTopEmbedding hk)
        (rectRightGramOrderedTopEmbedding_certificate A hk) a
    rw [hlast_sq, ha_sq]
    exact rectSingularValueSq_antitone A (rectTopIndex_le_last hk hk0 a)
  · intro c
    let s := rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)
    let b : Fin n := (sᶜ).orderEmbOfFin rfl c
    have hbmem : b ∈ sᶜ := by
      simp [b, Finset.orderEmbOfFin_mem]
    have hbnot : b ∉ s := Finset.mem_compl.mp hbmem
    have hle :
        rectRightGramBasisSingularValue A b ≤
          rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk last) := by
      simpa [s, b] using
        rectRightGramOrderedTopEmbedding_complement_singularValue_le_selected
          A hk hbnot last
    have htail_nonneg : 0 ≤ rectRightGramBasisSingularValue A b :=
      rectRightGramBasisSingularValue_nonneg A b
    have hhead_nonneg :
        0 ≤
          rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk last) :=
      rectRightGramBasisSingularValue_nonneg A
        (rectRightGramOrderedTopEmbedding hk last)
    have habs :
        |rectRightGramBasisSingularValue A b| ≤
          |rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk last)| := by
      simpa [abs_of_nonneg htail_nonneg, abs_of_nonneg hhead_nonneg] using hle
    have hsq := (sq_le_sq).mpr habs
    simpa [s, b, last] using hsq

/-- Partial left-block index set for the ordered nullspace-completion route:
all head columns are specified, and exactly the complement-tail columns with
nonzero singular value are specified.  Zero tail singular directions are left
free for orthonormal completion. -/
def rectRightGramOrderedNonzeroTailPartialSet {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Set (Fin k ⊕ rectRightGramOrderedTailIndex hk) :=
  fun bc =>
    match bc with
    | Sum.inl _ => True
    | Sum.inr c =>
        rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) ≠ 0

@[simp] theorem rectRightGramOrderedNonzeroTailPartialSet_head {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (a : Fin k) :
    Sum.inl a ∈ rectRightGramOrderedNonzeroTailPartialSet A hk := by
  change True
  trivial

@[simp] theorem rectRightGramOrderedNonzeroTailPartialSet_tail_iff {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (c : rectRightGramOrderedTailIndex hk) :
    Sum.inr c ∈ rectRightGramOrderedNonzeroTailPartialSet A hk ↔
      rectRightGramBasisSingularValue A
        (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) ≠ 0 := by
  rfl

/-- On the ordered partial set consisting of all head columns and only nonzero
tail singular directions, the zero-safe head/tail left candidates are already a
partial orthonormal family.  This is the concrete `S` instantiation needed by
the nullspace-completion theorem; zero tail directions are deliberately absent
from the specified set. -/
theorem rectRightGramOrderedNonzeroTailPartialSet_leftBasisBlock_col_orthonormal_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0))) :
    ∀ a b : rectRightGramOrderedNonzeroTailPartialSet A hk,
      (∑ i : Fin m,
        leftBasisBlock
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedTailLeft A hk) i a *
          leftBasisBlock
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedTailLeft A hk) i b) =
        if a = b then 1 else 0 := by
  classical
  intro a b
  rcases a with ⟨bc, hbc⟩
  rcases b with ⟨bd, hbd⟩
  cases bc with
  | inl ca =>
      cases bd with
      | inl db =>
          have hhead :=
            rectRightGramOrderedHeadLeft_col_orthonormal_of_last_pos
              A hk hk0 hlast ca db
          have hite :
              idMatrix k ca db =
                if (⟨Sum.inl ca, hbc⟩ :
                    rectRightGramOrderedNonzeroTailPartialSet A hk) =
                    ⟨Sum.inl db, hbd⟩ then 1 else 0 := by
            by_cases hcd : ca = db
            · subst db
              simp [idMatrix]
            · have hsub :
                  (⟨Sum.inl ca, hbc⟩ :
                    rectRightGramOrderedNonzeroTailPartialSet A hk) ≠
                    ⟨Sum.inl db, hbd⟩ := by
                intro hEq
                have hval : (Sum.inl ca :
                    Fin k ⊕ rectRightGramOrderedTailIndex hk) = Sum.inl db :=
                  congrArg Subtype.val hEq
                exact hcd (Sum.inl.inj hval)
              simp [idMatrix, hcd, hsub]
          calc
            (∑ i : Fin m,
              leftBasisBlock
                  (rectRightGramOrderedHeadLeft A hk)
                  (rectRightGramOrderedTailLeft A hk) i (Sum.inl ca) *
                leftBasisBlock
                  (rectRightGramOrderedHeadLeft A hk)
                  (rectRightGramOrderedTailLeft A hk) i (Sum.inl db))
                = idMatrix k ca db := by
                  simpa [leftBasisBlock] using hhead
            _ = if (⟨Sum.inl ca, hbc⟩ :
                    rectRightGramOrderedNonzeroTailPartialSet A hk) =
                    ⟨Sum.inl db, hbd⟩ then 1 else 0 := hite
      | inr db =>
          have hcross :=
            rectRightGramOrderedHeadTailLeft_cross_zero_of_last_pos
              A hk hk0 hlast ca db
          have hsub :
              (⟨Sum.inl ca, hbc⟩ :
                rectRightGramOrderedNonzeroTailPartialSet A hk) ≠
                ⟨Sum.inr db, hbd⟩ := by
            intro hEq
            cases congrArg Subtype.val hEq
          calc
            (∑ i : Fin m,
              leftBasisBlock
                  (rectRightGramOrderedHeadLeft A hk)
                  (rectRightGramOrderedTailLeft A hk) i (Sum.inl ca) *
                leftBasisBlock
                  (rectRightGramOrderedHeadLeft A hk)
                  (rectRightGramOrderedTailLeft A hk) i (Sum.inr db))
                = 0 := by
                  simpa [leftBasisBlock] using hcross
            _ = if (⟨Sum.inl ca, hbc⟩ :
                    rectRightGramOrderedNonzeroTailPartialSet A hk) =
                    ⟨Sum.inr db, hbd⟩ then 1 else 0 := by
                  simp [hsub]
  | inr ca =>
      cases bd with
      | inl db =>
          have hcross :=
            rectRightGramOrderedHeadTailLeft_cross_zero_of_last_pos
              A hk hk0 hlast db ca
          have hsub :
              (⟨Sum.inr ca, hbc⟩ :
                rectRightGramOrderedNonzeroTailPartialSet A hk) ≠
                ⟨Sum.inl db, hbd⟩ := by
            intro hEq
            cases congrArg Subtype.val hEq
          calc
            (∑ i : Fin m,
              leftBasisBlock
                  (rectRightGramOrderedHeadLeft A hk)
                  (rectRightGramOrderedTailLeft A hk) i (Sum.inr ca) *
                leftBasisBlock
                  (rectRightGramOrderedHeadLeft A hk)
                  (rectRightGramOrderedTailLeft A hk) i (Sum.inl db))
                =
                  ∑ i : Fin m,
                    rectRightGramOrderedHeadLeft A hk i db *
                      rectRightGramOrderedTailLeft A hk i ca := by
                    apply Finset.sum_congr rfl
                    intro i _
                    simp [leftBasisBlock]
                    ring
            _ = 0 := hcross
            _ = if (⟨Sum.inr ca, hbc⟩ :
                    rectRightGramOrderedNonzeroTailPartialSet A hk) =
                    ⟨Sum.inl db, hbd⟩ then 1 else 0 := by
                  simp [hsub]
      | inr db =>
          have hca_ne :
              rectRightGramBasisSingularValue A
                (((rectRightGramSelectedIndexSet
                  (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl ca) ≠
                0 := by
            simpa using
              (rectRightGramOrderedNonzeroTailPartialSet_tail_iff A hk ca).mp hbc
          have hdb_ne :
              rectRightGramBasisSingularValue A
                (((rectRightGramSelectedIndexSet
                  (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl db) ≠
                0 := by
            simpa using
              (rectRightGramOrderedNonzeroTailPartialSet_tail_iff A hk db).mp hbd
          have hca_pos :
              0 < rectRightGramBasisSingularValue A
                (((rectRightGramSelectedIndexSet
                  (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl ca) :=
            lt_of_le_of_ne
              (rectRightGramBasisSingularValue_nonneg A _)
              (Ne.symm hca_ne)
          have hdb_pos :
              0 < rectRightGramBasisSingularValue A
                (((rectRightGramSelectedIndexSet
                  (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl db) :=
            lt_of_le_of_ne
              (rectRightGramBasisSingularValue_nonneg A _)
              (Ne.symm hdb_ne)
          let s := rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)
          let ec : Fin n := (sᶜ).orderEmbOfFin rfl ca
          let ed : Fin n := (sᶜ).orderEmbOfFin rfl db
          have horth :
              ∑ i : Fin m,
                  rectRightGramLeftSingularZeroSafe A i ec *
                    rectRightGramLeftSingularZeroSafe A i ed =
                idMatrix n ec ed :=
            rectRightGramLeftSingularZeroSafe_col_orthonormal_of_pos
              A hca_pos hdb_pos
          have htail :
              (∑ i : Fin m,
                leftBasisBlock
                    (rectRightGramOrderedHeadLeft A hk)
                    (rectRightGramOrderedTailLeft A hk) i (Sum.inr ca) *
                  leftBasisBlock
                    (rectRightGramOrderedHeadLeft A hk)
                    (rectRightGramOrderedTailLeft A hk) i (Sum.inr db)) =
                idMatrix
                  (((rectRightGramSelectedIndexSet
                    (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ca db := by
            calc
              (∑ i : Fin m,
                leftBasisBlock
                    (rectRightGramOrderedHeadLeft A hk)
                    (rectRightGramOrderedTailLeft A hk) i (Sum.inr ca) *
                  leftBasisBlock
                    (rectRightGramOrderedHeadLeft A hk)
                    (rectRightGramOrderedTailLeft A hk) i (Sum.inr db))
                  = idMatrix n ec ed := by
                    simpa [leftBasisBlock, rectRightGramOrderedTailLeft,
                      rectRightGramBasisSVDTailLeft, s, ec, ed] using horth
              _ = idMatrix
                    (((rectRightGramSelectedIndexSet
                      (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ca db := by
                    by_cases hcd : ca = db
                    · subst db
                      simp [idMatrix, ec, ed]
                    · have hne : ec ≠ ed := by
                        intro hEq
                        exact hcd (((sᶜ).orderEmbOfFin rfl).injective hEq)
                      simp [idMatrix, hcd, hne]
          have hite :
              idMatrix
                  (((rectRightGramSelectedIndexSet
                    (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ca db =
                if (⟨Sum.inr ca, hbc⟩ :
                    rectRightGramOrderedNonzeroTailPartialSet A hk) =
                    ⟨Sum.inr db, hbd⟩ then 1 else 0 := by
            by_cases hcd : ca = db
            · subst db
              simp [idMatrix]
            · have hsub :
                  (⟨Sum.inr ca, hbc⟩ :
                    rectRightGramOrderedNonzeroTailPartialSet A hk) ≠
                    ⟨Sum.inr db, hbd⟩ := by
                intro hEq
                have hval : (Sum.inr ca :
                    Fin k ⊕ rectRightGramOrderedTailIndex hk) = Sum.inr db :=
                  congrArg Subtype.val hEq
                exact hcd (Sum.inr.inj hval)
              simp [idMatrix, hcd, hsub]
          exact htail.trans hite

/-- Concrete ordered nullspace-completion existence theorem for equation~(9).
Given an embedding of the constructed head plus complement-tail left columns into
the ambient `Fin m` column coordinates, completing the partial set consisting of
all head columns and the nonzero tail directions produces a replacement tail-left
table.  The replacement agrees with the zero-safe table on every nonzero
complement singular direction, has an orthonormal concatenated left block, and
therefore instantiates the ordered block source-SVD certificate through the
replacement-tail adapter. -/
theorem exists_rectRightGramOrdered_replacement_tail_left_block_certificate_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (e : Fin k ⊕ rectRightGramOrderedTailIndex hk ↪ Fin m) :
    ∃ Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ,
      (∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c) ∧
      (∀ bc bd : Fin k ⊕ rectRightGramOrderedTailIndex hk,
        (∑ i : Fin m,
          leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bc *
            leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bd) =
          if bc = bd then 1 else 0) ∧
      BlockDiagonalSourceSVDTailCertificate m n k
        (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
        A
        (rectRightGramOrderedHeadLeft A hk)
        (rectRightGramOrderedHeadSingularDiagonal A hk)
        (fun a : Fin k =>
          rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk a))
        (rectRightGramOrderedHeadRight A hk)
        Utail
        (rectRightGramOrderedTailSingularDiagonal A hk)
        (rectRightGramOrderedTailRight A hk) := by
  classical
  let S := rectRightGramOrderedNonzeroTailPartialSet A hk
  have hhead : ∀ a : Fin k, Sum.inl a ∈ S := by
    intro a
    simp [S]
  have hpartial : ∀ a b : S,
      (∑ i : Fin m,
        leftBasisBlock
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedTailLeft A hk) i a *
          leftBasisBlock
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedTailLeft A hk) i b) =
        if a = b then 1 else 0 :=
    rectRightGramOrderedNonzeroTailPartialSet_leftBasisBlock_col_orthonormal_of_last_pos
      A hk hk0 hlast
  obtain ⟨Utail, hpreserve, hcols⟩ :=
    partialLeftBasisBlock_exists_replacement_tail
      e
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedTailLeft A hk)
      S hhead hpartial
  have hfields :=
    leftBasisBlock_component_orthonormal_fields_of_col_orthonormal
      (rectRightGramOrderedHeadLeft A hk) Utail hcols
  have hagree :
      ∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c := by
    intro i c hτ
    have hc : Sum.inr c ∈ S := by
      simpa [S] using
        (rectRightGramOrderedNonzeroTailPartialSet_tail_iff A hk c).mpr hτ
    exact hpreserve c hc i
  refine ⟨Utail, hagree, hcols, ?_⟩
  exact
    BlockDiagonalSourceSVDTailCertificate.of_rectRightGramOrderedSourceSplit_replacement_tail_left_of_last_pos
      A hk hk0 hlast Utail hagree hfields.2.1 hfields.2.2

/-- Block-source-SVD version of the diagonal scalar equation-(9) rank/residual
surface.  The block certificate constructs the diagonal source-tail certificate
internally; the remaining assumptions are exactly the source full-rank
condition on `V^T Z` and the displayed cross-term radius. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_blockDiagonalSourceSVDTailCertificate
    {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp)
    (Z : Fin n → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_diagonalSourceSVDTailCertificate
    cert.to_diagonalSourceSVDTailCertificate Z heps hVZ hcrossTerm

/-- Ordered right-Gram source-split rank/residual surface.

This composes the constructed ordered replacement-tail source-SVD certificate
with the exact block-certificate equation-(9) rank surface.  The theorem keeps
the source full-rank condition on `V_ord^T Z` and the displayed
`Sigma_tail (V_tail^T Z)(V_ord^T Z)^{-1}` cross-term radius explicit.  It is
an exact-object/exact-law theorem: it does not compute the singular vectors,
projector, sketch Gram, inverse, or downstream products. -/
theorem exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (e : Fin k ⊕ rectRightGramOrderedTailIndex hk ↪ Fin m)
    (Z : Fin n → Fin k → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (rectRightGramOrderedHeadRight A hk) Z :
            Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (rectRightGramOrderedTailSingularDiagonal A hk)
            (rightSketchCrossGramRectInvFactor
              (rectRightGramOrderedTailRight A hk) Z
              (rectRightGramOrderedHeadRight A hk))) ≤
        eps * frobNorm (rectRightGramOrderedTailSingularDiagonal A hk)) :
    ∃ Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ,
      (∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c) ∧
      (∀ bc bd : Fin k ⊕ rectRightGramOrderedTailIndex hk,
        (∑ i : Fin m,
          leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bc *
            leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bd) =
          if bc = bd then 1 else 0) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n k
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 *
            (Real.sqrt (1 + eps ^ 2) *
              frobNorm (rectRightGramOrderedTailSingularDiagonal A hk)) := by
  classical
  obtain ⟨Utail, hagree, hcols, cert⟩ :=
    exists_rectRightGramOrdered_replacement_tail_left_block_certificate_of_last_pos
      A hk hk0 hlast e
  have hsurface :=
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_blockDiagonalSourceSVDTailCertificate
      cert Z heps hVZ hcrossTerm
  exact ⟨Utail, hagree, hcols, hsurface⟩

/-- Block-source-SVD version of the tail-optimal diagonal source-SVD relative
scalar-rate surface.  The source-head best-rank certificate is derived from
the supplied tail-optimality inequality after the block certificate has
constructed the diagonal source-tail certificate. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate
    {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp)
    (Z : Fin n → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail)
    (hopt : ∀ B, RectRankAtMost m n r B →
      frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp) ≤
        lowRankResidualFrob A B)
    (hrelative :
      2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) ≤
        rho * frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp)) :
    IsBestRankApproxFrob m n r A (sourceSVDFactorMatrix U SigmaHead V) ∧
      lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) =
        frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_diagonalSourceSVDTailCertificate
    cert.to_diagonalSourceSVDTailCertificate Z heps hVZ hcrossTerm hopt
    hrelative

/-- Block-source-SVD relative scalar-rate surface with the denominator written
as the displayed tail singular-value block norm.  The equality
`||Utail SigmaTail Vperpᵀ||_F = ||SigmaTail||_F` is supplied by the exact
orthonormal-factor identity, not by an implementation-facing computed SVD
routine. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate_sigmaTail
    {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp)
    (Z : Fin n → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail)
    (hopt : ∀ B, RectRankAtMost m n r B →
      frobNorm SigmaTail ≤ lowRankResidualFrob A B)
    (hrelative :
      2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) ≤
        rho * frobNorm SigmaTail) :
    IsBestRankApproxFrob m n r A (sourceSVDFactorMatrix U SigmaHead V) ∧
      lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) =
        frobNorm SigmaTail ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) := by
  have htail :
      frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp) =
        frobNorm SigmaTail :=
    cert.tail_frobNorm_eq_sigma
  have hopt' : ∀ B, RectRankAtMost m n r B →
      frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp) ≤
        lowRankResidualFrob A B := by
    intro B hB
    simpa [htail] using hopt B hB
  have hrelative' :
      2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) ≤
        rho * frobNormRect
          (sourceSVDFactorMatrix Utail SigmaTail Vperp) := by
    simpa [htail] using hrelative
  have hsurface :=
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate
      cert Z heps hVZ hcrossTerm hopt' hrelative'
  refine ⟨hsurface.1, ?_, hsurface.2.2.1, hsurface.2.2.2.1,
    hsurface.2.2.2.2.1, hsurface.2.2.2.2.2.1,
    hsurface.2.2.2.2.2.2.1, hsurface.2.2.2.2.2.2.2⟩
  simpa [htail] using hsurface.2.1

/-- Ordered right-Gram source-split relative surface with the tail-optimality
and scalar-comparison obligations still visible.

This composes the constructed ordered replacement-tail source-SVD certificate
with the block-certificate sigma-tail relative theorem.  It closes the exact
ordered source-split handoff for the relative equation-(9) surface, but it does
not prove the displayed tail-optimality inequality, derive the cross-term
radius from randomness, or certify computed non-probability SVD/projector/Gram
routine arithmetic. -/
theorem exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (e : Fin k ⊕ rectRightGramOrderedTailIndex hk ↪ Fin m)
    (Z : Fin n → Fin k → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (rectRightGramOrderedHeadRight A hk) Z :
            Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (rectRightGramOrderedTailSingularDiagonal A hk)
            (rightSketchCrossGramRectInvFactor
              (rectRightGramOrderedTailRight A hk) Z
              (rectRightGramOrderedHeadRight A hk))) ≤
        eps * frobNorm (rectRightGramOrderedTailSingularDiagonal A hk))
    (hopt : ∀ B, RectRankAtMost m n k B →
      frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) ≤
        lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (rectRightGramOrderedTailSingularDiagonal A hk)) ≤
        rho * frobNorm (rectRightGramOrderedTailSingularDiagonal A hk)) :
    ∃ Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ,
      (∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c) ∧
      (∀ bc bd : Fin k ⊕ rectRightGramOrderedTailIndex hk,
        (∑ i : Fin m,
          leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bc *
            leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bd) =
          if bc = bd then 1 else 0) ∧
      IsBestRankApproxFrob m n k A
        (sourceSVDFactorMatrix
          (rectRightGramOrderedHeadLeft A hk)
          (rectRightGramOrderedHeadSingularDiagonal A hk)
          (rectRightGramOrderedHeadRight A hk)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedHeadSingularDiagonal A hk)
            (rectRightGramOrderedHeadRight A hk)) =
        frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n k
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix
                (rectRightGramOrderedHeadLeft A hk)
                (rectRightGramOrderedHeadSingularDiagonal A hk)
                (rectRightGramOrderedHeadRight A hk)) := by
  classical
  obtain ⟨Utail, hagree, hcols, cert⟩ :=
    exists_rectRightGramOrdered_replacement_tail_left_block_certificate_of_last_pos
      A hk hk0 hlast e
  have hsurface :=
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate_sigmaTail
      cert Z heps hVZ hcrossTerm hopt hrelative
  exact ⟨Utail, hagree, hcols, hsurface⟩

/-- Head left singular-vector block obtained by splitting a square SVD table. -/
noncomputable def squareSVDHeadLeft {r q : ℕ}
    (Ufull : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin (r + q) → Fin r → ℝ :=
  fun i a => Ufull i (Fin.castAdd q a)

/-- Tail left singular-vector block obtained by splitting a square SVD table. -/
noncomputable def squareSVDTailLeft {r q : ℕ}
    (Ufull : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin (r + q) → Fin q → ℝ :=
  fun i c => Ufull i (Fin.natAdd r c)

/-- Head right singular-vector block obtained by splitting a square SVD table. -/
noncomputable def squareSVDHeadRight {r q : ℕ}
    (Vfull : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin (r + q) → Fin r → ℝ :=
  fun j a => Vfull j (Fin.castAdd q a)

/-- Tail right singular-vector block obtained by splitting a square SVD table. -/
noncomputable def squareSVDTailRight {r q : ℕ}
    (Vfull : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin (r + q) → Fin q → ℝ :=
  fun j c => Vfull j (Fin.natAdd r c)

/-- Head diagonal singular-value block obtained by splitting a square SVD
table. -/
noncomputable def squareSVDHeadDiagonal {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) : Fin r → Fin r → ℝ :=
  fun a b => if a = b then sigma (Fin.castAdd q a) else 0

/-- Tail diagonal singular-value block obtained by splitting a square SVD
table. -/
noncomputable def squareSVDTailDiagonal {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) : Fin q → Fin q → ℝ :=
  fun c d => if c = d then sigma (Fin.natAdd r c) else 0

/-- Squared Frobenius norm of the displayed tail diagonal equals the sum of
the displayed tail singular-value squares.

This is exact-object diagonal algebra for the multi-tail equation-(9)
Eckart--Young route; computed singular values require a separate
non-probability routine certificate. -/
theorem frobNormSq_diagonal_eq_sum {q : ℕ}
    (sigma : Fin q → ℝ) :
    frobNormSq (fun c d : Fin q => if c = d then sigma c else 0) =
      ∑ c : Fin q, sigma c ^ 2 := by
  unfold frobNormSq
  apply Finset.sum_congr rfl
  intro c _
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- Norm form of `frobNormSq_diagonal_eq_sum`. -/
theorem frobNorm_diagonal_eq_sqrt_sum {q : ℕ}
    (sigma : Fin q → ℝ) :
    frobNorm (fun c d : Fin q => if c = d then sigma c else 0) =
      Real.sqrt (∑ c : Fin q, sigma c ^ 2) := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNormSq_diagonal_eq_sum]

/-- Squared Frobenius norm of the constructed ordered complement-tail
singular-value block.

This is the constructed ordered-tail specialization needed before discharging
LR.1dt's visible Eckart--Young tail-optimality hypothesis.  It is exact-object
diagonal algebra only; computed singular values or singular-vector tables
remain non-probability implementation obligations. -/
theorem frobNormSq_rectRightGramOrderedTailSingularDiagonal_eq_sum
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    frobNormSq (rectRightGramOrderedTailSingularDiagonal A hk) =
      ∑ c : rectRightGramOrderedTailIndex hk,
        rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) ^ 2 := by
  simpa [rectRightGramOrderedTailSingularDiagonal,
    rectRightGramBasisSVDTailSingularDiagonal] using
    (frobNormSq_diagonal_eq_sum
      (fun c : rectRightGramOrderedTailIndex hk =>
        rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)))

/-- Norm form of
`frobNormSq_rectRightGramOrderedTailSingularDiagonal_eq_sum`. -/
theorem frobNorm_rectRightGramOrderedTailSingularDiagonal_eq_sqrt_sum
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) =
      Real.sqrt
        (∑ c : rectRightGramOrderedTailIndex hk,
          rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) ^ 2) := by
  rw [frobNorm_eq_sqrt_frobNormSq,
    frobNormSq_rectRightGramOrderedTailSingularDiagonal_eq_sum]

/-- Head-first `Fin (k+q)` left block for the constructed ordered source split,
where `q` is the complement-tail cardinality.  This is exact reindexing of the
analysis object only. -/
noncomputable def rectRightGramOrderedHeadTailLeftFinBlock {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ) :
    Fin m →
      Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
  fun i t =>
    match finSumFinEquiv.symm t with
    | Sum.inl a => rectRightGramOrderedHeadLeft A hk i a
    | Sum.inr c => Utail i c

/-- Head-first `Fin (k+q)` singular-value table for the constructed ordered
source split. -/
noncomputable def rectRightGramOrderedHeadTailSigmaFin {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
  fun t =>
    match finSumFinEquiv.symm t with
    | Sum.inl a =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a)
    | Sum.inr c =>
        rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)

/-- Head-first `Fin (k+q)` right block for the constructed ordered source split,
with rows pulled back along the exact ordered head-tail column equivalence. -/
noncomputable def rectRightGramOrderedHeadTailRightFinBlock {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card) →
      Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
  fun j t =>
    match finSumFinEquiv.symm t with
    | Sum.inl a =>
        rectRightGramOrderedHeadRight A hk
          (rectRightGramOrderedHeadTailColumnEquiv hk j) a
    | Sum.inr c =>
        rectRightGramOrderedTailRight A hk
          (rectRightGramOrderedHeadTailColumnEquiv hk j) c

/-- The same head-first right block before pulling rows back from the original
`Fin n` column domain to `Fin (k+q)`. -/
noncomputable def rectRightGramOrderedHeadTailRightOriginalFinBlock {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Fin n →
      Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
  fun j t =>
    match finSumFinEquiv.symm t with
    | Sum.inl a => rectRightGramOrderedHeadRight A hk j a
    | Sum.inr c => rectRightGramOrderedTailRight A hk j c

theorem rectRightGramOrderedHeadTailRightFinBlock_eq_original
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (j t : Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card)) :
    rectRightGramOrderedHeadTailRightFinBlock A hk j t =
      rectRightGramOrderedHeadTailRightOriginalFinBlock A hk
        (rectRightGramOrderedHeadTailColumnEquiv hk j) t := by
  cases h : finSumFinEquiv.symm t with
  | inl a =>
      simp [rectRightGramOrderedHeadTailRightFinBlock,
        rectRightGramOrderedHeadTailRightOriginalFinBlock, h]
  | inr c =>
      simp [rectRightGramOrderedHeadTailRightFinBlock,
        rectRightGramOrderedHeadTailRightOriginalFinBlock, h]

@[simp] theorem rectRightGramOrderedHeadTailLeftFinBlock_head
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ)
    (i : Fin m) (a : Fin k) :
    rectRightGramOrderedHeadTailLeftFinBlock A hk Utail i
        (Fin.castAdd
          ((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card a) =
      rectRightGramOrderedHeadLeft A hk i a := by
  simp [rectRightGramOrderedHeadTailLeftFinBlock]

@[simp] theorem rectRightGramOrderedHeadTailLeftFinBlock_tail
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ)
    (i : Fin m) (c : rectRightGramOrderedTailIndex hk) :
    rectRightGramOrderedHeadTailLeftFinBlock A hk Utail i
        (Fin.natAdd k c) =
      Utail i c := by
  simp [rectRightGramOrderedHeadTailLeftFinBlock]

@[simp] theorem rectRightGramOrderedHeadTailSigmaFin_head
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (a : Fin k) :
    rectRightGramOrderedHeadTailSigmaFin A hk
        (Fin.castAdd
          ((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card a) =
      rectRightGramBasisSingularValue A
        (rectRightGramOrderedTopEmbedding hk a) := by
  simp [rectRightGramOrderedHeadTailSigmaFin]

@[simp] theorem rectRightGramOrderedHeadTailSigmaFin_tail
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (c : rectRightGramOrderedTailIndex hk) :
    rectRightGramOrderedHeadTailSigmaFin A hk (Fin.natAdd k c) =
      rectRightGramBasisSingularValue A
        (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) := by
  simp [rectRightGramOrderedHeadTailSigmaFin]

@[simp] theorem rectRightGramOrderedHeadTailRightFinBlock_head
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (j : Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card)) (a : Fin k) :
    rectRightGramOrderedHeadTailRightFinBlock A hk j
        (Fin.castAdd
          ((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card a) =
      rectRightGramOrderedHeadRight A hk
        (rectRightGramOrderedHeadTailColumnEquiv hk j) a := by
  simp [rectRightGramOrderedHeadTailRightFinBlock]

@[simp] theorem rectRightGramOrderedHeadTailRightFinBlock_tail
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (j : Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card))
    (c : rectRightGramOrderedTailIndex hk) :
    rectRightGramOrderedHeadTailRightFinBlock A hk j (Fin.natAdd k c) =
      rectRightGramOrderedTailRight A hk
        (rectRightGramOrderedHeadTailColumnEquiv hk j) c := by
  simp [rectRightGramOrderedHeadTailRightFinBlock]

@[simp] theorem rectRightGramOrderedHeadTailRightOriginalFinBlock_head
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (j : Fin n) (a : Fin k) :
    rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j
        (Fin.castAdd
          ((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card a) =
      rectRightGramOrderedHeadRight A hk j a := by
  simp [rectRightGramOrderedHeadTailRightOriginalFinBlock]

@[simp] theorem rectRightGramOrderedHeadTailRightOriginalFinBlock_tail
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (j : Fin n) (c : rectRightGramOrderedTailIndex hk) :
    rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j (Fin.natAdd k c) =
      rectRightGramOrderedTailRight A hk j c := by
  simp [rectRightGramOrderedHeadTailRightOriginalFinBlock]

/-- The head-first `Fin (k+q)` left block inherits column orthonormality from
the sum-indexed constructed block. -/
theorem rectRightGramOrderedHeadTailLeftFinBlock_col_orthonormal
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ)
    (hcols :
      ∀ bc bd : Fin k ⊕ rectRightGramOrderedTailIndex hk,
        (∑ i : Fin m,
          leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bc *
            leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bd) =
          if bc = bd then 1 else 0)
    (a b : Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card)) :
    (∑ i : Fin m,
      rectRightGramOrderedHeadTailLeftFinBlock A hk Utail i a *
        rectRightGramOrderedHeadTailLeftFinBlock A hk Utail i b) =
      idMatrix
        (k + ((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) a b := by
  have h := hcols (finSumFinEquiv.symm a) (finSumFinEquiv.symm b)
  have hif :
      (if finSumFinEquiv.symm a = finSumFinEquiv.symm b then (1 : ℝ) else 0) =
        (if a = b then (1 : ℝ) else 0) := by
    by_cases hab : a = b
    · simp [hab]
    · have hsum : finSumFinEquiv.symm a ≠ finSumFinEquiv.symm b := by
        intro hsymm
        exact hab (finSumFinEquiv.symm.injective hsymm)
      simp [hab, hsum]
  trans
      (∑ i : Fin m,
        leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i
            (finSumFinEquiv.symm a) *
          leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i
            (finSumFinEquiv.symm b))
  · apply Finset.sum_congr rfl
    intro i _
    cases ha : finSumFinEquiv.symm a <;>
      cases hb : finSumFinEquiv.symm b <;>
      simp [rectRightGramOrderedHeadTailLeftFinBlock, leftBasisBlock, ha, hb]
  · simpa [idMatrix] using h.trans hif

/-- The head-first original right block inherits column orthonormality from the
tail-first right-basis block certificate. -/
theorem rectRightGramOrderedHeadTailRightOriginalFinBlock_col_orthonormal
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (hcols :
      ∀ bc bd : rectRightGramOrderedTailIndex hk ⊕ Fin k,
        (∑ j : Fin n,
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) j bc *
            rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) j bd) =
          if bc = bd then 1 else 0)
    (a b : Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card)) :
    (∑ j : Fin n,
      rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j a *
        rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j b) =
      idMatrix
        (k + ((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) a b := by
  classical
  let swap :
      Fin k ⊕ rectRightGramOrderedTailIndex hk →
        rectRightGramOrderedTailIndex hk ⊕ Fin k :=
    fun bc =>
      match bc with
      | Sum.inl a => Sum.inr a
      | Sum.inr c => Sum.inl c
  have h := hcols (swap (finSumFinEquiv.symm a))
    (swap (finSumFinEquiv.symm b))
  have hif :
      (if swap (finSumFinEquiv.symm a) =
          swap (finSumFinEquiv.symm b) then (1 : ℝ) else 0) =
        (if a = b then (1 : ℝ) else 0) := by
    by_cases hab : a = b
    · simp [hab]
    · have hsymm : finSumFinEquiv.symm a ≠ finSumFinEquiv.symm b := by
        intro hsymm
        exact hab (finSumFinEquiv.symm.injective hsymm)
      have hswap :
          swap (finSumFinEquiv.symm a) ≠
            swap (finSumFinEquiv.symm b) := by
        intro hs
        apply hsymm
        cases ha : finSumFinEquiv.symm a <;>
          cases hb : finSumFinEquiv.symm b <;>
          simp [swap, ha, hb] at hs ⊢ <;>
          assumption
      simp [hab, hswap]
  trans
      (∑ j : Fin n,
        rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) j
            (swap (finSumFinEquiv.symm a)) *
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) j
            (swap (finSumFinEquiv.symm b)))
  · apply Finset.sum_congr rfl
    intro j _
    cases ha : finSumFinEquiv.symm a <;>
      cases hb : finSumFinEquiv.symm b <;>
      simp [rectRightGramOrderedHeadTailRightOriginalFinBlock,
        rightBasisBlock, swap, ha, hb]
  · simpa [idMatrix] using h.trans hif

/-- The head-first original right block inherits row orthonormality from the
tail-first right-basis row-completeness certificate. -/
theorem rectRightGramOrderedHeadTailRightOriginalFinBlock_row_orthonormal
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (hrows :
      ∀ j l,
        (∑ bc : rectRightGramOrderedTailIndex hk ⊕ Fin k,
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) j bc *
            rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) l bc) =
          idMatrix n j l)
    (j l : Fin n) :
    (∑ t : Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
      rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j t *
        rectRightGramOrderedHeadTailRightOriginalFinBlock A hk l t) =
      idMatrix n j l := by
  classical
  let term :
      Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
    fun t =>
      rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j t *
        rectRightGramOrderedHeadTailRightOriginalFinBlock A hk l t
  have hsum :
      (∑ t : Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card), term t) =
        ∑ bc : Fin k ⊕ rectRightGramOrderedTailIndex hk,
          term (finSumFinEquiv bc) := by
    exact
      (Fintype.sum_equiv finSumFinEquiv
        (fun bc : Fin k ⊕ rectRightGramOrderedTailIndex hk =>
          term (finSumFinEquiv bc))
        term
        (fun _ => rfl)).symm
  change (∑ t : Fin (k + ((rectRightGramSelectedIndexSet
    (rectRightGramOrderedTopEmbedding hk))ᶜ).card), term t) =
      idMatrix n j l
  rw [hsum]
  rw [Fintype.sum_sum_type]
  have h := hrows j l
  rw [Fintype.sum_sum_type] at h
  simpa [term, rectRightGramOrderedHeadTailRightOriginalFinBlock,
    rightBasisBlock, add_comm] using h

/-- Pulling the head-first right block back along the ordered head-tail column
equivalence gives an orthogonal square table on `Fin (k+q)`. -/
theorem rectRightGramOrderedHeadTailRightFinBlock_isOrthogonal
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (hcols :
      ∀ bc bd : rectRightGramOrderedTailIndex hk ⊕ Fin k,
        (∑ j : Fin n,
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) j bc *
            rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) j bd) =
          if bc = bd then 1 else 0)
    (hrows :
      ∀ j l,
        (∑ bc : rectRightGramOrderedTailIndex hk ⊕ Fin k,
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) j bc *
            rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) l bc) =
          idMatrix n j l) :
    IsOrthogonal
      (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      (rectRightGramOrderedHeadTailRightFinBlock A hk) := by
  constructor
  · intro a b
    unfold matTranspose
    let π := rectRightGramOrderedHeadTailColumnEquiv hk
    let f :
        Fin (k + ((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
      fun j =>
        rectRightGramOrderedHeadTailRightFinBlock A hk j a *
          rectRightGramOrderedHeadTailRightFinBlock A hk j b
    let g : Fin n → ℝ :=
      fun j =>
        rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j a *
          rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j b
    have hsum :
        (∑ j : Fin (k + ((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card), f j) =
          ∑ j : Fin n, g j := by
      exact
        Fintype.sum_equiv π
          (fun j : Fin (k + ((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card) => f j)
          g
          (fun j => by
            simp [f, g, π,
              rectRightGramOrderedHeadTailRightFinBlock_eq_original])
    rw [hsum]
    exact
      rectRightGramOrderedHeadTailRightOriginalFinBlock_col_orthonormal
        A hk hcols a b
  · intro a b
    unfold matTranspose
    let π := rectRightGramOrderedHeadTailColumnEquiv hk
    calc
      (∑ t : Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        rectRightGramOrderedHeadTailRightFinBlock A hk a t *
          rectRightGramOrderedHeadTailRightFinBlock A hk b t)
          =
        ∑ t : Fin (k + ((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
          rectRightGramOrderedHeadTailRightOriginalFinBlock A hk (π a) t *
            rectRightGramOrderedHeadTailRightOriginalFinBlock A hk (π b) t := by
              apply Finset.sum_congr rfl
              intro t _
              simp [π, rectRightGramOrderedHeadTailRightFinBlock_eq_original]
      _ = idMatrix n (π a) (π b) :=
          rectRightGramOrderedHeadTailRightOriginalFinBlock_row_orthonormal
            A hk hrows (π a) (π b)
      _ =
        idMatrix
          (k + ((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card) a b := by
          by_cases h : a = b
          · simp [idMatrix, h]
          · have hp : π a ≠ π b := by
              intro hp
              exact h (π.injective hp)
            simp [idMatrix, h, hp]

/-- The head-first `Fin (k+q)` source factor is exactly the original matrix
pulled back along the constructed ordered head-tail column equivalence. -/
theorem sourceSVDFactorMatrix_rectRightGramOrderedHeadTailFinBlock_eq_reindexCols
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ)
    (hUtail :
      ∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c) :
    sourceSVDFactorMatrix
        (rectRightGramOrderedHeadTailLeftFinBlock A hk Utail)
        (fun a b =>
          if a = b then rectRightGramOrderedHeadTailSigmaFin A hk a else 0)
        (rectRightGramOrderedHeadTailRightFinBlock A hk) =
      rectReindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) A := by
  classical
  funext i j
  let π := rectRightGramOrderedHeadTailColumnEquiv hk
  let term :
      Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
    fun t =>
      rectRightGramOrderedHeadTailLeftFinBlock A hk Utail i t *
        (rectRightGramOrderedHeadTailSigmaFin A hk t *
          rectRightGramOrderedHeadTailRightFinBlock A hk j t)
  have hsum :
      (∑ t : Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card), term t) =
        ∑ bc : Fin k ⊕ rectRightGramOrderedTailIndex hk,
          term (finSumFinEquiv bc) := by
    exact
      (Fintype.sum_equiv finSumFinEquiv
        (fun bc : Fin k ⊕ rectRightGramOrderedTailIndex hk =>
          term (finSumFinEquiv bc))
        term
        (fun _ => rfl)).symm
  have hhead :=
    sourceSVDFactorMatrix_diagonal_eq_sum
      (rectRightGramOrderedHeadLeft A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk) i (π j)
  have htail :=
    sourceSVDFactorMatrix_diagonal_eq_sum
      Utail
      (fun c : rectRightGramOrderedTailIndex hk =>
        rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c))
      (rectRightGramOrderedTailRight A hk) i (π j)
  calc
    sourceSVDFactorMatrix
        (rectRightGramOrderedHeadTailLeftFinBlock A hk Utail)
        (fun a b =>
          if a = b then rectRightGramOrderedHeadTailSigmaFin A hk a else 0)
        (rectRightGramOrderedHeadTailRightFinBlock A hk) i j
        = ∑ t : Fin (k + ((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card), term t := by
            simpa [term] using
              sourceSVDFactorMatrix_diagonal_eq_sum
                (rectRightGramOrderedHeadTailLeftFinBlock A hk Utail)
                (rectRightGramOrderedHeadTailSigmaFin A hk)
                (rectRightGramOrderedHeadTailRightFinBlock A hk) i j
    _ = ∑ bc : Fin k ⊕ rectRightGramOrderedTailIndex hk,
          term (finSumFinEquiv bc) := hsum
    _ =
        sourceSVDFactorMatrix
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedHeadSingularDiagonal A hk)
            (rectRightGramOrderedHeadRight A hk) i (π j) +
          sourceSVDFactorMatrix
            Utail
            (rectRightGramOrderedTailSingularDiagonal A hk)
            (rectRightGramOrderedTailRight A hk) i (π j) := by
            rw [Fintype.sum_sum_type]
            simp [term, rectRightGramOrderedTailSingularDiagonal,
              rectRightGramOrderedHeadTailRightFinBlock_eq_original,
              rectRightGramOrderedHeadTailRightOriginalFinBlock]
            rw [← hhead, ← htail]
            rfl
    _ = A i (π j) :=
          rectRightGramOrdered_source_head_add_tail_replacement_left
            A hk Utail hUtail i (π j)
    _ = rectReindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) A i j := rfl

/-- Constructed ordered replacement-tail source split discharges the visible
Frobenius tail-optimality inequality used by LR.1dt.

This is exact-object Eckart--Young/tail lower-bound infrastructure for the
constructed ordered right-Gram split.  It still does not derive randomness or
certify computed non-probability SVD/singular-vector/projector/Gram/inverse/
sketch/product routines. -/
theorem frobNorm_rectRightGramOrderedTailSingularDiagonal_le_lowRankResidualFrob
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (e : Fin k ⊕ rectRightGramOrderedTailIndex hk ↪ Fin m)
    (B : Fin m → Fin n → ℝ) (hB : RectRankAtMost m n k B) :
    frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) ≤
      lowRankResidualFrob A B := by
  classical
  obtain ⟨Utail, hagree, hcols, cert⟩ :=
    exists_rectRightGramOrdered_replacement_tail_left_block_certificate_of_last_pos
      A hk hk0 hlast e
  let π := rectRightGramOrderedHeadTailColumnEquiv hk
  let Aπ : Fin m →
      Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
    rectReindexCols π A
  let Bπ : Fin m →
      Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
    rectReindexCols π B
  let Ufin :=
    rectRightGramOrderedHeadTailLeftFinBlock A hk Utail
  let sigmafin :=
    rectRightGramOrderedHeadTailSigmaFin A hk
  let Vfin :=
    rectRightGramOrderedHeadTailRightFinBlock A hk
  have hBπ : RectRankAtMost m
      (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) k Bπ := by
    simpa [Bπ, π] using
      RectRankAtMost.reindexCols_rectRightGramOrderedHeadTailColumnEquiv
        hk hB
  have hU :
      ∀ a b : Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        (∑ i : Fin m, Ufin i a * Ufin i b) =
          idMatrix
            (k + ((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).card) a b := by
    intro a b
    simpa [Ufin] using
      rectRightGramOrderedHeadTailLeftFinBlock_col_orthonormal
        A hk Utail hcols a b
  have hV :
      IsOrthogonal
        (k + ((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) Vfin := by
    simpa [Vfin] using
      rectRightGramOrderedHeadTailRightFinBlock_isOrthogonal
        A hk cert.right_columns cert.right_rows
  obtain ⟨eta, hhead_gap, htail_gap⟩ :=
    rectRightGramOrdered_head_tail_square_gap A hk hk0
  have hhead :
      ∀ a : Fin k,
        eta ≤ sigmafin
          (Fin.castAdd
            ((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).card a) ^ 2 := by
    intro a
    simpa [sigmafin] using hhead_gap a
  have htail :
      ∀ c : rectRightGramOrderedTailIndex hk,
        sigmafin (Fin.natAdd k c) ^ 2 ≤ eta := by
    intro c
    simpa [sigmafin] using htail_gap c
  have hsrc :
      sourceSVDFactorMatrix Ufin
          (fun a b => if a = b then sigmafin a else 0) Vfin =
        Aπ := by
    simpa [Ufin, sigmafin, Vfin, Aπ, π] using
      sourceSVDFactorMatrix_rectRightGramOrderedHeadTailFinBlock_eq_reindexCols
        A hk Utail hagree
  have hlower :
      Real.sqrt
          (∑ c : rectRightGramOrderedTailIndex hk,
            sigmafin (Fin.natAdd k c) ^ 2) ≤
        lowRankResidualFrob
          (sourceSVDFactorMatrix Ufin
            (fun a b => if a = b then sigmafin a else 0) Vfin) Bπ := by
    simpa [Ufin, sigmafin, Vfin, Bπ] using
      sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_gap
        Ufin sigmafin Vfin hU hV hhead htail Bπ hBπ
  have htail_norm :
      frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) =
        Real.sqrt
          (∑ c : rectRightGramOrderedTailIndex hk,
            sigmafin (Fin.natAdd k c) ^ 2) := by
    simpa [sigmafin] using
      frobNorm_rectRightGramOrderedTailSingularDiagonal_eq_sqrt_sum A hk
  calc
    frobNorm (rectRightGramOrderedTailSingularDiagonal A hk)
        =
          Real.sqrt
            (∑ c : rectRightGramOrderedTailIndex hk,
              sigmafin (Fin.natAdd k c) ^ 2) := htail_norm
    _ ≤
        lowRankResidualFrob
          (sourceSVDFactorMatrix Ufin
            (fun a b => if a = b then sigmafin a else 0) Vfin) Bπ := hlower
    _ =
        lowRankResidualFrob Aπ Bπ := by
          rw [hsrc]
    _ = lowRankResidualFrob A B := by
          simpa [Aπ, Bπ, π] using
            lowRankResidualFrob_rectRightGramOrderedHeadTailColumnEquiv hk A B

/-- Ordered right-Gram replacement-tail relative surface with the Frobenius
tail-optimality hypothesis discharged by the constructed D4 lower-bound route.

The scalar relative-comparison and cross-term radius remain visible, and
randomness/computed non-probability routine certificates remain separate. -/
theorem exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos_tailOptimal
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (e : Fin k ⊕ rectRightGramOrderedTailIndex hk ↪ Fin m)
    (Z : Fin n → Fin k → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (rectRightGramOrderedHeadRight A hk) Z :
            Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (rectRightGramOrderedTailSingularDiagonal A hk)
            (rightSketchCrossGramRectInvFactor
              (rectRightGramOrderedTailRight A hk) Z
              (rectRightGramOrderedHeadRight A hk))) ≤
        eps * frobNorm (rectRightGramOrderedTailSingularDiagonal A hk))
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (rectRightGramOrderedTailSingularDiagonal A hk)) ≤
        rho * frobNorm (rectRightGramOrderedTailSingularDiagonal A hk)) :
    ∃ Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ,
      (∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c) ∧
      (∀ bc bd : Fin k ⊕ rectRightGramOrderedTailIndex hk,
        (∑ i : Fin m,
          leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bc *
            leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bd) =
          if bc = bd then 1 else 0) ∧
      IsBestRankApproxFrob m n k A
        (sourceSVDFactorMatrix
          (rectRightGramOrderedHeadLeft A hk)
          (rectRightGramOrderedHeadSingularDiagonal A hk)
          (rectRightGramOrderedHeadRight A hk)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedHeadSingularDiagonal A hk)
            (rectRightGramOrderedHeadRight A hk)) =
        frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n k
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix
                (rectRightGramOrderedHeadLeft A hk)
                (rectRightGramOrderedHeadSingularDiagonal A hk)
                (rectRightGramOrderedHeadRight A hk)) := by
  exact
    exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos
      A hk hk0 hlast e Z heps hVZ hcrossTerm
      (fun B hB =>
        frobNorm_rectRightGramOrderedTailSingularDiagonal_le_lowRankResidualFrob
          A hk hk0 hlast e B hB)
      hrelative

/-- Scalar relative-comparison expansion.

If the displayed scalar rate `2 * sqrt (1 + eps^2)` is at most `rho`, then
multiplying by any nonnegative tail norm gives the product-form comparison
used by the equation-(9) relative surfaces. -/
theorem two_sqrt_one_add_sq_mul_tail_le_of_scalar
    {eps rho tail : ℝ}
    (hscalar : 2 * Real.sqrt (1 + eps ^ 2) ≤ rho)
    (htail : 0 ≤ tail) :
    2 * (Real.sqrt (1 + eps ^ 2) * tail) ≤ rho * tail := by
  calc
    2 * (Real.sqrt (1 + eps ^ 2) * tail)
        = (2 * Real.sqrt (1 + eps ^ 2)) * tail := by
          ring
    _ ≤ rho * tail :=
        mul_le_mul_of_nonneg_right hscalar htail

/-- Ordered right-Gram replacement-tail relative surface with the scalar
comparison stated as the cleaner coefficient inequality
`2 * sqrt (1 + eps^2) <= rho`.

This removes the raw product-form `hrelative` hypothesis from the LR.1eb
surface by using nonnegativity of the constructed tail Frobenius norm.  The
cross-term radius, randomness, and computed non-probability routine
certificates remain separate obligations. -/
theorem exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos_tailOptimal_of_scalarRelative
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (e : Fin k ⊕ rectRightGramOrderedTailIndex hk ↪ Fin m)
    (Z : Fin n → Fin k → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (rectRightGramOrderedHeadRight A hk) Z :
            Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (rectRightGramOrderedTailSingularDiagonal A hk)
            (rightSketchCrossGramRectInvFactor
              (rectRightGramOrderedTailRight A hk) Z
              (rectRightGramOrderedHeadRight A hk))) ≤
        eps * frobNorm (rectRightGramOrderedTailSingularDiagonal A hk))
    (hscalar : 2 * Real.sqrt (1 + eps ^ 2) ≤ rho) :
    ∃ Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ,
      (∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c) ∧
      (∀ bc bd : Fin k ⊕ rectRightGramOrderedTailIndex hk,
        (∑ i : Fin m,
          leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bc *
            leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bd) =
          if bc = bd then 1 else 0) ∧
      IsBestRankApproxFrob m n k A
        (sourceSVDFactorMatrix
          (rectRightGramOrderedHeadLeft A hk)
          (rectRightGramOrderedHeadSingularDiagonal A hk)
          (rectRightGramOrderedHeadRight A hk)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedHeadSingularDiagonal A hk)
            (rectRightGramOrderedHeadRight A hk)) =
        frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n k
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix
                (rectRightGramOrderedHeadLeft A hk)
                (rectRightGramOrderedHeadSingularDiagonal A hk)
                (rectRightGramOrderedHeadRight A hk)) := by
  exact
    exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos_tailOptimal
      A hk hk0 hlast e Z heps hVZ hcrossTerm
      (two_sqrt_one_add_sq_mul_tail_le_of_scalar hscalar
        (frobNorm_nonneg (rectRightGramOrderedTailSingularDiagonal A hk)))

theorem frobNormSq_squareSVDTailDiagonal_eq_sum {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) :
    frobNormSq (squareSVDTailDiagonal (r := r) (q := q) sigma) =
      ∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2 := by
  simpa [squareSVDTailDiagonal] using
    (frobNormSq_diagonal_eq_sum
      (fun c : Fin q => sigma (Fin.natAdd r c)))

/-- Norm form of `frobNormSq_squareSVDTailDiagonal_eq_sum`. -/
theorem frobNorm_squareSVDTailDiagonal_eq_sqrt_sum {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) :
    frobNorm (squareSVDTailDiagonal (r := r) (q := q) sigma) =
      Real.sqrt (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) := by
  rw [frobNorm_eq_sqrt_frobNormSq,
    frobNormSq_squareSVDTailDiagonal_eq_sum]

/-- Head singular values obtained by splitting a square SVD table. -/
noncomputable def squareSVDHeadValues {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) : Fin r → ℝ :=
  fun a => sigma (Fin.castAdd q a)

/-- Strict positivity of the displayed head singular entries is inherited by
the split head-value table. -/
theorem squareSVDHeadValues_pos {r q : ℕ}
    {sigma : Fin (r + q) → ℝ}
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a)) :
    ∀ a : Fin r, 0 < squareSVDHeadValues sigma a := by
  intro a
  simpa [squareSVDHeadValues] using hhead_pos a

/-- Source-style strict positivity of the displayed head singular entries
supplies the nonzero-head field used by the determinant/source-SVD
constructors. -/
theorem squareSVDHeadValues_nonzero_of_pos {r q : ℕ}
    {sigma : Fin (r + q) → ℝ}
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a)) :
    ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0 := by
  intro a
  exact ne_of_gt (hhead_pos a)

/-- The source-head factor built from the split square SVD diagonal expands to
the head part of the full square SVD sum. -/
theorem sourceSVDFactorMatrix_squareSVDHeadDiagonal
    {r q : ℕ}
    (Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (i j : Fin (r + q)) :
    sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull) i j =
      ∑ a : Fin r,
        Ufull i (Fin.castAdd q a) *
          (sigma (Fin.castAdd q a) * Vfull j (Fin.castAdd q a)) := by
  unfold sourceSVDFactorMatrix squareSVDHeadLeft squareSVDHeadRight
    squareSVDHeadDiagonal
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- The source-tail factor built from the split square SVD diagonal expands to
the tail part of the full square SVD sum. -/
theorem sourceSVDFactorMatrix_squareSVDTailDiagonal
    {r q : ℕ}
    (Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (i j : Fin (r + q)) :
    sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
        (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull) i j =
      ∑ c : Fin q,
        Ufull i (Fin.natAdd r c) *
          (sigma (Fin.natAdd r c) * Vfull j (Fin.natAdd r c)) := by
  unfold sourceSVDFactorMatrix squareSVDTailLeft squareSVDTailRight
    squareSVDTailDiagonal
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- A square exact SVD certificate, supplied as full orthogonal tables and a
pointwise representation, constructs the block source-SVD certificate consumed
by the equation-(9) surface.

This remains exact-object source algebra: it does not assert existence of the
SVD, singular-value ordering, Eckart--Young optimality, or any floating-point
routine for computing/storing the singular vectors or diagonal blocks. Those
are tracked separately as non-probability computed-quantity obligations. -/
theorem BlockDiagonalSourceSVDTailCertificate.of_squareSVD
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0) :
    BlockDiagonalSourceSVDTailCertificate (r + q) (r + q) r q A
      (squareSVDHeadLeft Ufull) (squareSVDHeadDiagonal sigma)
      (squareSVDHeadValues sigma) (squareSVDHeadRight Vfull)
      (squareSVDTailLeft Ufull) (squareSVDTailDiagonal sigma)
      (squareSVDTailRight Vfull) where
  split := by
    intro i j
    rw [hrepr i j]
    rw [Fin.sum_univ_add]
    rw [sourceSVDFactorMatrix_squareSVDHeadDiagonal,
      sourceSVDFactorMatrix_squareSVDTailDiagonal]
  left_columns := by
    intro bc bd
    cases bc with
    | inl a =>
        cases bd with
        | inl b =>
            simpa [leftBasisBlock, squareSVDHeadLeft, idMatrix] using
              hU.col_orthonormal (Fin.castAdd q a) (Fin.castAdd q b)
        | inr c =>
            have hne : Fin.castAdd q a ≠ Fin.natAdd r c := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [leftBasisBlock, squareSVDHeadLeft, squareSVDTailLeft,
              hne] using
              hU.col_orthonormal (Fin.castAdd q a) (Fin.natAdd r c)
    | inr c =>
        cases bd with
        | inl a =>
            have hne : Fin.natAdd r c ≠ Fin.castAdd q a := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [leftBasisBlock, squareSVDHeadLeft, squareSVDTailLeft,
              hne] using
              hU.col_orthonormal (Fin.natAdd r c) (Fin.castAdd q a)
        | inr d =>
            simpa [leftBasisBlock, squareSVDTailLeft, idMatrix] using
              hU.col_orthonormal (Fin.natAdd r c) (Fin.natAdd r d)
  head_diagonal := by
    intro a b
    rfl
  head_nonzero := by
    intro a
    exact hhead_nonzero a
  right_columns := by
    intro bc bd
    cases bc with
    | inl c =>
        cases bd with
        | inl d =>
            simpa [rightBasisBlock, squareSVDTailRight, idMatrix] using
              hV.col_orthonormal (Fin.natAdd r c) (Fin.natAdd r d)
        | inr a =>
            have hne : Fin.natAdd r c ≠ Fin.castAdd q a := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [rightBasisBlock, squareSVDHeadRight, squareSVDTailRight,
              hne] using
              hV.col_orthonormal (Fin.natAdd r c) (Fin.castAdd q a)
    | inr a =>
        cases bd with
        | inl c =>
            have hne : Fin.castAdd q a ≠ Fin.natAdd r c := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [rightBasisBlock, squareSVDHeadRight, squareSVDTailRight,
              hne] using
              hV.col_orthonormal (Fin.castAdd q a) (Fin.natAdd r c)
        | inr b =>
            simpa [rightBasisBlock, squareSVDHeadRight, idMatrix] using
              hV.col_orthonormal (Fin.castAdd q a) (Fin.castAdd q b)
  right_rows := by
    intro j k
    have hrow := hV.row_orthonormal j k
    rw [Fin.sum_univ_add] at hrow
    calc
      (∑ bc : Fin q ⊕ Fin r,
        rightBasisBlock (squareSVDTailRight Vfull)
            (squareSVDHeadRight Vfull) j bc *
          rightBasisBlock (squareSVDTailRight Vfull)
            (squareSVDHeadRight Vfull) k bc)
          =
        (∑ c : Fin q,
          Vfull j (Fin.natAdd r c) * Vfull k (Fin.natAdd r c)) +
          (∑ a : Fin r,
            Vfull j (Fin.castAdd q a) * Vfull k (Fin.castAdd q a)) := by
            simp [rightBasisBlock, squareSVDTailRight, squareSVDHeadRight,
              Fintype.sum_sum_type]
      _ =
        (∑ a : Fin r,
          Vfull j (Fin.castAdd q a) * Vfull k (Fin.castAdd q a)) +
          (∑ c : Fin q,
            Vfull j (Fin.natAdd r c) * Vfull k (Fin.natAdd r c)) := by
            ring
      _ = idMatrix (r + q) j k := by
            simpa [idMatrix] using hrow

/-- Square SVD split constructor with a source-style strict-positive head
singular-value hypothesis instead of a raw nonzero-head hypothesis.

This closes only the positivity-to-nonzero handoff; SVD existence,
singular-value ordering, Eckart--Young optimality, randomness, and computed
non-probability routines remain separate obligations. -/
theorem BlockDiagonalSourceSVDTailCertificate.of_squareSVD_head_pos
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a)) :
    BlockDiagonalSourceSVDTailCertificate (r + q) (r + q) r q A
      (squareSVDHeadLeft Ufull) (squareSVDHeadDiagonal sigma)
      (squareSVDHeadValues sigma) (squareSVDHeadRight Vfull)
      (squareSVDTailLeft Ufull) (squareSVDTailDiagonal sigma)
      (squareSVDTailRight Vfull) :=
  BlockDiagonalSourceSVDTailCertificate.of_squareSVD hU hV hrepr
    (squareSVDHeadValues_nonzero_of_pos hhead_pos)

/-- The tail factor obtained by splitting supplied square SVD tables has
Frobenius norm exactly equal to the displayed tail singular-value block.  This
is exact-object algebra; computed singular-vector and product routines remain
separate non-probability FP obligations. -/
theorem frobNormRect_squareSVDTail_eq_sigmaTail
    {r q : ℕ}
    (Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull) :
    frobNormRect
        (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
          (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) =
      frobNorm (squareSVDTailDiagonal sigma) :=
  frobNormRect_sourceSVDFactorMatrix_orthonormal
    (squareSVDTailLeft Ufull) (squareSVDTailDiagonal sigma)
    (squareSVDTailRight Vfull)
    (by
      intro c d
      simpa [squareSVDTailLeft, idMatrix] using
        hU.col_orthonormal (Fin.natAdd r c) (Fin.natAdd r d))
    (by
      intro c d
      simpa [squareSVDTailRight, idMatrix] using
        hV.col_orthonormal (Fin.natAdd r c) (Fin.natAdd r d))

/-- For supplied square SVD-style tables, the source-head residual is exactly
the Frobenius norm of the displayed tail singular-value block. -/
theorem lowRankResidualFrob_squareSVDHead_eq_sigmaTail
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0) :
    lowRankResidualFrob A
        (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
      frobNorm (squareSVDTailDiagonal sigma) :=
  (BlockDiagonalSourceSVDTailCertificate.of_squareSVD
    hU hV hrepr hhead_nonzero).tail_lowRankResidual_eq_sigma

/-- Supplied square SVD-style data give a Frobenius best-rank certificate once
the tail-optimality inequality is stated with the displayed tail singular-value
block.  This is only a handoff from a visible Eckart--Young-style hypothesis,
not a proof of that hypothesis. -/
theorem isBestRankApproxFrob_of_squareSVD_sigmaTail_optimal
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (hopt : ∀ B, RectRankAtMost (r + q) (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B) :
    IsBestRankApproxFrob (r + q) (r + q) r A
      (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) := by
  have hopt' : ∀ B, RectRankAtMost (r + q) (r + q) r B →
      frobNormRect
          (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ≤
        lowRankResidualFrob A B := by
    intro B hB
    rw [frobNormRect_squareSVDTail_eq_sigmaTail Ufull Vfull sigma hU hV]
    exact hopt B hB
  exact
    (BlockDiagonalSourceSVDTailCertificate.of_squareSVD
      hU hV hrepr hhead_nonzero).isBestRankApproxFrob_of_tail_optimal
        hopt'

/-- Strict-positive-head version of
`isBestRankApproxFrob_of_squareSVD_sigmaTail_optimal`. -/
theorem isBestRankApproxFrob_of_squareSVD_head_pos_sigmaTail_optimal
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (hopt : ∀ B, RectRankAtMost (r + q) (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B) :
    IsBestRankApproxFrob (r + q) (r + q) r A
      (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  isBestRankApproxFrob_of_squareSVD_sigmaTail_optimal
    hU hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos) hopt

/-- Ordered supplied square-SVD data give the tail-optimality inequality for
the displayed tail singular-value block.

The proof uses LR.1dp's q-dimensional exact source-factor lower bound and the
tail-diagonal Frobenius identity.  It is exact-object Eckart--Young assembly
only: it does not construct the SVD, prove ordering from an SVD routine, or
certify computed singular-vector/projector/Gram/sketch/product arithmetic.
Sampling probabilities and laws remain exact mathematical inputs. -/
theorem squareSVD_sigmaTail_le_lowRankResidualFrob_of_antitone
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (B : Fin (r + q) → Fin (r + q) → ℝ)
    (hB : RectRankAtMost (r + q) (r + q) r B) :
    frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B := by
  have hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin (r + q), Ufull i a * Ufull i b) =
          idMatrix (r + q) a b := by
    intro a b
    simpa [idMatrix] using hU.col_orthonormal a b
  have hsource :=
    sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_antitone
      Ufull sigma Vfull hUcols hV hmono B hB
  have hsource_eq :
      sourceSVDFactorMatrix Ufull
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) Vfull =
        A := by
    funext i j
    calc
      sourceSVDFactorMatrix Ufull
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) Vfull i j
          =
            ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k) := by
              exact sourceSVDFactorMatrix_diagonal_eq_sum Ufull sigma Vfull i j
      _ = A i j := (hrepr i j).symm
  rw [frobNorm_squareSVDTailDiagonal_eq_sqrt_sum]
  simpa [hsource_eq] using hsource

/-- Supplied square SVD-style data with exact ordered singular-square entries
give a Frobenius best rank-`r` source-head certificate.

This removes the formerly visible tail-optimality hypothesis by deriving it
from LR.1dp.  The theorem is exact-law/exact-object only; computed SVD,
singular-vector, projector, Gram, sketch, and product routines remain
non-probability FP/certificate obligations. -/
theorem isBestRankApproxFrob_of_squareSVD_antitone
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    IsBestRankApproxFrob (r + q) (r + q) r A
      (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  isBestRankApproxFrob_of_squareSVD_sigmaTail_optimal
    hU hV hrepr hhead_nonzero
    (fun B hB =>
      squareSVD_sigmaTail_le_lowRankResidualFrob_of_antitone
        hU hV hrepr hmono B hB)

/-- Strict-positive-head version of
`isBestRankApproxFrob_of_squareSVD_antitone`. -/
theorem isBestRankApproxFrob_of_squareSVD_head_pos_antitone
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    IsBestRankApproxFrob (r + q) (r + q) r A
      (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  isBestRankApproxFrob_of_squareSVD_antitone
    hU hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos) hmono

/-- Square-SVD certificate version of the block source-SVD scalar
equation-(9) rank/residual surface.  The exact sampling/sketch matrix `Z` and
sampling law remain mathematical inputs; computing the SVD, sketch, Gram
inverse, projector, and products is a separate FP/certificate obligation. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_squareSVD
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma)) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 *
            (Real.sqrt (1 + eps ^ 2) *
              frobNorm (squareSVDTailDiagonal sigma)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_blockDiagonalSourceSVDTailCertificate
      (BlockDiagonalSourceSVDTailCertificate.of_squareSVD
        hU hV hrepr hhead_nonzero)
      Z heps hVZ hcrossTerm

/-- Square-SVD scalar equation-(9) rank/residual surface with a strict-positive
source-head singular-value hypothesis. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_squareSVD_head_pos
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma)) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 *
            (Real.sqrt (1 + eps ^ 2) *
              frobNorm (squareSVDTailDiagonal sigma)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_squareSVD
      hU hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
      Z heps hVZ hcrossTerm

/-- Tail-optimal square-SVD certificate version of the scalar-rate relative
equation-(9) surface.  The tail-optimality hypothesis is exactly the remaining
Eckart--Young/SVD-order obligation; computing the displayed SVD objects remains
a non-probability FP/certificate obligation. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost (r + q) (r + q) r B →
      frobNormRect
          (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ≤
        lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho *
          frobNormRect
            (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
              (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull))) :
    IsBestRankApproxFrob (r + q) (r + q) r A
        (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNormRect
          (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate
      (BlockDiagonalSourceSVDTailCertificate.of_squareSVD
        hU hV hrepr hhead_nonzero)
      Z heps hVZ hcrossTerm hopt hrelative

/-- Tail-optimal square-SVD scalar-rate relative surface with a strict-positive
source-head singular-value hypothesis.  Tail optimality remains the visible
Eckart--Young/SVD-order obligation. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_head_pos
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost (r + q) (r + q) r B →
      frobNormRect
          (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ≤
        lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho *
          frobNormRect
            (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
              (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull))) :
    IsBestRankApproxFrob (r + q) (r + q) r A
        (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNormRect
          (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD
      hU hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
      Z heps hVZ hcrossTerm hopt hrelative

/-- Square-SVD scalar-rate relative surface with the source-head residual,
tail-optimality hypothesis, and scalar comparison written directly in terms of
the displayed tail singular-value block.  This uses the exact tail norm
identity for supplied SVD-style tables; it is not a proof of SVD existence or
Eckart--Young tail optimality. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost (r + q) (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob (r + q) (r + q) r A
        (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate_sigmaTail
    (BlockDiagonalSourceSVDTailCertificate.of_squareSVD
      hU hV hrepr hhead_nonzero)
    Z heps hVZ hcrossTerm hopt hrelative

/-- Strict-positive-head version of
`columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail`. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_head_pos_sigmaTail
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost (r + q) (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob (r + q) (r + q) r A
        (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail
    hU hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
    Z heps hVZ hcrossTerm hopt hrelative

/-- Ordered square-SVD scalar-rate relative surface with the source-head
residual and scalar comparison written directly in terms of the displayed tail
singular-value block.

Compared with
`columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail`,
the raw tail-optimality hypothesis is discharged by LR.1dq from exact
singular-square antitonicity.  This is still exact-object theorem-surface
propagation; computed SVD/projector/Gram/inverse/sketch/product routines and
randomness-derived cross-term certificates remain separate obligations. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail_antitone
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob (r + q) (r + q) r A
        (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail
    hU hV hrepr hhead_nonzero Z heps hVZ hcrossTerm
    (fun B hB =>
      squareSVD_sigmaTail_le_lowRankResidualFrob_of_antitone
        hU hV hrepr hmono B hB)
    hrelative

/-- Strict-positive-head version of
`columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail_antitone`. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_head_pos_sigmaTail_antitone
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob (r + q) (r + q) r A
        (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail_antitone
    hU hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
    Z heps hVZ hcrossTerm hmono hrelative

/-- Head left singular-vector block obtained by splitting a thin rectangular
SVD table. -/
noncomputable def rectangularThinSVDHeadLeft {m r q : ℕ}
    (Ufull : Fin m → Fin (r + q) → ℝ) : Fin m → Fin r → ℝ :=
  fun i a => Ufull i (Fin.castAdd q a)

/-- Tail left singular-vector block obtained by splitting a thin rectangular
SVD table. -/
noncomputable def rectangularThinSVDTailLeft {m r q : ℕ}
    (Ufull : Fin m → Fin (r + q) → ℝ) : Fin m → Fin q → ℝ :=
  fun i c => Ufull i (Fin.natAdd r c)

/-- The source-head factor built from a split thin rectangular SVD table
expands to the head part of the full SVD sum. -/
theorem sourceSVDFactorMatrix_rectangularThinSVDHeadDiagonal
    {m r q : ℕ}
    (Ufull : Fin m → Fin (r + q) → ℝ)
    (Vfull : Fin (r + q) → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (i : Fin m) (j : Fin (r + q)) :
    sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull) i j =
      ∑ a : Fin r,
        Ufull i (Fin.castAdd q a) *
          (sigma (Fin.castAdd q a) * Vfull j (Fin.castAdd q a)) := by
  unfold sourceSVDFactorMatrix rectangularThinSVDHeadLeft squareSVDHeadRight
    squareSVDHeadDiagonal
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- The source-tail factor built from a split thin rectangular SVD table
expands to the tail part of the full SVD sum. -/
theorem sourceSVDFactorMatrix_rectangularThinSVDTailDiagonal
    {m r q : ℕ}
    (Ufull : Fin m → Fin (r + q) → ℝ)
    (Vfull : Fin (r + q) → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (i : Fin m) (j : Fin (r + q)) :
    sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
        (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull) i j =
      ∑ c : Fin q,
        Ufull i (Fin.natAdd r c) *
          (sigma (Fin.natAdd r c) * Vfull j (Fin.natAdd r c)) := by
  unfold sourceSVDFactorMatrix rectangularThinSVDTailLeft squareSVDTailRight
    squareSVDTailDiagonal
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- A thin rectangular exact SVD certificate with a full right orthogonal
basis constructs the block source-SVD certificate consumed by the
equation-(9) surface.

The left table is rectangular and only needs exact column orthonormality; the
right table is square orthogonal and supplies the row-completeness field.  This
still does not prove existence of the rectangular SVD, singular-value ordering,
Eckart--Young optimality, or any floating-point routine for computing/storing
the singular vectors or diagonal blocks. -/
theorem BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0) :
    BlockDiagonalSourceSVDTailCertificate m (r + q) r q A
      (rectangularThinSVDHeadLeft Ufull) (squareSVDHeadDiagonal sigma)
      (squareSVDHeadValues sigma) (squareSVDHeadRight Vfull)
      (rectangularThinSVDTailLeft Ufull) (squareSVDTailDiagonal sigma)
      (squareSVDTailRight Vfull) where
  split := by
    intro i j
    rw [hrepr i j]
    rw [Fin.sum_univ_add]
    rw [sourceSVDFactorMatrix_rectangularThinSVDHeadDiagonal,
      sourceSVDFactorMatrix_rectangularThinSVDTailDiagonal]
  left_columns := by
    intro bc bd
    cases bc with
    | inl a =>
        cases bd with
        | inl b =>
            simpa [leftBasisBlock, rectangularThinSVDHeadLeft, idMatrix] using
              hUcols (Fin.castAdd q a) (Fin.castAdd q b)
        | inr c =>
            have hne : Fin.castAdd q a ≠ Fin.natAdd r c := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [leftBasisBlock, rectangularThinSVDHeadLeft,
              rectangularThinSVDTailLeft, hne] using
              hUcols (Fin.castAdd q a) (Fin.natAdd r c)
    | inr c =>
        cases bd with
        | inl a =>
            have hne : Fin.natAdd r c ≠ Fin.castAdd q a := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [leftBasisBlock, rectangularThinSVDHeadLeft,
              rectangularThinSVDTailLeft, hne] using
              hUcols (Fin.natAdd r c) (Fin.castAdd q a)
        | inr d =>
            simpa [leftBasisBlock, rectangularThinSVDTailLeft, idMatrix] using
              hUcols (Fin.natAdd r c) (Fin.natAdd r d)
  head_diagonal := by
    intro a b
    rfl
  head_nonzero := by
    intro a
    exact hhead_nonzero a
  right_columns := by
    intro bc bd
    cases bc with
    | inl c =>
        cases bd with
        | inl d =>
            simpa [rightBasisBlock, squareSVDTailRight, idMatrix] using
              hV.col_orthonormal (Fin.natAdd r c) (Fin.natAdd r d)
        | inr a =>
            have hne : Fin.natAdd r c ≠ Fin.castAdd q a := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [rightBasisBlock, squareSVDHeadRight, squareSVDTailRight,
              hne] using
              hV.col_orthonormal (Fin.natAdd r c) (Fin.castAdd q a)
    | inr a =>
        cases bd with
        | inl c =>
            have hne : Fin.castAdd q a ≠ Fin.natAdd r c := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [rightBasisBlock, squareSVDHeadRight, squareSVDTailRight,
              hne] using
              hV.col_orthonormal (Fin.castAdd q a) (Fin.natAdd r c)
        | inr b =>
            simpa [rightBasisBlock, squareSVDHeadRight, idMatrix] using
              hV.col_orthonormal (Fin.castAdd q a) (Fin.castAdd q b)
  right_rows := by
    intro j k
    have hrow := hV.row_orthonormal j k
    rw [Fin.sum_univ_add] at hrow
    calc
      (∑ bc : Fin q ⊕ Fin r,
        rightBasisBlock (squareSVDTailRight Vfull)
            (squareSVDHeadRight Vfull) j bc *
          rightBasisBlock (squareSVDTailRight Vfull)
            (squareSVDHeadRight Vfull) k bc)
          =
        (∑ c : Fin q,
          Vfull j (Fin.natAdd r c) * Vfull k (Fin.natAdd r c)) +
          (∑ a : Fin r,
            Vfull j (Fin.castAdd q a) * Vfull k (Fin.castAdd q a)) := by
            simp [rightBasisBlock, squareSVDTailRight, squareSVDHeadRight,
              Fintype.sum_sum_type]
      _ =
        (∑ a : Fin r,
          Vfull j (Fin.castAdd q a) * Vfull k (Fin.castAdd q a)) +
          (∑ c : Fin q,
            Vfull j (Fin.natAdd r c) * Vfull k (Fin.natAdd r c)) := by
            ring
      _ = idMatrix (r + q) j k := by
            simpa [idMatrix] using hrow

/-- Thin-rectangular SVD split constructor with a source-style strict-positive
head singular-value hypothesis instead of a raw nonzero-head hypothesis.

This remains exact-object source algebra; it closes only the
positivity-to-nonzero field for the supplied SVD-style data. -/
theorem BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD_head_pos
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a)) :
    BlockDiagonalSourceSVDTailCertificate m (r + q) r q A
      (rectangularThinSVDHeadLeft Ufull) (squareSVDHeadDiagonal sigma)
      (squareSVDHeadValues sigma) (squareSVDHeadRight Vfull)
      (rectangularThinSVDTailLeft Ufull) (squareSVDTailDiagonal sigma)
      (squareSVDTailRight Vfull) :=
  BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD
    hUcols hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)

/-- The tail factor obtained by splitting supplied thin-rectangular SVD tables
has Frobenius norm exactly equal to the displayed tail singular-value block. -/
theorem frobNormRect_rectangularThinSVDTail_eq_sigmaTail
    {m r q : ℕ}
    (Ufull : Fin m → Fin (r + q) → ℝ)
    (Vfull : Fin (r + q) → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull) :
    frobNormRect
        (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
          (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) =
      frobNorm (squareSVDTailDiagonal sigma) :=
  frobNormRect_sourceSVDFactorMatrix_orthonormal
    (rectangularThinSVDTailLeft Ufull) (squareSVDTailDiagonal sigma)
    (squareSVDTailRight Vfull)
    (by
      intro c d
      simpa [rectangularThinSVDTailLeft, idMatrix] using
        hUcols (Fin.natAdd r c) (Fin.natAdd r d))
    (by
      intro c d
      simpa [squareSVDTailRight, idMatrix] using
        hV.col_orthonormal (Fin.natAdd r c) (Fin.natAdd r d))

/-- For supplied thin-rectangular SVD-style tables, the source-head residual is
exactly the Frobenius norm of the displayed tail singular-value block. -/
theorem lowRankResidualFrob_rectangularThinSVDHead_eq_sigmaTail
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0) :
    lowRankResidualFrob A
        (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
      frobNorm (squareSVDTailDiagonal sigma) :=
  (BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD
    hUcols hV hrepr hhead_nonzero).tail_lowRankResidual_eq_sigma

/-- Supplied thin-rectangular SVD-style data give a Frobenius best-rank
certificate once the tail-optimality inequality is stated with the displayed
tail singular-value block. -/
theorem isBestRankApproxFrob_of_rectangularThinSVD_sigmaTail_optimal
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (hopt : ∀ B, RectRankAtMost m (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B) :
    IsBestRankApproxFrob m (r + q) r A
      (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) := by
  have hopt' : ∀ B, RectRankAtMost m (r + q) r B →
      frobNormRect
          (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ≤
        lowRankResidualFrob A B := by
    intro B hB
    rw [frobNormRect_rectangularThinSVDTail_eq_sigmaTail
      Ufull Vfull sigma hUcols hV]
    exact hopt B hB
  exact
    (BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD
      hUcols hV hrepr hhead_nonzero).isBestRankApproxFrob_of_tail_optimal
        hopt'

/-- Strict-positive-head version of
`isBestRankApproxFrob_of_rectangularThinSVD_sigmaTail_optimal`. -/
theorem isBestRankApproxFrob_of_rectangularThinSVD_head_pos_sigmaTail_optimal
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (hopt : ∀ B, RectRankAtMost m (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B) :
    IsBestRankApproxFrob m (r + q) r A
      (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  isBestRankApproxFrob_of_rectangularThinSVD_sigmaTail_optimal
    hUcols hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos) hopt

/-- Ordered supplied thin-rectangular SVD data give the tail-optimality
inequality for the displayed tail singular-value block.

This is the thin rectangular analogue of
`squareSVD_sigmaTail_le_lowRankResidualFrob_of_antitone`.  It is exact-object
Eckart--Young assembly only and leaves computed singular-vector/projector/
Gram/sketch/product arithmetic as non-probability FP/certificate obligations. -/
theorem rectangularThinSVD_sigmaTail_le_lowRankResidualFrob_of_antitone
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (B : Fin m → Fin (r + q) → ℝ)
    (hB : RectRankAtMost m (r + q) r B) :
    frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B := by
  have hUcols' :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          idMatrix (r + q) a b := by
    intro a b
    simpa [idMatrix] using hUcols a b
  have hsource :=
    sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_antitone
      Ufull sigma Vfull hUcols' hV hmono B hB
  have hsource_eq :
      sourceSVDFactorMatrix Ufull
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) Vfull =
        A := by
    funext i j
    calc
      sourceSVDFactorMatrix Ufull
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) Vfull i j
          =
            ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k) := by
              exact sourceSVDFactorMatrix_diagonal_eq_sum Ufull sigma Vfull i j
      _ = A i j := (hrepr i j).symm
  rw [frobNorm_squareSVDTailDiagonal_eq_sqrt_sum]
  simpa [hsource_eq] using hsource

/-- Supplied thin-rectangular SVD-style data with exact ordered
singular-square entries give a Frobenius best rank-`r` source-head
certificate.

The tail-optimality inequality is derived from LR.1dp.  This theorem is
exact-law/exact-object only; computed SVD, singular-vector, projector, Gram,
sketch, and product routines remain non-probability FP/certificate
obligations. -/
theorem isBestRankApproxFrob_of_rectangularThinSVD_antitone
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    IsBestRankApproxFrob m (r + q) r A
      (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  isBestRankApproxFrob_of_rectangularThinSVD_sigmaTail_optimal
    hUcols hV hrepr hhead_nonzero
    (fun B hB =>
      rectangularThinSVD_sigmaTail_le_lowRankResidualFrob_of_antitone
        hUcols hV hrepr hmono B hB)

/-- Strict-positive-head version of
`isBestRankApproxFrob_of_rectangularThinSVD_antitone`. -/
theorem isBestRankApproxFrob_of_rectangularThinSVD_head_pos_antitone
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    IsBestRankApproxFrob m (r + q) r A
      (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  isBestRankApproxFrob_of_rectangularThinSVD_antitone
    hUcols hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos) hmono

/-- A one-column tail diagonal has Frobenius norm equal to its single
nonnegative displayed singular value.

This is exact-object diagonal algebra for the equation-(9) one-step
coefficient block; it does not model a computed singular-value routine. -/
theorem frobNorm_squareSVDTailDiagonal_one {r : ℕ}
    (sigma : Fin (r + 1) → ℝ)
    (hsigma_tail : 0 ≤ sigma (Fin.natAdd r (0 : Fin 1))) :
    frobNorm (squareSVDTailDiagonal (r := r) (q := 1) sigma) =
      sigma (Fin.natAdd r (0 : Fin 1)) := by
  rw [frobNorm_eq_sqrt_frobNormSq]
  unfold frobNormSq squareSVDTailDiagonal
  simp [hsigma_tail]

/-- The ordered top-`r+1` right-Gram coefficient block has the displayed
one-step rank-`r` truncation as a Frobenius best-rank approximation.

This instantiates the exact-object Eckart--Young handoff for the coefficient
block used in equation (9).  The sampling law is an exact mathematical input by
project convention, and this theorem deliberately does not certify any
computed SVD, singular-vector table, projector, sketch, Gram inverse, or matrix
product routine. -/
theorem isBestRankApproxFrob_of_rectRightGramOrderedHeadDiagonal_succ
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : r + 1 ≤ n)
    (hlast :
      0 < rectSingularValue A
        (rectTopIndex hk (rectTopLastIndex (Nat.succ_pos r)))) :
    IsBestRankApproxFrob m (r + 1) r
      (sourceSVDFactorMatrix
        (rectRightGramOrderedHeadLeft A hk)
        (rectRightGramOrderedHeadSingularDiagonal A hk)
        (idMatrix (r + 1)))
      (sourceSVDFactorMatrix
        (rectangularThinSVDHeadLeft (r := r) (q := 1)
          (rectRightGramOrderedHeadLeft A hk))
        (squareSVDHeadDiagonal (r := r) (q := 1)
          (fun a : Fin (r + 1) =>
            rectRightGramBasisSingularValue A
              (rectRightGramOrderedTopEmbedding hk a)))
        (squareSVDHeadRight (r := r) (q := 1) (idMatrix (r + 1)))) := by
  classical
  let Ufull : Fin m → Fin (r + 1) → ℝ :=
    rectRightGramOrderedHeadLeft A hk
  let Vfull : Fin (r + 1) → Fin (r + 1) → ℝ :=
    idMatrix (r + 1)
  let sigmaVals : Fin (r + 1) → ℝ :=
    fun a => rectRightGramBasisSingularValue A
      (rectRightGramOrderedTopEmbedding hk a)
  let Acoeff : Fin m → Fin (r + 1) → ℝ :=
    sourceSVDFactorMatrix Ufull
      (rectRightGramOrderedHeadSingularDiagonal A hk) Vfull
  have hUcols :
      ∀ a b : Fin (r + 1),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0 := by
    intro a b
    simpa [Ufull, idMatrix] using
      rectRightGramOrderedHeadLeft_col_orthonormal_of_last_pos
        A hk (Nat.succ_pos r) hlast a b
  have hrepr :
      ∀ i j,
        Acoeff i j =
          ∑ k : Fin (r + 1), Ufull i k *
            (sigmaVals k * Vfull j k) := by
    intro i j
    simp [Acoeff, Ufull, Vfull, sigmaVals, sourceSVDFactorMatrix,
      rectRightGramOrderedHeadSingularDiagonal, idMatrix,
      Finset.sum_ite_eq, Finset.mem_univ]
  have hhead_pos :
      ∀ a : Fin r, 0 < sigmaVals (Fin.castAdd 1 a) := by
    intro a
    exact
      rectRightGramOrderedTopEmbedding_selected_pos_of_last_pos
        A hk (Nat.succ_pos r) hlast (Fin.castAdd 1 a)
  have htail_eq :
      frobNorm (squareSVDTailDiagonal (r := r) (q := 1) sigmaVals) =
        rectSingularValue A
          (rectTopIndex hk (rectTopLastIndex (Nat.succ_pos r))) := by
    have htail_nonneg :
        0 ≤ sigmaVals (Fin.natAdd r (0 : Fin 1)) := by
      exact rectRightGramBasisSingularValue_nonneg A _
    rw [frobNorm_squareSVDTailDiagonal_one sigmaVals htail_nonneg]
    have hidx :
        (Fin.natAdd r (0 : Fin 1) : Fin (r + 1)) =
          rectTopLastIndex (Nat.succ_pos r) := by
      apply Fin.ext
      simp [rectTopLastIndex]
    dsimp [sigmaVals]
    rw [(rectRightGramOrderedTopEmbedding_certificate A hk).singularValue_eq
      (Fin.natAdd r (0 : Fin 1))]
    simp [hidx]
  have hopt :
      ∀ B, RectRankAtMost m (r + 1) r B →
        frobNorm (squareSVDTailDiagonal (r := r) (q := 1) sigmaVals) ≤
          lowRankResidualFrob Acoeff B := by
    intro B hB
    rw [htail_eq]
    exact
      rectRankAtMost_lowRankResidualFrob_ge_of_rectRightGramOrderedHeadDiagonal_succ
        A hk hlast B hB
  have hbest :=
    isBestRankApproxFrob_of_rectangularThinSVD_head_pos_sigmaTail_optimal
      (m := m) (r := r) (q := 1) (A := Acoeff)
      (Ufull := Ufull) (Vfull := Vfull) (sigma := sigmaVals)
      hUcols (IsOrthogonal.id (r + 1)) hrepr hhead_pos hopt
  simpa [Acoeff, Ufull, Vfull, sigmaVals,
    rectRightGramOrderedHeadSingularDiagonal] using hbest

/-- Thin-rectangular SVD certificate version of the block source-SVD scalar
equation-(9) rank/residual surface.  The sketch matrix `Z` and sampling law
remain exact mathematical inputs; computing the SVD, sketch, Gram inverse,
projector, and products is a separate FP/certificate obligation. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_rectangularThinSVD
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma)) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 *
            (Real.sqrt (1 + eps ^ 2) *
              frobNorm (squareSVDTailDiagonal sigma)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_blockDiagonalSourceSVDTailCertificate
      (BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD
        hUcols hV hrepr hhead_nonzero)
      Z heps hVZ hcrossTerm

/-- Thin-rectangular SVD scalar equation-(9) rank/residual surface with a
strict-positive source-head singular-value hypothesis. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_rectangularThinSVD_head_pos
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma)) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 *
            (Real.sqrt (1 + eps ^ 2) *
              frobNorm (squareSVDTailDiagonal sigma)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_rectangularThinSVD
      hUcols hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
      Z heps hVZ hcrossTerm

/-- Tail-optimal thin-rectangular SVD certificate version of the scalar-rate
relative equation-(9) surface.  Tail optimality remains the visible
Eckart--Young/SVD-order obligation. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost m (r + q) r B →
      frobNormRect
          (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ≤
        lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho *
          frobNormRect
            (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
              (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull))) :
    IsBestRankApproxFrob m (r + q) r A
        (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNormRect
          (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate
      (BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD
        hUcols hV hrepr hhead_nonzero)
      Z heps hVZ hcrossTerm hopt hrelative

/-- Tail-optimal thin-rectangular SVD scalar-rate relative surface with a
strict-positive source-head singular-value hypothesis.  Tail optimality remains
the visible Eckart--Young/SVD-order obligation. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_head_pos
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost m (r + q) r B →
      frobNormRect
          (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ≤
        lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho *
          frobNormRect
            (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
              (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull))) :
    IsBestRankApproxFrob m (r + q) r A
        (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNormRect
          (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD
      hUcols hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
      Z heps hVZ hcrossTerm hopt hrelative

/-- Thin-rectangular SVD scalar-rate relative surface with the source-head
residual, tail-optimality hypothesis, and scalar comparison written directly
in terms of the displayed tail singular-value block. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost m (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob m (r + q) r A
        (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate_sigmaTail
    (BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD
      hUcols hV hrepr hhead_nonzero)
    Z heps hVZ hcrossTerm hopt hrelative

/-- Strict-positive-head version of
`columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail`. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_head_pos_sigmaTail
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost m (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob m (r + q) r A
        (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail
    hUcols hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
    Z heps hVZ hcrossTerm hopt hrelative

/-- Ordered thin-rectangular SVD scalar-rate relative surface with the
source-head residual and scalar comparison written directly in terms of the
displayed tail singular-value block.

The visible tail-optimality hypothesis from
`columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail`
is discharged by LR.1dq from exact singular-square antitonicity.  This remains
exact-object theorem-surface propagation and does not certify computed
SVD/projector/Gram/inverse/sketch/product arithmetic. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail_antitone
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob m (r + q) r A
        (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail
    hUcols hV hrepr hhead_nonzero Z heps hVZ hcrossTerm
    (fun B hB =>
      rectangularThinSVD_sigmaTail_le_lowRankResidualFrob_of_antitone
        hUcols hV hrepr hmono B hB)
    hrelative

/-- Strict-positive-head version of
`columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail_antitone`. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_head_pos_sigmaTail_antitone
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob m (r + q) r A
        (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail_antitone
    hUcols hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
    Z heps hVZ hcrossTerm hmono hrelative

end NumStability
