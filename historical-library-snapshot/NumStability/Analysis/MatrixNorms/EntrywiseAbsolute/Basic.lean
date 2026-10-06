import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model

/-!
# NumStability Analysis MatrixNorms EntrywiseAbsolute Basic

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter10` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Matrix-vector action commutes with vector negation. -/
theorem matMulVec_neg (n : ℕ) (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    matMulVec n A (fun k => -(v k)) = fun i => -(matMulVec n A v i) := by
  funext i
  unfold matMulVec
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Quadratic-form bound from an operator-norm certificate** (the
Rayleigh–Weyl step of the Theorem 10.7 induction, Higham p. 200):
`opNorm2Le E c` gives `|xᵀEx| ≤ c ‖x‖₂²` — precisely the perturbation
hypothesis consumed by the Theorem 10.7 threshold theorems, so any
operator-norm certificate for the scaled backward error feeds them
directly. -/
theorem quadForm_abs_le_of_opNorm2Le (n : ℕ) (E : Fin n → Fin n → ℝ)
    (c : ℝ) (hE : opNorm2Le E c) (x : Fin n → ℝ) :
    |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤
      c * ∑ i : Fin n, x i ^ 2 := by
  have hform : ∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j =
      ∑ i : Fin n, x i * matMulVec n E x i := by
    apply Finset.sum_congr rfl
    intro i _
    unfold matMulVec
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hform]
  have hxnn := vecNorm2_nonneg x
  have hsq : vecNorm2 x * vecNorm2 x = ∑ i : Fin n, x i ^ 2 := by
    rw [← sq, vecNorm2_sq]
    rfl
  calc |∑ i : Fin n, x i * matMulVec n E x i|
      ≤ vecNorm2 x * vecNorm2 (matMulVec n E x) :=
        abs_vecInnerProduct_le_vecNorm2_mul x (matMulVec n E x)
    _ ≤ vecNorm2 x * (c * vecNorm2 x) :=
        mul_le_mul_of_nonneg_left (hE x) hxnn
    _ = c * (vecNorm2 x * vecNorm2 x) := by ring
    _ = c * ∑ i : Fin n, x i ^ 2 := by rw [hsq]

/-- **Componentwise domination transfers operator-2-norm certificates**
(used for the normwise equation (10.7) reading of Theorem 10.3): if
`|M| ≤ B` entrywise and `B` satisfies the vector-action certificate
`opNorm2Le B c`, then so does `M`. -/
theorem opNorm2Le_of_abs_le (n : ℕ) (M B : Fin n → Fin n → ℝ)
    (hdom : ∀ i j, |M i j| ≤ B i j) (c : ℝ) (hB : opNorm2Le B c) :
    opNorm2Le M c := by
  intro x
  have hentry : ∀ i : Fin n,
      |matMulVec n M x i| ≤ matMulVec n B (absVec n x) i := by
    intro i
    unfold matMulVec absVec
    calc |∑ j : Fin n, M i j * x j|
        ≤ ∑ j : Fin n, |M i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n, B i j * |x j| := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hdom i j) (abs_nonneg _)
  have hsq : vecNorm2Sq (matMulVec n M x) ≤
      vecNorm2Sq (matMulVec n B (absVec n x)) := by
    unfold vecNorm2Sq
    apply Finset.sum_le_sum
    intro i _
    have h1 := hentry i
    nlinarith [abs_nonneg (matMulVec n M x i),
      sq_abs (matMulVec n M x i)]
  have h5 : vecNorm2 (absVec n x) = vecNorm2 x := by
    unfold vecNorm2 vecNorm2Sq absVec
    congr 1
    exact Finset.sum_congr rfl fun i _ => sq_abs (x i)
  calc vecNorm2 (matMulVec n M x)
      ≤ vecNorm2 (matMulVec n B (absVec n x)) := Real.sqrt_le_sqrt hsq
    _ ≤ c * vecNorm2 (absVec n x) := hB (absVec n x)
    _ = c * vecNorm2 x := by rw [h5]

/-- **Lemma 6.6 chain, step 1** (used by equation (10.7)): a vector-action
operator-2-norm certificate bounds the squared Frobenius norm by `n c²`,
since each column is the image of a standard basis vector. -/
theorem frobNormSq_le_of_opNorm2Le (n : ℕ) (M : Fin n → Fin n → ℝ)
    (c : ℝ) (h : opNorm2Le M c) :
    frobNormSq M ≤ n * c ^ 2 := by
  have hcol : ∀ j : Fin n, matMulVec n M (fun k => if k = j then 1 else 0) =
      fun i => M i j := by
    intro j
    funext i
    unfold matMulVec
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)]
    simp
  have hbasis_norm : ∀ j : Fin n,
      vecNorm2 (fun k : Fin n => if k = j then (1:ℝ) else 0) = 1 := by
    intro j
    unfold vecNorm2 vecNorm2Sq
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)]
    simp
  have hcolsq : ∀ j : Fin n, ∑ i : Fin n, M i j ^ 2 ≤ c ^ 2 := by
    intro j
    have h1 := h (fun k => if k = j then 1 else 0)
    rw [hcol j, hbasis_norm j, mul_one] at h1
    have h2 : vecNorm2 (fun i => M i j) ^ 2 ≤ c ^ 2 := by
      have hnn : 0 ≤ vecNorm2 (fun i => M i j) := vecNorm2_nonneg _
      nlinarith
    rw [vecNorm2_sq] at h2
    exact h2
  unfold frobNormSq
  rw [Finset.sum_comm]
  calc ∑ j : Fin n, ∑ i : Fin n, M i j ^ 2
      ≤ ∑ _j : Fin n, c ^ 2 := Finset.sum_le_sum fun j _ => hcolsq j
    _ = n * c ^ 2 := by simp

/-- **Lemma 6.6 chain, step 2** (Higham Lemma 6.6, `‖|A|‖₂ ≤ √n ‖A‖₂`, in
vector-action form): the componentwise absolute value of a matrix carries
an operator-2-norm certificate inflated by `√n`, through the Frobenius
norm (which is invariant under componentwise absolute value). -/
theorem opNorm2Le_abs_of_opNorm2Le (n : ℕ) (M : Fin n → Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (h : opNorm2Le M c) :
    opNorm2Le (fun i j => |M i j|) (Real.sqrt n * c) := by
  intro x
  have habs_frob : frobNormSq (fun i j => |M i j|) = frobNormSq M := by
    unfold frobNormSq
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => sq_abs (M i j)
  calc vecNorm2 (matMulVec n (fun i j => |M i j|) x)
      ≤ frobNorm (fun i j => |M i j|) * vecNorm2 x :=
        vecNorm2_matMulVec_le_frobNorm_mul _ x
    _ ≤ Real.sqrt n * c * vecNorm2 x := by
        apply mul_le_mul_of_nonneg_right _ (vecNorm2_nonneg x)
        rw [frobNorm_eq_sqrt_frobNormSq, habs_frob]
        calc Real.sqrt (frobNormSq M)
            ≤ Real.sqrt (n * c ^ 2) :=
              Real.sqrt_le_sqrt (frobNormSq_le_of_opNorm2Le n M c h)
          _ = Real.sqrt n * c := by
              rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hc]

/-- Vector-action operator-2-norm certificates compose across the
repository matrix product. -/
theorem opNorm2Le_matMul (n : ℕ) (A B : Fin n → Fin n → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hA : opNorm2Le A a) (hB : opNorm2Le B b) :
    opNorm2Le (matMul n A B) (a * b) := by
  intro x
  have hcomp : matMulVec n (matMul n A B) x =
      matMulVec n A (matMulVec n B x) := by
    funext i
    unfold matMulVec matMul
    calc ∑ j : Fin n, (∑ k : Fin n, A i k * B k j) * x j
        = ∑ j : Fin n, ∑ k : Fin n, A i k * B k j * x j := by
          exact Finset.sum_congr rfl fun j _ => Finset.sum_mul _ _ _
      _ = ∑ k : Fin n, ∑ j : Fin n, A i k * B k j * x j :=
          Finset.sum_comm
      _ = ∑ k : Fin n, A i k * ∑ j : Fin n, B k j * x j := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  rw [hcomp]
  calc vecNorm2 (matMulVec n A (matMulVec n B x))
      ≤ a * vecNorm2 (matMulVec n B x) := hA _
    _ ≤ a * (b * vecNorm2 x) := mul_le_mul_of_nonneg_left (hB x) ha
    _ = a * b * vecNorm2 x := by ring

/-- Nonnegative scaling of a vector-action operator-2-norm certificate. -/
theorem opNorm2Le_smul (n : ℕ) (B : Fin n → Fin n → ℝ) (c ε : ℝ)
    (hε : 0 ≤ ε) (hB : opNorm2Le B c) :
    opNorm2Le (fun i j => ε * B i j) (ε * c) := by
  intro x
  have hvec : matMulVec n (fun i j => ε * B i j) x =
      fun i => ε * matMulVec n B x i := by
    funext i
    unfold matMulVec
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hvec]
  have hnorm : vecNorm2 (fun i => ε * matMulVec n B x i) =
      ε * vecNorm2 (matMulVec n B x) := by
    unfold vecNorm2 vecNorm2Sq
    rw [show ∑ i : Fin n, (ε * matMulVec n B x i) ^ 2 =
        ε ^ 2 * ∑ i : Fin n, matMulVec n B x i ^ 2 by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
    rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε]
  rw [hnorm]
  calc ε * vecNorm2 (matMulVec n B x)
      ≤ ε * (c * vecNorm2 x) := mul_le_mul_of_nonneg_left (hB x) hε
    _ = ε * c * vecNorm2 x := by ring

/-- **Lemma 6.6 chain, transpose form**: `‖|Rᵀ|‖₂ ≤ √n c` from an
operator-2-norm certificate on `R`, via the transpose-invariant Frobenius
norm. -/
theorem opNorm2Le_abs_transpose_of_opNorm2Le (n : ℕ)
    (R : Fin n → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) (h : opNorm2Le R c) :
    opNorm2Le (fun i j => |R j i|) (Real.sqrt n * c) := by
  intro x
  have hfrob : frobNormSq (fun i j : Fin n => |R j i|) = frobNormSq R := by
    unfold frobNormSq
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => sq_abs (R i j)
  calc vecNorm2 (matMulVec n (fun i j => |R j i|) x)
      ≤ frobNorm (fun i j => |R j i|) * vecNorm2 x :=
        vecNorm2_matMulVec_le_frobNorm_mul _ x
    _ ≤ Real.sqrt n * c * vecNorm2 x := by
        apply mul_le_mul_of_nonneg_right _ (vecNorm2_nonneg x)
        rw [frobNorm_eq_sqrt_frobNormSq, hfrob]
        calc Real.sqrt (frobNormSq R)
            ≤ Real.sqrt (n * c ^ 2) :=
              Real.sqrt_le_sqrt (frobNormSq_le_of_opNorm2Le n R c h)
          _ = Real.sqrt n * c := by
              rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hc]

/-- The Gram quadratic form is the squared image norm:
`xᵀ(RᵀR)x = ‖Rx‖₂²` in the repository's column convention. -/
theorem gram_quadForm_eq_sq_norm (n : ℕ) (R : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    ∑ i : Fin n, ∑ l : Fin n,
      x i * (∑ p : Fin n, R p i * R p l) * x l =
    vecNorm2Sq (matMulVec n R x) := by
  unfold vecNorm2Sq matMulVec
  calc ∑ i : Fin n, ∑ l : Fin n,
      x i * (∑ p : Fin n, R p i * R p l) * x l
      = ∑ i : Fin n, ∑ l : Fin n, ∑ p : Fin n,
          (R p i * x i) * (R p l * x l) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro l _
        rw [mul_comm (x i) _, Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        ring
    _ = ∑ p : Fin n, ∑ i : Fin n, ∑ l : Fin n,
          (R p i * x i) * (R p l * x l) := by
        refine Eq.trans
          (Finset.sum_congr rfl fun i _ => Finset.sum_comm) ?_
        exact Finset.sum_comm
    _ = ∑ p : Fin n, (∑ j : Fin n, R p j * x j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [sq, Finset.sum_mul_sum]

/-- Splitting a double sum over `Fin (m+1)` into interior, two borders,
and corner. -/
theorem sum_sum_castSucc_split (m : ℕ) (F : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ∑ i : Fin (m + 1), ∑ l : Fin (m + 1), F i l =
      (∑ i : Fin m, ∑ l : Fin m, F i.castSucc l.castSucc) +
      (∑ i : Fin m, F i.castSucc (Fin.last m)) +
      (∑ l : Fin m, F (Fin.last m) l.castSucc) +
      F (Fin.last m) (Fin.last m) := by
  rw [Fin.sum_univ_castSucc]
  rw [show ∑ i : Fin m, ∑ l : Fin (m + 1), F i.castSucc l =
      ∑ i : Fin m, ((∑ l : Fin m, F i.castSucc l.castSucc) +
        F i.castSucc (Fin.last m)) from
    Finset.sum_congr rfl fun i _ => Fin.sum_univ_castSucc _]
  rw [Fin.sum_univ_castSucc (f := fun l => F (Fin.last m) l)]
  rw [Finset.sum_add_distrib]
  ring

/-- **Theorem 10.7 foundation** (Higham §10.1, proof of Theorem 10.7): the
all-ones rank-one matrix `e eᵀ` has operator 2-norm at most `n`, in the
repository's vector-action certificate form `‖(e eᵀ)x‖₂ ≤ n ‖x‖₂`.  This is
the estimate that converts the componentwise scaled backward-error bound
`|E| ≤ c · e eᵀ` into the normwise hypothesis of the Theorem 10.7
success/failure thresholds. -/
theorem higham10_7_onesMatrix_opNorm2Le (n : ℕ) :
    opNorm2Le (fun _ _ : Fin n => (1 : ℝ)) n := by
  intro x
  have hmv : matMulVec n (fun _ _ => (1:ℝ)) x =
      fun _ : Fin n => ∑ j : Fin n, x j := by
    funext i
    unfold matMulVec
    exact Finset.sum_congr rfl fun j _ => one_mul (x j)
  rw [hmv]
  have hcs : (∑ j : Fin n, x j) ^ 2 ≤ (n : ℝ) * vecNorm2Sq x := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin n => (1:ℝ)) x
    have h1 : ∑ j : Fin n, (1:ℝ) * x j = ∑ j : Fin n, x j :=
      Finset.sum_congr rfl fun j _ => one_mul (x j)
    have h2 : ∑ _j : Fin n, ((1:ℝ)) ^ 2 = (n : ℝ) := by simp
    rw [h1, h2] at h
    exact h
  have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold vecNorm2 vecNorm2Sq
  have hconst : ∑ _i : Fin n, (∑ j : Fin n, x j) ^ 2 =
      (n : ℝ) * (∑ j : Fin n, x j) ^ 2 := by simp
  rw [hconst]
  have hbound : (n : ℝ) * (∑ j : Fin n, x j) ^ 2 ≤
      (n : ℝ) ^ 2 * ∑ i : Fin n, x i ^ 2 := by
    have := mul_le_mul_of_nonneg_left hcs hn0
    calc (n : ℝ) * (∑ j : Fin n, x j) ^ 2
        ≤ (n : ℝ) * ((n : ℝ) * vecNorm2Sq x) := this
      _ = (n : ℝ) ^ 2 * ∑ i : Fin n, x i ^ 2 := by
          unfold vecNorm2Sq; ring
  calc Real.sqrt ((n : ℝ) * (∑ j : Fin n, x j) ^ 2)
      ≤ Real.sqrt ((n : ℝ) ^ 2 * ∑ i : Fin n, x i ^ 2) :=
        Real.sqrt_le_sqrt hbound
    _ = (n : ℝ) * Real.sqrt (∑ i : Fin n, x i ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hn0]

/-- **Entrywise bound to quadratic-form bound** (Theorem 10.7 induction,
Higham p. 200): a uniform entrywise bound `|E i j| ≤ ε` gives
`|xᵀEx| ≤ ε n ‖x‖₂²`, through the `‖eeᵀ‖₂ ≤ n` certificate. -/
theorem quadForm_abs_le_of_entrywise_le (n : ℕ)
    (E : Fin n → Fin n → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hE : ∀ i j, |E i j| ≤ ε) (x : Fin n → ℝ) :
    |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤
      ε * n * ∑ i : Fin n, x i ^ 2 := by
  have h2 := opNorm2Le_smul n (fun _ _ : Fin n => (1:ℝ)) n ε hε
    (higham10_7_onesMatrix_opNorm2Le n)
  have h3 := opNorm2Le_of_abs_le n E (fun _ _ : Fin n => ε * 1)
    (fun i j => by rw [mul_one]; exact hE i j) (ε * n) h2
  exact quadForm_abs_le_of_opNorm2Le n E (ε * n) h3 x

/-- **Block split of the quadratic form** under a `Fin.append`
    partition: the (k+m)-dimensional quadratic form decomposes into the
    four block forms. -/
lemma quadForm_append_split {k m : ℕ}
    (A : Fin (k + m) → Fin (k + m) → ℝ)
    (u : Fin k → ℝ) (v : Fin m → ℝ) :
    ∑ i : Fin (k + m), ∑ j : Fin (k + m),
      Fin.append u v i * A i j * Fin.append u v j =
    (∑ i : Fin k, ∑ j : Fin k,
      u i * A (Fin.castAdd m i) (Fin.castAdd m j) * u j)
    + (∑ i : Fin k, ∑ j : Fin m,
      u i * A (Fin.castAdd m i) (Fin.natAdd k j) * v j)
    + (∑ i : Fin m, ∑ j : Fin k,
      v i * A (Fin.natAdd k i) (Fin.castAdd m j) * u j)
    + (∑ i : Fin m, ∑ j : Fin m,
      v i * A (Fin.natAdd k i) (Fin.natAdd k j) * v j) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Finset.sum_add_distrib]
  ring

/-- Operator-norm certificates add across matrix sums. -/
lemma opNorm2Le_add {n : ℕ} (A B : Fin n → Fin n → ℝ) (a b : ℝ)
    (hA : opNorm2Le A a) (hB : opNorm2Le B b) :
    opNorm2Le (fun i j => A i j + B i j) (a + b) := by
  intro x
  have hsplit : matMulVec n (fun i j => A i j + B i j) x =
      fun i => matMulVec n A x i + matMulVec n B x i := by
    funext i
    unfold matMulVec
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  calc vecNorm2 (fun i => matMulVec n A x i + matMulVec n B x i)
      ≤ vecNorm2 (matMulVec n A x) + vecNorm2 (matMulVec n B x) :=
        vecNorm2_add_le _ _
    _ ≤ a * vecNorm2 x + b * vecNorm2 x := add_le_add (hA x) (hB x)
    _ = (a + b) * vecNorm2 x := by ring

/-- **Quadratic-form certificate from an entrywise bound** (the
    dimension-costing conversion behind display (10.21)'s
    `r·γ_{r+1}/(1−γ_{r+1})` value): entries bounded by `c` give
    `|zᵀEz| ≤ c·m·‖z‖²` by the ones-vector Cauchy–Schwarz. -/
lemma quadForm_cert_of_entrywise {m : ℕ} (E : Fin m → Fin m → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hE : ∀ i j : Fin m, |E i j| ≤ c) :
    ∀ z : Fin m → ℝ,
      |∑ i : Fin m, ∑ j : Fin m, z i * E i j * z j| ≤
      c * (m : ℝ) * ∑ i : Fin m, z i ^ 2 := by
  intro z
  have h1 : |∑ i : Fin m, ∑ j : Fin m, z i * E i j * z j| ≤
      ∑ i : Fin m, ∑ j : Fin m, |z i| * c * |z j| := by
    calc |∑ i : Fin m, ∑ j : Fin m, z i * E i j * z j|
        ≤ ∑ i : Fin m, |∑ j : Fin m, z i * E i j * z j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin m, ∑ j : Fin m, |z i * E i j * z j| :=
          Finset.sum_le_sum fun i _ =>
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin m, ∑ j : Fin m, |z i| * c * |z j| := by
          refine Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg _))
            (abs_nonneg _)
  have h2 : ∑ i : Fin m, ∑ j : Fin m, |z i| * c * |z j| =
      c * (∑ i : Fin m, |z i|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : (∑ i : Fin m, |z i|) ^ 2 ≤
      (m : ℝ) * ∑ i : Fin m, z i ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin m => (1:ℝ)) (fun i => |z i|)
    have hL : ∑ i : Fin m, (1:ℝ) * |z i| = ∑ i : Fin m, |z i| := by
      simp
    have h1s : ∑ _i : Fin m, ((1:ℝ)) ^ 2 = (m : ℝ) := by simp
    have h2s : ∑ i : Fin m, |z i| ^ 2 = ∑ i : Fin m, z i ^ 2 :=
      Finset.sum_congr rfl fun i _ => sq_abs _
    rw [hL, h1s, h2s] at h
    exact h
  calc |∑ i : Fin m, ∑ j : Fin m, z i * E i j * z j|
      ≤ c * (∑ i : Fin m, |z i|) ^ 2 := h1.trans_eq h2
    _ ≤ c * ((m : ℝ) * ∑ i : Fin m, z i ^ 2) :=
        mul_le_mul_of_nonneg_left h3 hc
    _ = c * (m : ℝ) * ∑ i : Fin m, z i ^ 2 := by ring

/-- **Two-sided inverses of a finite square matrix are unique** (Higham §10.4,
    the well-definedness fact the GE stage induction needs so the stage Gram
    `Q(S) = Sᵀ H⁻¹ S` does not depend on which `spd_inverse_exists` inverse is
    chosen at each stage): a left inverse `A` and a right inverse `B` of the same
    `T` coincide, `A = A(TB) = (AT)B = B`. -/
theorem matMul_leftInverse_eq_rightInverse {n : ℕ}
    (T A B : Fin n → Fin n → ℝ)
    (hA : IsLeftInverse n T A) (hB : IsRightInverse n T B) : A = B := by
  have hAT : matMul n A T = idMatrix n := by funext i j; exact hA i j
  have hTB : matMul n T B = idMatrix n := by funext i j; exact hB i j
  calc A = matMul n A (idMatrix n) := (matMul_id_right n A).symm
    _ = matMul n A (matMul n T B) := by rw [hTB]
    _ = matMul n (matMul n A T) B := (matMul_assoc n A T B).symm
    _ = matMul n (idMatrix n) B := by rw [hAT]
    _ = B := matMul_id_left n B

end NumStability
