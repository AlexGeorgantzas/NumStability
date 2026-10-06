import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Logic.Equiv.Fin.Rotate
import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Source.Higham.Chapter07.Equation26.ComponentwiseDistance.Basic
import NumStability.Source.Higham.Chapter09.DoolittleClosure
import NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivot

/-!
# Chapter07 Equation26 RumpCycle Basic

Canonical destination for material split out of
`NumStability.Algorithms.Higham726Rump` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter
open scoped BigOperators Topology

namespace NumStability

/-- Multiplication of the rows of a real matrix by the entries of `d`. -/
def higham7_26_rowScale {n : ℕ}
    (d : Fin n → ℝ) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j ↦ d i * A i j

/-- Multiplication of the columns of a real matrix by the entries of `s`. -/
def higham7_26_columnScale {n : ℕ}
    (A : Fin n → Fin n → ℝ) (s : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j ↦ A i j * s j

@[simp]
lemma higham7_26_columnScale_mulVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (s x : Fin n → ℝ) :
    matMulVec n (higham7_26_columnScale A s) x =
      matMulVec n A (fun j ↦ s j * x j) := by
  funext i
  unfold matMulVec higham7_26_columnScale
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The characteristic determinant of a row-scaled matrix. -/
def higham7_26_rowScaledCharDet {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℝ) (d : Fin n → ℝ) : ℝ :=
  (Matrix.scalar (Fin n) r - Matrix.of (higham7_26_rowScale d A)).det

@[simp]
lemma higham7_26_rowScale_mulVec {n : ℕ}
    (d : Fin n → ℝ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    Matrix.mulVec (Matrix.of (higham7_26_rowScale d A) :
        Matrix (Fin n) (Fin n) ℝ) x =
      fun i ↦ d i * matMulVec n A x i := by
  funext i
  unfold Matrix.mulVec dotProduct matMulVec
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [higham7_26_rowScale]
  ring

@[simp]
lemma higham7_26_rowScale_matMulVec {n : ℕ}
    (d : Fin n → ℝ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    matMulVec n (higham7_26_rowScale d A) x =
      fun i ↦ d i * matMulVec n A x i := by
  funext i
  unfold matMulVec higham7_26_rowScale
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Replacing one row multiplier by a convex combination gives the same
convex combination of characteristic determinants. -/
lemma higham7_26_rowScaledCharDet_update_convex {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r θ a b : ℝ)
    (d : Fin n → ℝ) (i : Fin n) :
    higham7_26_rowScaledCharDet A r
        (Function.update d i (θ * a + (1 - θ) * b)) =
      θ * higham7_26_rowScaledCharDet A r (Function.update d i a) +
        (1 - θ) *
          higham7_26_rowScaledCharDet A r (Function.update d i b) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.scalar (Fin n) r - Matrix.of (higham7_26_rowScale d A)
  let row : ℝ → Fin n → ℝ := fun c j ↦
    (Matrix.scalar (Fin n) r) i j - c * A i j
  have hmatrix (c : ℝ) :
      Matrix.scalar (Fin n) r -
          Matrix.of (higham7_26_rowScale (Function.update d i c) A) =
        B.updateRow i (row c) := by
    ext p q
    by_cases hpi : p = i
    · subst p
      simp [B, row, higham7_26_rowScale]
    · simp [B, row, higham7_26_rowScale, hpi]
  have hrow :
      row (θ * a + (1 - θ) * b) =
        θ • row a + (1 - θ) • row b := by
    funext j
    simp [row]
    ring
  simp only [higham7_26_rowScaledCharDet, hmatrix]
  rw [hrow, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.det_updateRow_smul]

/-- One of the two signs prevents an existing partial sum from decreasing the
absolute value of a new summand. -/
lemma higham7_26_exists_sign_abs_add_mul_ge
    (a b : ℝ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ |a + ε * b| ≥ |b| := by
  by_cases h : 0 ≤ a * b
  · refine ⟨1, Or.inl rfl, ?_⟩
    have hsquare : b ^ 2 ≤ (a + b) ^ 2 := by
      nlinarith [sq_nonneg a]
    have hb := abs_nonneg b
    have hab := abs_nonneg (a + b)
    rw [show a + 1 * b = a + b by ring]
    nlinarith [sq_abs b, sq_abs (a + b)]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have hneg : a * b < 0 := lt_of_not_ge h
    have hsquare : b ^ 2 ≤ (a - b) ^ 2 := by
      nlinarith [sq_nonneg a]
    have hb := abs_nonneg b
    have hab := abs_nonneg (a - b)
    rw [show a + (-1) * b = a - b by ring]
    nlinarith [sq_abs b, sq_abs (a - b)]

/-- Rump's Lemma 4.2, in the equivalent form where the diagonal has already
been combined with the strictly lower-triangular part.  Column signs can be
chosen successively so that every row dominates its diagonal contribution. -/
theorem higham7_26_exists_columnSignature_lowerTriangular_diagonal_dominance
    {n : ℕ} (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hB : ∀ i j : Fin n, i.val < j.val → B i j = 0) :
    ∃ s : Fin n → ℝ,
      (∀ j : Fin n, s j = 1 ∨ s j = -1) ∧
      ∀ i : Fin n,
        |matMulVec n B (fun j ↦ s j * x j) i| ≥ |B i i * x i| := by
  classical
  have hstage : ∀ k : ℕ, k ≤ n →
      ∃ s : Fin n → ℝ,
        (∀ j : Fin n, s j = 1 ∨ s j = -1) ∧
        ∀ i : Fin n, i.val < k →
          |matMulVec n B (fun j ↦ s j * x j) i| ≥ |B i i * x i| := by
    intro k hk
    induction k with
    | zero =>
        exact ⟨fun _ ↦ 1, by simp, by simp⟩
    | succ k ih =>
        have hklt : k < n := Nat.lt_of_succ_le hk
        obtain ⟨s, hsign, hrows⟩ := ih (Nat.le_of_succ_le hk)
        let i : Fin n := ⟨k, hklt⟩
        let a : ℝ :=
          ∑ j ∈ (Finset.univ.erase i), B i j * (s j * x j)
        let b : ℝ := B i i * x i
        obtain ⟨ε, hεsign, hεbound⟩ :=
          higham7_26_exists_sign_abs_add_mul_ge a b
        let s' : Fin n → ℝ := Function.update s i ε
        refine ⟨s', ?_, ?_⟩
        · intro j
          by_cases hji : j = i
          · subst j
            simpa [s'] using hεsign
          · simpa [s', Function.update_of_ne hji] using hsign j
        · intro p hp
          have hp_cases : p.val < k ∨ p = i := by
            have hple : p.val ≤ k := Nat.le_of_lt_succ hp
            rcases Nat.lt_or_eq_of_le hple with hpk | hpk
            · exact Or.inl hpk
            · right
              apply Fin.ext
              simpa [i] using hpk
          rcases hp_cases with hpk | rfl
          · have hpi : p ≠ i := by
              intro h
              subst p
              simp [i] at hpk
            have hzero : B p i = 0 := hB p i (by simpa [i] using hpk)
            have hsame :
                matMulVec n B (fun j ↦ s' j * x j) p =
                  matMulVec n B (fun j ↦ s j * x j) p := by
              unfold matMulVec
              apply Finset.sum_congr rfl
              intro j _
              by_cases hji : j = i
              · subst j
                simp [hzero]
              · simp [s', Function.update_of_ne hji]
            rw [hsame]
            exact hrows p hpk
          · have hrow :
                matMulVec n B (fun j ↦ s' j * x j) i = a + ε * b := by
              unfold matMulVec
              rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
              congr 1
              · apply Finset.sum_congr rfl
                intro j hj
                have hji : j ≠ i := Finset.ne_of_mem_erase hj
                simp [s', Function.update_of_ne hji]
              · simp [s', b]
                ring
            rw [hrow]
            exact hεbound
  obtain ⟨s, hsign, hrows⟩ := hstage n le_rfl
  exact ⟨s, hsign, fun i ↦ hrows i i.isLt⟩

/-- The geometric tail over `Fin n` is bounded by the corresponding infinite
geometric tail. -/
lemma higham7_26_fin_geometric_tail_le {n : ℕ} (i : Fin n) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑ j ∈ Finset.Ioi i, q ^ j.val ≤ q ^ (i.val + 1) / (1 - q) := by
  have hsum :
      (∑ j ∈ Finset.Ioi i, q ^ j.val) =
        ∑ m ∈ Finset.Ico (i.val + 1) n, q ^ m := by
    calc
      (∑ j ∈ Finset.Ioi i, q ^ j.val) =
          ∑ m ∈ (Finset.Ioi i).map Fin.valEmbedding, q ^ m := by
            rw [Finset.sum_map]
            rfl
      _ = ∑ m ∈ Finset.Ioo i.val n, q ^ m := by
            rw [Fin.map_valEmbedding_Ioi]
      _ = ∑ m ∈ Finset.Ico (i.val + 1) n, q ^ m := by
            have hinterval :
                Finset.Ioo i.val n = Finset.Ico (i.val + 1) n := by
              simpa [Nat.succ_eq_add_one] using
                (Finset.Ico_succ_left_eq_Ioo i.val n).symm
            rw [hinterval]
  rw [hsum]
  exact geom_sum_Ico_le_of_lt_one hq0 hq1

/-- Rump's optimizing geometric ratio. -/
noncomputable def higham7_26_rumpGeometricRatio : ℝ :=
  1 - Real.sqrt 2 / 2

/-- The reciprocal of Rump's universal constant `3 + 2√2`. -/
noncomputable def higham7_26_rumpCycleConstant : ℝ :=
  1 / (3 + 2 * Real.sqrt 2)

lemma higham7_26_rumpGeometricRatio_pos :
    0 < higham7_26_rumpGeometricRatio := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp [higham7_26_rumpGeometricRatio]
  nlinarith

lemma higham7_26_rumpGeometricRatio_lt_one :
    higham7_26_rumpGeometricRatio < 1 := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  dsimp [higham7_26_rumpGeometricRatio]
  linarith

lemma higham7_26_rumpCycleConstant_pos :
    0 < higham7_26_rumpCycleConstant := by
  dsimp [higham7_26_rumpCycleConstant]
  positivity

/-- The scalar identity optimized in Rump's proof of Lemma 4.3. -/
lemma higham7_26_rumpGeometricRatio_identity :
    higham7_26_rumpGeometricRatio *
          (1 - 2 * higham7_26_rumpGeometricRatio) /
        (1 - higham7_26_rumpGeometricRatio) =
      higham7_26_rumpCycleConstant := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp [higham7_26_rumpGeometricRatio, higham7_26_rumpCycleConstant]
  field_simp
  nlinarith

lemma higham7_26_rumpCycleConstant_le_wrap_margin :
    higham7_26_rumpCycleConstant ≤
      1 - higham7_26_rumpGeometricRatio /
        (1 - higham7_26_rumpGeometricRatio) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp [higham7_26_rumpGeometricRatio, higham7_26_rumpCycleConstant]
  field_simp
  nlinarith

/-- A simple directed cycle in the functional graph of `f`, ordered by the
standard cyclic permutation of `Fin length`. -/
structure Higham7_26FunctionalCycle {α : Type*} (f : α → α) where
  length : ℕ
  length_pos : 0 < length
  vertex : Fin length → α
  vertex_injective : Function.Injective vertex
  next_vertex : ∀ t : Fin length,
    f (vertex t) = vertex (finRotate length t)

/-- A finite family has an entry which is both maximal and at least its
arithmetic average. -/
lemma higham7_26_exists_max_entry_ge_average {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (r : ℝ) (hr : r ≤ ∑ j : Fin n, a j) :
    ∃ j : Fin n,
      r / (n : ℝ) ≤ a j ∧ ∀ l : Fin n, a l ≤ a j := by
  classical
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  obtain ⟨j, _hj, hjmax⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin n))) huniv a
  have hmax : ∀ l : Fin n, a l ≤ a j := by
    intro l
    rw [← hjmax]
    exact Finset.le_sup' (s := (Finset.univ : Finset (Fin n)))
      (f := a) (Finset.mem_univ l)
  refine ⟨j, ?_, hmax⟩
  have hsum : (∑ l : Fin n, a l) ≤ (n : ℝ) * a j := by
    calc
      (∑ l : Fin n, a l) ≤ ∑ _l : Fin n, a j :=
        Finset.sum_le_sum fun l _ ↦ hmax l
      _ = (n : ℝ) * a j := by simp
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).2
  simpa [mul_comm] using hr.trans hsum

/-- A real sign chosen so that `a * sign(a) = |a|`. -/
noncomputable def higham7_26_entrySign (a : ℝ) : ℝ :=
  if 0 ≤ a then 1 else -1

lemma higham7_26_entrySign_eq_one_or_neg_one (a : ℝ) :
    higham7_26_entrySign a = 1 ∨ higham7_26_entrySign a = -1 := by
  by_cases h : 0 ≤ a
  · left
    simp [higham7_26_entrySign, h]
  · right
    simp [higham7_26_entrySign, h]

@[simp]
lemma higham7_26_abs_entrySign (a : ℝ) :
    |higham7_26_entrySign a| = 1 := by
  rcases higham7_26_entrySign_eq_one_or_neg_one a with h | h <;> simp [h]

@[simp]
lemma higham7_26_mul_entrySign (a : ℝ) :
    a * higham7_26_entrySign a = |a| := by
  by_cases h : 0 ≤ a
  · simp [higham7_26_entrySign, h, abs_of_nonneg h]
  · have ha : a < 0 := lt_of_not_ge h
    simp [higham7_26_entrySign, h, abs_of_neg ha]

/-- Choose the signs in each cycle-target column of `F` so that `Ainv * F`
agrees with `|Ainv|E` on every selected cycle edge.  The same construction is
globally dominated in absolute value by `|Ainv|E`. -/
theorem higham7_26_exists_signedMatrix_realizing_cycle
    {n k : ℕ} (hn : 0 < n)
    (Ainv E : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (vertex : Fin k → Fin n) (hvertex : Function.Injective vertex) :
    ∃ F : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |F i j| ≤ E i j) ∧
      (∀ i j : Fin n,
        |matMul n Ainv F i j| ≤
          higham7_26_distanceMajorant n Ainv E i j) ∧
      (∀ t : Fin k,
        matMul n Ainv F (vertex t) (vertex (finRotate k t)) =
          higham7_26_distanceMajorant n Ainv E
            (vertex t) (vertex (finRotate k t))) := by
  classical
  let predecessor : Fin n → Fin n := fun j ↦
    if h : ∃ t : Fin k, vertex (finRotate k t) = j then
      vertex (Classical.choose h)
    else ⟨0, hn⟩
  have hpredecessor : ∀ t : Fin k,
      predecessor (vertex (finRotate k t)) = vertex t := by
    intro t
    dsimp [predecessor]
    rw [dif_pos ⟨t, rfl⟩]
    let u : Fin k := Classical.choose
      (show ∃ u : Fin k,
        vertex (finRotate k u) = vertex (finRotate k t) from ⟨t, rfl⟩)
    have hu : vertex (finRotate k u) = vertex (finRotate k t) :=
      Classical.choose_spec
        (show ∃ u : Fin k,
          vertex (finRotate k u) = vertex (finRotate k t) from ⟨t, rfl⟩)
    have hrot : finRotate k u = finRotate k t := hvertex hu
    have hut : u = t := (finRotate k).injective hrot
    exact congrArg vertex hut
  let F : Fin n → Fin n → ℝ := fun a j ↦
    higham7_26_entrySign (Ainv (predecessor j) a) * E a j
  refine ⟨F, ?_, ?_, ?_⟩
  · intro a j
    simp [F, abs_mul, abs_of_nonneg (hE a j)]
  · intro i j
    calc
      |matMul n Ainv F i j| ≤
          ∑ a : Fin n, |Ainv i a * F a j| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a : Fin n, |Ainv i a| * E a j := by
        apply Finset.sum_congr rfl
        intro a _
        simp [F, abs_mul, abs_of_nonneg (hE a j)]
      _ = higham7_26_distanceMajorant n Ainv E i j := by
        rfl
  · intro t
    unfold matMul
    dsimp [F]
    rw [show predecessor (vertex (finRotate k t)) = vertex t from hpredecessor t]
    change
      (∑ a : Fin n,
        Ainv (vertex t) a *
          (higham7_26_entrySign (Ainv (vertex t) a) *
            E a (vertex (finRotate k t)))) =
        ∑ a : Fin n, |Ainv (vertex t) a| * E a (vertex (finRotate k t))
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc, higham7_26_mul_entrySign]

/-- Extend coefficients on an injectively indexed cycle by zero to the ambient
index type.  The sum presentation makes subsequent matrix-vector algebra
independent of a chosen inverse to `vertex`. -/
noncomputable def higham7_26_cycleEmbed {n k : ℕ}
    (vertex : Fin k → Fin n) (c : Fin k → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ t : Fin k, if vertex t = i then c t else 0

@[simp]
lemma higham7_26_cycleEmbed_vertex {n k : ℕ}
    (vertex : Fin k → Fin n) (hvertex : Function.Injective vertex)
    (c : Fin k → ℝ) (t : Fin k) :
    higham7_26_cycleEmbed vertex c (vertex t) = c t := by
  classical
  unfold higham7_26_cycleEmbed
  rw [Finset.sum_eq_single t]
  · simp
  · intro u _ hut
    have hne : vertex u ≠ vertex t := fun h ↦ hut (hvertex h)
    simp [hne]
  · simp

lemma higham7_26_cycleEmbed_eq_zero_of_not_mem {n k : ℕ}
    (vertex : Fin k → Fin n) (c : Fin k → ℝ) (i : Fin n)
    (hi : ¬ ∃ t : Fin k, vertex t = i) :
    higham7_26_cycleEmbed vertex c i = 0 := by
  classical
  unfold higham7_26_cycleEmbed
  apply Finset.sum_eq_zero
  intro t _
  have hne : vertex t ≠ i := fun h ↦ hi ⟨t, h⟩
  simp [hne]

lemma higham7_26_matMulVec_cycleEmbed_vertex {n k : ℕ}
    (A : Fin n → Fin n → ℝ) (vertex : Fin k → Fin n)
    (c : Fin k → ℝ) (t : Fin k) :
    matMulVec n A (higham7_26_cycleEmbed vertex c) (vertex t) =
      ∑ u : Fin k, A (vertex t) (vertex u) * c u := by
  classical
  unfold matMulVec higham7_26_cycleEmbed
  calc
    (∑ j : Fin n, A (vertex t) j *
        ∑ u : Fin k, if vertex u = j then c u else 0) =
        ∑ j : Fin n, ∑ u : Fin k,
          A (vertex t) j * (if vertex u = j then c u else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ u : Fin k, ∑ j : Fin n,
        A (vertex t) j * (if vertex u = j then c u else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ u : Fin k, A (vertex t) (vertex u) * c u := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_eq_single (vertex u)]
      · simp
      · intro j _ hju
        simp [Ne.symm hju]
      · simp

end NumStability
