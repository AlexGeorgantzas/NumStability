-- Algorithms/QR/HouseholderSpecSupport.lean
-- Support definitions and exact lemmas for trailing/stored Householder QR.
import NumStability.Algorithms.QR.HouseholderSpec

namespace NumStability

open scoped BigOperators

theorem householder_row_eq_id_of_zero_prefix (n k : ℕ)
    (v : Fin n → ℝ) (β : ℝ)
    (hprefix : ∀ i : Fin n, i.val < k → v i = 0)
    (i j : Fin n) (hi : i.val < k) :
    householder n v β i j = idMatrix n i j := by
  simp [householder, hprefix i hi]

/-- Column companion to `householder_row_eq_id_of_zero_prefix`. -/
theorem householder_col_eq_id_of_zero_prefix (n k : ℕ)
    (v : Fin n → ℝ) (β : ℝ)
    (hprefix : ∀ i : Fin n, i.val < k → v i = 0)
    (i j : Fin n) (hj : j.val < k) :
    householder n v β i j = idMatrix n i j := by
  simp [householder, hprefix j hj]

/-- A zero-prefix Householder reflector preserves the corresponding prefix of
    every vector. -/
theorem matMulVec_householder_eq_self_of_zero_prefix (n k : ℕ)
    (v x : Fin n → ℝ) (β : ℝ)
    (hprefix : ∀ i : Fin n, i.val < k → v i = 0)
    (i : Fin n) (hi : i.val < k) :
    matMulVec n (householder n v β) x i = x i := by
  have hrow : ∀ j : Fin n, householder n v β i j = idMatrix n i j := by
    intro j
    exact householder_row_eq_id_of_zero_prefix n k v β hprefix i j hi
  unfold matMulVec
  simp_rw [hrow]
  simpa [matMulVec] using congrFun (matMulVec_id n x) i

/-- A zero-prefix Householder reflector preserves the corresponding rows of a
    square matrix under left multiplication. -/
theorem matMul_householder_eq_self_row_of_zero_prefix (n k : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (A : Fin n → Fin n → ℝ)
    (hprefix : ∀ i : Fin n, i.val < k → v i = 0)
    (i j : Fin n) (hi : i.val < k) :
    matMul n (householder n v β) A i j = A i j := by
  have hrow : ∀ l : Fin n, householder n v β i l = idMatrix n i l := by
    intro l
    exact householder_row_eq_id_of_zero_prefix n k v β hprefix i l hi
  unfold matMul
  simp_rw [hrow]
  simpa [matMul] using congrFun (congrFun (matMul_id_left n A) i) j

/-- A zero-prefix Householder reflector preserves the corresponding rows of a
    rectangular matrix under left multiplication. -/
theorem matMulRectLeft_householder_eq_self_row_of_zero_prefix {m n k : ℕ}
    (v : Fin m → ℝ) (β : ℝ) (A : Fin m → Fin n → ℝ)
    (hprefix : ∀ i : Fin m, i.val < k → v i = 0)
    (i : Fin m) (j : Fin n) (hi : i.val < k) :
    matMulRectLeft (householder m v β) A i j = A i j := by
  have hrow : ∀ l : Fin m, householder m v β i l = idMatrix m i l := by
    intro l
    exact householder_row_eq_id_of_zero_prefix m k v β hprefix i l hi
  unfold matMulRectLeft
  simp_rw [hrow]
  simpa [matMulRectLeft] using congrFun (congrFun (matMulRectLeft_id A) i) j

/-- A zero-prefix Householder reflector preserves any vector supported on the
    same prefix.  This column-side companion is needed for the trailing
    Householder construction: the exact reflector leaves the already-finished
    prefix part of the active column unchanged. -/
theorem matMulVec_householder_eq_self_of_zero_prefix_support (n k : ℕ)
    (v x : Fin n → ℝ) (β : ℝ)
    (hprefix : ∀ i : Fin n, i.val < k → v i = 0)
    (hsupport : ∀ i : Fin n, k ≤ i.val → x i = 0) :
    matMulVec n (householder n v β) x = x := by
  ext i
  have hterm : ∀ j : Fin n,
      householder n v β i j * x j = idMatrix n i j * x j := by
    intro j
    by_cases hj : j.val < k
    · rw [householder_col_eq_id_of_zero_prefix n k v β hprefix i j hj]
    · have hxj : x j = 0 := hsupport j (le_of_not_gt hj)
      simp [hxj]
  unfold matMulVec
  simp_rw [hterm]
  simpa [matMulVec] using congrFun (matMulVec_id n x) i

/-- Active Householder vector `v = x - alpha e_p`.

    The exact active-column zeroing theorem below uses this vector for the
    column segment being eliminated. -/
noncomputable def householderActiveVector (n : ℕ) (p : Fin n)
    (x : Fin n → ℝ) (alpha : ℝ) : Fin n → ℝ :=
  fun i => x i - if i = p then alpha else 0

/-- Exact Householder normalization `beta = 2/(v^T v)`. -/
noncomputable def householderBetaSpec (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  2 / ∑ i : Fin n, v i * v i

/-- The exact Householder beta `2/(v^T v)` is nonnegative. -/
theorem householderBetaSpec_nonneg (n : ℕ) (v : Fin n → ℝ) :
    0 ≤ householderBetaSpec n v := by
  have hden_nonneg : 0 ≤ ∑ i : Fin n, v i * v i := by
    simpa [vecNorm2Sq, pow_two] using vecNorm2Sq_nonneg v
  unfold householderBetaSpec
  exact div_nonneg (by norm_num) hden_nonneg

/-- Normalizing the exact Householder beta leaves the exact reflector
unchanged. -/
theorem householder_normalizedVector_eq_betaSpec (n : ℕ)
    (v : Fin n → ℝ) :
    householder n (householderNormalizedVector n v (householderBetaSpec n v)) 1 =
      householder n v (householderBetaSpec n v) :=
  householder_normalizedVector_eq n v (householderBetaSpec n v)
    (householderBetaSpec_nonneg n v)

/-- The exact Householder normalization satisfies `beta * (v^T v) = 2`
whenever the denominator is nonzero. -/
theorem householderBeta_mul_inner_self_eq_two (n : ℕ) (v : Fin n → ℝ)
    (hden : (∑ i : Fin n, v i * v i) ≠ 0) :
    householderBetaSpec n v * (∑ i : Fin n, v i * v i) = 2 := by
  have hden_sq : (∑ i : Fin n, v i ^ 2) ≠ 0 := by
    simpa [pow_two] using hden
  unfold householderBetaSpec
  field_simp [hden_sq]

/-- If a Householder vector is already normalized with squared norm `2`, its
exact beta is `1`. -/
theorem householderBetaSpec_eq_one_of_inner_self_eq_two (n : Nat)
    (v : Fin n -> Real)
    (hden : (∑ i : Fin n, v i * v i) = 2) :
    householderBetaSpec n v = 1 := by
  unfold householderBetaSpec
  rw [hden]
  norm_num

/-- Absolute normalization form of `householderBeta_mul_inner_self_eq_two`.

For a nonzero Householder denominator, the exact choice
`β = 2 / (vᵀv)` satisfies `|β| ‖v‖₂² = 2`.  This is the exact-algebra bridge
used by the compact floating-point coefficient route: the floating-point
coefficient depends on the product `|β| ‖v‖₂²`, while the existing reflector
normalization lemma is stated with the raw denominator `∑ᵢ vᵢ vᵢ`. -/
theorem abs_householderBeta_mul_vecNorm2_sq_eq_two (n : ℕ)
    (v : Fin n → ℝ)
    (hden : (∑ i : Fin n, v i * v i) ≠ 0) :
    |householderBetaSpec n v| * vecNorm2 v ^ 2 = 2 := by
  have hden_nonneg : 0 ≤ ∑ i : Fin n, v i * v i := by
    simpa [vecNorm2Sq, pow_two] using vecNorm2Sq_nonneg v
  have hbeta_nonneg : 0 ≤ householderBetaSpec n v := by
    unfold householderBetaSpec
    exact div_nonneg (by linarith) hden_nonneg
  calc
    |householderBetaSpec n v| * vecNorm2 v ^ 2
        = householderBetaSpec n v * vecNorm2 v ^ 2 := by
            rw [abs_of_nonneg hbeta_nonneg]
    _ = householderBetaSpec n v * vecNorm2Sq v := by
            rw [vecNorm2_sq]
    _ = 2 := by
            simpa [vecNorm2Sq, pow_two] using
              householderBeta_mul_inner_self_eq_two n v hden

/-- Inequality form of `abs_householderBeta_mul_vecNorm2_sq_eq_two`. -/
theorem abs_householderBeta_mul_vecNorm2_sq_le_two (n : ℕ)
    (v : Fin n → ℝ)
    (hden : (∑ i : Fin n, v i * v i) ≠ 0) :
    |householderBetaSpec n v| * vecNorm2 v ^ 2 ≤ 2 :=
  le_of_eq (abs_householderBeta_mul_vecNorm2_sq_eq_two n v hden)

/-- Prefix part of a vector before pivot `p`. -/
noncomputable def householderPrefixPart (n : ℕ) (p : Fin n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i.val < p.val then x i else 0

/-- Trailing part of a vector from pivot `p` onward. -/
noncomputable def householderTrailingPart (n : ℕ) (p : Fin n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i.val < p.val then 0 else x i

/-- Squared norm of the trailing part of a vector. -/
noncomputable def householderTrailingNorm2Sq (n : ℕ) (p : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  vecNorm2Sq (householderTrailingPart n p x)

/-- Squared norm of column `j`, restricted to rows at or below pivot row `p`. -/
noncomputable def householderTrailingColumnNorm2Sq {m n : ℕ} (p : Fin m)
    (A : Fin m → Fin n → ℝ) (j : Fin n) : ℝ :=
  householderTrailingNorm2Sq m p (fun i => A i j)

/-- Squared Frobenius mass of the active trailing block from row `p` and
column `k` onward. -/
noncomputable def householderActiveBlockNorm2Sq {m n : ℕ}
    (p : Fin m) (k : Fin n) (A : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n,
    if p.val ≤ i.val ∧ k.val ≤ j.val then A i j ^ 2 else 0

/-- Positivity of the active-block squared mass exposes a nonzero active entry.

This is the finite-support bridge used by the Cox--Higham pivoted route: a
source invariant may be stated as positive active-block mass, while the signed
Householder nonbreakdown theorem consumes an explicit nonzero entry. -/
theorem exists_active_entry_ne_of_householderActiveBlockNorm2Sq_pos
    {m n : ℕ} (p : Fin m) (k : Fin n) (A : Fin m → Fin n → ℝ)
    (hpos : 0 < householderActiveBlockNorm2Sq p k A) :
    ∃ l : Fin n, k.val ≤ l.val ∧
      ∃ i : Fin m, p.val ≤ i.val ∧ A i l ≠ 0 := by
  classical
  by_contra hno
  have hzero : ∀ i : Fin m, ∀ l : Fin n,
      p.val ≤ i.val → k.val ≤ l.val → A i l = 0 := by
    intro i l hi hl
    by_contra hne
    exact hno ⟨l, hl, i, hi, hne⟩
  have hsum :
      householderActiveBlockNorm2Sq p k A = 0 := by
    unfold householderActiveBlockNorm2Sq
    refine Finset.sum_eq_zero ?_
    intro i _hi
    refine Finset.sum_eq_zero ?_
    intro l _hl
    by_cases hrow : p.val ≤ i.val
    · by_cases hcol : k.val ≤ l.val
      · have hz := hzero i l hrow hcol
        simp [hrow, hcol, hz]
      · simp [hrow, hcol]
    · simp [hrow]
  rw [hsum] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- A nonzero active entry makes the active-block squared mass positive. -/
theorem householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne
    {m n : ℕ} (p : Fin m) (k : Fin n) (A : Fin m → Fin n → ℝ)
    (h :
      ∃ l : Fin n, k.val ≤ l.val ∧
        ∃ i : Fin m, p.val ≤ i.val ∧ A i l ≠ 0) :
    0 < householderActiveBlockNorm2Sq p k A := by
  classical
  obtain ⟨l, hl, i, hi, hne⟩ := h
  unfold householderActiveBlockNorm2Sq
  refine Finset.sum_pos' ?hnonneg ?hpos
  · intro r _hr
    refine Finset.sum_nonneg ?_
    intro c _hc
    by_cases hactive : p ≤ r ∧ k ≤ c
    · exact by
        simp [hactive, sq_nonneg]
    · simp [hactive]
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    refine Finset.sum_pos' ?hrow_nonneg ?hrow_pos
    · intro c _hc
      by_cases hactive : p ≤ i ∧ k ≤ c
      · exact by
          simp [hactive, sq_nonneg]
      · simp [hactive]
    · refine ⟨l, Finset.mem_univ l, ?_⟩
      have hactive : p ≤ i ∧ k ≤ l := ⟨hi, hl⟩
      have hsquare : 0 < A i l ^ 2 := sq_pos_of_ne_zero hne
      simpa [hactive] using hsquare

/-- A finite active column set has a column whose active trailing norm is
    maximal.

This is the local finite-order substrate for Cox--Higham column pivoting: at a
given column step `k`, one can choose a remaining column maximizing the trailing
Householder norm. -/
theorem exists_householderTrailingColumnNorm2Sq_active_max {m n : ℕ}
    (p : Fin m) (k : Fin n) (A : Fin m → Fin n → ℝ) :
    ∃ j : Fin n,
      k.val ≤ j.val ∧
        ∀ l : Fin n, k.val ≤ l.val →
          householderTrailingColumnNorm2Sq (m := m) (n := n) p A l ≤
            householderTrailingColumnNorm2Sq (m := m) (n := n) p A j := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun j => k.val ≤ j.val
  have hs : s.Nonempty := by
    refine ⟨k, ?_⟩
    simp [s]
  obtain ⟨j, hj, hmax⟩ :=
    Finset.exists_max_image s
      (fun j => householderTrailingColumnNorm2Sq (m := m) (n := n) p A j) hs
  refine ⟨j, ?_, ?_⟩
  · simpa [s] using hj
  · intro l hl
    have hl_fin : k ≤ l := by
      exact hl
    exact hmax l (by simpa [s] using hl_fin)

/-- A concrete finite max-pivot selector for active trailing column norms. -/
noncomputable def householderActiveMaxPivotColumn {m n : ℕ}
    (p : Fin m) (k : Fin n) (A : Fin m → Fin n → ℝ) : Fin n :=
  Classical.choose (exists_householderTrailingColumnNorm2Sq_active_max p k A)

/-- The finite max-pivot selector chooses a remaining column. -/
theorem householderActiveMaxPivotColumn_ge {m n : ℕ}
    (p : Fin m) (k : Fin n) (A : Fin m → Fin n → ℝ) :
    k.val ≤ (householderActiveMaxPivotColumn p k A).val :=
  (Classical.choose_spec
    (exists_householderTrailingColumnNorm2Sq_active_max p k A)).1

/-- The finite max-pivot selector maximizes the active trailing column norm
among remaining columns. -/
theorem householderActiveMaxPivotColumn_pivot_max {m n : ℕ}
    (p : Fin m) (k : Fin n) (A : Fin m → Fin n → ℝ) :
    ∀ l : Fin n, k.val ≤ l.val →
      householderTrailingColumnNorm2Sq (m := m) (n := n) p A l ≤
        householderTrailingColumnNorm2Sq
          (m := m) (n := n) p A (householderActiveMaxPivotColumn p k A) :=
  (Classical.choose_spec
    (exists_householderTrailingColumnNorm2Sq_active_max p k A)).2

/-- Swap two columns of a rectangular matrix.

This is the one-step sorting primitive for the Cox--Higham pivoted route: after
choosing an active max column, swap it into the displayed active position before
forming the signed Householder reflector. -/
def householderSwapColumns {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a b : Fin n) : Fin m → Fin n → ℝ :=
  fun i j => if j = a then A i b else if j = b then A i a else A i j

/-- After swapping columns `a` and `b`, the displayed column `a` has the old
active trailing norm of column `b`. -/
theorem householderTrailingColumnNorm2Sq_swapColumns_left {m n : ℕ}
    (p : Fin m) (A : Fin m → Fin n → ℝ) (a b : Fin n) :
    householderTrailingColumnNorm2Sq (m := m) (n := n) p
        (householderSwapColumns A a b) a =
      householderTrailingColumnNorm2Sq (m := m) (n := n) p A b := by
  simp [householderTrailingColumnNorm2Sq, householderSwapColumns]

/-- After swapping columns `a` and `b`, a column different from both keeps its
active trailing norm. -/
theorem householderTrailingColumnNorm2Sq_swapColumns_of_ne {m n : ℕ}
    (p : Fin m) (A : Fin m → Fin n → ℝ) (a b j : Fin n)
    (hja : j ≠ a) (hjb : j ≠ b) :
    householderTrailingColumnNorm2Sq (m := m) (n := n) p
        (householderSwapColumns A a b) j =
      householderTrailingColumnNorm2Sq (m := m) (n := n) p A j := by
  simp [householderTrailingColumnNorm2Sq, householderSwapColumns, hja, hjb]

/-- Swapping the finite active max-pivot column into the displayed active
position makes the displayed column pivot-maximal on the active suffix.

This is the concrete one-step sorting-policy bridge missing from the
Cox--Higham route: the active max selector is applied before the swap, and the
post-swap matrix satisfies the raw pivot-max field consumed by the exact
signed-pivot Householder step. -/
theorem householderSwapColumns_activeMaxPivotColumn_pivot_max {m n : ℕ}
    (p : Fin m) (k : Fin n) (A : Fin m → Fin n → ℝ) :
    ∀ l : Fin n, k.val ≤ l.val →
      householderTrailingColumnNorm2Sq (m := m) (n := n) p
          (householderSwapColumns A k (householderActiveMaxPivotColumn p k A)) l ≤
        householderTrailingColumnNorm2Sq (m := m) (n := n) p
          (householderSwapColumns A k (householderActiveMaxPivotColumn p k A)) k := by
  intro l hl
  let q : Fin n := householderActiveMaxPivotColumn p k A
  have hright :
      householderTrailingColumnNorm2Sq (m := m) (n := n) p
          (householderSwapColumns A k q) k =
        householderTrailingColumnNorm2Sq (m := m) (n := n) p A q :=
    householderTrailingColumnNorm2Sq_swapColumns_left p A k q
  by_cases hlk : l = k
  · subst l
    exact le_rfl
  · by_cases hlq : l = q
    · subst l
      have hqk : ¬ q = k := by
        intro h
        exact hlk h
      have hleft :
          householderTrailingColumnNorm2Sq (m := m) (n := n) p
              (householderSwapColumns A k q) q =
            householderTrailingColumnNorm2Sq (m := m) (n := n) p A k := by
        simp [householderTrailingColumnNorm2Sq, householderSwapColumns, hqk]
      have hmax :
          householderTrailingColumnNorm2Sq (m := m) (n := n) p A k ≤
            householderTrailingColumnNorm2Sq (m := m) (n := n) p A q :=
        householderActiveMaxPivotColumn_pivot_max p k A k le_rfl
      simpa [q, hleft, hright] using hmax
    · have hleft :
          householderTrailingColumnNorm2Sq (m := m) (n := n) p
              (householderSwapColumns A k q) l =
            householderTrailingColumnNorm2Sq (m := m) (n := n) p A l := by
        simp [householderTrailingColumnNorm2Sq, householderSwapColumns, hlk, hlq]
      have hmax :
          householderTrailingColumnNorm2Sq (m := m) (n := n) p A l ≤
            householderTrailingColumnNorm2Sq (m := m) (n := n) p A q :=
      householderActiveMaxPivotColumn_pivot_max p k A l hl
      simpa [q, hleft, hright] using hmax

/-- Swapping two columns inside the active suffix preserves positivity of the
active-block squared mass.

This is the nonbreakdown companion to the swapped pivot-policy theorem: if the
raw active block has positive mass and the selected column lies in the active
suffix, then the displayed post-swap active block also has positive mass. -/
theorem householderActiveBlockNorm2Sq_swapColumns_pos_of_pos {m n : ℕ}
    (p : Fin m) (k q : Fin n) (A : Fin m → Fin n → ℝ)
    (hq : k.val ≤ q.val)
    (hpos : 0 < householderActiveBlockNorm2Sq p k A) :
    0 < householderActiveBlockNorm2Sq p k (householderSwapColumns A k q) := by
  classical
  obtain ⟨l, hl, i, hi, hne⟩ :=
    exists_active_entry_ne_of_householderActiveBlockNorm2Sq_pos p k A hpos
  refine
    householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne
      p k (householderSwapColumns A k q) ?_
  by_cases hlk : l = k
  · subst l
    refine ⟨q, hq, i, hi, ?_⟩
    by_cases hqk : q = k
    · subst q
      simpa [householderSwapColumns] using hne
    · simpa [householderSwapColumns, hqk] using hne
  · by_cases hlq : l = q
    · subst l
      refine ⟨k, le_rfl, i, hi, ?_⟩
      simpa [householderSwapColumns, hlk] using hne
    · refine ⟨l, hl, i, hi, ?_⟩
      simpa [householderSwapColumns, hlk, hlq] using hne

/-- A trailing-column norm is positive as soon as some active trailing entry is
    nonzero.

    This is the elementary bridge needed before a rank/nonbreakdown theorem:
    rank or conditioning should provide a nonzero entry in the current trailing
    column; this lemma converts that witness into the positive squared norm used
    by the Householder sign-choice nonbreakdown theorem. -/
theorem householderTrailingNorm2Sq_pos_of_exists_ne
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ)
    (h : ∃ i : Fin n, p.val ≤ i.val ∧ x i ≠ 0) :
    0 < householderTrailingNorm2Sq n p x := by
  classical
  obtain ⟨i, hpi, hxi⟩ := h
  unfold householderTrailingNorm2Sq vecNorm2Sq
  refine Finset.sum_pos' ?hnonneg ?hpos
  · intro j _
    simpa [pow_two] using
      mul_self_nonneg (householderTrailingPart n p x j)
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    have hnot : ¬ i.val < p.val := Nat.not_lt.mpr hpi
    simpa [householderTrailingPart, hnot, pow_two] using
      (mul_self_pos.mpr hxi)

/-- A nonzero pivot entry is a special case of
    `householderTrailingNorm2Sq_pos_of_exists_ne`. -/
theorem householderTrailingNorm2Sq_pos_of_pivot_ne_zero
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ)
    (hp : x p ≠ 0) :
    0 < householderTrailingNorm2Sq n p x :=
  householderTrailingNorm2Sq_pos_of_exists_ne n p x ⟨p, le_rfl, hp⟩

/-- A column chosen with maximal active trailing norm has positive active norm
as soon as some remaining active column has positive active norm.

This is the local nonbreakdown bridge for column-pivoted Cox--Higham steps:
the pivot-max condition converts any nonzero active mass in the remaining block
into the positive pivot-column norm required by the signed Householder step. -/
theorem householderTrailingColumnNorm2Sq_pos_of_pivot_max_exists_pos
    {m n : ℕ} (p : Fin m) (k pivotCol : Fin n)
    (A : Fin m → Fin n → ℝ)
    (hpivotMax :
      ∀ l : Fin n, k.val ≤ l.val →
        householderTrailingColumnNorm2Sq (m := m) (n := n) p A l ≤
          householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol)
    (hexists :
      ∃ l : Fin n, k.val ≤ l.val ∧
        0 < householderTrailingColumnNorm2Sq (m := m) (n := n) p A l) :
    0 < householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol := by
  obtain ⟨l, hl, hpos⟩ := hexists
  exact lt_of_lt_of_le hpos (hpivotMax l hl)

/-- Active-entry version of
`householderTrailingColumnNorm2Sq_pos_of_pivot_max_exists_pos`.

It is often easier for a concrete loop invariant to state that some entry in
the remaining active block is nonzero; this lemma converts that witness into
positive norm for the pivot column selected by a column-pivoting/maximality
condition. -/
theorem householderTrailingColumnNorm2Sq_pos_of_pivot_max_exists_active_entry_ne
    {m n : ℕ} (p : Fin m) (k pivotCol : Fin n)
    (A : Fin m → Fin n → ℝ)
    (hpivotMax :
      ∀ l : Fin n, k.val ≤ l.val →
        householderTrailingColumnNorm2Sq (m := m) (n := n) p A l ≤
          householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol)
    (hexists :
      ∃ l : Fin n, k.val ≤ l.val ∧
        ∃ i : Fin m, p.val ≤ i.val ∧ A i l ≠ 0) :
    0 < householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol := by
  obtain ⟨l, hl, i, hpi, hne⟩ := hexists
  exact
    householderTrailingColumnNorm2Sq_pos_of_pivot_max_exists_pos
      p k pivotCol A hpivotMax
      ⟨l, hl, by
        simpa [householderTrailingColumnNorm2Sq] using
          householderTrailingNorm2Sq_pos_of_exists_ne
            m p (fun r => A r l) ⟨i, hpi, hne⟩⟩

/-- A two-entry active column with zero pivot but nonzero trailing norm.

    This counterexample records a failed red-bottleneck route: Householder
    nonbreakdown of the active trailing column does not imply that the current
    unpivoted leading entry is nonzero. -/
noncomputable def householderTrailingPivotCounterexample2 : Fin 2 → ℝ :=
  fun i => if i.val = 0 then 0 else 1

theorem householderTrailingPivotCounterexample2_pivot_zero :
    householderTrailingPivotCounterexample2 ⟨0, by decide⟩ = 0 := by
  simp [householderTrailingPivotCounterexample2]

theorem householderTrailingPivotCounterexample2_trailingNorm2Sq_pos :
    0 <
      householderTrailingNorm2Sq 2 ⟨0, by decide⟩
        householderTrailingPivotCounterexample2 := by
  refine
    householderTrailingNorm2Sq_pos_of_exists_ne 2 ⟨0, by decide⟩
      householderTrailingPivotCounterexample2 ?_
  refine ⟨⟨1, by decide⟩, by simp, ?_⟩
  simp [householderTrailingPivotCounterexample2]

theorem not_forall_trailingNorm2Sq_pos_implies_pivot_ne_zero :
    ¬ ∀ x : Fin 2 → ℝ,
        0 < householderTrailingNorm2Sq 2 ⟨0, by decide⟩ x →
          x ⟨0, by decide⟩ ≠ 0 := by
  intro h
  exact
    h householderTrailingPivotCounterexample2
      householderTrailingPivotCounterexample2_trailingNorm2Sq_pos
      householderTrailingPivotCounterexample2_pivot_zero

/-- If `alpha^2` is the squared trailing-column norm, then `|alpha|` is the
    square root of that norm.  This exposes the scalar lower bound needed by
    the stored QR nonbreakdown budget condition `budget_k < |alpha_k|`. -/
theorem abs_alpha_eq_sqrt_trailingNorm2Sq
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ) (alpha : ℝ)
    (halpha : alpha * alpha = householderTrailingNorm2Sq n p x) :
    |alpha| = Real.sqrt (householderTrailingNorm2Sq n p x) := by
  have hpow : alpha ^ 2 = householderTrailingNorm2Sq n p x := by
    simpa [pow_two] using halpha
  exact (Real.sqrt_sq_eq_abs alpha).symm.trans (congrArg Real.sqrt hpow)

/-- A square-root trailing-norm budget is exactly the stored QR scalar
    nonbreakdown budget once `alpha^2 = ||x_tail||_2^2`. -/
theorem budget_lt_abs_alpha_of_lt_sqrt_trailingNorm2Sq
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ) (alpha budget : ℝ)
    (halpha : alpha * alpha = householderTrailingNorm2Sq n p x)
    (hbudget : budget < Real.sqrt (householderTrailingNorm2Sq n p x)) :
    budget < |alpha| := by
  simpa [abs_alpha_eq_sqrt_trailingNorm2Sq n p x alpha halpha] using hbudget

/-- Nonnegativity of the trailing squared norm. -/
theorem householderTrailingNorm2Sq_nonneg
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ) :
    0 ≤ householderTrailingNorm2Sq n p x := by
  simpa [householderTrailingNorm2Sq] using
    vecNorm2Sq_nonneg (householderTrailingPart n p x)

/-- A nonnegative budget strictly below the square root of the trailing squared
    norm forces that trailing squared norm to be positive. -/
theorem householderTrailingNorm2Sq_pos_of_nonneg_budget_lt_sqrt
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ) (budget : ℝ)
    (hbudget_nonneg : 0 ≤ budget)
    (hbudget : budget < Real.sqrt (householderTrailingNorm2Sq n p x)) :
    0 < householderTrailingNorm2Sq n p x := by
  have hsqrt_pos : 0 < Real.sqrt (householderTrailingNorm2Sq n p x) :=
    lt_of_le_of_lt hbudget_nonneg hbudget
  have hsq_pos :
      0 < (Real.sqrt (householderTrailingNorm2Sq n p x)) ^ 2 :=
    sq_pos_of_pos hsqrt_pos
  rw [Real.sq_sqrt (householderTrailingNorm2Sq_nonneg n p x)] at hsq_pos
  exact hsq_pos

/-- Source-style signed Householder scalar.

    With `norm = ||x_tail||_2`, this chooses the sign opposite to the pivot
    entry, so the Householder denominator nonbreakdown condition follows from
    algebra rather than a separate sign hypothesis. -/
noncomputable def signedHouseholderAlpha (norm pivot : ℝ) : ℝ :=
  if 0 ≤ pivot then -norm else norm

/-- The signed Householder scalar has the requested squared magnitude. -/
theorem signedHouseholderAlpha_sq (norm pivot : ℝ) :
    signedHouseholderAlpha norm pivot *
      signedHouseholderAlpha norm pivot = norm * norm := by
  unfold signedHouseholderAlpha
  by_cases hp : 0 ≤ pivot
  · simp [hp]
  · simp [hp]

/-- The signed Householder scalar has nonpositive product with the pivot. -/
theorem signedHouseholderAlpha_mul_pivot_nonpos {norm pivot : ℝ}
    (hnorm : 0 ≤ norm) :
    signedHouseholderAlpha norm pivot * pivot ≤ 0 := by
  by_cases hp : 0 ≤ pivot
  · have hmul : 0 ≤ norm * pivot := mul_nonneg hnorm hp
    simpa [signedHouseholderAlpha, hp, neg_mul] using
      (neg_nonpos.mpr hmul)
  · have hp_nonpos : pivot ≤ 0 := le_of_not_ge hp
    exact
      (by
        simpa [signedHouseholderAlpha, hp] using
          mul_nonpos_of_nonneg_of_nonpos hnorm hp_nonpos)

/-- The signed Householder scalar specialized to the trailing norm has exactly
    the trailing squared norm as its square. -/
theorem signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ) :
    signedHouseholderAlpha
        (Real.sqrt (householderTrailingNorm2Sq n p x)) (x p) *
      signedHouseholderAlpha
        (Real.sqrt (householderTrailingNorm2Sq n p x)) (x p) =
        householderTrailingNorm2Sq n p x := by
  rw [signedHouseholderAlpha_sq]
  exact Real.mul_self_sqrt (householderTrailingNorm2Sq_nonneg n p x)

/-- The trailing-norm specialization satisfies the source Householder
    sign-choice inequality. -/
theorem signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ) :
    signedHouseholderAlpha
        (Real.sqrt (householderTrailingNorm2Sq n p x)) (x p) * x p ≤ 0 :=
  signedHouseholderAlpha_mul_pivot_nonpos (Real.sqrt_nonneg _)

/-- Any active trailing entry is bounded by the square root of the trailing
    squared norm.

    This is the quantitative companion to
    `householderTrailingNorm2Sq_pos_of_exists_ne`: a future rank or
    nonbreakdown invariant may provide a concrete lower bound on one active
    trailing entry, and this lemma turns it into the square-root norm lower
    bound consumed by the stored QR budget route. -/
theorem abs_entry_le_sqrt_householderTrailingNorm2Sq_of_pivot_le
    (n : ℕ) (p i : Fin n) (x : Fin n → ℝ)
    (hpi : p.val ≤ i.val) :
    |x i| ≤ Real.sqrt (householderTrailingNorm2Sq n p x) := by
  have hcoord :
      |householderTrailingPart n p x i| ≤
        vecNorm2 (householderTrailingPart n p x) :=
    abs_coord_le_vecNorm2 (householderTrailingPart n p x) i
  have hnot : ¬ i.val < p.val := Nat.not_lt.mpr hpi
  simpa [vecNorm2, householderTrailingNorm2Sq, householderTrailingPart,
    hnot] using hcoord

/-- If the rounded update budget is below one concrete active trailing entry,
    then it is below the square root of the full trailing squared norm. -/
theorem budget_lt_sqrt_householderTrailingNorm2Sq_of_lt_abs_active_entry
    (n : ℕ) (p i : Fin n) (x : Fin n → ℝ) (budget : ℝ)
    (hpi : p.val ≤ i.val)
    (hbudget : budget < |x i|) :
    budget < Real.sqrt (householderTrailingNorm2Sq n p x) :=
  lt_of_lt_of_le hbudget
    (abs_entry_le_sqrt_householderTrailingNorm2Sq_of_pivot_le n p i x hpi)

/-- If the trailing squared norm is larger than `n * budget^2`, then some
    active trailing entry exceeds the budget in absolute value.

    This is the finite-dimensional pigeonhole bridge used by the QR bottleneck:
    a future conditioning or nonbreakdown invariant can supply the norm-square
    margin, and this lemma converts it into the concrete active-entry lower
    bound consumed by the stored QR nonbreakdown route. -/
theorem exists_active_entry_budget_lt_abs_of_dim_mul_budget_sq_lt_trailingNorm2Sq
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ) (budget : ℝ)
    (hbudget_nonneg : 0 ≤ budget)
    (hmargin : (n : ℝ) * budget ^ 2 <
      householderTrailingNorm2Sq n p x) :
    ∃ i : Fin n, p.val ≤ i.val ∧ budget < |x i| := by
  classical
  by_contra hnone
  have hle_abs : ∀ i : Fin n, p.val ≤ i.val → |x i| ≤ budget := by
    intro i hpi
    exact le_of_not_gt (fun hlt => hnone ⟨i, hpi, hlt⟩)
  have hupper :
      householderTrailingNorm2Sq n p x ≤ (n : ℝ) * budget ^ 2 := by
    unfold householderTrailingNorm2Sq vecNorm2Sq
    calc
      ∑ i : Fin n, householderTrailingPart n p x i ^ 2
          ≤ ∑ _i : Fin n, budget ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro i _
            by_cases hi : i.val < p.val
            · simpa [householderTrailingPart, hi] using sq_nonneg budget
            · have hpi : p.val ≤ i.val := Nat.le_of_not_gt hi
              have habs : |x i| ≤ budget := hle_abs i hpi
              have hsquare : x i ^ 2 ≤ budget ^ 2 := by
                have hxabs : |x i| ^ 2 = x i ^ 2 := by
                  simp [pow_two]
                nlinarith [habs, abs_nonneg (x i), hbudget_nonneg, hxabs]
              simpa [householderTrailingPart, hi] using hsquare
      _ = (n : ℝ) * budget ^ 2 := by simp
  exact not_lt_of_ge hupper hmargin

/-- A dimensioned trailing-norm-square margin directly gives the square-root
    budget used by the stored QR pivot nonbreakdown route. -/
theorem budget_lt_sqrt_householderTrailingNorm2Sq_of_dim_mul_budget_sq_lt_trailingNorm2Sq
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ) (budget : ℝ)
    (hbudget_nonneg : 0 ≤ budget)
    (hmargin : (n : ℝ) * budget ^ 2 <
      householderTrailingNorm2Sq n p x) :
    budget < Real.sqrt (householderTrailingNorm2Sq n p x) := by
  rcases
    exists_active_entry_budget_lt_abs_of_dim_mul_budget_sq_lt_trailingNorm2Sq
      n p x budget hbudget_nonneg hmargin with
    ⟨i, hpi, hbudget_i⟩
  exact
    budget_lt_sqrt_householderTrailingNorm2Sq_of_lt_abs_active_entry
      n p i x budget hpi hbudget_i

/-- QR trailing active vector: it has a zero prefix and equals
    `x - alpha e_p` on the trailing rows. -/
noncomputable def householderTrailingActiveVector (n : ℕ) (p : Fin n)
    (x : Fin n → ℝ) (alpha : ℝ) : Fin n → ℝ :=
  householderActiveVector n p (householderTrailingPart n p x) alpha

/-- The prefix/trailing split reconstructs the original vector. -/
theorem householderPrefixPart_add_trailingPart (n : ℕ) (p : Fin n)
    (x : Fin n → ℝ) :
    (fun i => householderPrefixPart n p x i +
      householderTrailingPart n p x i) = x := by
  ext i
  by_cases hi : i.val < p.val
  · simp [householderPrefixPart, householderTrailingPart, hi]
  · simp [householderPrefixPart, householderTrailingPart, hi]

/-- The prefix part is supported before the pivot. -/
theorem householderPrefixPart_support (n : ℕ) (p : Fin n)
    (x : Fin n → ℝ) :
    ∀ i : Fin n, p.val ≤ i.val → householderPrefixPart n p x i = 0 := by
  intro i hi
  have hnot : ¬ i.val < p.val := Nat.not_lt.mpr hi
  simp [householderPrefixPart, hnot]

/-- The QR trailing active vector has the required zero prefix. -/
theorem householderTrailingActiveVector_zero_prefix (n : ℕ) (p : Fin n)
    (x : Fin n → ℝ) (alpha : ℝ) :
    ∀ i : Fin n, i.val < p.val →
      householderTrailingActiveVector n p x alpha i = 0 := by
  intro i hi
  have hip : i ≠ p := by
    intro h
    subst i
    exact Nat.lt_irrefl p.val hi
  simp [householderTrailingActiveVector, householderActiveVector,
    householderTrailingPart, hi, hip]

/-- The trailing active Householder vector has nonzero squared norm whenever
    the active pivot entry is not equal to the chosen `alpha`.

    This is the scalar nonbreakdown condition for the denominator
    `vᵀv`: it avoids hiding the denominator hypothesis behind the sum of
    squares. -/
theorem householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ) (alpha : ℝ)
    (hpivot : x p ≠ alpha) :
    (∑ i : Fin n,
      householderTrailingActiveVector n p x alpha i *
        householderTrailingActiveVector n p x alpha i) ≠ 0 := by
  classical
  let v : Fin n → ℝ := householderTrailingActiveVector n p x alpha
  intro hsum
  have hsq : vecNorm2Sq v = 0 := by
    simpa [v, vecNorm2Sq, pow_two] using hsum
  have hnorm : vecNorm2 v = 0 := by
    unfold vecNorm2
    rw [hsq]
    simp
  have hvp := (vecNorm2_eq_zero_iff v).mp hnorm p
  have hnot_lt : ¬ p.val < p.val := Nat.lt_irrefl p.val
  have hsub : x p - alpha = 0 := by
    simpa [v, householderTrailingActiveVector, householderActiveVector,
      householderTrailingPart, hnot_lt] using hvp
  exact hpivot (sub_eq_zero.mp hsub)

/-- The standard Householder sign choice gives the scalar pivot
    nonbreakdown condition.

    If `alpha^2` is the squared norm of the trailing pivot column and `alpha`
    is chosen so that `alpha * x_p <= 0`, then a positive trailing norm forces
    `x_p != alpha`.  This is the small algebraic bridge used before any
    rank/conditioning theorem: rank should prove the positive trailing norm,
    while the sign convention proves the denominator side condition. -/
theorem householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ) (alpha : ℝ)
    (halpha : alpha * alpha = householderTrailingNorm2Sq n p x)
    (hnorm : 0 < householderTrailingNorm2Sq n p x)
    (hsign : alpha * x p ≤ 0) :
    x p ≠ alpha := by
  intro h
  rw [h] at hsign
  have hsqpos : 0 < alpha * alpha := by
    simpa [halpha]
  nlinarith

/-- Denominator nonbreakdown from the standard Householder sign convention and
    a positive trailing-column norm. -/
theorem householderTrailingActiveVector_inner_self_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ) (alpha : ℝ)
    (halpha : alpha * alpha = householderTrailingNorm2Sq n p x)
    (hnorm : 0 < householderTrailingNorm2Sq n p x)
    (hsign : alpha * x p ≤ 0) :
    (∑ i : Fin n,
      householderTrailingActiveVector n p x alpha i *
        householderTrailingActiveVector n p x alpha i) ≠ 0 := by
  exact householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha
    n p x alpha
    (householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos
      n p x alpha halpha hnorm hsign)

/-- Inner product of the active Householder vector with the active column. -/
lemma householderActiveVector_inner_x (n : ℕ) (p : Fin n)
    (x : Fin n → ℝ) (alpha : ℝ) :
    (∑ i : Fin n, householderActiveVector n p x alpha i * x i) =
      vecNorm2Sq x - alpha * x p := by
  unfold householderActiveVector vecNorm2Sq
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · simp [pow_two]
  · simp

/-- Squared norm of the active Householder vector. -/
lemma householderActiveVector_inner_self (n : ℕ) (p : Fin n)
    (x : Fin n → ℝ) (alpha : ℝ) :
    (∑ i : Fin n, householderActiveVector n p x alpha i *
        householderActiveVector n p x alpha i) =
      vecNorm2Sq x - 2 * alpha * x p + alpha * alpha := by
  unfold householderActiveVector vecNorm2Sq
  have hterm : ∀ i : Fin n,
      (x i - (if i = p then alpha else 0)) *
          (x i - (if i = p then alpha else 0)) =
        x i * x i - 2 * (if i = p then alpha else 0) * x i +
          (if i = p then alpha else 0) * (if i = p then alpha else 0) := by
    intro i
    by_cases h : i = p
    · simp [h]
      have hone : ((Nat.rawCast 1 : ℝ) = 1) := by norm_num
      nlinarith
    · simp [h]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp
  ring_nf

/-- Cox--Higham denominator lower bound for the signed Householder vector.

    If `alpha^2` is the trailing-column squared norm and the sign is chosen so
    that `alpha * x_p <= 0`, then the active Householder denominator is at
    least twice the trailing squared norm.  This is the local algebra behind
    Cox--Higham Lemma 2.1 / equation (2.5) before pivoting is used to compare
    against other columns. -/
theorem householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_of_mul_nonpos
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ) (alpha : ℝ)
    (halpha : alpha * alpha = householderTrailingNorm2Sq n p x)
    (hsign : alpha * x p ≤ 0) :
    2 * householderTrailingNorm2Sq n p x ≤
      ∑ i : Fin n,
        householderTrailingActiveVector n p x alpha i *
          householderTrailingActiveVector n p x alpha i := by
  let xTail := householderTrailingPart n p x
  have htail_p : xTail p = x p := by
    simp [xTail, householderTrailingPart]
  have hsum :
      (∑ i : Fin n,
        householderTrailingActiveVector n p x alpha i *
          householderTrailingActiveVector n p x alpha i) =
        vecNorm2Sq xTail - 2 * alpha * xTail p + alpha * alpha := by
    simpa [xTail, householderTrailingActiveVector] using
      householderActiveVector_inner_self n p xTail alpha
  have halpha_tail : alpha * alpha = vecNorm2Sq xTail := by
    simpa [xTail, householderTrailingNorm2Sq] using halpha
  rw [hsum, htail_p, halpha_tail]
  have hnorm_eq :
      householderTrailingNorm2Sq n p x = vecNorm2Sq xTail := by
    simp [xTail, householderTrailingNorm2Sq]
  rw [hnorm_eq]
  nlinarith

/-- Signed-alpha specialization of
    `householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_of_mul_nonpos`. -/
theorem householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_signed
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ) :
    2 * householderTrailingNorm2Sq n p x ≤
      ∑ i : Fin n,
        householderTrailingActiveVector n p x
            (signedHouseholderAlpha
              (Real.sqrt (householderTrailingNorm2Sq n p x)) (x p)) i *
          householderTrailingActiveVector n p x
            (signedHouseholderAlpha
              (Real.sqrt (householderTrailingNorm2Sq n p x)) (x p)) i := by
  exact
    householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_of_mul_nonpos
      n p x
      (signedHouseholderAlpha
        (Real.sqrt (householderTrailingNorm2Sq n p x)) (x p))
      (signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq n p x)
      (signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos n p x)

/-- Cox--Higham column-pivoting comparison in Cauchy--Schwarz form.

If the active trailing norm of `y` is bounded by the active trailing norm of the
pivot column `x`, then the inner product of the signed Householder vector for
`x` with the active part of `y` is bounded by `||v||₂ ||x_tail||₂`. -/
theorem abs_inner_householderTrailingActiveVector_trailingPart_le_vecNorm2_mul_sqrt
    (n : ℕ) (p : Fin n) (x y : Fin n → ℝ) (alpha : ℝ)
    (hle : householderTrailingNorm2Sq n p y ≤ householderTrailingNorm2Sq n p x) :
    |∑ i : Fin n,
        householderTrailingActiveVector n p x alpha i *
          householderTrailingPart n p y i| ≤
      vecNorm2 (householderTrailingActiveVector n p x alpha) *
        Real.sqrt (householderTrailingNorm2Sq n p x) := by
  let v := householderTrailingActiveVector n p x alpha
  let yTail := householderTrailingPart n p y
  have hcs :
      |∑ i : Fin n, v i * yTail i| ≤ vecNorm2 v * vecNorm2 yTail :=
    abs_vecInnerProduct_le_vecNorm2_mul v yTail
  have htail_le :
      vecNorm2 yTail ≤ Real.sqrt (householderTrailingNorm2Sq n p x) := by
    simpa [vecNorm2, yTail, householderTrailingNorm2Sq] using
      Real.sqrt_le_sqrt hle
  have hmul :
      vecNorm2 v * vecNorm2 yTail ≤
        vecNorm2 v * Real.sqrt (householderTrailingNorm2Sq n p x) :=
    mul_le_mul_of_nonneg_left htail_le (vecNorm2_nonneg v)
  simpa [v, yTail] using hcs.trans hmul

/-- Column-pivoting specialization of the active-vector comparison.

The hypothesis says column `k` is chosen with maximal active trailing norm among
the remaining columns.  Then every remaining column `j` satisfies the
Cauchy--Schwarz comparison used in the Cox--Higham row-wise QR route. -/
theorem abs_inner_householderTrailingActiveVector_column_le_vecNorm2_mul_sqrt_of_pivot_max
    {m n : ℕ} (p : Fin m) (k j : Fin n) (A : Fin m → Fin n → ℝ)
    (alpha : ℝ)
    (hpivot :
      ∀ l : Fin n, k.val ≤ l.val →
        householderTrailingColumnNorm2Sq (m := m) (n := n) p A l ≤
          householderTrailingColumnNorm2Sq (m := m) (n := n) p A k)
    (hj : k.val ≤ j.val) :
    |∑ i : Fin m,
        householderTrailingActiveVector m p (fun r => A r k) alpha i *
          householderTrailingPart m p (fun r => A r j) i| ≤
      vecNorm2 (householderTrailingActiveVector m p (fun r => A r k) alpha) *
        Real.sqrt (householderTrailingColumnNorm2Sq (m := m) (n := n) p A k) := by
  exact
    abs_inner_householderTrailingActiveVector_trailingPart_le_vecNorm2_mul_sqrt
      m p (fun r => A r k) (fun r => A r j) alpha (hpivot j hj)

/-- Scalar arithmetic behind the Cox--Higham `sqrt 2` bound.

If `S` is the Householder denominator, `T` is the pivot-column trailing norm
squared, `2T <= S`, and an inner product is bounded by `sqrt S * sqrt T`,
then multiplying by the exact Householder coefficient `2/S` gives a `sqrt 2`
bound. -/
lemma abs_two_div_mul_le_sqrt_two_of_abs_le_sqrt_mul_sqrt {S T inner : ℝ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hden : 2 * T ≤ S)
    (hinner : |inner| ≤ Real.sqrt S * Real.sqrt T) :
    |(2 / S) * inner| ≤ Real.sqrt 2 := by
  by_cases hSzero : S = 0
  · have hTzero : T = 0 := by nlinarith
    have hinner0 : inner = 0 := by
      have hle0 : |inner| ≤ 0 := by
        simpa [hSzero, hTzero] using hinner
      exact abs_eq_zero.mp (le_antisymm hle0 (abs_nonneg inner))
    simp [hSzero, hinner0]
  · have hSpos : 0 < S := lt_of_le_of_ne' hS hSzero
    have hcoef_nonneg : 0 ≤ 2 / S := div_nonneg (by norm_num) hS
    have hleft :
        |(2 / S) * inner| ≤ (2 / S) * (Real.sqrt S * Real.sqrt T) := by
      rw [abs_mul, abs_of_nonneg hcoef_nonneg]
      exact mul_le_mul_of_nonneg_left hinner hcoef_nonneg
    have htarget : (2 / S) * (Real.sqrt S * Real.sqrt T) ≤ Real.sqrt 2 := by
      apply Real.le_sqrt_of_sq_le
      have hsq :
          ((2 / S) * (Real.sqrt S * Real.sqrt T)) ^ 2 = 4 * T / S := by
        rw [show ((2 / S) * (Real.sqrt S * Real.sqrt T)) ^ 2 =
            (2 / S) ^ 2 * ((Real.sqrt S) ^ 2 * (Real.sqrt T) ^ 2) by ring]
        rw [Real.sq_sqrt hS, Real.sq_sqrt hT]
        field_simp [ne_of_gt hSpos]
        ring
      rw [hsq]
      exact (div_le_iff₀ hSpos).mpr (by nlinarith)
    exact hleft.trans htarget

/-- Cox--Higham Lemma 2.1 in scalar form.

For the source Householder sign convention, if the pivot column has at least
the active trailing norm of `y`, then the exact Householder update scalar
`beta * v^T y` is bounded by `sqrt 2`. -/
theorem abs_householderBeta_mul_inner_trailingPart_le_sqrt_two_of_mul_nonpos
    (n : ℕ) (p : Fin n) (x y : Fin n → ℝ) (alpha : ℝ)
    (halpha : alpha * alpha = householderTrailingNorm2Sq n p x)
    (hsign : alpha * x p ≤ 0)
    (hle : householderTrailingNorm2Sq n p y ≤ householderTrailingNorm2Sq n p x) :
    |householderBetaSpec n (householderTrailingActiveVector n p x alpha) *
        (∑ i : Fin n,
          householderTrailingActiveVector n p x alpha i *
            householderTrailingPart n p y i)| ≤
      Real.sqrt 2 := by
  let v := householderTrailingActiveVector n p x alpha
  let T := householderTrailingNorm2Sq n p x
  let inner := ∑ i : Fin n, v i * householderTrailingPart n p y i
  let S := ∑ i : Fin n, v i * v i
  have hS_nonneg : 0 ≤ S := by
    simpa [S, vecNorm2Sq, pow_two] using (vecNorm2Sq_nonneg v)
  have hT_nonneg : 0 ≤ T := by
    simpa [T, householderTrailingNorm2Sq] using
      (vecNorm2Sq_nonneg (householderTrailingPart n p x))
  have hden : 2 * T ≤ S := by
    simpa [S, T, v] using
      householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_of_mul_nonpos
        n p x alpha halpha hsign
  have hinner :
      |inner| ≤ Real.sqrt S * Real.sqrt T := by
    simpa [inner, S, T, v, vecNorm2, vecNorm2Sq, pow_two] using
      abs_inner_householderTrailingActiveVector_trailingPart_le_vecNorm2_mul_sqrt
        n p x y alpha hle
  simpa [householderBetaSpec, S, inner, v] using
    abs_two_div_mul_le_sqrt_two_of_abs_le_sqrt_mul_sqrt
      hS_nonneg hT_nonneg hden hinner

/-- Signed-alpha specialization of the Cox--Higham scalar `sqrt 2` bound. -/
theorem abs_householderBeta_mul_inner_trailingPart_le_sqrt_two_signed
    (n : ℕ) (p : Fin n) (x y : Fin n → ℝ)
    (hle : householderTrailingNorm2Sq n p y ≤ householderTrailingNorm2Sq n p x) :
    |householderBetaSpec n
        (householderTrailingActiveVector n p x
          (signedHouseholderAlpha
            (Real.sqrt (householderTrailingNorm2Sq n p x)) (x p))) *
        (∑ i : Fin n,
          householderTrailingActiveVector n p x
              (signedHouseholderAlpha
                (Real.sqrt (householderTrailingNorm2Sq n p x)) (x p)) i *
            householderTrailingPart n p y i)| ≤
      Real.sqrt 2 := by
  exact
    abs_householderBeta_mul_inner_trailingPart_le_sqrt_two_of_mul_nonpos
      n p x y
      (signedHouseholderAlpha
        (Real.sqrt (householderTrailingNorm2Sq n p x)) (x p))
      (signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq n p x)
      (signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos n p x)
      hle

/-- Column-pivoting specialization of Cox--Higham Lemma 2.1.

If column `k` maximizes the active trailing norm among remaining columns, then
the exact Householder update scalar for every remaining column is bounded by
`sqrt 2`. -/
theorem abs_householderBeta_mul_inner_column_le_sqrt_two_of_signed_pivot_max
    {m n : ℕ} (p : Fin m) (k j : Fin n) (A : Fin m → Fin n → ℝ)
    (hpivot :
      ∀ l : Fin n, k.val ≤ l.val →
        householderTrailingColumnNorm2Sq (m := m) (n := n) p A l ≤
          householderTrailingColumnNorm2Sq (m := m) (n := n) p A k)
    (hj : k.val ≤ j.val) :
    |householderBetaSpec m
        (householderTrailingActiveVector m p (fun r => A r k)
          (signedHouseholderAlpha
            (Real.sqrt (householderTrailingColumnNorm2Sq (m := m) (n := n) p A k))
            (A p k))) *
        (∑ i : Fin m,
          householderTrailingActiveVector m p (fun r => A r k)
              (signedHouseholderAlpha
                (Real.sqrt (householderTrailingColumnNorm2Sq (m := m) (n := n) p A k))
                (A p k)) i *
            householderTrailingPart m p (fun r => A r j) i)| ≤
      Real.sqrt 2 := by
  exact
    abs_householderBeta_mul_inner_trailingPart_le_sqrt_two_signed
      m p (fun r => A r k) (fun r => A r j) (hpivot j hj)

/-- Scalar row-growth step used in Cox--Higham Lemma 4.1.

If both entries in a row are bounded by `B` and the Householder update scalar
has absolute value at most `sqrt 2`, then the updated entry is bounded by
`(1 + sqrt 2) B`. -/
lemma abs_sub_mul_le_one_add_sqrt_two_mul_bound {y phi x B : ℝ}
    (hy : |y| ≤ B) (hx : |x| ≤ B)
    (hphi : |phi| ≤ Real.sqrt 2) :
    |y - phi * x| ≤ (1 + Real.sqrt 2) * B := by
  have hsub : |y - phi * x| ≤ |y| + |phi * x| := by
    simpa using (abs_sub_le y 0 (phi * x))
  have hmul : |phi * x| ≤ Real.sqrt 2 * B := by
    rw [abs_mul]
    exact mul_le_mul hphi hx (abs_nonneg x) (Real.sqrt_nonneg 2)
  have hadd : |y| + |phi * x| ≤ B + Real.sqrt 2 * B :=
    add_le_add hy hmul
  have hrewrite : B + Real.sqrt 2 * B = (1 + Real.sqrt 2) * B := by ring
  exact hsub.trans (hadd.trans_eq hrewrite)

/-- Cox--Higham off-pivot row-growth step under signed column pivoting.

For a remaining column `j`, the exact Householder update scalar supplied by the
signed, column-pivoted construction has absolute value at most `sqrt 2`.  Hence
if the row entries in the pivot and target columns are bounded by `B`, the
updated row entry is bounded by `(1 + sqrt 2) B`.  This is the finite-entry
form of the growth estimate behind equation (4.3). -/
theorem abs_householder_signed_pivot_update_entry_le_one_add_sqrt_two_mul_row_bound
    {m n : ℕ} (p row : Fin m) (k j : Fin n) (A : Fin m → Fin n → ℝ)
    (B : ℝ)
    (hpivot :
      ∀ l : Fin n, k.val ≤ l.val →
        householderTrailingColumnNorm2Sq (m := m) (n := n) p A l ≤
          householderTrailingColumnNorm2Sq (m := m) (n := n) p A k)
    (hj : k.val ≤ j.val)
    (hrowBound : ∀ l : Fin n, k.val ≤ l.val → |A row l| ≤ B) :
    |A row j -
        (householderBetaSpec m
          (householderTrailingActiveVector m p (fun r => A r k)
            (signedHouseholderAlpha
              (Real.sqrt (householderTrailingColumnNorm2Sq (m := m) (n := n) p A k))
              (A p k))) *
          (∑ i : Fin m,
            householderTrailingActiveVector m p (fun r => A r k)
                (signedHouseholderAlpha
                  (Real.sqrt (householderTrailingColumnNorm2Sq (m := m) (n := n) p A k))
                  (A p k)) i *
              householderTrailingPart m p (fun r => A r j) i)) *
          A row k| ≤
      (1 + Real.sqrt 2) * B := by
  let phi :=
    householderBetaSpec m
      (householderTrailingActiveVector m p (fun r => A r k)
        (signedHouseholderAlpha
          (Real.sqrt (householderTrailingColumnNorm2Sq (m := m) (n := n) p A k))
          (A p k))) *
      (∑ i : Fin m,
        householderTrailingActiveVector m p (fun r => A r k)
            (signedHouseholderAlpha
              (Real.sqrt (householderTrailingColumnNorm2Sq (m := m) (n := n) p A k))
              (A p k)) i *
          householderTrailingPart m p (fun r => A r j) i)
  have hphi : |phi| ≤ Real.sqrt 2 := by
    simpa [phi] using
      abs_householderBeta_mul_inner_column_le_sqrt_two_of_signed_pivot_max
        p k j A hpivot hj
  simpa [phi] using
    abs_sub_mul_le_one_add_sqrt_two_mul_bound
      (hrowBound j hj) (hrowBound k (le_refl k.val)) hphi

/-- The Cox--Higham one-step row-growth factor is nonnegative. -/
lemma coxHighamGrowthFactor_nonneg : 0 ≤ (1 + Real.sqrt 2 : ℝ) := by
  linarith [Real.sqrt_nonneg (2 : ℝ)]

/-- Unified one-step active-row growth factor for the Cox--Higham pivoted
    route.

The non-pivot branch contributes `1 + sqrt 2`; the pivot-row active-tail norm
branch currently contributes the ambient `sqrt m` factor. -/
noncomputable def coxHighamActiveRowGrowthFactor (m : ℕ) : ℝ :=
  max (1 + Real.sqrt 2) (Real.sqrt (m : ℝ))

/-- The unified Cox--Higham active-row factor is nonnegative. -/
lemma coxHighamActiveRowGrowthFactor_nonneg (m : ℕ) :
    0 ≤ coxHighamActiveRowGrowthFactor m := by
  unfold coxHighamActiveRowGrowthFactor
  exact
    le_trans coxHighamGrowthFactor_nonneg
      (le_max_left (1 + Real.sqrt 2) (Real.sqrt (m : ℝ)))

/-- The unified Cox--Higham active-row factor is at least one. -/
lemma one_le_coxHighamActiveRowGrowthFactor (m : ℕ) :
    1 ≤ coxHighamActiveRowGrowthFactor m := by
  unfold coxHighamActiveRowGrowthFactor
  have hleft : 1 ≤ 1 + Real.sqrt 2 := by
    linarith [Real.sqrt_nonneg (2 : ℝ)]
  exact le_trans hleft (le_max_left (1 + Real.sqrt 2) (Real.sqrt (m : ℝ)))

/-- Repeated scalar growth bound.

If a nonnegative factor `c` bounds each one-step growth
`M (t+1) <= c * M t` through `steps`, then
`M steps <= c^steps * M 0`.  This is the arithmetic induction used when
turning the one-step Cox--Higham row-growth estimate into a multi-stage row
bound. -/
lemma scalar_growth_iterate_bound (c : ℝ) (M : ℕ → ℝ) (steps : ℕ)
    (hc : 0 ≤ c)
    (hstep : ∀ t : ℕ, t < steps → M (t + 1) ≤ c * M t) :
    M steps ≤ c ^ steps * M 0 := by
  induction steps with
  | zero =>
      simp
  | succ steps ih =>
      have hprev : M steps ≤ c ^ steps * M 0 := by
        exact ih (fun t ht => hstep t (Nat.lt_trans ht (Nat.lt_succ_self steps)))
      have hstep_last : M (steps + 1) ≤ c * M steps :=
        hstep steps (Nat.lt_succ_self steps)
      have hmul : c * M steps ≤ c * (c ^ steps * M 0) :=
        mul_le_mul_of_nonneg_left hprev hc
      calc
        M (steps + 1) ≤ c * M steps := hstep_last
        _ ≤ c * (c ^ steps * M 0) := hmul
        _ = c ^ (steps + 1) * M 0 := by
          rw [pow_succ]
          ring

/-- Additive scalar growth budget.

`scalarAffineGrowthBudget c eta steps` is the accumulated additive error in the
recurrence `M (t+1) <= c * M t + eta t`. -/
def scalarAffineGrowthBudget (c : ℝ) (eta : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | steps + 1 => c * scalarAffineGrowthBudget c eta steps + eta steps

/-- Repeated scalar growth with additive per-step perturbations.

If a nonnegative factor `c` and step errors `eta t` satisfy
`M (t+1) <= c * M t + eta t`, then after `steps` iterations the value is
bounded by the homogeneous growth of the initial value plus the accumulated
additive budget. -/
lemma scalar_affine_growth_iterate_bound (c : ℝ) (M eta : ℕ → ℝ) (steps : ℕ)
    (hc : 0 ≤ c)
    (hstep : ∀ t : ℕ, t < steps → M (t + 1) ≤ c * M t + eta t) :
    M steps ≤ c ^ steps * M 0 + scalarAffineGrowthBudget c eta steps := by
  induction steps with
  | zero =>
      simp [scalarAffineGrowthBudget]
  | succ steps ih =>
      have hprev :
          M steps ≤ c ^ steps * M 0 + scalarAffineGrowthBudget c eta steps := by
        exact ih (fun t ht => hstep t (Nat.lt_trans ht (Nat.lt_succ_self steps)))
      have hstep_last :
          M (steps + 1) ≤ c * M steps + eta steps :=
        hstep steps (Nat.lt_succ_self steps)
      have hmul :
          c * M steps ≤
            c * (c ^ steps * M 0 + scalarAffineGrowthBudget c eta steps) :=
        mul_le_mul_of_nonneg_left hprev hc
      calc
        M (steps + 1) ≤ c * M steps + eta steps := hstep_last
        _ ≤ c * (c ^ steps * M 0 + scalarAffineGrowthBudget c eta steps) +
              eta steps := add_le_add hmul le_rfl
        _ = c ^ (steps + 1) * M 0 +
              scalarAffineGrowthBudget c eta (steps + 1) := by
          simp [scalarAffineGrowthBudget, pow_succ]
          ring

/-- Cox--Higham row-sorting transfer for active entries.

Assume rows are initially sorted by a row bound `row0Bound`, so every active row
`r >= k` has `row0Bound r <= row0Bound k`.  If prior stages have grown every
active entry by at most `(1 + sqrt 2)^k`, then every active entry at stage `k`
is bounded by the same factor times the pivot row's initial bound.  This is the
formal row-sorting step used in Cox--Higham Lemma 4.2. -/
theorem coxHigham_rowSorting_active_entry_bound_of_prior_growth
    {m n : ℕ} (k : Fin m) (r : Fin m) (j : Fin n)
    (Astage : Fin m → Fin n → ℝ) (row0Bound : Fin m → ℝ)
    (hr : k.val ≤ r.val)
    (hsorted : ∀ s : Fin m, k.val ≤ s.val → row0Bound s ≤ row0Bound k)
    (hprior :
      ∀ s : Fin m, ∀ l : Fin n, k.val ≤ s.val →
        |Astage s l| ≤ (1 + Real.sqrt 2) ^ k.val * row0Bound s) :
    |Astage r j| ≤ (1 + Real.sqrt 2) ^ k.val * row0Bound k := by
  have hpow_nonneg : 0 ≤ (1 + Real.sqrt 2 : ℝ) ^ k.val :=
    pow_nonneg coxHighamGrowthFactor_nonneg k.val
  exact
    (hprior r j hr).trans
      (mul_le_mul_of_nonneg_left (hsorted r hr) hpow_nonneg)

/-- Cox--Higham row-sorting transfer with the prior growth proved by scalar
iteration.

This combines `scalar_growth_iterate_bound` with the row-sorting transfer:
for a fixed active entry, if each previous stage grows its absolute value by at
most `1 + sqrt 2`, and the initial row bounds are sorted, then after `k` stages
that entry is bounded by `(1 + sqrt 2)^k` times the pivot row's initial bound. -/
theorem coxHigham_rowSorting_active_entry_bound_of_stage_growth
    {m n : ℕ} (k : Fin m) (r : Fin m) (j : Fin n)
    (Astage : ℕ → Fin m → Fin n → ℝ) (row0Bound : Fin m → ℝ)
    (hr : k.val ≤ r.val)
    (hsorted : ∀ s : Fin m, k.val ≤ s.val → row0Bound s ≤ row0Bound k)
    (hinit : |Astage 0 r j| ≤ row0Bound r)
    (hstep :
      ∀ t : ℕ, t < k.val →
        |Astage (t + 1) r j| ≤ (1 + Real.sqrt 2) * |Astage t r j|) :
    |Astage k.val r j| ≤ (1 + Real.sqrt 2) ^ k.val * row0Bound k := by
  let c : ℝ := 1 + Real.sqrt 2
  let M : ℕ → ℝ := fun t => |Astage t r j|
  have hiter : M k.val ≤ c ^ k.val * M 0 :=
    scalar_growth_iterate_bound c M k.val coxHighamGrowthFactor_nonneg hstep
  have hpow_nonneg : 0 ≤ c ^ k.val :=
    pow_nonneg coxHighamGrowthFactor_nonneg k.val
  have hrow : c ^ k.val * M 0 ≤ c ^ k.val * row0Bound r :=
    mul_le_mul_of_nonneg_left hinit hpow_nonneg
  have hsort_scaled : c ^ k.val * row0Bound r ≤ c ^ k.val * row0Bound k :=
    mul_le_mul_of_nonneg_left (hsorted r hr) hpow_nonneg
  exact hiter.trans (hrow.trans hsort_scaled)

/-- Cox--Higham pivot-row active-entry bound from the active-tail column norm.

This is the local Lean form of the pivot-row step in equations (4.4)--(4.5):
if the next pivot-row entry is bounded by the Euclidean norm of the active tail
of the previous column, and every active-tail entry of that previous column is
bounded by `B`, then the pivot-row entry is bounded by `sqrt m * B`.  The source
has the sharper `sqrt (m-k+1)` factor; this repository lemma keeps the dimension
factor explicit while using the existing ambient `Fin m` norm infrastructure. -/
theorem coxHigham_pivot_row_entry_bound_of_active_tail_entry_bound
    {m n : ℕ} (k : Fin m) (j : Fin n)
    (Aprev Anext : Fin m → Fin n → ℝ) {B : ℝ}
    (hB : 0 ≤ B)
    (hcol :
      |Anext k j| ≤
        vecNorm2 (householderTrailingPart m k (fun i => Aprev i j)))
    (hentry : ∀ i : Fin m, k.val ≤ i.val → |Aprev i j| ≤ B) :
    |Anext k j| ≤ Real.sqrt (m : ℝ) * B := by
  have htail :
      ∀ i : Fin m,
        |householderTrailingPart m k (fun r => Aprev r j) i| ≤ B := by
    intro i
    by_cases hi : i.val < k.val
    · simpa [householderTrailingPart, hi] using hB
    · have hki : k.val ≤ i.val := le_of_not_gt hi
      simpa [householderTrailingPart, hi] using hentry i hki
  exact
    hcol.trans
      (vecNorm2_le_sqrt_card_mul_of_abs_le
        (householderTrailingPart m k (fun i => Aprev i j)) hB htail)

/-- Cox--Higham row-sorting pivot-row bound with the stage-growth factor.

This wraps `coxHigham_pivot_row_entry_bound_of_active_tail_entry_bound` in the
same `(1 + sqrt 2)^k` row-sorting scale used by the off-pivot row-growth
lemmas.  It is a source-route dependency for the pivoted/sorted QR analysis,
not a complete row-wise QR/preconditioner theorem. -/
theorem coxHigham_pivot_row_entry_bound_of_stage_entry_bound
    {m n : ℕ} (k : Fin m) (j : Fin n)
    (Astage : ℕ → Fin m → Fin n → ℝ) (row0Bound : Fin m → ℝ)
    (hrow0 : 0 ≤ row0Bound k)
    (hcol :
      |Astage (k.val + 1) k j| ≤
        vecNorm2 (householderTrailingPart m k (fun i => Astage k.val i j)))
    (hentry :
      ∀ i : Fin m, k.val ≤ i.val →
        |Astage k.val i j| ≤ (1 + Real.sqrt 2) ^ k.val * row0Bound k) :
    |Astage (k.val + 1) k j| ≤
      Real.sqrt (m : ℝ) * ((1 + Real.sqrt 2) ^ k.val * row0Bound k) := by
  have hB : 0 ≤ (1 + Real.sqrt 2) ^ k.val * row0Bound k :=
    mul_nonneg (pow_nonneg coxHighamGrowthFactor_nonneg k.val) hrow0
  exact
    coxHigham_pivot_row_entry_bound_of_active_tail_entry_bound
      k j (Astage k.val) (Astage (k.val + 1)) hB hcol hentry

/-- Cox--Higham row-sorting transfer with additive per-stage row perturbations.

This is the scalar accumulation shape needed for the row-wise perturbation
part of the pivoted/sorted Cox--Higham route: exact row growth contributes the
factor `(1 + sqrt 2)^k`, while `stepBudget` records the additive row-wise error
introduced at each previous stage. -/
theorem coxHigham_rowSorting_active_entry_bound_of_stage_growth_with_additive
    {m n : ℕ} (k : Fin m) (r : Fin m) (j : Fin n)
    (Astage : ℕ → Fin m → Fin n → ℝ) (row0Bound : Fin m → ℝ)
    (stepBudget : ℕ → ℝ)
    (hr : k.val ≤ r.val)
    (hsorted : ∀ s : Fin m, k.val ≤ s.val → row0Bound s ≤ row0Bound k)
    (hinit : |Astage 0 r j| ≤ row0Bound r)
    (hstep :
      ∀ t : ℕ, t < k.val →
        |Astage (t + 1) r j| ≤
          (1 + Real.sqrt 2) * |Astage t r j| + stepBudget t) :
    |Astage k.val r j| ≤
      (1 + Real.sqrt 2) ^ k.val * row0Bound k +
        scalarAffineGrowthBudget (1 + Real.sqrt 2) stepBudget k.val := by
  let c : ℝ := 1 + Real.sqrt 2
  let M : ℕ → ℝ := fun t => |Astage t r j|
  have hiter :
      M k.val ≤ c ^ k.val * M 0 + scalarAffineGrowthBudget c stepBudget k.val :=
    scalar_affine_growth_iterate_bound c M stepBudget k.val
      coxHighamGrowthFactor_nonneg hstep
  have hpow_nonneg : 0 ≤ c ^ k.val :=
    pow_nonneg coxHighamGrowthFactor_nonneg k.val
  have hrow : c ^ k.val * M 0 ≤ c ^ k.val * row0Bound r :=
    mul_le_mul_of_nonneg_left hinit hpow_nonneg
  have hsort_scaled : c ^ k.val * row0Bound r ≤ c ^ k.val * row0Bound k :=
    mul_le_mul_of_nonneg_left (hsorted r hr) hpow_nonneg
  exact hiter.trans (by
    simpa [c] using
      add_le_add (hrow.trans hsort_scaled)
        (le_refl (scalarAffineGrowthBudget c stepBudget k.val)))

/-- Row-wise accumulated perturbation for two Cox--Higham stage sequences.

If the row-entry discrepancy between a computed sequence and an exact sequence
satisfies the affine recurrence
`E (t+1) <= (1 + sqrt 2) * E t + stepBudget t`, then after `k` stages it is
bounded by the initial discrepancy grown by `(1 + sqrt 2)^k` plus the additive
accumulation budget. -/
theorem coxHigham_rowwise_error_accumulation_bound
    {m n : ℕ} (k : Fin m) (r : Fin m) (j : Fin n)
    (Ahat Aexact : ℕ → Fin m → Fin n → ℝ) (stepBudget : ℕ → ℝ)
    (hstep :
      ∀ t : ℕ, t < k.val →
        |Ahat (t + 1) r j - Aexact (t + 1) r j| ≤
          (1 + Real.sqrt 2) * |Ahat t r j - Aexact t r j| + stepBudget t) :
    |Ahat k.val r j - Aexact k.val r j| ≤
      (1 + Real.sqrt 2) ^ k.val * |Ahat 0 r j - Aexact 0 r j| +
        scalarAffineGrowthBudget (1 + Real.sqrt 2) stepBudget k.val := by
  let c : ℝ := 1 + Real.sqrt 2
  let M : ℕ → ℝ := fun t => |Ahat t r j - Aexact t r j|
  simpa [c, M] using
    scalar_affine_growth_iterate_bound c M stepBudget k.val
      coxHighamGrowthFactor_nonneg hstep

/-- Combine an exact row bound with a row-wise accumulated perturbation bound. -/
theorem coxHigham_abs_entry_le_exact_bound_add_error
    {m n : ℕ} (k : ℕ) (r : Fin m) (j : Fin n)
    (Ahat Aexact : ℕ → Fin m → Fin n → ℝ) (exactBound errorBound : ℝ)
    (hexact : |Aexact k r j| ≤ exactBound)
    (herr : |Ahat k r j - Aexact k r j| ≤ errorBound) :
    |Ahat k r j| ≤ exactBound + errorBound := by
  have htri :
      |Ahat k r j| ≤ |Aexact k r j| + |Ahat k r j - Aexact k r j| := by
    have habs := abs_add_le (Aexact k r j) (Ahat k r j - Aexact k r j)
    have hsum : Aexact k r j + (Ahat k r j - Aexact k r j) = Ahat k r j := by
      ring
    simpa [hsum] using habs
  exact htri.trans (add_le_add hexact herr)

/-- Cox--Higham row-sorting bound plus accumulated computed/exact row error. -/
theorem coxHigham_rowSorting_active_entry_bound_with_accumulated_error
    {m n : ℕ} (k : Fin m) (r : Fin m) (j : Fin n)
    (Ahat Aexact : ℕ → Fin m → Fin n → ℝ) (row0Bound : Fin m → ℝ)
    (stepBudget : ℕ → ℝ)
    (hr : k.val ≤ r.val)
    (hsorted : ∀ s : Fin m, k.val ≤ s.val → row0Bound s ≤ row0Bound k)
    (hinitExact : |Aexact 0 r j| ≤ row0Bound r)
    (hstepExact :
      ∀ t : ℕ, t < k.val →
        |Aexact (t + 1) r j| ≤ (1 + Real.sqrt 2) * |Aexact t r j|)
    (hstepErr :
      ∀ t : ℕ, t < k.val →
        |Ahat (t + 1) r j - Aexact (t + 1) r j| ≤
          (1 + Real.sqrt 2) * |Ahat t r j - Aexact t r j| + stepBudget t) :
    |Ahat k.val r j| ≤
      (1 + Real.sqrt 2) ^ k.val * row0Bound k +
        ((1 + Real.sqrt 2) ^ k.val * |Ahat 0 r j - Aexact 0 r j| +
          scalarAffineGrowthBudget (1 + Real.sqrt 2) stepBudget k.val) := by
  have hexact :
      |Aexact k.val r j| ≤
        (1 + Real.sqrt 2) ^ k.val * row0Bound k :=
    coxHigham_rowSorting_active_entry_bound_of_stage_growth
      k r j Aexact row0Bound hr hsorted hinitExact hstepExact
  have herr :
      |Ahat k.val r j - Aexact k.val r j| ≤
        (1 + Real.sqrt 2) ^ k.val * |Ahat 0 r j - Aexact 0 r j| +
          scalarAffineGrowthBudget (1 + Real.sqrt 2) stepBudget k.val :=
    coxHigham_rowwise_error_accumulation_bound k r j Ahat Aexact stepBudget hstepErr
  exact
    coxHigham_abs_entry_le_exact_bound_add_error k r j Ahat Aexact
      ((1 + Real.sqrt 2) ^ k.val * row0Bound k)
      ((1 + Real.sqrt 2) ^ k.val * |Ahat 0 r j - Aexact 0 r j| +
        scalarAffineGrowthBudget (1 + Real.sqrt 2) stepBudget k.val)
      hexact herr

/-- If `alpha^2 = ||x||_2^2`, then `v^T v = 2 v^T x` for
    `v = x - alpha e_p`. -/
lemma householderActiveVector_inner_self_eq_two_inner_x (n : ℕ) (p : Fin n)
    (x : Fin n → ℝ) (alpha : ℝ)
    (halpha : alpha * alpha = vecNorm2Sq x) :
    (∑ i : Fin n, householderActiveVector n p x alpha i *
        householderActiveVector n p x alpha i) =
      2 * (∑ i : Fin n, householderActiveVector n p x alpha i * x i) := by
  rw [householderActiveVector_inner_self, householderActiveVector_inner_x]
  rw [← halpha]
  ring

/-- The exact Householder beta satisfies `beta * v^T x = 1` for the active
    construction whenever `alpha^2 = ||x||_2^2` and `v^T v ≠ 0`. -/
lemma householderBeta_mul_activeVector_inner_x (n : ℕ) (p : Fin n)
    (x : Fin n → ℝ) (alpha : ℝ)
    (halpha : alpha * alpha = vecNorm2Sq x)
    (hden : (∑ i : Fin n, householderActiveVector n p x alpha i *
        householderActiveVector n p x alpha i) ≠ 0) :
    householderBetaSpec n (householderActiveVector n p x alpha) *
        (∑ i : Fin n, householderActiveVector n p x alpha i * x i) = 1 := by
  let v := householderActiveVector n p x alpha
  have hdeneq : (∑ i : Fin n, v i * v i) =
      2 * (∑ i : Fin n, v i * x i) := by
    simpa [v] using householderActiveVector_inner_self_eq_two_inner_x n p x alpha halpha
  have hinner_ne : (∑ i : Fin n, v i * x i) ≠ 0 := by
    intro hzero
    apply hden
    rw [hdeneq, hzero]
    norm_num
  change (2 / (∑ i : Fin n, v i * v i)) * (∑ i : Fin n, v i * x i) = 1
  rw [hdeneq]
  field_simp [hinner_ne]

/-- Exact active-column zeroing for the constructed Householder reflector.

    If `v = x - alpha e_p`, `alpha^2 = ||x||_2^2`, and `v^T v` is nonzero,
    then the exact Householder reflector `I - beta vv^T` maps `x` to
    `alpha e_p`.  This is the active-column algebra needed by a concrete
    rectangular Householder QR implementation before floating-point update
    errors are introduced. -/
theorem matMulVec_householder_activeVector_eq_alpha_basis (n : ℕ)
    (p : Fin n) (x : Fin n → ℝ) (alpha : ℝ)
    (halpha : alpha * alpha = vecNorm2Sq x)
    (hden : (∑ i : Fin n, householderActiveVector n p x alpha i *
        householderActiveVector n p x alpha i) ≠ 0)
    (i : Fin n) :
    matMulVec n
        (householder n (householderActiveVector n p x alpha)
          (householderBetaSpec n (householderActiveVector n p x alpha))) x i =
      if i = p then alpha else 0 := by
  let v := householderActiveVector n p x alpha
  let beta := householderBetaSpec n v
  have hbetax : beta * (∑ j : Fin n, v j * x j) = 1 := by
    simpa [v, beta] using householderBeta_mul_activeVector_inner_x n p x alpha halpha hden
  have hId : (∑ j : Fin n, idMatrix n i j * x j) = x i := by
    simpa [matMulVec] using congrFun (matMulVec_id n x) i
  have hsecond : (∑ j : Fin n, (beta * v i * v j) * x j) =
      v i * (beta * ∑ j : Fin n, v j * x j) := by
    calc
      (∑ j : Fin n, (beta * v i * v j) * x j)
          = ∑ j : Fin n, (beta * v i) * (v j * x j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = (beta * v i) * (∑ j : Fin n, v j * x j) := by
              rw [← Finset.mul_sum]
      _ = v i * (beta * ∑ j : Fin n, v j * x j) := by
              ring
  unfold matMulVec householder
  change (∑ j : Fin n, (idMatrix n i j - beta * v i * v j) * x j) =
      if i = p then alpha else 0
  have hsplit : ∀ j : Fin n,
      (idMatrix n i j - beta * v i * v j) * x j =
        idMatrix n i j * x j - (beta * v i * v j) * x j := by
    intro j
    ring
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, hId, hsecond, hbetax]
  unfold v householderActiveVector
  by_cases h : i = p
  · simp [h]
  · simp [h]

/-- Off-pivot form of the exact active-column zeroing theorem. -/
theorem matMulVec_householder_activeVector_eq_zero_of_ne (n : ℕ)
    (p : Fin n) (x : Fin n → ℝ) (alpha : ℝ)
    (halpha : alpha * alpha = vecNorm2Sq x)
    (hden : (∑ i : Fin n, householderActiveVector n p x alpha i *
        householderActiveVector n p x alpha i) ≠ 0)
    (i : Fin n) (hi : i ≠ p) :
    matMulVec n
        (householder n (householderActiveVector n p x alpha)
          (householderBetaSpec n (householderActiveVector n p x alpha))) x i = 0 := by
  rw [matMulVec_householder_activeVector_eq_alpha_basis n p x alpha halpha hden i]
  simp [hi]

/-- Exact active-column zeroing for the QR trailing Householder vector.

    The standard rectangular QR construction forms a reflector from the
    trailing column segment.  This theorem states the exact algebraic shape:
    rows before the pivot are unchanged, the pivot becomes `alpha`, and rows
    below the pivot become zero. -/
theorem matMulVec_householder_trailingActiveVector_eq_prefix_alpha_zero (n : ℕ)
    (p : Fin n) (x : Fin n → ℝ) (alpha : ℝ)
    (halpha : alpha * alpha = householderTrailingNorm2Sq n p x)
    (hden : (∑ i : Fin n, householderTrailingActiveVector n p x alpha i *
        householderTrailingActiveVector n p x alpha i) ≠ 0)
    (i : Fin n) :
    matMulVec n
        (householder n (householderTrailingActiveVector n p x alpha)
          (householderBetaSpec n (householderTrailingActiveVector n p x alpha))) x i =
      if i.val < p.val then x i else if i = p then alpha else 0 := by
  let xPrefix := householderPrefixPart n p x
  let xTail := householderTrailingPart n p x
  let v := householderTrailingActiveVector n p x alpha
  let β := householderBetaSpec n v
  let P := householder n v β
  have hvprefix : ∀ i : Fin n, i.val < p.val → v i = 0 := by
    intro i hi
    simpa [v] using householderTrailingActiveVector_zero_prefix n p x alpha i hi
  have hxsplit : (fun i => xPrefix i + xTail i) = x := by
    simpa [xPrefix, xTail] using householderPrefixPart_add_trailingPart n p x
  have hprefix_support : ∀ i : Fin n, p.val ≤ i.val → xPrefix i = 0 := by
    simpa [xPrefix] using householderPrefixPart_support n p x
  have hPprefix :
      matMulVec n P xPrefix = xPrefix := by
    simpa [P, v, β] using
      matMulVec_householder_eq_self_of_zero_prefix_support n p.val
        v xPrefix β hvprefix hprefix_support
  have hv_active :
      v = householderActiveVector n p xTail alpha := rfl
  have hden_active :
      (∑ i : Fin n, householderActiveVector n p xTail alpha i *
          householderActiveVector n p xTail alpha i) ≠ 0 := by
    simpa [v, xTail, householderTrailingActiveVector] using hden
  have halpha_tail : alpha * alpha = vecNorm2Sq xTail := by
    simpa [householderTrailingNorm2Sq, xTail] using halpha
  have hPtail :
      ∀ i : Fin n, matMulVec n P xTail i =
        if i = p then alpha else 0 := by
    intro i
    simpa [P, v, β, hv_active] using
      matMulVec_householder_activeVector_eq_alpha_basis
        n p xTail alpha halpha_tail hden_active i
  have hmul_split :
      matMulVec n P x =
        fun i => matMulVec n P xPrefix i + matMulVec n P xTail i := by
    rw [← hxsplit]
    exact matMulVec_add_right n P xPrefix xTail
  calc
    matMulVec n P x i
        = matMulVec n P xPrefix i + matMulVec n P xTail i := by
          rw [hmul_split]
    _ = xPrefix i + (if i = p then alpha else 0) := by
          rw [congrFun hPprefix i, hPtail i]
    _ = if i.val < p.val then x i else if i = p then alpha else 0 := by
          by_cases hi : i.val < p.val
          · have hip : i ≠ p := by
              intro h
              subst i
              exact Nat.lt_irrefl p.val hi
            simp [xPrefix, householderPrefixPart, hi, hip]
          · simp [xPrefix, householderPrefixPart, hi]

/-- Off-pivot below-pivot form of the exact trailing Householder zeroing
    theorem. -/
theorem matMulVec_householder_trailingActiveVector_eq_zero_of_pivot_lt
    (n : ℕ) (p : Fin n) (x : Fin n → ℝ) (alpha : ℝ)
    (halpha : alpha * alpha = householderTrailingNorm2Sq n p x)
    (hden : (∑ i : Fin n, householderTrailingActiveVector n p x alpha i *
        householderTrailingActiveVector n p x alpha i) ≠ 0)
    (i : Fin n) (hi : p.val < i.val) :
    matMulVec n
        (householder n (householderTrailingActiveVector n p x alpha)
          (householderBetaSpec n (householderTrailingActiveVector n p x alpha))) x i = 0 := by
  rw [matMulVec_householder_trailingActiveVector_eq_prefix_alpha_zero
    n p x alpha halpha hden i]
  have hnot_lt : ¬ i.val < p.val := Nat.not_lt.mpr (le_of_lt hi)
  have hne : i ≠ p := by
    intro h
    subst i
    exact Nat.lt_irrefl p.val hi
  simp [hnot_lt, hne]

/-- (vvᵀ)(vvᵀ) = (vᵀv)·vvᵀ: key identity for Householder orthogonality.

    The outer product of v with itself, squared as a matrix product,
    equals the scalar (vᵀv) times the outer product. -/
theorem abs_matMulVec_householder_pivot_le_trailing_vecNorm2_of_zero_prefix_orthogonal
    (n : ℕ) (p : Fin n) (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hvprefix : ∀ i : Fin n, i.val < p.val → v i = 0)
    (horth : IsOrthogonal n (householder n v β)) :
    |matMulVec n (householder n v β) b p| ≤
      vecNorm2 (householderTrailingPart n p b) := by
  let bPrefix := householderPrefixPart n p b
  let bTail := householderTrailingPart n p b
  let P := householder n v β
  have hb_split : (fun i : Fin n => bPrefix i + bTail i) = b := by
    simpa [bPrefix, bTail] using householderPrefixPart_add_trailingPart n p b
  have hprefix_support : ∀ i : Fin n, p.val ≤ i.val → bPrefix i = 0 := by
    simpa [bPrefix] using householderPrefixPart_support n p b
  have hPprefix :
      matMulVec n P bPrefix = bPrefix := by
    simpa [P] using
      matMulVec_householder_eq_self_of_zero_prefix_support n p.val
        v bPrefix β hvprefix hprefix_support
  have hmul_split :
      matMulVec n P b =
        fun i => matMulVec n P bPrefix i + matMulVec n P bTail i := by
    rw [← hb_split]
    exact matMulVec_add_right n P bPrefix bTail
  have hp_prefix_zero : bPrefix p = 0 := by
    simp [bPrefix, householderPrefixPart]
  have hp_eq :
      matMulVec n P b p = matMulVec n P bTail p := by
    rw [congrFun hmul_split p, congrFun hPprefix p, hp_prefix_zero]
    ring
  calc
    |matMulVec n P b p| = |matMulVec n P bTail p| := by
      exact congrArg (fun x : ℝ => |x|) hp_eq
    _ ≤ vecNorm2 (matMulVec n P bTail) :=
      abs_coord_le_vecNorm2 (matMulVec n P bTail) p
    _ = vecNorm2 bTail := vecNorm2_orthogonal P bTail horth

/-- Exact signed-pivot Householder pivot-row update is bounded by the active
tail norm of the updated column.

The reflector is formed from pivot column `pivotCol`; the column being updated
is `j`.  A positive active norm for the pivot column supplies the denominator
nonbreakdown needed for orthogonality. -/
theorem coxHigham_signed_pivot_row_update_abs_le_trailing_vecNorm2
    {m n : ℕ} (p : Fin m) (pivotCol j : Fin n)
    (A : Fin m → Fin n → ℝ)
    (hnorm :
      0 < householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol) :
    |matMulVec m
        (householder m
          (householderTrailingActiveVector m p (fun r => A r pivotCol)
            (signedHouseholderAlpha
              (Real.sqrt
                (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
              (A p pivotCol)))
          (householderBetaSpec m
            (householderTrailingActiveVector m p (fun r => A r pivotCol)
              (signedHouseholderAlpha
                (Real.sqrt
                  (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
                (A p pivotCol)))))
        (fun r => A r j) p| ≤
      vecNorm2 (householderTrailingPart m p (fun r => A r j)) := by
  let alpha : ℝ :=
    signedHouseholderAlpha
      (Real.sqrt
        (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
      (A p pivotCol)
  let v : Fin m → ℝ :=
    householderTrailingActiveVector m p (fun r => A r pivotCol) alpha
  let β : ℝ := householderBetaSpec m v
  have halpha :
      alpha * alpha = householderTrailingNorm2Sq m p (fun r => A r pivotCol) := by
    simpa [alpha, householderTrailingColumnNorm2Sq] using
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
        m p (fun r => A r pivotCol)
  have hsign : alpha * A p pivotCol ≤ 0 := by
    simpa [alpha, householderTrailingColumnNorm2Sq] using
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
        m p (fun r => A r pivotCol)
  have hnorm' :
      0 < householderTrailingNorm2Sq m p (fun r => A r pivotCol) := by
    simpa [householderTrailingColumnNorm2Sq] using hnorm
  have hden :
      (∑ i : Fin m, v i * v i) ≠ 0 := by
    simpa [v] using
      householderTrailingActiveVector_inner_self_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos
        m p (fun r => A r pivotCol) alpha halpha hnorm' hsign
  have hβ : β * (∑ i : Fin m, v i * v i) = 2 := by
    exact householderBeta_mul_inner_self_eq_two m v hden
  have horth : IsOrthogonal m (householder m v β) :=
    householder_orthogonal m v β hβ
  have hvprefix : ∀ i : Fin m, i.val < p.val → v i = 0 := by
    intro i hi
    simpa [v] using
      householderTrailingActiveVector_zero_prefix
        m p (fun r => A r pivotCol) alpha i hi
  exact
    abs_matMulVec_householder_pivot_le_trailing_vecNorm2_of_zero_prefix_orthogonal
      m p v β (fun r => A r j) hvprefix horth

/-- Exact signed-pivot Householder pivot-row update with the Cox--Higham
row-sorted stage budget.

This composes the exact pivot-row active-tail norm bound with the already
formalized ambient-dimension tail-entry estimate.  It is a route dependency for
the pivoted/sorted rectangular QR proof, not a final QR/preconditioner theorem. -/
theorem coxHigham_exact_signed_pivot_row_entry_bound_of_stage_entry_bound
    {m n : ℕ} (p : Fin m) (pivotCol j : Fin n)
    (A : Fin m → Fin n → ℝ) (row0Bound : Fin m → ℝ)
    (hnorm :
      0 < householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol)
    (hrow0 : 0 ≤ row0Bound p)
    (hentry :
      ∀ i : Fin m, p.val ≤ i.val →
        |A i j| ≤ (1 + Real.sqrt 2) ^ p.val * row0Bound p) :
    |matMulVec m
        (householder m
          (householderTrailingActiveVector m p (fun r => A r pivotCol)
            (signedHouseholderAlpha
              (Real.sqrt
                (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
              (A p pivotCol)))
          (householderBetaSpec m
            (householderTrailingActiveVector m p (fun r => A r pivotCol)
              (signedHouseholderAlpha
                (Real.sqrt
                  (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
                (A p pivotCol)))))
        (fun r => A r j) p| ≤
      Real.sqrt (m : ℝ) *
        ((1 + Real.sqrt 2) ^ p.val * row0Bound p) := by
  let alpha : ℝ :=
    signedHouseholderAlpha
      (Real.sqrt
        (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
      (A p pivotCol)
  let v : Fin m → ℝ :=
    householderTrailingActiveVector m p (fun r => A r pivotCol) alpha
  let β : ℝ := householderBetaSpec m v
  let P : Fin m → Fin m → ℝ := householder m v β
  let Aupdate : Fin m → Fin n → ℝ :=
    fun i l => matMulVec m P (fun r => A r l) i
  have hcol :
      |Aupdate p j| ≤ vecNorm2 (householderTrailingPart m p (fun i => A i j)) := by
    simpa [Aupdate, P, v, β, alpha] using
      coxHigham_signed_pivot_row_update_abs_le_trailing_vecNorm2
        p pivotCol j A hnorm
  exact
    coxHigham_pivot_row_entry_bound_of_active_tail_entry_bound
      p j A Aupdate
      (mul_nonneg (pow_nonneg coxHighamGrowthFactor_nonneg p.val) hrow0)
      hcol hentry

-- ============================================================
-- §18.3  Lemma 18.2: Householder application backward error
-- ============================================================

/-- **Backward error model for Householder application** (Lemma 18.2).

    When a Householder matrix P is applied to a vector b in
    floating-point arithmetic, the computed result ŷ satisfies
    ŷ = (P + ΔP)b where ‖ΔP‖_F ≤ c.

    This structure records the result of Lemma 18.2 since the detailed proof
    requires low-level FP analysis of the dot product + outer product
    computation pattern (Lemma 18.1 + eq 18.3). The bound c is
    typically γ̃_{cm} where c is a small constant and m = n. -/
theorem HouseholderAppError.of_forward_error
    (n : ℕ) (P : Fin n → Fin n → ℝ) (b y_hat : Fin n → ℝ) {c : ℝ}
    (horth : IsOrthogonal n P) (hc : 0 ≤ c)
    (hforward :
      vecNorm2 (fun i : Fin n => y_hat i - matMulVec n P b i) ≤
        c * vecNorm2 b) :
    HouseholderAppError n P b y_hat c := by
  refine ⟨horth, ?_⟩
  let e : Fin n → ℝ := fun i => y_hat i - matMulVec n P b i
  by_cases hb : vecNorm2 b = 0
  · let ΔP : Fin n → Fin n → ℝ := fun _ _ => 0
    refine ⟨ΔP, ?_, ?_⟩
    · have hzero : frobNorm ΔP = 0 := by
        rw [frobNorm_eq_sqrt_frobNormSq]
        simp [ΔP, frobNormSq]
      simpa [hzero] using hc
    · intro i
      have he_le : vecNorm2 e ≤ 0 := by
        simpa [e, hb] using hforward
      have he_norm : vecNorm2 e = 0 :=
        le_antisymm he_le (vecNorm2_nonneg e)
      have he_i : e i = 0 := (vecNorm2_eq_zero_iff e).mp he_norm i
      have hmat :
          matMulVec n (fun a b => P a b + ΔP a b) b i =
            matMulVec n P b i := by
        simp [ΔP, matMulVec]
      calc
        y_hat i = matMulVec n P b i := by
          dsimp [e] at he_i
          linarith
        _ = matMulVec n (fun a b => P a b + ΔP a b) b i := by
          rw [hmat]
  · let den : ℝ := vecNorm2Sq b
    let ΔP : Fin n → Fin n → ℝ := fun i j => (1 / den) * (e i * b j)
    refine ⟨ΔP, ?_, ?_⟩
    · have hbpos : 0 < vecNorm2 b :=
        lt_of_le_of_ne (vecNorm2_nonneg b) (Ne.symm hb)
      have hΔnorm : frobNorm ΔP = vecNorm2 e / vecNorm2 b := by
        simpa [ΔP, den] using frobNorm_rankOne_div_vecNorm2Sq e b hb
      rw [hΔnorm]
      exact (div_le_iff₀ hbpos).mpr (by simpa [e] using hforward)
    · have hden_ne : den ≠ 0 := by
        intro hden_zero
        apply hb
        unfold den at hden_zero
        unfold vecNorm2
        rw [hden_zero, Real.sqrt_zero]
      have hΔ_mul : ∀ i : Fin n, matMulVec n ΔP b i = e i := by
        intro i
        unfold matMulVec ΔP den
        calc
          (∑ j : Fin n, ((1 / vecNorm2Sq b) * (e i * b j)) * b j)
              = ∑ j : Fin n,
                  ((1 / vecNorm2Sq b) * e i) * (b j * b j) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    ring
          _ = ((1 / vecNorm2Sq b) * e i) *
                ∑ j : Fin n, b j * b j := by
                    rw [Finset.mul_sum]
          _ = ((1 / vecNorm2Sq b) * e i) * vecNorm2Sq b := by
                    congr 1
                    unfold vecNorm2Sq
                    apply Finset.sum_congr rfl
                    intro j _
                    ring
          _ = e i := by
                    have hden_ne' : vecNorm2Sq b ≠ 0 := by
                      simpa [den] using hden_ne
                    field_simp [hden_ne']
      intro i
      have hsplit :=
        congrFun (matMulVec_add_left n P ΔP b) i
      calc
        y_hat i = matMulVec n P b i + e i := by
          dsimp [e]
          ring
        _ = matMulVec n P b i + matMulVec n ΔP b i := by
          rw [hΔ_mul i]
        _ = matMulVec n (fun a b => P a b + ΔP a b) b i := by
          rw [hsplit]

/-- Common backward-error contract for applying one Householder reflector to a
    rectangular matrix panel and to the right-hand side.

    This is deliberately stronger than the vector-only `HouseholderAppError`:
    it exposes one shared perturbation matrix `ΔP` that explains both the
    matrix update and the right-hand-side update.  The rectangular QR route
    needs this common-`ΔP` shape before the existing common-orthogonal-factor
    accumulation theorem can be used. -/
structure HouseholderPanelAppError (m n : ℕ) (P : Fin m → Fin m → ℝ)
    (A A_hat : Fin m → Fin n → ℝ) (b b_hat : Fin m → ℝ) (c : ℝ) : Prop where
  /-- The exact reflector represented by the rounded update is orthogonal. -/
  orth : IsOrthogonal m P
  /-- The same perturbation matrix explains both rounded applications. -/
  pert : ∃ ΔP : Fin m → Fin m → ℝ,
    frobNorm ΔP ≤ c ∧
    (∀ i j, A_hat i j =
      matMulRectLeft (fun a b => P a b + ΔP a b) A i j) ∧
    ∀ i, b_hat i = matMulVec m (fun a b => P a b + ΔP a b) b i

/-- Columnwise backward-error contract for applying one Householder reflector
    to a rectangular matrix panel and to the right-hand side.

    This is the source-faithful shape for Householder QR: when a reflector is
    applied independently to the columns of a panel, each column may have its
    own perturbation matrix.  The exact reflector `P` is common, so later
    accumulation can still expose one theoretical orthogonal factor `Q`, but
    the rounded perturbations are columnwise rather than a single shared
    `ΔP`. -/
structure HouseholderColumnwisePanelAppError (m n : ℕ)
    (P : Fin m → Fin m → ℝ)
    (A A_hat : Fin m → Fin n → ℝ) (b b_hat : Fin m → ℝ) (c : ℝ) : Prop where
  /-- The exact reflector represented by the rounded update is orthogonal. -/
  orth : IsOrthogonal m P
  /-- Each matrix-panel column has its own admissible perturbation. -/
  col_pert : ∀ j : Fin n, ∃ ΔP : Fin m → Fin m → ℝ,
    frobNorm ΔP ≤ c ∧
    ∀ i, A_hat i j =
      matMulVec m (fun a b => P a b + ΔP a b) (fun a => A a j) i
  /-- The right-hand side is one more vector application, with its own
      admissible perturbation. -/
  rhs_pert : ∃ ΔP : Fin m → Fin m → ℝ,
    frobNorm ΔP ≤ c ∧
    ∀ i, b_hat i = matMulVec m (fun a b => P a b + ΔP a b) b i

/-- Vector-level Householder application contracts imply the columnwise panel
    contract, but not the stronger shared-`ΔP` panel contract. -/
theorem HouseholderColumnwisePanelAppError.of_vector_applications
    (m n : ℕ) (P : Fin m → Fin m → ℝ)
    (A A_hat : Fin m → Fin n → ℝ) (b b_hat : Fin m → ℝ) (c : ℝ)
    (hcols : ∀ j : Fin n,
      HouseholderAppError m P (fun i => A i j) (fun i => A_hat i j) c)
    (hrhs : HouseholderAppError m P b b_hat c) :
    HouseholderColumnwisePanelAppError m n P A A_hat b b_hat c := by
  refine ⟨(hrhs.orth), ?_, ?_⟩
  · intro j
    exact (hcols j).pert
  · exact hrhs.pert

/-- Per-column normwise vector forward-error bounds imply the source-faithful
    columnwise Householder panel contract. -/
theorem HouseholderColumnwisePanelAppError.of_forward_errors
    (m n : ℕ) (P : Fin m → Fin m → ℝ)
    (A A_hat : Fin m → Fin n → ℝ) (b b_hat : Fin m → ℝ) {c : ℝ}
    (horth : IsOrthogonal m P) (hc : 0 ≤ c)
    (hcols : ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
          A_hat i j - matMulVec m P (fun a => A a j) i) ≤
        c * vecNorm2 (fun i : Fin m => A i j))
    (hrhs :
      vecNorm2 (fun i : Fin m => b_hat i - matMulVec m P b i) ≤
        c * vecNorm2 b) :
    HouseholderColumnwisePanelAppError m n P A A_hat b b_hat c := by
  apply HouseholderColumnwisePanelAppError.of_vector_applications
  · intro j
    exact HouseholderAppError.of_forward_error m P
      (fun i : Fin m => A i j) (fun i : Fin m => A_hat i j)
      horth hc (hcols j)
  · exact HouseholderAppError.of_forward_error m P b b_hat horth hc hrhs

end NumStability
