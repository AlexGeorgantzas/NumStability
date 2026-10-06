import Mathlib

namespace HighamBenchCandidate

/-- The Euclidean norm of a real vector. -/
noncomputable def euclideanNorm {k : ℕ} (v : Fin k → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin k, (v i) ^ 2)

/-- The Frobenius norm of a real matrix. -/
noncomputable def frobeniusNorm {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, (M i j) ^ 2)

/-- With the right-hand side fixed, zero minimizes the perturbed least-squares
residual over every possible solution vector. -/
def zeroIsLeastSquaresSolution {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  ∀ x : Fin n → ℝ,
    euclideanNorm (b - M.mulVec (0 : Fin n → ℝ)) ≤
      euclideanNorm (b - M.mulVec x)

/-- The value of the matrix-only backward error at the zero vector. -/
noncomputable def zeroBackwardErrorValue {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : ℝ :=
  if b = 0 then 0 else euclideanNorm (A.transpose.mulVec b) / euclideanNorm b

private lemma sum_sq_nonneg {k : ℕ} (v : Fin k → ℝ) :
    0 ≤ ∑ i : Fin k, (v i) ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma euclideanNorm_sq {k : ℕ} (v : Fin k → ℝ) :
    euclideanNorm v ^ 2 = ∑ i : Fin k, (v i) ^ 2 := by
  exact Real.sq_sqrt (sum_sq_nonneg v)

private lemma frobeniusNorm_sq {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm M ^ 2 = ∑ i : Fin m, ∑ j : Fin n, (M i j) ^ 2 := by
  apply Real.sq_sqrt
  exact Finset.sum_nonneg fun _ _ => sum_sq_nonneg _

private lemma euclideanNorm_ne_zero {k : ℕ} {v : Fin k → ℝ} (hv : v ≠ 0) :
    euclideanNorm v ≠ 0 := by
  intro hn
  apply hv
  funext i
  have hs : (∑ j : Fin k, (v j) ^ 2) = 0 := by
    rw [← euclideanNorm_sq, hn]
    ring
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => sq_nonneg (v j))).mp hs i
      (Finset.mem_univ i)
  exact (sq_eq_zero_iff).mp hi

private lemma quadratic_zero {q c : ℝ} (hq : 0 ≤ q)
    (h : ∀ t : ℝ, 0 ≤ q * t ^ 2 - 2 * c * t) : c = 0 := by
  have hd : q + 1 ≠ 0 := by linarith
  have ht := h (c / (q + 1))
  have hpos : 0 < q + 1 := by linarith
  have hmul := mul_nonneg ht (sq_nonneg (q + 1))
  have hs : (q + 1) ^ 2 * (c / (q + 1)) = (q + 1) * c := by
    field_simp
  have hs2 : (q + 1) ^ 2 * (c / (q + 1)) ^ 2 = c ^ 2 := by
    field_simp
  nlinarith [sq_nonneg c]

private lemma min_imp_dot_zero {k : ℕ} (b v : Fin k → ℝ)
    (h : ∀ t : ℝ, euclideanNorm b ≤ euclideanNorm (fun i => b i - t * v i)) :
    (∑ i : Fin k, b i * v i) = 0 := by
  apply quadratic_zero (sum_sq_nonneg v)
  intro t
  have hcalc :
      (∑ i : Fin k, (b i - t * v i) ^ 2) =
        (∑ i : Fin k, (b i) ^ 2) -
          2 * (∑ i : Fin k, b i * v i) * t +
          (∑ i : Fin k, (v i) ^ 2) * t ^ 2 := by
    calc
      _ = (∑ i : Fin k, ((b i) ^ 2 - 2 * (b i * v i) * t + (v i) ^ 2 * t ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_mul, ← Finset.mul_sum]
  have hb := euclideanNorm_sq b
  have hr := euclideanNorm_sq (fun i => b i - t * v i)
  rw [hcalc] at hr
  have hb0 : 0 ≤ euclideanNorm b := Real.sqrt_nonneg _
  have hr0 : 0 ≤ euclideanNorm (fun i => b i - t * v i) := Real.sqrt_nonneg _
  have hh := h t
  nlinarith

private lemma optimal_imp_normal {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (h : zeroIsLeastSquaresSolution M b) : M.transpose.mulVec b = 0 := by
  funext j
  have hscalar (t : ℝ) :
      euclideanNorm b ≤ euclideanNorm (fun i => b i - t * M i j) := by
    have hh := h (Pi.single j t)
    simpa [zeroIsLeastSquaresSolution, Matrix.mulVec_single, Matrix.col_apply,
      Matrix.mulVec_zero, Pi.smul_apply, smul_eq_mul, mul_comm] using hh
  have hd := min_imp_dot_zero b (fun i => M i j) hscalar
  simpa [Matrix.mulVec, dotProduct, mul_comm] using hd

private lemma dot_zero_imp_min {k : ℕ} (b v : Fin k → ℝ)
    (hd : (∑ i : Fin k, b i * v i) = 0) :
    euclideanNorm b ≤ euclideanNorm (b - v) := by
  have hcalc : (∑ i : Fin k, (b i - v i) ^ 2) =
      (∑ i : Fin k, (b i) ^ 2) + (∑ i : Fin k, (v i) ^ 2) := by
    calc
      _ = (∑ i : Fin k, ((b i) ^ 2 - 2 * (b i * v i) + (v i) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, hd, mul_zero, sub_zero]
  have hb := euclideanNorm_sq b
  have hr : euclideanNorm (b - v) ^ 2 =
      (∑ i : Fin k, (b i) ^ 2) + (∑ i : Fin k, (v i) ^ 2) := by
    calc
      _ = ∑ i : Fin k, ((b - v) i) ^ 2 := euclideanNorm_sq _
      _ = ∑ i : Fin k, (b i - v i) ^ 2 := by simp only [Pi.sub_apply]
      _ = _ := hcalc
  have hb0 : 0 ≤ euclideanNorm b := Real.sqrt_nonneg _
  have hr0 : 0 ≤ euclideanNorm (b - v) := Real.sqrt_nonneg _
  nlinarith [sum_sq_nonneg v]

private lemma normal_imp_optimal {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (h : M.transpose.mulVec b = 0) : zeroIsLeastSquaresSolution M b := by
  intro x
  simp only [Matrix.mulVec_zero, sub_zero]
  apply dot_zero_imp_min
  change b ⬝ᵥ M.mulVec x = 0
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h]
  simp

private lemma transpose_mulVec_norm_le {m n : ℕ}
    (E : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    euclideanNorm (E.transpose.mulVec b) ≤ frobeniusNorm E * euclideanNorm b := by
  have hc (j : Fin n) :
      ((E.transpose.mulVec b) j) ^ 2 ≤
        (∑ i : Fin m, (E i j) ^ 2) * (∑ i : Fin m, (b i) ^ 2) := by
    simpa [Matrix.mulVec, dotProduct, mul_comm] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
        (fun i => E i j) b)
  have hsum :
      (∑ j : Fin n, ((E.transpose.mulVec b) j) ^ 2) ≤
        (∑ i : Fin m, ∑ j : Fin n, (E i j) ^ 2) *
          (∑ i : Fin m, (b i) ^ 2) := by
    calc
      _ ≤ ∑ j : Fin n,
          ((∑ i : Fin m, (E i j) ^ 2) * (∑ i : Fin m, (b i) ^ 2)) :=
        Finset.sum_le_sum fun j _ => hc j
      _ = _ := by
        rw [← Finset.sum_mul, Finset.sum_comm]
  have hv := euclideanNorm_sq (E.transpose.mulVec b)
  have hE := frobeniusNorm_sq E
  have hb := euclideanNorm_sq b
  have hE0 : 0 ≤ frobeniusNorm E := Real.sqrt_nonneg _
  have hb0 : 0 ≤ euclideanNorm b := Real.sqrt_nonneg _
  have hv0 : 0 ≤ euclideanNorm (E.transpose.mulVec b) := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hE0 hb0]

private lemma rankOne_properties {m n : ℕ} (b : Fin m → ℝ) (v : Fin n → ℝ)
    (hb : b ≠ 0) :
    let q : ℝ := ∑ i : Fin m, (b i) ^ 2
    let D : Matrix (Fin m) (Fin n) ℝ := fun i j => -(b i * v j / q)
    D.transpose.mulVec b = -v ∧
      frobeniusNorm D = euclideanNorm v / euclideanNorm b := by
  dsimp only
  let q : ℝ := ∑ i : Fin m, (b i) ^ 2
  let D : Matrix (Fin m) (Fin n) ℝ := fun i j => -(b i * v j / q)
  have hbn : euclideanNorm b ≠ 0 := euclideanNorm_ne_zero hb
  have hq : q = euclideanNorm b ^ 2 := (euclideanNorm_sq b).symm
  have hq0 : q ≠ 0 := by rw [hq]; exact pow_ne_zero _ hbn
  have hDb : D.transpose.mulVec b = -v := by
    funext j
    change (∑ i : Fin m, D i j * b i) = -v j
    calc
      _ = (∑ i : Fin m, -(v j) * ((b i) ^ 2 / q)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [D]
        ring
      _ = -(v j) * ((∑ i : Fin m, (b i) ^ 2) / q) := by
        rw [← Finset.mul_sum, ← Finset.sum_div]
      _ = -v j := by rw [show (∑ i : Fin m, (b i) ^ 2) = q from rfl, div_self hq0]; ring
  have hDsum : (∑ i : Fin m, ∑ j : Fin n, (D i j) ^ 2) =
      (∑ j : Fin n, (v j) ^ 2) / q := by
    calc
      _ = ∑ i : Fin m, ∑ j : Fin n, (b i) ^ 2 * (v j) ^ 2 / q ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp [D]
        ring
      _ = (∑ i : Fin m, ∑ j : Fin n, (b i) ^ 2 * (v j) ^ 2) / q ^ 2 := by
        simp only [Finset.sum_div]
      _ = ((∑ i : Fin m, (b i) ^ 2) * (∑ j : Fin n, (v j) ^ 2)) / q ^ 2 := by
        congr 1
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
      _ = _ := by
        rw [show (∑ i : Fin m, (b i) ^ 2) = q from rfl]
        field_simp
  have hnormsq : frobeniusNorm D ^ 2 =
      (euclideanNorm v / euclideanNorm b) ^ 2 := by
    rw [frobeniusNorm_sq, hDsum, div_pow, euclideanNorm_sq v, ← hq]
  constructor
  · exact hDb
  · have hD0 : 0 ≤ frobeniusNorm D := Real.sqrt_nonneg _
    have hv0 : 0 ≤ euclideanNorm v / euclideanNorm b :=
      div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith

theorem target :
    ∀ (m n : ℕ) (_ : n ≤ m)
      (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
      ∃ ΔA : Matrix (Fin m) (Fin n) ℝ,
        zeroIsLeastSquaresSolution (A + ΔA) b ∧
        frobeniusNorm ΔA = zeroBackwardErrorValue A b ∧
        ∀ E : Matrix (Fin m) (Fin n) ℝ,
          zeroIsLeastSquaresSolution (A + E) b →
            zeroBackwardErrorValue A b ≤ frobeniusNorm E := by
  intro m n hmn A b
  by_cases hb : b = 0
  · subst b
    refine ⟨0, ?_, ?_, ?_⟩
    · apply normal_imp_optimal
      simp
    · simp [frobeniusNorm, zeroBackwardErrorValue]
    · intro E hE
      have hnn : 0 ≤ frobeniusNorm E := Real.sqrt_nonneg _
      simpa only [zeroBackwardErrorValue, if_pos rfl] using hnn
  · let v : Fin n → ℝ := A.transpose.mulVec b
    let q : ℝ := ∑ i : Fin m, (b i) ^ 2
    let D : Matrix (Fin m) (Fin n) ℝ := fun i j => -(b i * v j / q)
    have hD : D.transpose.mulVec b = -v ∧
        frobeniusNorm D = euclideanNorm v / euclideanNorm b := by
      exact rankOne_properties b v hb
    have hbpos : 0 < euclideanNorm b := by
      have hn := euclideanNorm_ne_zero hb
      have hp : 0 ≤ euclideanNorm b := Real.sqrt_nonneg _
      exact lt_of_le_of_ne hp (Ne.symm hn)
    refine ⟨D, ?_, ?_, ?_⟩
    · apply normal_imp_optimal
      rw [Matrix.transpose_add, Matrix.add_mulVec, hD.1]
      simp [v]
    · simpa [zeroBackwardErrorValue, hb, v] using hD.2
    · intro E hE
      have hz := optimal_imp_normal (A + E) b hE
      have hEd : E.transpose.mulVec b = -v := by
        have hh : v + E.transpose.mulVec b = 0 := by
          simpa [Matrix.transpose_add, Matrix.add_mulVec, v] using hz
        exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hh)
      have hvnorm : euclideanNorm v = euclideanNorm (E.transpose.mulVec b) := by
        rw [hEd]
        simp [euclideanNorm, Pi.neg_apply]
      rw [zeroBackwardErrorValue, if_neg hb]
      apply (div_le_iff₀ hbpos).2
      calc
        euclideanNorm (A.transpose.mulVec b) = euclideanNorm v := rfl
        _ = euclideanNorm (E.transpose.mulVec b) := hvnorm
        _ ≤ frobeniusNorm E * euclideanNorm b := transpose_mulVec_norm_le E b

end HighamBenchCandidate
