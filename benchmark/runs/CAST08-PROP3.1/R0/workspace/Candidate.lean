import Mathlib

namespace HighamBenchCandidate

/-- Sum `count + 1` child totals from left to right. The first total is
loaded directly; each later addition incurs its own relative error. -/
def roundedPrefix (δ : ℕ → ℕ → ℕ → ℝ) (level node : ℕ)
    (child : ℕ → ℝ) : ℕ → ℝ
  | 0 => child 0
  | k + 1 =>
      (roundedPrefix δ level node child k + child (k + 1)) *
        (1 + δ level node k)

/-- At level zero the nodes are inputs. Each further level combines `b`
consecutive nodes of the preceding level, in their original order. This is the
mathematical t-level summation in Section 3 and Figure 3.2. The literal loop
in Figure 3.1(a) omits the final transfer to temporary zero, so it does not
implement the described summation as printed. -/
def superblockLevel (b : ℕ) (x : ℕ → ℝ)
    (δ : ℕ → ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, node => x node
  | level + 1, node =>
      roundedPrefix δ level node
        (fun j => superblockLevel b x δ level (node * b + j)) (b - 1)

/-- The independently rounded additions actually performed in a `t` level
equal-block summation satisfy the standard relative-error model. -/
def admissibleErrors (t b : ℕ) (u : ℝ)
    (δ : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ level node step : ℕ,
    level < t → node < b ^ (t - level - 1) → step < b - 1 →
      |δ level node step| ≤ u

noncomputable def gamma (u : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) * u / (1 - (m : ℝ) * u)

private theorem roundedPrefix_zero (level node k : ℕ) (child : ℕ → ℝ) :
    roundedPrefix (fun _ _ _ => 0) level node child k =
      ∑ j ∈ Finset.range (k + 1), child j := by
  induction k with
  | zero => simp [roundedPrefix]
  | succ k ih =>
      simpa only [roundedPrefix, ih, add_zero, mul_one,
        Finset.sum_range_succ] using congrArg (fun z : ℝ => z + child (k + 1)) ih

private theorem sum_blocks (k m : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range k, ∑ i ∈ Finset.range m, f (j * m + i)) =
      ∑ i ∈ Finset.range (k * m), f i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]

private theorem superblockLevel_zero (b : ℕ) (x : ℕ → ℝ)
    (hb : 0 < b) (level node : ℕ) :
    superblockLevel b x (fun _ _ _ => 0) level node =
      ∑ i ∈ Finset.range (b ^ level), x (node * b ^ level + i) := by
  induction level generalizing node with
  | zero => simp [superblockLevel]
  | succ level ih =>
      have hpred : b - 1 + 1 = b := by omega
      rw [superblockLevel, roundedPrefix_zero, hpred]
      simp_rw [ih]
      calc
        (∑ j ∈ Finset.range b,
            ∑ i ∈ Finset.range (b ^ level), x ((node * b + j) * b ^ level + i)) =
            ∑ j ∈ Finset.range b,
              ∑ i ∈ Finset.range (b ^ level),
                x (node * b ^ (level + 1) + (j * b ^ level + i)) := by
                  congr 1
                  ext j
                  congr 1
                  ext i
                  congr 1
                  rw [pow_succ]
                  ring
        _ = ∑ i ∈ Finset.range (b ^ (level + 1)),
              x (node * b ^ (level + 1) + i) := by
                rw [pow_succ, mul_comm (b ^ level) b]
                exact sum_blocks b (b ^ level)
                  (fun i => x (node * (b * b ^ level) + i))

private theorem round_step_bound (p q P Q d u : ℝ)
    (hu : 0 ≤ u) (hd : |d| ≤ u) :
    |(p + q) * (1 + d) - (P + Q)| ≤
      (1 + u) * (|p - P| + |q - Q|) + u * (|P| + |Q|) := by
  have h1 : |1 + d| ≤ 1 + u := by
    calc
      |1 + d| ≤ |(1 : ℝ)| + |d| := abs_add_le _ _
      _ ≤ 1 + u := by simpa using add_le_add_left hd 1
  have h2 : 0 ≤ 1 + u := by linarith
  calc
    |(p + q) * (1 + d) - (P + Q)| =
        |(1 + d) * ((p - P) + (q - Q)) + d * (P + Q)| := by
          congr 1
          ring
    _ ≤ |1 + d| * |(p - P) + (q - Q)| + |d| * |P + Q| := by
          simpa only [abs_mul] using
            (abs_add_le ((1 + d) * ((p - P) + (q - Q))) (d * (P + Q)))
    _ ≤ (1 + u) * (|p - P| + |q - Q|) + u * (|P| + |Q|) := by
          apply add_le_add
          · exact (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)).trans
              (mul_le_mul_of_nonneg_left (abs_add_le _ _) h2)
          · exact (mul_le_mul_of_nonneg_right hd (abs_nonneg _)).trans
              (mul_le_mul_of_nonneg_left (abs_add_le _ _) hu)

private theorem roundedPrefix_bound
    (δ : ℕ → ℕ → ℕ → ℝ) (level node : ℕ)
    (child exact weight : ℕ → ℝ) (u A : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hA : 1 ≤ A)
    (hδ : ∀ j < k, |δ level node j| ≤ u)
    (hchild : ∀ j ≤ k, |child j - exact j| ≤ (A - 1) * weight j)
    (hexact : ∀ j ≤ k, |exact j| ≤ weight j) :
    |roundedPrefix δ level node child k -
        ∑ j ∈ Finset.range (k + 1), exact j| ≤
      (A * (1 + u) ^ k - 1) *
        ∑ j ∈ Finset.range (k + 1), weight j := by
  induction k with
  | zero =>
      simpa [roundedPrefix] using hchild 0 (le_refl 0)
  | succ k ih =>
      let S : ℝ := ∑ j ∈ Finset.range (k + 1), exact j
      let W : ℝ := ∑ j ∈ Finset.range (k + 1), weight j
      have hW : 0 ≤ W := by
        apply Finset.sum_nonneg
        intro j hj
        exact (abs_nonneg _).trans (hexact j (by
          have := Finset.mem_range.mp hj
          omega))
      have hS : |S| ≤ W := by
        calc
          |S| ≤ ∑ j ∈ Finset.range (k + 1), |exact j| := by
            exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ W := by
            apply Finset.sum_le_sum
            intro j hj
            exact hexact j (by
              have := Finset.mem_range.mp hj
              omega)
      have hprev :
          |roundedPrefix δ level node child k - S| ≤
            (A * (1 + u) ^ k - 1) * W := by
        apply ih
        · intro j hj
          exact hδ j (by omega)
        · intro j hj
          exact hchild j (by omega)
        · intro j hj
          exact hexact j (by omega)
      have hnext := hchild (k + 1) (le_refl _)
      have hweight : 0 ≤ weight (k + 1) :=
        (abs_nonneg _).trans (hexact (k + 1) (le_refl _))
      have hA0 : 0 ≤ A := by linarith
      have ha : 1 ≤ 1 + u := by linarith
      have hak : 1 ≤ (1 + u) ^ k := one_le_pow₀ ha
      have hcoeff : A * (1 + u) - 1 ≤ A * (1 + u) ^ (k + 1) - 1 := by
        rw [pow_succ]
        nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hak),
          mul_nonneg (mul_nonneg hA0 (sub_nonneg.mpr hak)) (by linarith : 0 ≤ 1 + u)]
      have hround := round_step_bound
        (roundedPrefix δ level node child k) (child (k + 1))
        S (exact (k + 1)) (δ level node k) u hu
        (hδ k (by omega))
      have hpre :
          |roundedPrefix δ level node child (k + 1) -
            (S + exact (k + 1))| ≤
            (1 + u) * (|roundedPrefix δ level node child k - S| +
              |child (k + 1) - exact (k + 1)|) +
              u * (|S| + |exact (k + 1)|) := by
        simpa only [roundedPrefix] using hround
      have hbound :
          |roundedPrefix δ level node child (k + 1) -
            (S + exact (k + 1))| ≤
            (A * (1 + u) ^ (k + 1) - 1) *
              (W + weight (k + 1)) := by
        have hstep :
            (1 + u) * (|roundedPrefix δ level node child k - S| +
              |child (k + 1) - exact (k + 1)|) +
              u * (|S| + |exact (k + 1)|) ≤
            (1 + u) * ((A * (1 + u) ^ k - 1) * W +
              (A - 1) * weight (k + 1)) +
              u * (W + weight (k + 1)) := by
          gcongr
          exact hexact (k + 1) (le_refl _)
        calc
          _ ≤ (1 + u) * ((A * (1 + u) ^ k - 1) * W +
                (A - 1) * weight (k + 1)) +
                u * (W + weight (k + 1)) := hpre.trans hstep
          _ ≤ (A * (1 + u) ^ (k + 1) - 1) *
                (W + weight (k + 1)) := by
              calc
                _ = (A * (1 + u) ^ (k + 1) - 1) * W +
                    (A * (1 + u) - 1) * weight (k + 1) := by
                      rw [pow_succ]
                      ring
                _ ≤ (A * (1 + u) ^ (k + 1) - 1) *
                    (W + weight (k + 1)) := by
                      nlinarith [mul_le_mul_of_nonneg_right hcoeff hweight]
      simpa only [S, W, Finset.sum_range_succ] using hbound

private theorem child_index (t b level node j : ℕ)
    (hle : level + 1 ≤ t) (hn : node < b ^ (t - (level + 1)))
    (hj : j < b) : node * b + j < b ^ (t - level) := by
  have he : t - level = (t - (level + 1)) + 1 := by omega
  rw [he, pow_succ]
  have hm := Nat.mul_le_mul_right b (Nat.succ_le_iff.mpr hn)
  rw [Nat.succ_mul] at hm
  omega

private theorem superblockLevel_bound
    (t b : ℕ) (hb : 0 < b) (u : ℝ) (hu : 0 ≤ u)
    (x : ℕ → ℝ) (δ : ℕ → ℕ → ℕ → ℝ)
    (hδ : admissibleErrors t b u δ)
    (level node : ℕ) (hle : level ≤ t)
    (hn : node < b ^ (t - level)) :
    |superblockLevel b x δ level node -
      superblockLevel b x (fun _ _ _ => 0) level node| ≤
      ((1 + u) ^ (level * (b - 1)) - 1) *
        superblockLevel b (fun n => |x n|) (fun _ _ _ => 0) level node := by
  induction level generalizing node with
  | zero => simp [superblockLevel]
  | succ level ih =>
      have hpred : b - 1 + 1 = b := by omega
      have hparent : level < t := by omega
      have ha : 1 ≤ 1 + u := by linarith
      have hchild (j : ℕ) (hj : j ≤ b - 1) :
          node * b + j < b ^ (t - level) := by
        apply child_index t b level node j hle hn
        omega
      have hchildbound (j : ℕ) (hj : j ≤ b - 1) :
          |superblockLevel b x δ level (node * b + j) -
            superblockLevel b x (fun _ _ _ => 0) level (node * b + j)| ≤
            ((1 + u) ^ (level * (b - 1)) - 1) *
              superblockLevel b (fun n => |x n|) (fun _ _ _ => 0)
                level (node * b + j) :=
        ih (node * b + j) (by omega) (hchild j hj)
      have habs (j : ℕ) (hj : j ≤ b - 1) :
          |superblockLevel b x (fun _ _ _ => 0) level (node * b + j)| ≤
            superblockLevel b (fun n => |x n|) (fun _ _ _ => 0)
              level (node * b + j) := by
        rw [superblockLevel_zero b x hb,
          superblockLevel_zero b (fun n => |x n|) hb]
        exact Finset.abs_sum_le_sum_abs _ _
      have hp := roundedPrefix_bound δ level node
        (fun j => superblockLevel b x δ level (node * b + j))
        (fun j => superblockLevel b x (fun _ _ _ => 0) level (node * b + j))
        (fun j => superblockLevel b (fun n => |x n|) (fun _ _ _ => 0)
          level (node * b + j))
        u ((1 + u) ^ (level * (b - 1))) (b - 1)
        hu (one_le_pow₀ ha)
        (by
          intro j hj
          exact hδ level node j hparent (by simpa only [Nat.succ_eq_add_one] using hn) hj)
        hchildbound habs
      have hexp :
          (1 + u) ^ (level * (b - 1)) * (1 + u) ^ (b - 1) =
            (1 + u) ^ ((level + 1) * (b - 1)) := by
        rw [← pow_add, Nat.add_mul]
        simp
      simpa only [superblockLevel, roundedPrefix_zero, hpred, hexp] using hp

private theorem pow_one_add_le_inv (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hm : (m : ℝ) * u < 1) :
    (1 + u) ^ m ≤ 1 / (1 - (m : ℝ) * u) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm' : (m : ℝ) * u < 1 := by
        have hc : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc hu) hm
      have hd : 0 < 1 - ((m + 1 : ℕ) : ℝ) * u := by
        have : (((m + 1 : ℕ) : ℝ) * u) < 1 := hm
        linarith
      have hd' : 0 < 1 - (m : ℝ) * u := by linarith
      have hmul :
          (1 + u) * (1 - ((m + 1 : ℕ) : ℝ) * u) ≤
            1 - (m : ℝ) * u := by
        push_cast
        nlinarith [sq_nonneg u, mul_nonneg (Nat.cast_nonneg m) hu]
      calc
        (1 + u) ^ (m + 1) = (1 + u) ^ m * (1 + u) := pow_succ _ _
        _ ≤ (1 / (1 - (m : ℝ) * u)) * (1 + u) := by
          exact mul_le_mul_of_nonneg_right (ih hm') (by linarith)
        _ = (1 + u) / (1 - (m : ℝ) * u) := by ring
        _ ≤ 1 / (1 - ((m + 1 : ℕ) : ℝ) * u) := by
          apply (div_le_div_iff₀ hd' hd).mpr
          simpa only [mul_one, one_mul] using hmul

private theorem pow_error_le_gamma (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hm : (m : ℝ) * u < 1) :
    (1 + u) ^ m - 1 ≤ gamma u m := by
  have hd : 1 - (m : ℝ) * u ≠ 0 := by linarith
  calc
    (1 + u) ^ m - 1 ≤ 1 / (1 - (m : ℝ) * u) - 1 :=
      sub_le_sub_right (pow_one_add_le_inv u m hu hm) _
    _ = gamma u m := by
      unfold gamma
      field_simp
      ring

private theorem optimal_counter (t b : ℕ) (ht : 0 < t) (hb : 0 < b)
    (factors : Fin t → ℕ) (hf : ∀ i, 0 < factors i)
    (hprod : (∏ i : Fin t, factors i) = b ^ t) :
    t * (b - 1) ≤ ∑ i : Fin t, (factors i - 1) := by
  have ham := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset (Fin t)) (fun _ => (1 : ℝ))
    (fun i => (factors i : ℝ))
    (by simp) (by simp [ht]) (by simp)
  have hprodR : (∏ i : Fin t, (factors i : ℝ)) = (b : ℝ) ^ t := by
    exact_mod_cast hprod
  have hpow : (b : ℝ) ^ t > 0 := pow_pos (by exact_mod_cast hb) _
  have hroot : ((b : ℝ) ^ t) ^ ((t : ℝ)⁻¹) = b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (by exact_mod_cast hb))]
    have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
    rw [mul_inv_cancel₀ htR, Real.rpow_one]
  have hsumR : (t : ℝ) * b ≤ ∑ i : Fin t, (factors i : ℝ) := by
    simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, one_mul, mul_one] at ham
    rw [hprodR, hroot] at ham
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    have htmp : (b : ℝ) * t ≤ ∑ i : Fin t, (factors i : ℝ) :=
      (le_div_iff₀ htpos).mp ham
    simpa [mul_comm] using htmp
  have hsumN : t * b ≤ ∑ i : Fin t, factors i := by
    exact_mod_cast hsumR
  have hcounter :
      (∑ i : Fin t, (factors i - 1)) + t =
        ∑ i : Fin t, factors i := by
    calc
      _ = ∑ i : Fin t, ((factors i - 1) + 1) := by simp [Finset.sum_add_distrib]
      _ = ∑ i : Fin t, factors i := by
        apply Finset.sum_congr rfl
        intro i _
        have := hf i
        omega
  have htb : t * (b - 1) + t = t * b := by
    have : b - 1 + 1 = b := by omega
    calc
      t * (b - 1) + t = t * (b - 1 + 1) := by ring
      _ = t * b := by rw [this]
  omega

/-- Proposition 3.1: equal integral blocking is optimal for the error
counter, and its recursively computed sum has the corresponding forward
error bound under the standard no-overflow/no-underflow relative model. -/
theorem target :
    ∀ (t b : ℕ), 0 < t → 0 < b →
      (∀ factors : Fin t → ℕ,
        (∀ i, 0 < factors i) →
        (∏ i : Fin t, factors i) = b ^ t →
        t * (b - 1) ≤ ∑ i : Fin t, (factors i - 1)) ∧
      (∏ _i : Fin t, b) = b ^ t ∧
      (∑ _i : Fin t, (b - 1)) = t * (b - 1) ∧
      (∀ (u : ℝ) (x : Fin (b ^ t) → ℝ)
          (δ : ℕ → ℕ → ℕ → ℝ),
        0 < u → (t * (b - 1) : ℕ) * u < 1 →
        admissibleErrors t b u δ →
        |superblockLevel b
            (fun n => if h : n < b ^ t then x ⟨n, h⟩ else 0)
            δ t 0 - ∑ i : Fin (b ^ t), x i| ≤
          gamma u (t * (b - 1)) *
            ∑ i : Fin (b ^ t), |x i|) := by
  intro t b ht hb
  constructor
  · intro factors hf hprod
    exact optimal_counter t b ht hb factors hf hprod
  constructor
  · simp
  constructor
  · simp
  intro u x δ hu hvalid hδ
  let y : ℕ → ℝ := fun n => if h : n < b ^ t then x ⟨n, h⟩ else 0
  have hsum :
      superblockLevel b y (fun _ _ _ => 0) t 0 =
        ∑ i : Fin (b ^ t), x i := by
    rw [superblockLevel_zero b y hb]
    simp only [Nat.zero_mul, zero_add]
    rw [Finset.sum_fin_eq_sum_range]
  have habssum :
      superblockLevel b (fun n => |y n|) (fun _ _ _ => 0) t 0 =
        ∑ i : Fin (b ^ t), |x i| := by
    rw [superblockLevel_zero b (fun n => |y n|) hb]
    simp only [Nat.zero_mul, zero_add]
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [y, Finset.mem_range.mp hi]
  have hlevel := superblockLevel_bound t b hb u (le_of_lt hu) y δ hδ t 0
    (le_refl t) (by simp)
  have hgamma := pow_error_le_gamma u (t * (b - 1)) (le_of_lt hu) hvalid
  have hnonneg : (0 : ℝ) ≤ ∑ i : Fin (b ^ t), |x i| := by positivity
  change |superblockLevel b y δ t 0 - ∑ i : Fin (b ^ t), x i| ≤
    gamma u (t * (b - 1)) * ∑ i : Fin (b ^ t), |x i|
  calc
    |superblockLevel b y δ t 0 - ∑ i : Fin (b ^ t), x i| ≤
        ((1 + u) ^ (t * (b - 1)) - 1) *
          ∑ i : Fin (b ^ t), |x i| := by
            simpa only [hsum, habssum] using hlevel
    _ ≤ gamma u (t * (b - 1)) * ∑ i : Fin (b ^ t), |x i| :=
      mul_le_mul_of_nonneg_right hgamma hnonneg

end HighamBenchCandidate
