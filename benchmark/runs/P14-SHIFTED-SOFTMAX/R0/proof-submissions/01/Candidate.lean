import Mathlib

namespace HighamBenchCandidate

/-- The exact shifted exponential at each input entry. -/
noncomputable def exactWeight {n : ℕ} (x : Fin n → ℝ) (k i : Fin n) : ℝ :=
  Real.exp (x i - x k)

/-- The exponential after a rounded subtraction and a relative error in `exp`. -/
noncomputable def computedWeight {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (subError expError : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp ((x i - x k) * (1 + subError i)) * (1 + expError i)

/-- Sum the nonmaximal weights in the supplied order. The first term is copied
exactly; every subsequent addition has one relative rounding error. -/
def roundedSum {n : ℕ} (w addError : Fin n → ℝ) : List (Fin n) → ℝ
  | [] => 0
  | i :: is => is.foldl (fun s j => (s + w j) * (1 + addError j)) (w i)

/-- Exact softmax, using the selected maximum as the shift. -/
noncomputable def exactSoftmax {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (order : List (Fin n)) (i : Fin n) : ℝ :=
  exactWeight x k i / (1 + (order.map (exactWeight x k)).sum)

/-- Shifted softmax with rounded exponentials, recursively summed nonmaximal
weights, and one rounded division per output. -/
noncomputable def computedSoftmax {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (order : List (Fin n)) (subError expError addError divError : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  let w := computedWeight x k subError expError
  (w i / (1 + roundedSum w addError order)) * (1 + divError i)

/-- The minimum input entry. -/
noncomputable def minimumEntry {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sInf (Set.range x)

private theorem minimumEntry_le {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    minimumEntry x ≤ x i := by
  unfold minimumEntry
  exact csInf_le (Finite.bddBelow_range x) ⟨i, rfl⟩

private theorem shift_nonneg {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (hk : ∀ i, x i ≤ x k) (i : Fin n) : 0 ≤ x k - x i := by
  exact sub_nonneg.mpr (hk i)

private theorem shift_le_range {n : ℕ} (x : Fin n → ℝ) (k i : Fin n) :
    x k - x i ≤ x k - minimumEntry x := by
  exact sub_le_sub_left (minimumEntry_le x i) _

private theorem exp_linear_bound (t u D : ℝ) (hu : 0 ≤ u) (hD : 0 ≤ D)
    (ht : |t| ≤ D * u) (hsmall : D * u ≤ 1) :
    |Real.exp t - 1| ≤ D * u + D ^ 2 * u ^ 2 := by
  have hrem : |Real.exp t - 1 - t| ≤ |t| ^ 2 := by
    simpa only [Real.norm_eq_abs] using
      (Real.norm_exp_sub_one_sub_id_le (show ‖t‖ ≤ 1 by
        simpa only [Real.norm_eq_abs] using ht.trans hsmall))
  have hsq : |t| ^ 2 ≤ (D * u) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht)
      (add_nonneg (abs_nonneg t) (mul_nonneg hD hu))]
  calc
    |Real.exp t - 1| = |(Real.exp t - 1 - t) + t| := by ring
    _ ≤ |Real.exp t - 1 - t| + |t| := abs_add_le _ _
    _ ≤ |t| ^ 2 + |t| := by gcongr
    _ ≤ D * u + D ^ 2 * u ^ 2 := by nlinarith

private theorem exp_factor_bound (t e u D : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hD : 0 ≤ D) (ht : |t| ≤ D * u) (hsmall : D * u ≤ 1)
    (he : |e| ≤ u) :
    |Real.exp t * (1 + e) - 1| ≤
      (D + 1) * u + (2 * D ^ 2 + D) * u ^ 2 := by
  have hlin := exp_linear_bound t u D hu hD ht hsmall
  have hprod : |(Real.exp t - 1) * e| ≤
      (D * u + D ^ 2 * u ^ 2) * u := by
    rw [abs_mul]
    exact mul_le_mul hlin he (abs_nonneg _) (by positivity)
  have hmain : Real.exp t * (1 + e) - 1 =
      (Real.exp t - 1) + e + (Real.exp t - 1) * e := by ring
  rw [hmain]
  calc
    |(Real.exp t - 1) + e + (Real.exp t - 1) * e| ≤
        |(Real.exp t - 1) + e| + |(Real.exp t - 1) * e| := abs_add_le _ _
    _ ≤ |Real.exp t - 1| + |e| + |(Real.exp t - 1) * e| := by
      exact add_le_add_left (abs_add_le (Real.exp t - 1) e)
        |(Real.exp t - 1) * e|
    _ ≤ D * u + D ^ 2 * u ^ 2 + u +
        (D * u + D ^ 2 * u ^ 2) * u := by gcongr
    _ ≤ (D + 1) * u + (2 * D ^ 2 + D) * u ^ 2 := by
      have hDsq : 0 ≤ D ^ 2 := sq_nonneg D
      nlinarith [mul_nonneg (mul_nonneg hDsq (sq_nonneg u)) (sub_nonneg.mpr hu1)]

private theorem computedWeight_error {n : ℕ} (x : Fin n → ℝ) (k i : Fin n)
    (hk : ∀ j, x j ≤ x k) (subError expError : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hsmall : (x k - minimumEntry x) * u ≤ 1)
    (hsub : ∀ j, |subError j| ≤ u) (hexp : ∀ j, |expError j| ≤ u) :
    |computedWeight x k subError expError i - exactWeight x k i| ≤
      exactWeight x k i *
        (((x k - minimumEntry x) + 1) * u +
          (2 * (x k - minimumEntry x) ^ 2 + (x k - minimumEntry x)) * u ^ 2) := by
  let D := x k - minimumEntry x
  have hD : 0 ≤ D := sub_nonneg.mpr (minimumEntry_le x k)
  have ht : |(x i - x k) * subError i| ≤ D * u := by
    rw [abs_mul, abs_sub_comm, abs_of_nonneg (shift_nonneg x k hk i)]
    exact mul_le_mul (shift_le_range x k i) (hsub i) (abs_nonneg _) hD
  have hf := exp_factor_bound ((x i - x k) * subError i)
    (expError i) u D hu hu1 hD ht hsmall (hexp i)
  have heq : computedWeight x k subError expError i =
      exactWeight x k i *
        (Real.exp ((x i - x k) * subError i) * (1 + expError i)) := by
    unfold computedWeight exactWeight
    rw [show (x i - x k) * (1 + subError i) =
        (x i - x k) + (x i - x k) * subError i by ring, Real.exp_add]
    ring
  rw [heq]
  have hwpos : 0 ≤ exactWeight x k i := (Real.exp_pos _).le
  calc
    |exactWeight x k i *
        (Real.exp ((x i - x k) * subError i) * (1 + expError i)) -
        exactWeight x k i| =
      exactWeight x k i *
        |Real.exp ((x i - x k) * subError i) * (1 + expError i) - 1| := by
          rw [show exactWeight x k i *
              (Real.exp ((x i - x k) * subError i) * (1 + expError i)) -
              exactWeight x k i = exactWeight x k i *
              (Real.exp ((x i - x k) * subError i) * (1 + expError i) - 1) by ring,
            abs_mul, abs_of_nonneg hwpos]
    _ ≤ exactWeight x k i *
        ((D + 1) * u + (2 * D ^ 2 + D) * u ^ 2) := by
          exact mul_le_mul_of_nonneg_left hf hwpos

private def sumQuadratic : ℕ → ℝ → ℝ → ℝ
  | 0, _, B => B
  | m + 1, A, B => sumQuadratic m (A + 1) (2 * B + A)

private theorem sumQuadratic_nonneg (m : ℕ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ sumQuadratic m A B := by
  induction m generalizing A B with
  | zero => simpa [sumQuadratic] using hB
  | succ m ih =>
      exact ih (A + 1) (2 * B + A) (by positivity) (by positivity)

private theorem fold_error_bound {α : Type*} (ls : List α) :
    ∀ (e w addError : α → ℝ) (s es A B u : ℝ),
      0 ≤ u → u ≤ 1 → 0 ≤ A → 0 ≤ B → 0 ≤ es →
      (∀ j ∈ ls, 0 ≤ e j ∧ |w j - e j| ≤ e j * (A * u + B * u ^ 2)) →
      |s - es| ≤ es * (A * u + B * u ^ 2) →
      (∀ j ∈ ls, |addError j| ≤ u) →
      |ls.foldl (fun acc j => (acc + w j) * (1 + addError j)) s -
          (es + (ls.map e).sum)| ≤
        (es + (ls.map e).sum) *
          ((A + (ls.length : ℝ)) * u + sumQuadratic ls.length A B * u ^ 2) := by
  induction ls with
  | nil =>
      intro e w addError s es A B u hu hu1 hA hB hes hw hs hd
      simpa [sumQuadratic] using hs
  | cons j js ih =>
      intro e w addError s es A B u hu hu1 hA hB hes hw hs hd
      have hj := hw j (by simp)
      have hδ := hd j (by simp)
      let E := es + e j
      let q := A * u + B * u ^ 2
      have hE : 0 ≤ E := add_nonneg hes hj.1
      have hbefore : |s + w j - E| ≤ E * q := by
        have heq : s + w j - E = (s - es) + (w j - e j) := by
          dsimp [E]
          ring
        rw [heq]
        calc
          |(s - es) + (w j - e j)| ≤ |s - es| + |w j - e j| := abs_add_le _ _
          _ ≤ es * q + e j * q := add_le_add hs hj.2
          _ = E * q := by dsimp [E]; ring
      have hbeforeAbs : |s + w j| ≤ E + E * q := by
        have h := abs_add_le (s + w j - E) E
        have heq : s + w j - E + E = s + w j := by ring
        rw [heq, abs_of_nonneg hE] at h
        calc
          |s + w j| ≤ |s + w j - E| + E := h
          _ ≤ E * q + E := add_le_add_left hbefore E
          _ = E + E * q := by ring
      have hnew : |(s + w j) * (1 + addError j) - E| ≤
          E * ((A + 1) * u + (2 * B + A) * u ^ 2) := by
        have heq : (s + w j) * (1 + addError j) - E =
            (s + w j - E) + (s + w j) * addError j := by ring
        rw [heq]
        have hmul : |(s + w j) * addError j| ≤ (E + E * q) * u := by
          rw [abs_mul]
          exact mul_le_mul hbeforeAbs hδ (abs_nonneg _) (by positivity)
        have hrough : |(s + w j - E) + (s + w j) * addError j| ≤
            E * q + (E + E * q) * u :=
          (abs_add_le _ _).trans (add_le_add hbefore hmul)
        have hnonneg : 0 ≤ E * B * u ^ 2 := by positivity
        have hsmall : E * B * u ^ 3 ≤ E * B * u ^ 2 := by
          nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hu1)]
        dsimp [q] at hrough
        nlinarith
      have hweight' : ∀ t ∈ js, 0 ≤ e t ∧
          |w t - e t| ≤ e t * ((A + 1) * u + (2 * B + A) * u ^ 2) := by
        intro t ht
        have h := hw t (by simp [ht])
        refine ⟨h.1, h.2.trans ?_⟩
        have hq : A * u + B * u ^ 2 ≤
            (A + 1) * u + (2 * B + A) * u ^ 2 := by
          nlinarith [sq_nonneg u, mul_nonneg (add_nonneg hB hA) (sq_nonneg u)]
        exact mul_le_mul_of_nonneg_left hq h.1
      have htail : ∀ t ∈ js, |addError t| ≤ u := by
        intro t ht
        exact hd t (by simp [ht])
      have hres := ih e w addError ((s + w j) * (1 + addError j)) E
        (A + 1) (2 * B + A) u hu hu1 (by positivity) (by positivity)
        hE hweight' hnew htail
      simpa [sumQuadratic, E, List.foldl_cons, List.map_cons, Nat.cast_add,
        Nat.cast_one, add_assoc, add_comm, add_left_comm] using hres

private def sumRemainder {n : ℕ} (order : List (Fin n)) (D : ℝ) : ℝ :=
  match order with
  | [] => 0
  | _ :: rest => sumQuadratic rest.length (D + 1) (2 * D ^ 2 + D)

private theorem sumRemainder_nonneg {n : ℕ} (order : List (Fin n)) (D : ℝ)
    (hD : 0 ≤ D) : 0 ≤ sumRemainder order D := by
  cases order with
  | nil => simp [sumRemainder]
  | cons _ rest =>
      simpa [sumRemainder] using
        (sumQuadratic_nonneg rest.length (D + 1) (2 * D ^ 2 + D)
          (by positivity) (by positivity))

private theorem roundedSum_error {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (order : List (Fin n)) (horder : order.Nodup)
    (hk : ∀ j, x j ≤ x k) (subError expError addError : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hsmall : (x k - minimumEntry x) * u ≤ 1)
    (hsub : ∀ j, |subError j| ≤ u)
    (hexp : ∀ j, |expError j| ≤ u)
    (hadd : ∀ j, |addError j| ≤ u) :
    |roundedSum (computedWeight x k subError expError) addError order -
        (order.map (exactWeight x k)).sum| ≤
      (order.map (exactWeight x k)).sum *
        (((n : ℝ) + (x k - minimumEntry x)) * u +
          sumRemainder order (x k - minimumEntry x) * u ^ 2) := by
  let D := x k - minimumEntry x
  have hD : 0 ≤ D := sub_nonneg.mpr (minimumEntry_le x k)
  cases order with
  | nil => simp [roundedSum]
  | cons i rest =>
      let e := exactWeight x k
      let w := computedWeight x k subError expError
      have hA : 0 ≤ D + 1 := by positivity
      have hB : 0 ≤ 2 * D ^ 2 + D := by positivity
      have hweights : ∀ j ∈ rest, 0 ≤ e j ∧
          |w j - e j| ≤ e j * ((D + 1) * u + (2 * D ^ 2 + D) * u ^ 2) := by
        intro j _
        exact ⟨(Real.exp_pos _).le,
          computedWeight_error x k j hk subError expError u hu hu1 hsmall hsub hexp⟩
      have hstart : |w i - e i| ≤
          e i * ((D + 1) * u + (2 * D ^ 2 + D) * u ^ 2) :=
        computedWeight_error x k i hk subError expError u hu hu1 hsmall hsub hexp
      have hfold := fold_error_bound rest e w addError (w i) (e i)
        (D + 1) (2 * D ^ 2 + D) u hu hu1 hA hB
        (Real.exp_pos _).le hweights hstart (fun j _ => hadd j)
      have hlenNat : rest.length + 1 ≤ n := by
        have h := horder.length_le_card
        simpa using h
      have hlen : (rest.length : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlenNat
      have hcoeff : D + 1 + (rest.length : ℝ) ≤ (n : ℝ) + D := by linarith
      have hinner : ((D + 1) + (rest.length : ℝ)) * u +
          sumQuadratic rest.length (D + 1) (2 * D ^ 2 + D) * u ^ 2 ≤
          ((n : ℝ) + D) * u +
          sumQuadratic rest.length (D + 1) (2 * D ^ 2 + D) * u ^ 2 := by
        gcongr
      have hsum : 0 ≤ e i + (rest.map e).sum := by
        have hrest : 0 ≤ (rest.map e).sum := by
          apply List.sum_nonneg
          intro z hz
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
          exact (Real.exp_pos _).le
        exact add_nonneg (Real.exp_pos _).le hrest
      have hfin := hfold.trans (mul_le_mul_of_nonneg_left hinner hsum)
      simpa [roundedSum, sumRemainder, e, w, D, add_assoc,
        add_comm, add_left_comm] using hfin

private theorem multiply_relative_error (v w δ A B u : ℝ)
    (hw : 0 ≤ w) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hv : |v - w| ≤ w * (A * u + B * u ^ 2))
    (hδ : |δ| ≤ u) :
    |v * (1 + δ) - w| ≤
      w * ((A + 1) * u + (2 * B + A) * u ^ 2) := by
  let q := A * u + B * u ^ 2
  have hvabs : |v| ≤ w + w * q := by
    have h := abs_add_le (v - w) w
    have heq : v - w + w = v := by ring
    rw [heq, abs_of_nonneg hw] at h
    calc
      |v| ≤ |v - w| + w := h
      _ ≤ w * q + w := add_le_add_left hv w
      _ = w + w * q := by ring
  have hmul : |v * δ| ≤ (w + w * q) * u := by
    rw [abs_mul]
    exact mul_le_mul hvabs hδ (abs_nonneg _) (by positivity)
  have heq : v * (1 + δ) - w = (v - w) + v * δ := by ring
  rw [heq]
  have hrough : |(v - w) + v * δ| ≤ w * q + (w + w * q) * u :=
    (abs_add_le _ _).trans (add_le_add hv hmul)
  have hsmall : w * B * u ^ 3 ≤ w * B * u ^ 2 := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ w * B * u ^ 2)
      (sub_nonneg.mpr hu1)]
  dsimp [q] at hrough
  nlinarith

private theorem quotient_relative_error (v w V T a b d e u : ℝ)
    (hw : 0 ≤ w) (hT : 0 < T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hnum : |v - w| ≤ w * (a * u + b * u ^ 2))
    (hden : |V - T| ≤ T * (d * u + e * u ^ 2))
    (hhalf : (d + e) * u ≤ 1 / 2) :
    |v / V - w / T| ≤
      (w / T) * ((a + d) * u +
        2 * (b + e + (d + e) * (a + d)) * u ^ 2) := by
  let qn := a * u + b * u ^ 2
  let qd := d * u + e * u ^ 2
  let A := a + d
  let B := b + e
  let c := d + e
  let C := 2 * (B + c * A)
  let p := A * u + C * u ^ 2
  have hqdn : 0 ≤ qd := by dsimp [qd]; positivity
  have hqdu : qd ≤ c * u := by
    dsimp [qd, c]
    nlinarith [mul_nonneg he (mul_nonneg hu (sub_nonneg.mpr hu1))]
  have hqh : qd ≤ 1 / 2 := hqdu.trans hhalf
  have hVlower : T * (1 - qd) ≤ V := by
    have h := (abs_le.mp hden).1
    dsimp [qd] at *
    nlinarith
  have hV : 0 < V := by
    have hq : 0 < 1 - qd := by linarith
    exact lt_of_lt_of_le (mul_pos hT hq) hVlower
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hscalar : qn + qd ≤ (1 - qd) * p := by
    have h1 : qd * (A * u) ≤ c * A * u ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hqdu)
        (mul_nonneg hA hu)]
    have h2 : qd * (C * u ^ 2) ≤ (1 / 2) * (C * u ^ 2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hqh)
        (mul_nonneg hC (sq_nonneg u))]
    dsimp [qn, qd, p, A, B, c, C] at *
    nlinarith
  have hcompare : T * (qn + qd) ≤ V * p := by
    have h1 := mul_le_mul_of_nonneg_left hscalar hT.le
    have h2 := mul_le_mul_of_nonneg_right hVlower hp
    nlinarith
  have hN : |(v - w) * T - w * (V - T)| ≤ w * T * (qn + qd) := by
    calc
      |(v - w) * T - w * (V - T)| ≤
          |(v - w) * T| + |w * (V - T)| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              (abs_add_le ((v - w) * T) (-(w * (V - T))))
      _ = |v - w| * T + w * |V - T| := by
        rw [abs_mul, abs_mul, abs_of_pos hT, abs_of_nonneg hw]
      _ ≤ (w * qn) * T + w * (T * qd) := by
        exact add_le_add (mul_le_mul_of_nonneg_right hnum hT.le)
          (mul_le_mul_of_nonneg_left hden hw)
      _ = w * T * (qn + qd) := by ring
  have heq : v / V - w / T =
      ((v - w) * T - w * (V - T)) / (V * T) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (mul_pos hV hT)]
  calc
    |(v - w) * T - w * (V - T)| / (V * T) ≤
        (w * V * p) / (V * T) := by
          apply div_le_div_of_nonneg_right _ (mul_pos hV hT).le
          exact hN.trans (by simpa only [mul_assoc] using
            (mul_le_mul_of_nonneg_left hcompare hw))
    _ = (w / T) * p := by field_simp

/-- Theorem 4.3, equation (4.11), of Blanchard, D. J. Higham, and N. J.
Higham. The quadratic remainder is uniform in all local rounding errors for
each fixed input, selected maximum, and summation order. -/
theorem target :
    ∀ (n : ℕ) (x : Fin n → ℝ) (k : Fin n) (order : List (Fin n)),
      2 ≤ n →
      (∀ i, x i ≤ x k) →
      order.Nodup →
      (∀ i, i ∈ order ↔ i ≠ k) →
      ∃ (C ε : ℝ), 0 ≤ C ∧ 0 < ε ∧
        ∀ (u : ℝ), 0 < u → u < ε →
          ∀ (subError expError addError divError : Fin n → ℝ),
            (∀ i, |subError i| ≤ u) →
            (∀ i, |expError i| ≤ u) →
            (∀ i, |addError i| ≤ u) →
            (∀ i, |divError i| ≤ u) →
            ‖(fun i : Fin n =>
                computedSoftmax x k order subError expError addError divError i -
                  exactSoftmax x k order i)‖ /
                ‖(fun i : Fin n => exactSoftmax x k order i)‖ ≤
              ((n : ℝ) + 2 + 2 * (x k - minimumEntry x)) * u + C * u ^ 2 := by
  intro n x k order hn hk hnodup horder
  let D : ℝ := x k - minimumEntry x
  let S : ℝ := (order.map (exactWeight x k)).sum
  let T : ℝ := 1 + S
  let aw : ℝ := D + 1
  let bw : ℝ := 2 * D ^ 2 + D
  let a : ℝ := aw + 1
  let b : ℝ := 2 * bw + aw
  let d : ℝ := (n : ℝ) + D
  let e : ℝ := sumRemainder order D
  let c : ℝ := d + e
  let A : ℝ := a + d
  let C : ℝ := 2 * (b + e + c * A)
  let M : ℝ := D + c + 2
  let ε : ℝ := 1 / (2 * M)
  have hD : 0 ≤ D := sub_nonneg.mpr (minimumEntry_le x k)
  have he : 0 ≤ e := sumRemainder_nonneg order D hD
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hc : 0 ≤ c := add_nonneg hd he
  have ha : 0 ≤ a := by dsimp [a, aw]; positivity
  have hb : 0 ≤ b := by dsimp [b, bw, aw]; positivity
  have hA : 0 ≤ A := add_nonneg ha hd
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hMtwo : 2 ≤ M := by dsimp [M]; linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hS : 0 ≤ S := by
    dsimp [S]
    apply List.sum_nonneg
    intro z hz
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
    exact (Real.exp_pos _).le
  have hT : 0 < T := by dsimp [T]; linarith
  refine ⟨C, ε, hC, hε, ?_⟩
  intro u hu huε subError expError addError divError hsub hexp hadd hdiv
  have huu : 0 ≤ u := hu.le
  have huM : u * (2 * M) < 1 :=
    (lt_div_iff₀ (by positivity : 0 < 2 * M)).mp huε
  have hu1 : u ≤ 1 := by nlinarith [mul_nonneg huu (sub_nonneg.mpr hMtwo)]
  have hsmall : D * u ≤ 1 := by
    have hDM : D ≤ M := by dsimp [M]; linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hDM) huu]
  have hhalf : c * u ≤ 1 / 2 := by
    have hcM : c ≤ M := by dsimp [M]; linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hcM) huu]
  let w := computedWeight x k subError expError
  let V : ℝ := 1 + roundedSum w addError order
  have hden0 := roundedSum_error x k order hnodup hk subError expError addError u
    huu hu1 hsmall hsub hexp hadd
  have hden : |V - T| ≤ T * (d * u + e * u ^ 2) := by
    have heq : V - T = roundedSum w addError order - S := by
      dsimp [V, T]
      ring
    rw [heq]
    have hq : 0 ≤ d * u + e * u ^ 2 := by positivity
    have hST : S ≤ T := by dsimp [T]; linarith
    exact hden0.trans (mul_le_mul_of_nonneg_right hST hq)
  have hcomponent : ∀ i : Fin n,
      |computedSoftmax x k order subError expError addError divError i -
          exactSoftmax x k order i| ≤
        exactSoftmax x k order i * (A * u + C * u ^ 2) := by
    intro i
    have hwi := computedWeight_error x k i hk subError expError u
      huu hu1 hsmall hsub hexp
    have hnum := multiply_relative_error (w i) (exactWeight x k i)
      (divError i) aw bw u (Real.exp_pos _).le
      (by dsimp [aw]; positivity) (by dsimp [bw]; positivity)
      huu hu1 hwi (hdiv i)
    have hquot := quotient_relative_error (w i * (1 + divError i))
      (exactWeight x k i) V T a b d e u
      (Real.exp_pos _).le hT ha hb hd he huu hu1 hnum hden hhalf
    rw [← div_mul_eq_mul_div] at hquot
    simpa only [computedSoftmax, exactSoftmax, w, V, T, S, a, b, d, e, c, A, C,
      aw, bw, D] using hquot
  let g : Fin n → ℝ := exactSoftmax x k order
  let ghat : Fin n → ℝ :=
    computedSoftmax x k order subError expError addError divError
  have hbound : 0 ≤ A * u + C * u ^ 2 := by positivity
  have hnorm : ‖fun i : Fin n => ghat i - g i‖ ≤
      ‖g‖ * (A * u + C * u ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg g) hbound)).2
    intro i
    have hgi : 0 ≤ g i := by
      dsimp [g, exactSoftmax, T, S]
      exact div_nonneg (Real.exp_pos _).le hT.le
    have hgi_norm : g i ≤ ‖g‖ := by
      have h := norm_le_pi_norm g i
      simpa only [Real.norm_eq_abs, abs_of_nonneg hgi] using h
    calc
      ‖(fun j : Fin n => ghat j - g j) i‖ =
          |ghat i - g i| := Real.norm_eq_abs _
      _ ≤ g i * (A * u + C * u ^ 2) := hcomponent i
      _ ≤ ‖g‖ * (A * u + C * u ^ 2) :=
        mul_le_mul_of_nonneg_right hgi_norm hbound
  have hgnorm : 0 < ‖g‖ := by
    have hgk : 0 < g k := by
      dsimp [g, exactSoftmax, T, S]
      exact div_pos (Real.exp_pos _) hT
    have h := norm_le_pi_norm g k
    have hkg : 0 < ‖g k‖ := by
      simpa only [Real.norm_eq_abs, abs_of_pos hgk] using hgk
    exact lt_of_lt_of_le hkg h
  have hmain : ‖fun i : Fin n => ghat i - g i‖ / ‖g‖ ≤
      A * u + C * u ^ 2 := (div_le_iff₀ hgnorm).2 (by
        simpa only [mul_comm] using hnorm)
  have hcoef : A = (n : ℝ) + 2 + 2 * D := by
    dsimp [A, a, d, aw]
    ring
  rw [hcoef] at hmain
  simpa only [g, ghat, D] using hmain

end HighamBenchCandidate
