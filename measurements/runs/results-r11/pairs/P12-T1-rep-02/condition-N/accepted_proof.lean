import HighamBench.P12Definitions
import Mathlib

namespace HighamBench

private lemma p12_small_lattice_is_finite
    (fmt : P12RadixFormat) (negative : Bool) :
    ∀ (d m : ℕ),
      0 < m →
      m < fmt.beta ^ fmt.precision →
      fmt.normalEmin + (d : ℤ) ≤ fmt.normalEmax →
      p12FiniteSystem fmt
        (fmt.signValue negative * (m : ℝ) *
          fmt.betaR ^ (fmt.normalEmin + (d : ℤ) - (fmt.precision : ℤ))) := by
  intro d
  induction d with
  | zero =>
      intro m hmpos hmupper herange
      by_cases hnormal : fmt.minNormalMantissa ≤ m
      · right
        left
        refine ⟨negative, m, fmt.normalEmin, ⟨hnormal, hmupper⟩, ?_, ?_⟩
        · exact ⟨le_rfl, by simpa using herange⟩
        · simp [P12RadixFormat.normalizedValue]
      · right
        right
        refine ⟨negative, m, ⟨hmpos, lt_of_not_ge hnormal⟩, ?_⟩
        simp [P12RadixFormat.normalEmin, P12RadixFormat.subnormalValue]
  | succ d ih =>
      intro m hmpos hmupper herange
      by_cases hnormal : fmt.minNormalMantissa ≤ m
      · right
        left
        refine ⟨negative, m, fmt.normalEmin + ((d + 1 : ℕ) : ℤ),
          ⟨hnormal, hmupper⟩, ?_, rfl⟩
        constructor
        · omega
        · simpa only [Nat.cast_add, Nat.cast_one] using herange
      · have hsmall : m < fmt.beta ^ (fmt.precision - 1) :=
          lt_of_not_ge hnormal
        have hbeta_pos : 0 < fmt.beta := lt_of_lt_of_le (by omega) fmt.beta_ge_two
        have hmprod_pos : 0 < m * fmt.beta := Nat.mul_pos hmpos hbeta_pos
        have hprec : fmt.precision - 1 + 1 = fmt.precision := by
          have := fmt.precision_pos
          omega
        have hmprod_upper : m * fmt.beta < fmt.beta ^ fmt.precision := by
          calc
            m * fmt.beta < fmt.beta ^ (fmt.precision - 1) * fmt.beta :=
              (Nat.mul_lt_mul_right hbeta_pos).2 hsmall
            _ = fmt.beta ^ fmt.precision := by
              rw [← pow_succ, hprec]
        have herange' : fmt.normalEmin + (d : ℤ) ≤ fmt.normalEmax := by
          omega
        have hrec := ih (m * fmt.beta) hmprod_pos hmprod_upper herange'
        convert hrec using 1
        rw [show fmt.normalEmin + ((d + 1 : ℕ) : ℤ) - (fmt.precision : ℤ) =
            (fmt.normalEmin + (d : ℤ) - (fmt.precision : ℤ)) + 1 by omega]
        rw [zpow_add_one₀]
        · simp only [P12RadixFormat.betaR, Nat.cast_mul]
          ring
        · simpa only [P12RadixFormat.betaR] using
            (show (fmt.beta : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hbeta_pos))

private lemma p12_bounded_nat_lattice_is_finite
    (fmt : P12RadixFormat) (negative : Bool) (m : ℕ) (e : ℤ)
    (hmpos : 0 < m)
    (hmupper : m ≤ fmt.beta ^ fmt.precision)
    (hemin : fmt.normalEmin ≤ e)
    (hemax : e < fmt.normalEmax) :
    p12FiniteSystem fmt
      (fmt.signValue negative * (m : ℝ) *
        fmt.betaR ^ (e - (fmt.precision : ℤ))) := by
  by_cases hstrict : m < fmt.beta ^ fmt.precision
  · let d : ℕ := (e - fmt.normalEmin).toNat
    have hdiff : 0 ≤ e - fmt.normalEmin := by omega
    have hed : fmt.normalEmin + (d : ℤ) = e := by
      dsimp [d]
      rw [Int.toNat_of_nonneg hdiff]
      omega
    have herange : fmt.normalEmin + (d : ℤ) ≤ fmt.normalEmax := by
      omega
    have h := p12_small_lattice_is_finite fmt negative d m hmpos hstrict herange
    rwa [hed] at h
  · have hm_eq : m = fmt.beta ^ fmt.precision := by omega
    have hbeta : 1 < fmt.beta := fmt.beta_ge_two
    have hprecision : fmt.precision - 1 < fmt.precision := by
      have := fmt.precision_pos
      omega
    have hmantissa_upper :
        fmt.beta ^ (fmt.precision - 1) < fmt.beta ^ fmt.precision :=
      Nat.pow_lt_pow_right hbeta hprecision
    right
    left
    refine ⟨negative, fmt.beta ^ (fmt.precision - 1), e + 1,
      ⟨le_rfl, hmantissa_upper⟩, ?_, ?_⟩
    · exact ⟨by omega, by omega⟩
    · have hbetaR : fmt.betaR ≠ 0 := by
        simp only [P12RadixFormat.betaR]
        exact_mod_cast (ne_of_gt (lt_trans Nat.zero_lt_one hbeta))
      rw [hm_eq]
      unfold P12RadixFormat.normalizedValue
      have hpcast : ((fmt.precision - 1 : ℕ) : ℤ) =
          (fmt.precision : ℤ) - 1 := by
        have := fmt.precision_pos
        omega
      calc
        fmt.signValue negative * (↑(fmt.beta ^ fmt.precision) : ℝ) *
              fmt.betaR ^ (e - (fmt.precision : ℤ)) =
            fmt.signValue negative *
              (fmt.betaR ^ (fmt.precision : ℤ) *
                fmt.betaR ^ (e - (fmt.precision : ℤ))) := by
                  simp [P12RadixFormat.betaR]
                  ring
        _ = fmt.signValue negative * fmt.betaR ^ e := by
              rw [← zpow_add₀ hbetaR]
              congr 2
              omega
        _ = fmt.signValue negative *
              (fmt.betaR ^ ((fmt.precision : ℤ) - 1) *
                fmt.betaR ^ (e + 1 - (fmt.precision : ℤ))) := by
              rw [← zpow_add₀ hbetaR]
              congr 2
              omega
        _ = fmt.signValue negative *
              (↑(fmt.beta ^ (fmt.precision - 1)) : ℝ) *
                fmt.betaR ^ (e + 1 - (fmt.precision : ℤ)) := by
              rw [← hpcast]
              simp [P12RadixFormat.betaR]
              ring

private lemma p12_bounded_int_lattice_is_finite
    (fmt : P12RadixFormat) (q : ℤ) (e : ℤ)
    (hq : q.natAbs ≤ fmt.beta ^ fmt.precision)
    (hemin : fmt.normalEmin ≤ e)
    (hemax : e < fmt.normalEmax) :
    p12FiniteSystem fmt
      ((q : ℝ) * fmt.betaR ^ (e - (fmt.precision : ℤ))) := by
  cases q with
  | ofNat n =>
      by_cases hn : n = 0
      · subst n
        left
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have h := p12_bounded_nat_lattice_is_finite
          fmt false n e hnpos hq hemin hemax
        simpa [P12RadixFormat.signValue] using h
  | negSucc n =>
      have hnpos : 0 < n + 1 := Nat.succ_pos n
      have h := p12_bounded_nat_lattice_is_finite
        fmt true (n + 1) e hnpos hq hemin hemax
      simpa [P12RadixFormat.signValue, Int.cast_negSucc] using h

private lemma p12_normalized_on_lower_lattice
    (fmt : P12RadixFormat) (x : ℝ) (ex e : ℤ)
    (hx : P12NormalizedExponentRepresentation fmt x ex)
    (he : e ≤ ex) :
    ∃ q : ℤ, x = (q : ℝ) * fmt.betaR ^ (e - (fmt.precision : ℤ)) := by
  rcases hx with ⟨negative, m, hm, herange, hx⟩
  let d : ℕ := (ex - e).toNat
  have hdiff : 0 ≤ ex - e := by omega
  have hd : (d : ℤ) = ex - e := by
    dsimp [d]
    rw [Int.toNat_of_nonneg hdiff]
  have hbeta : 0 < fmt.beta := lt_of_lt_of_le (by omega) fmt.beta_ge_two
  have hbetaR : fmt.betaR ≠ 0 := by
    simp only [P12RadixFormat.betaR]
    exact_mod_cast (ne_of_gt hbeta)
  cases negative with
  | false =>
      refine ⟨(m * fmt.beta ^ d : ℕ), ?_⟩
      rw [hx]
      unfold P12RadixFormat.normalizedValue P12RadixFormat.signValue
      rw [show ex - (fmt.precision : ℤ) =
          (ex - e) + (e - (fmt.precision : ℤ)) by omega]
      rw [zpow_add₀ hbetaR, ← hd]
      simp [P12RadixFormat.betaR]
      ring
  | true =>
      refine ⟨-((m * fmt.beta ^ d : ℕ) : ℤ), ?_⟩
      rw [hx]
      unfold P12RadixFormat.normalizedValue P12RadixFormat.signValue
      rw [show ex - (fmt.precision : ℤ) =
          (ex - e) + (e - (fmt.precision : ℤ)) by omega]
      rw [zpow_add₀ hbetaR, ← hd]
      simp [P12RadixFormat.betaR]
      ring

theorem p12_t1_exact_subtraction
    (fmt : P12RadixFormat) (x y rounded : ℝ) (ex ey : ℤ)
    (hx : P12NormalizedExponentRepresentation fmt x ex)
    (hy : P12NormalizedExponentRepresentation fmt y ey)
    (hmag : |x - y| ≤ fmt.betaR ^ min ex ey)
    (hnoOverflow : min ex ey < fmt.normalEmax)
    (hround : p12FaithfulInFormat fmt (x - y) rounded) :
    p12FiniteSystem fmt (x - y) ∧ rounded = x - y := by
  -- PROOF_START P12-T1-H001
  let e : ℤ := min ex ey
  have he_ex : e ≤ ex := by
    exact min_le_left _ _
  have he_ey : e ≤ ey := by
    exact min_le_right _ _
  obtain ⟨qx, hxq⟩ := p12_normalized_on_lower_lattice fmt x ex e hx he_ex
  obtain ⟨qy, hyq⟩ := p12_normalized_on_lower_lattice fmt y ey e hy he_ey
  let q : ℤ := qx - qy
  have hxy : x - y =
      (q : ℝ) * fmt.betaR ^ (e - (fmt.precision : ℤ)) := by
    rw [hxq, hyq]
    dsimp [q]
    push_cast
    ring
  have hexrange : fmt.normalEmin ≤ ex := by
    rcases hx with ⟨negative, m, hm, herange, hxval⟩
    exact herange.1
  have heyrange : fmt.normalEmin ≤ ey := by
    rcases hy with ⟨negative, m, hm, herange, hyval⟩
    exact herange.1
  have he_lower : fmt.normalEmin ≤ e := by
    exact le_min hexrange heyrange
  have hbeta : 0 < fmt.beta := lt_of_lt_of_le (by omega) fmt.beta_ge_two
  have hbetaR_pos : 0 < fmt.betaR := by
    simpa only [P12RadixFormat.betaR] using (show (0 : ℝ) < fmt.beta by exact_mod_cast hbeta)
  have hscale_pos :
      0 < fmt.betaR ^ (e - (fmt.precision : ℤ)) :=
    zpow_pos hbetaR_pos _
  have hbetaR_ne : fmt.betaR ≠ 0 := ne_of_gt hbetaR_pos
  have hpower : fmt.betaR ^ e =
      (↑(fmt.beta ^ fmt.precision) : ℝ) *
        fmt.betaR ^ (e - (fmt.precision : ℤ)) := by
    calc
      fmt.betaR ^ e =
          fmt.betaR ^ ((fmt.precision : ℤ) +
            (e - (fmt.precision : ℤ))) := by congr 1 <;> omega
      _ = fmt.betaR ^ (fmt.precision : ℤ) *
            fmt.betaR ^ (e - (fmt.precision : ℤ)) :=
          zpow_add₀ hbetaR_ne _ _
      _ = (↑(fmt.beta ^ fmt.precision) : ℝ) *
            fmt.betaR ^ (e - (fmt.precision : ℤ)) := by
          simp [P12RadixFormat.betaR]
  have hq_real : |(q : ℝ)| ≤ (↑(fmt.beta ^ fmt.precision) : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right hscale_pos).mp
    calc
      |(q : ℝ)| * fmt.betaR ^ (e - (fmt.precision : ℤ)) =
          |(q : ℝ) * fmt.betaR ^ (e - (fmt.precision : ℤ))| := by
            rw [abs_mul, abs_of_pos hscale_pos]
      _ = |x - y| := by rw [hxy]
      _ ≤ fmt.betaR ^ min ex ey := hmag
      _ = fmt.betaR ^ e := by rfl
      _ = (↑(fmt.beta ^ fmt.precision) : ℝ) *
            fmt.betaR ^ (e - (fmt.precision : ℤ)) := hpower
  have hq : q.natAbs ≤ fmt.beta ^ fmt.precision := by
    exact_mod_cast (show (q.natAbs : ℝ) ≤
      (↑(fmt.beta ^ fmt.precision) : ℝ) by
        simpa only [Nat.cast_natAbs, Int.cast_abs] using hq_real)
  have he_upper : e < fmt.normalEmax := by
    simpa only [e] using hnoOverflow
  have hexact := p12_bounded_int_lattice_is_finite
    fmt q e hq he_lower he_upper
  rw [← hxy] at hexact
  refine ⟨hexact, ?_⟩
  rcases hround with ⟨hrounded, hfaithful⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hfaithful (x - y) hexact (Or.inl ⟨hlt, le_rfl⟩)
  · exact hfaithful (x - y) hexact (Or.inr ⟨le_rfl, hgt⟩)

end HighamBench
