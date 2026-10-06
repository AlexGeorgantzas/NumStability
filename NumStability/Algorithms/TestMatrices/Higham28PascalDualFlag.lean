import NumStability.Algorithms.TestMatrices.Higham28PascalOscillation
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fintype.Sort

namespace NumStability

open scoped BigOperators

theorem pascalOscillation_strictMono_card_below
    {k N : ℕ} (f : Fin k → Fin N) (hf : StrictMono f) (i : Fin k) :
    ((Finset.image f Finset.univ).filter (fun x => x < f i)).card = i.val := by
  have heq :
      (Finset.image f Finset.univ).filter (fun x => x < f i) =
        Finset.image f (Finset.Iio i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_Iio]
    constructor
    · rintro ⟨⟨j, rfl⟩, hji⟩
      exact ⟨j, hf.lt_iff_lt.mp hji, rfl⟩
    · rintro ⟨j, hji, rfl⟩
      exact ⟨⟨j, rfl⟩, hf hji⟩
  rw [heq, Finset.card_image_of_injective _ hf.injective, Fin.card_Iio]

noncomputable def pascalOscillationFRange {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) : Finset (Fin (q + l + 1)) :=
  Finset.image f Finset.univ

theorem pascalOscillationFRange_card {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f) :
    (pascalOscillationFRange f).card = l + 1 := by
  rw [pascalOscillationFRange, Finset.card_image_of_injective _ hf.injective,
    Finset.card_univ, Fintype.card_fin]

theorem pascalOscillationFRange_orderEmb_eq {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f) :
    (pascalOscillationFRange f).orderEmbOfFin (pascalOscillationFRange_card f hf) = f := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro x
    simp [pascalOscillationFRange]
  · exact hf

theorem pascalOscillationFRange_compl_card {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f) :
    (pascalOscillationFRange f)ᶜ.card = q := by
  rw [Finset.card_compl, pascalOscillationFRange_card f hf]
  simp only [Fintype.card_fin]
  omega

noncomputable def pascalOscillationComplementRows {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f) :
    Fin q → Fin (q + l + 1) :=
  ((pascalOscillationFRange f)ᶜ).orderEmbOfFin (pascalOscillationFRange_compl_card f hf)

theorem pascalOscillationComplementRows_strictMono {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f) :
    StrictMono (pascalOscillationComplementRows f hf) :=
  (((pascalOscillationFRange f)ᶜ).orderEmbOfFin
    (pascalOscillationFRange_compl_card f hf)).strictMono

theorem pascalOscillationComplementRows_mem_compl {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f) (j : Fin q) :
    pascalOscillationComplementRows f hf j ∈ (pascalOscillationFRange f)ᶜ := by
  exact Finset.orderEmbOfFin_mem _ _ _

noncomputable def pascalOscillationInsertedRows {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (r : Fin (l + 1)) : Finset (Fin (q + l + 1)) :=
  insert (f r) (pascalOscillationFRange f)ᶜ

theorem pascalOscillationInsertedRows_card {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (r : Fin (l + 1)) : (pascalOscillationInsertedRows f hf r).card = q + 1 := by
  have hn : f r ∉ (pascalOscillationFRange f)ᶜ := by
    simp [pascalOscillationFRange]
  simp [pascalOscillationInsertedRows, hn, pascalOscillationFRange_compl_card f hf]

noncomputable def pascalOscillationInsertedRowsOrder {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (r : Fin (l + 1)) : Fin (q + 1) → Fin (q + l + 1) :=
  (pascalOscillationInsertedRows f hf r).orderEmbOfFin (pascalOscillationInsertedRows_card f hf r)

noncomputable def pascalOscillationInsertedPosition {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (r : Fin (l + 1)) : Fin (q + 1) :=
  ((pascalOscillationInsertedRows f hf r).orderIsoOfFin
      (pascalOscillationInsertedRows_card f hf r)).symm
    ⟨f r, by simp [pascalOscillationInsertedRows]⟩

theorem pascalOscillationInsertedRowsOrder_position {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (r : Fin (l + 1)) :
    pascalOscillationInsertedRowsOrder f hf r (pascalOscillationInsertedPosition f hf r) = f r := by
  exact congrArg Subtype.val
    (((pascalOscillationInsertedRows f hf r).orderIsoOfFin
      (pascalOscillationInsertedRows_card f hf r)).apply_symm_apply
        ⟨f r, by simp [pascalOscillationInsertedRows]⟩)

theorem pascalOscillationInsertedRowsOrder_succAbove_position {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (r : Fin (l + 1)) (j : Fin q) :
    pascalOscillationInsertedRowsOrder f hf r
        ((pascalOscillationInsertedPosition f hf r).succAbove j) =
      pascalOscillationComplementRows f hf j := by
  classical
  let h : Fin (q + 1) → Fin (q + l + 1) :=
    pascalOscillationInsertedRowsOrder f hf r
  let p : Fin (q + 1) := pascalOscillationInsertedPosition f hf r
  let x : Fin q → Fin (q + l + 1) := fun j => h (p.succAbove j)
  have hxmono : StrictMono x :=
    ((pascalOscillationInsertedRows f hf r).orderEmbOfFin
      (pascalOscillationInsertedRows_card f hf r)).strictMono.comp
        (Fin.strictMono_succAbove p)
  have hxmem : ∀ j, x j ∈ (pascalOscillationFRange f)ᶜ := by
    intro a
    have hmem : x a ∈ pascalOscillationInsertedRows f hf r := by
      exact Finset.orderEmbOfFin_mem _ _ _
    have hne : x a ≠ f r := by
      intro heq
      have hp := pascalOscillationInsertedRowsOrder_position f hf r
      have hinj := ((pascalOscillationInsertedRows f hf r).orderEmbOfFin
        (pascalOscillationInsertedRows_card f hf r)).injective
      have heqi : p.succAbove a = p := hinj (heq.trans hp.symm)
      exact (p.succAbove_ne a) heqi
    simpa [pascalOscillationInsertedRows, hne] using hmem
  have hx : x = pascalOscillationComplementRows f hf := by
    apply Finset.orderEmbOfFin_unique (pascalOscillationFRange_compl_card f hf) hxmem hxmono
  exact congrFun hx j

theorem pascalOscillation_cons_complement_cycleRange {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (r : Fin (l + 1)) :
    ((Fin.cons (f r) (pascalOscillationComplementRows f hf) :
        Fin (q + 1) → Fin (q + l + 1))) ∘
        (pascalOscillationInsertedPosition f hf r).cycleRange =
      pascalOscillationInsertedRowsOrder f hf r := by
  let p := pascalOscillationInsertedPosition f hf r
  rw [Fin.cons_comp_cycleRange]
  symm
  apply Fin.eq_insertNth_iff.mpr
  constructor
  · exact pascalOscillationInsertedRowsOrder_position f hf r
  · funext j
    exact pascalOscillationInsertedRowsOrder_succAbove_position f hf r j

theorem pascalOscillation_det_cons_complement_eq_position_sign
    {q l : ℕ} (Q : Matrix (Fin (q + l + 1)) (Fin (q + l + 1)) ℝ)
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (r : Fin (l + 1)) :
    Matrix.det (fun a b : Fin (q + 1) =>
        Q ((Fin.cons (f r) (pascalOscillationComplementRows f hf) :
            Fin (q + 1) → Fin (q + l + 1)) a)
          (Fin.castLE (by omega) b)) =
      (-1 : ℝ) ^ (pascalOscillationInsertedPosition f hf r).val *
        Matrix.det (fun a b : Fin (q + 1) =>
          Q (pascalOscillationInsertedRowsOrder f hf r a)
            (Fin.castLE (by omega) b)) := by
  let p := pascalOscillationInsertedPosition f hf r
  let M : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ := fun a b =>
    Q ((Fin.cons (f r) (pascalOscillationComplementRows f hf) :
        Fin (q + 1) → Fin (q + l + 1)) a)
      (Fin.castLE (by omega) b)
  have hrows := pascalOscillation_cons_complement_cycleRange f hf r
  have hperm0 := Matrix.det_permute p.cycleRange M
  have hperm : (M.submatrix p.cycleRange id).det =
      (-1 : ℝ) ^ p.val * Matrix.det M := by
    simpa using hperm0
  have hsorted : Matrix.det (fun a b : Fin (q + 1) =>
      Q (pascalOscillationInsertedRowsOrder f hf r a) (Fin.castLE (by omega) b)) =
      (-1 : ℝ) ^ p.val * Matrix.det M := by
    rw [← hperm]
    congr 1
    funext a b
    exact congrArg (fun z => Q z (Fin.castLE (by omega) b))
      (congrFun hrows a).symm
  have hp : (-1 : ℝ) ^ p.val * (-1 : ℝ) ^ p.val = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow (Even.add_self p.val)
  change Matrix.det M = (-1 : ℝ) ^ p.val *
    Matrix.det (fun a b : Fin (q + 1) =>
      Q (pascalOscillationInsertedRowsOrder f hf r a) (Fin.castLE (by omega) b))
  rw [hsorted]
  calc
    Matrix.det M = 1 * Matrix.det M := by ring
    _ = (((-1 : ℝ) ^ p.val) * ((-1 : ℝ) ^ p.val)) *
        Matrix.det M := by rw [hp]
    _ = (-1 : ℝ) ^ p.val *
        ((-1 : ℝ) ^ p.val * Matrix.det M) := by ring

def pascalOscillationLeadingColumn {q l : ℕ} : Fin (q + 1) → Fin (q + l + 1) :=
  Fin.castLE (by omega)

def pascalOscillationTrailingColumn {q l : ℕ} (c : Fin l) : Fin (q + l + 1) :=
  ⟨q + 1 + c.val, by omega⟩

theorem pascalOscillationLeadingColumn_ne_trailingColumn {q l : ℕ}
    (a : Fin (q + 1)) (b : Fin l) :
    pascalOscillationLeadingColumn a ≠ pascalOscillationTrailingColumn b := by
  intro h
  have hv := congrArg Fin.val h
  simp [pascalOscillationLeadingColumn, pascalOscillationTrailingColumn] at hv
  omega

noncomputable def pascalOscillationLeadingCofactor {q l : ℕ}
    (Q : Matrix (Fin (q + l + 1)) (Fin (q + l + 1)) ℝ)
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (c : Fin (q + 1)) : ℝ :=
  (-1 : ℝ) ^ c.val * Matrix.det (fun a b : Fin q =>
    Q (pascalOscillationComplementRows f hf a) (pascalOscillationLeadingColumn (c.succAbove b)))

noncomputable def pascalOscillationLeadingCofactorVector {q l : ℕ}
    (Q : Matrix (Fin (q + l + 1)) (Fin (q + l + 1)) ℝ)
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (x : Fin (q + l + 1)) : ℝ :=
  ∑ c : Fin (q + 1), Q x (pascalOscillationLeadingColumn c) *
    pascalOscillationLeadingCofactor Q f hf c

theorem pascalOscillationLeadingCofactorVector_eq_det_cons {q l : ℕ}
    (Q : Matrix (Fin (q + l + 1)) (Fin (q + l + 1)) ℝ)
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (x : Fin (q + l + 1)) :
    pascalOscillationLeadingCofactorVector Q f hf x =
      Matrix.det (fun a b : Fin (q + 1) =>
        Q ((Fin.cons x (pascalOscillationComplementRows f hf) :
            Fin (q + 1) → Fin (q + l + 1)) a)
          (pascalOscillationLeadingColumn b)) := by
  let M : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ := fun a b =>
    Q ((Fin.cons x (pascalOscillationComplementRows f hf) :
        Fin (q + 1) → Fin (q + l + 1)) a)
      (pascalOscillationLeadingColumn b)
  rw [Matrix.det_succ_row_zero M]
  unfold pascalOscillationLeadingCofactorVector pascalOscillationLeadingCofactor
  apply Finset.sum_congr rfl
  intro c _
  have hsub : Matrix.det (M.submatrix Fin.succ c.succAbove) =
      Matrix.det (fun a b : Fin q =>
        Q (pascalOscillationComplementRows f hf a)
          (pascalOscillationLeadingColumn (c.succAbove b))) := by
    congr 1
  rw [hsub]
  simp only [M, Fin.cons_zero]
  ring

theorem pascalOscillation_complement_position_parity
    {q l : ℕ} (f : Fin (l + 1) → Fin (q + l + 1))
    (hf : StrictMono f) (r : Fin (l + 1)) :
    (pascalOscillationInsertedPosition f hf r).val + r.val = (f r).val := by
  classical
  let sf := pascalOscillationFRange f
  let sg := sfᶜ
  let sr := pascalOscillationInsertedRows f hf r
  let h := pascalOscillationInsertedRowsOrder f hf r
  let p := pascalOscillationInsertedPosition f hf r
  have hp : h p = f r := pascalOscillationInsertedRowsOrder_position f hf r
  have hpCard : (sr.filter (fun x => x < f r)).card = p.val := by
    have hbelow := pascalOscillation_strictMono_card_below h
      ((pascalOscillationInsertedRows f hf r).orderEmbOfFin
        (pascalOscillationInsertedRows_card f hf r)).strictMono p
    rw [hp] at hbelow
    have himage : Finset.image h Finset.univ = sr := by
      dsimp [h, sr, pascalOscillationInsertedRowsOrder]
      exact Finset.image_orderEmbOfFin_univ _ _
    rw [himage] at hbelow
    exact hbelow
  have hrCard : (sf.filter (fun x => x < f r)).card = r.val := by
    simpa [sf, pascalOscillationFRange] using pascalOscillation_strictMono_card_below f hf r
  have hsrsg : sr.filter (fun x => x < f r) =
      sg.filter (fun x => x < f r) := by
    ext x
    simp [sr, sg, sf, pascalOscillationInsertedRows]
    aesop
  have hpartition : Finset.Iio (f r) =
      (sf.filter (fun x => x < f r)) ∪
        (sg.filter (fun x => x < f r)) := by
    ext x
    by_cases hx : x ∈ sf <;> simp [sg, hx]
  have hdisjoint : Disjoint (sf.filter (fun x => x < f r))
      (sg.filter (fun x => x < f r)) := by
    apply Finset.disjoint_left.mpr
    intro x hxs hxg
    have hs : x ∈ sf := (Finset.mem_filter.mp hxs).1
    have hg : x ∈ sg := (Finset.mem_filter.mp hxg).1
    simpa [sg, hs] using hg
  have hcard := congrArg Finset.card hpartition
  rw [Finset.card_union_of_disjoint hdisjoint, Fin.card_Iio,
    hrCard, ← hsrsg, hpCard] at hcard
  omega

theorem pascalOscillationLeadingCofactorVector_sign {q l : ℕ}
    (Q : Matrix (Fin (q + l + 1)) (Fin (q + l + 1)) ℝ)
    (hlead : ∃ ε : ℝ, ∀ (u : Fin (q + 1) → Fin (q + l + 1)),
      StrictMono u → 0 < ε * Matrix.det (fun a b : Fin (q + 1) =>
        Q (u a) (pascalOscillationLeadingColumn b)))
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f) :
    ∃ ε : ℝ, ∀ r : Fin (l + 1),
      0 < ε * (-1 : ℝ) ^ r.val *
        ((-1 : ℝ) ^ (f r).val * pascalOscillationLeadingCofactorVector Q f hf (f r)) := by
  obtain ⟨ε, hε⟩ := hlead
  refine ⟨ε, ?_⟩
  intro r
  rw [pascalOscillationLeadingCofactorVector_eq_det_cons]
  have hdet := pascalOscillation_det_cons_complement_eq_position_sign Q f hf r
  change Matrix.det (fun a b : Fin (q + 1) =>
      Q ((Fin.cons (f r) (pascalOscillationComplementRows f hf) :
          Fin (q + 1) → Fin (q + l + 1)) a)
        (pascalOscillationLeadingColumn b)) = _ at hdet
  rw [hdet]
  let p := pascalOscillationInsertedPosition f hf r
  have hparity : p.val + r.val = (f r).val :=
    pascalOscillation_complement_position_parity f hf r
  have hp : (-1 : ℝ) ^ r.val * (-1 : ℝ) ^ (f r).val *
      (-1 : ℝ) ^ p.val = 1 := by
    have heven : Even (r.val + (f r).val + p.val) := by
      refine ⟨(f r).val, ?_⟩
      omega
    rw [← pow_add, ← pow_add]
    exact Even.neg_one_pow heven
  have hmono : StrictMono (pascalOscillationInsertedRowsOrder f hf r) :=
    ((pascalOscillationInsertedRows f hf r).orderEmbOfFin
      (pascalOscillationInsertedRows_card f hf r)).strictMono
  have hpos := hε (pascalOscillationInsertedRowsOrder f hf r) hmono
  change 0 < ε * (-1 : ℝ) ^ r.val *
    ((-1 : ℝ) ^ (f r).val *
      ((-1 : ℝ) ^ p.val *
        Matrix.det (fun a b : Fin (q + 1) =>
          Q (pascalOscillationInsertedRowsOrder f hf r a) (pascalOscillationLeadingColumn b))))
  convert hpos using 1
  calc
    ε * (-1 : ℝ) ^ r.val *
        ((-1 : ℝ) ^ (f r).val *
          ((-1 : ℝ) ^ p.val *
            Matrix.det (fun a b : Fin (q + 1) =>
              Q (pascalOscillationInsertedRowsOrder f hf r a) (pascalOscillationLeadingColumn b)))) =
      ε * (((-1 : ℝ) ^ r.val * (-1 : ℝ) ^ (f r).val *
          (-1 : ℝ) ^ p.val)) *
          Matrix.det (fun a b : Fin (q + 1) =>
            Q (pascalOscillationInsertedRowsOrder f hf r a) (pascalOscillationLeadingColumn b)) := by ring
    _ = _ := by rw [hp, mul_one]

theorem pascalOscillationLeadingCofactorVector_orthogonal_trailing {q l : ℕ}
    (Q : Matrix (Fin (q + l + 1)) (Fin (q + l + 1)) ℝ)
    (hQ : Q.transpose * Q = 1)
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (d : Fin l) :
    ∑ x : Fin (q + l + 1),
      pascalOscillationLeadingCofactorVector Q f hf x * Q x (pascalOscillationTrailingColumn d) = 0 := by
  have hcross : ∀ c : Fin (q + 1),
      (∑ x : Fin (q + l + 1),
        Q x (pascalOscillationLeadingColumn c) * Q x (pascalOscillationTrailingColumn d)) = 0 := by
    intro c
    have hc := congrArg
      (fun M : Matrix (Fin (q + l + 1)) (Fin (q + l + 1)) ℝ =>
        M (pascalOscillationLeadingColumn c) (pascalOscillationTrailingColumn d)) hQ
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      pascalOscillationLeadingColumn_ne_trailingColumn c d, if_false] at hc
    exact hc
  simp only [pascalOscillationLeadingCofactorVector]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c _
  calc
    (∑ x, Q x (pascalOscillationLeadingColumn c) * pascalOscillationLeadingCofactor Q f hf c *
        Q x (pascalOscillationTrailingColumn d)) =
      pascalOscillationLeadingCofactor Q f hf c *
        (∑ x, Q x (pascalOscillationLeadingColumn c) * Q x (pascalOscillationTrailingColumn d)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = 0 := by rw [hcross c, mul_zero]

theorem pascalOscillationLeadingCofactorVector_complement_zero {q l : ℕ}
    (Q : Matrix (Fin (q + l + 1)) (Fin (q + l + 1)) ℝ)
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (j : Fin q) :
    pascalOscillationLeadingCofactorVector Q f hf (pascalOscillationComplementRows f hf j) = 0 := by
  rw [pascalOscillationLeadingCofactorVector_eq_det_cons]
  let M : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ := fun a b =>
    Q ((Fin.cons (pascalOscillationComplementRows f hf j) (pascalOscillationComplementRows f hf) :
        Fin (q + 1) → Fin (q + l + 1)) a) (pascalOscillationLeadingColumn b)
  change Matrix.det M = 0
  apply Matrix.det_zero_of_row_eq (Ne.symm (Fin.succ_ne_zero j))
  funext b
  simp [M]

theorem pascalOscillation_sum_fRange_complement {q l : ℕ}
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (z : Fin (q + l + 1) → ℝ) :
    (∑ x, z x) =
      (∑ r : Fin (l + 1), z (f r)) +
        ∑ j : Fin q, z (pascalOscillationComplementRows f hf j) := by
  let e : Fin (l + 1) ⊕ Fin q ≃ Fin (q + l + 1) :=
    finSumEquivOfFinset (pascalOscillationFRange_card f hf)
      (pascalOscillationFRange_compl_card f hf)
  rw [← e.sum_comp, Fintype.sum_sum_type]
  simp only [e, finSumEquivOfFinset_inl, finSumEquivOfFinset_inr]
  rw [pascalOscillationFRange_orderEmb_eq f hf]
  rfl

theorem pascalOscillation2_alternatingCofactor_relation
    {N k : ℕ} (B : Fin N → Fin k → ℝ) (c : Fin k)
    (f : Fin (k + 1) → Fin N) :
    (∑ r : Fin (k + 1),
      (-1 : ℝ) ^ (r.val + k) * B (f r) c *
        Matrix.det (fun a b : Fin k => B (f (r.succAbove a)) b)) = 0 := by
  let A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := fun r j =>
    Fin.lastCases (B (f r) c) (fun q => B (f r) q) j
  have hlast_ne : (Fin.last k : Fin (k + 1)) ≠ c.castSucc := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hdet0 : Matrix.det A = 0 := by
    apply Matrix.det_zero_of_column_eq hlast_ne
    intro r
    simp [A]
  have hexp := Matrix.det_succ_column A (Fin.last k)
  rw [hdet0] at hexp
  simpa [A, Matrix.submatrix] using hexp.symm

theorem pascalOscillation_leftKernel_orients_maximal_minors {l : ℕ}
    (B : Fin (l + 1) → Fin l → ℝ)
    (z : Fin (l + 1) → ℝ)
    (hzker : ∀ c : Fin l, (∑ r : Fin (l + 1), z r * B r c) = 0)
    (hzsign : ∃ ε : ℝ, ∀ r : Fin (l + 1),
      0 < ε * (-1 : ℝ) ^ r.val * z r)
    (hminor₀ : Matrix.det (fun a b : Fin l => B (Fin.succ a) b) ≠ 0) :
    ∃ η : ℝ, ∀ r : Fin (l + 1),
      0 < η * Matrix.det (fun a b : Fin l => B (r.succAbove a) b) := by
  let w : Fin (l + 1) → ℝ := fun r =>
    (-1 : ℝ) ^ (r.val + l) *
      Matrix.det (fun a b : Fin l => B (r.succAbove a) b)
  have hwker : ∀ c : Fin l, (∑ r : Fin (l + 1), w r * B r c) = 0 := by
    intro c
    have hrel := pascalOscillation2_alternatingCofactor_relation B c id
    simpa [w, mul_assoc, mul_comm, mul_left_comm] using hrel
  obtain ⟨ε, hε⟩ := hzsign
  have hz₀ : z 0 ≠ 0 := by
    intro hz
    have hp := hε 0
    rw [hz, mul_zero] at hp
    exact (lt_irrefl 0) hp
  have hw₀ : w 0 ≠ 0 := by
    dsimp [w]
    simp only [Fin.val_zero, zero_add, Fin.zero_succAbove]
    exact mul_ne_zero (by norm_num) hminor₀
  let t : ℝ := w 0 / z 0
  have ht : t ≠ 0 := div_ne_zero hw₀ hz₀
  let d : Fin (l + 1) → ℝ := fun r => w r - t * z r
  have hdker : ∀ c : Fin l, (∑ r : Fin (l + 1), d r * B r c) = 0 := by
    intro c
    simp only [d, sub_mul]
    rw [Finset.sum_sub_distrib, hwker c]
    have hz := hzker c
    have hfactor : (∑ x : Fin (l + 1), t * z x * B x c) =
        t * (∑ x : Fin (l + 1), z x * B x c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hfactor, hz, mul_zero]
    ring
  have hd₀ : d 0 = 0 := by
    dsimp [d, t]
    rw [div_mul_cancel₀ _ hz₀]
    ring
  let D : Matrix (Fin l) (Fin l) ℝ := fun a b => B (Fin.succ a) b
  let ds : Fin l → ℝ := fun a => d (Fin.succ a)
  have hDTds : Matrix.mulVec D.transpose ds = 0 := by
    funext c
    have hc := hdker c
    rw [Fin.sum_univ_succ, hd₀, zero_mul, zero_add] at hc
    simpa [D, ds, Matrix.mulVec, dotProduct, mul_comm] using hc
  have hDTne : Matrix.det D.transpose ≠ 0 := by
    simpa [D] using hminor₀
  have hds : ds = 0 := Matrix.eq_zero_of_mulVec_eq_zero hDTne hDTds
  have hd : d = 0 := by
    funext r
    refine Fin.cases hd₀ (fun a => ?_) r
    have ha := congrFun hds a
    simpa [ds] using ha
  have hwtz : ∀ r, w r = t * z r := by
    intro r
    have hr := congrFun hd r
    simpa [d] using sub_eq_zero.mp hr
  refine ⟨ε * (-1 : ℝ) ^ l * t, ?_⟩
  intro r
  have hzr := hε r
  have hpowr : (-1 : ℝ) ^ (r.val + l) *
      (-1 : ℝ) ^ (r.val + l) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow (Even.add_self (r.val + l))
  have hdetrel : Matrix.det (fun a b : Fin l => B (r.succAbove a) b) =
      (-1 : ℝ) ^ (r.val + l) * (t * z r) := by
    calc
      _ = 1 * Matrix.det (fun a b : Fin l => B (r.succAbove a) b) := by ring
      _ = (((-1 : ℝ) ^ (r.val + l)) *
          ((-1 : ℝ) ^ (r.val + l))) *
          Matrix.det (fun a b : Fin l => B (r.succAbove a) b) := by rw [hpowr]
      _ = (-1 : ℝ) ^ (r.val + l) * w r := by
        simp only [w]
        ring
      _ = _ := by rw [hwtz r]
  rw [hdetrel]
  have hpowl : (-1 : ℝ) ^ l * (-1 : ℝ) ^ l = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow (Even.add_self l)
  have heq : (ε * (-1 : ℝ) ^ l * t) *
      ((-1 : ℝ) ^ (r.val + l) * (t * z r)) =
        (t * t) * (ε * (-1 : ℝ) ^ r.val * z r) := by
    rw [pow_add]
    calc
      _ = (t * t) * (ε * (-1 : ℝ) ^ r.val *
          (((-1 : ℝ) ^ l * (-1 : ℝ) ^ l) * z r)) := by ring
      _ = _ := by rw [hpowl, one_mul]
  rw [heq]
  exact mul_pos (mul_self_pos.mpr ht) hzr

theorem pascalOscillationTrailingMinor_ne_zero {q l : ℕ}
    (Q : Matrix (Fin (q + l + 1)) (Fin (q + l + 1)) ℝ)
    (hQ : Q.transpose * Q = 1)
    (hlead : ∃ ε : ℝ, ∀ (u : Fin (q + 1) → Fin (q + l + 1)),
      StrictMono u → 0 < ε * Matrix.det (fun a b : Fin (q + 1) =>
        Q (u a) (pascalOscillationLeadingColumn b)))
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f)
    (r₀ : Fin (l + 1)) :
    Matrix.det (fun a b : Fin l =>
      Q (f (r₀.succAbove a)) (pascalOscillationTrailingColumn b)) ≠ 0 := by
  intro hdet
  let D : Matrix (Fin l) (Fin l) ℝ := fun a b =>
    Q (f (r₀.succAbove a)) (pascalOscillationTrailingColumn b)
  have hDdet : Matrix.det D = 0 := hdet
  obtain ⟨v, hvne, hDv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hDdet
  let X : Fin (q + l + 1) → ℝ := fun x =>
    ∑ d : Fin l, Q x (pascalOscillationTrailingColumn d) * v d
  have hXother : ∀ a : Fin l, X (f (r₀.succAbove a)) = 0 := by
    intro a
    have ha := congrFun hDv a
    simpa [D, X, Matrix.mulVec, dotProduct] using ha
  have hcross : ∀ (c : Fin (q + 1)) (d : Fin l),
      (∑ x : Fin (q + l + 1),
        Q x (pascalOscillationLeadingColumn c) * Q x (pascalOscillationTrailingColumn d)) = 0 := by
    intro c d
    have hc := congrArg
      (fun M : Matrix (Fin (q + l + 1)) (Fin (q + l + 1)) ℝ =>
        M (pascalOscillationLeadingColumn c) (pascalOscillationTrailingColumn d)) hQ
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      pascalOscillationLeadingColumn_ne_trailingColumn c d, if_false] at hc
    exact hc
  have hXorth : ∀ c : Fin (q + 1),
      (∑ x : Fin (q + l + 1), Q x (pascalOscillationLeadingColumn c) * X x) = 0 := by
    intro c
    simp only [X]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro d _
    calc
      (∑ x, Q x (pascalOscillationLeadingColumn c) *
          (Q x (pascalOscillationTrailingColumn d) * v d)) =
        (∑ x, Q x (pascalOscillationLeadingColumn c) *
          Q x (pascalOscillationTrailingColumn d)) * v d := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = 0 := by rw [hcross c d, zero_mul]
  have hsumf (c : Fin (q + 1)) :
      (∑ r : Fin (l + 1), Q (f r) (pascalOscillationLeadingColumn c) * X (f r)) =
        Q (f r₀) (pascalOscillationLeadingColumn c) * X (f r₀) := by
    apply Finset.sum_eq_single r₀
    · intro r _ hr
      obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hr
      rw [← ha, hXother a, mul_zero]
    · intro hr
      exact (hr (Finset.mem_univ r₀)).elim
  have hrestricted (c : Fin (q + 1)) :
      Q (f r₀) (pascalOscillationLeadingColumn c) * X (f r₀) +
        (∑ j : Fin q, Q (pascalOscillationComplementRows f hf j)
          (pascalOscillationLeadingColumn c) * X (pascalOscillationComplementRows f hf j)) = 0 := by
    have hpart := pascalOscillation_sum_fRange_complement f hf
      (fun x => Q x (pascalOscillationLeadingColumn c) * X x)
    rw [hXorth c, hsumf c] at hpart
    exact hpart.symm
  let A : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ := fun a b =>
    Q ((Fin.cons (f r₀) (pascalOscillationComplementRows f hf) :
        Fin (q + 1) → Fin (q + l + 1)) a) (pascalOscillationLeadingColumn b)
  let w : Fin (q + 1) → ℝ :=
    Fin.cons (X (f r₀)) (fun j => X (pascalOscillationComplementRows f hf j))
  have hATw : Matrix.mulVec A.transpose w = 0 := by
    funext c
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply]
    rw [Fin.sum_univ_succ]
    simpa [A, w] using hrestricted c
  have hAne : Matrix.det A ≠ 0 := by
    obtain ⟨ε, hε⟩ := pascalOscillationLeadingCofactorVector_sign Q hlead f hf
    have hp := hε r₀
    rw [pascalOscillationLeadingCofactorVector_eq_det_cons] at hp
    intro hzero
    change Matrix.det (fun a b : Fin (q + 1) =>
      Q ((Fin.cons (f r₀) (pascalOscillationComplementRows f hf) :
          Fin (q + 1) → Fin (q + l + 1)) a) (pascalOscillationLeadingColumn b)) = 0 at hzero
    rw [hzero] at hp
    norm_num at hp
  have hATne : Matrix.det A.transpose ≠ 0 := by
    simpa using hAne
  have hw : w = 0 := Matrix.eq_zero_of_mulVec_eq_zero hATne hATw
  have hXr₀ : X (f r₀) = 0 := by
    have h := congrFun hw 0
    simpa [w] using h
  have hXg : ∀ j : Fin q, X (pascalOscillationComplementRows f hf j) = 0 := by
    intro j
    have h := congrFun hw j.succ
    simpa [w] using h
  have hXzero : X = 0 := by
    funext x
    let e : Fin (l + 1) ⊕ Fin q ≃ Fin (q + l + 1) :=
      finSumEquivOfFinset (pascalOscillationFRange_card f hf)
        (pascalOscillationFRange_compl_card f hf)
    obtain ⟨y, rfl⟩ := e.surjective x
    cases y with
    | inl r =>
        rw [show e (Sum.inl r) = f r by
          simp [e, pascalOscillationFRange_orderEmb_eq f hf]]
        by_cases hr : r = r₀
        · subst r
          simpa using hXr₀
        · obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hr
          rw [← ha, hXother a]
          rfl
    | inr j =>
        rw [show e (Sum.inr j) = pascalOscillationComplementRows f hf j by rfl,
          hXg j]
        rfl
  have htailOrth : ∀ d e : Fin l,
      (∑ x : Fin (q + l + 1),
        Q x (pascalOscillationTrailingColumn d) * Q x (pascalOscillationTrailingColumn e)) =
          if d = e then 1 else 0 := by
    intro d e
    have hc := congrArg
      (fun M : Matrix (Fin (q + l + 1)) (Fin (q + l + 1)) ℝ =>
        M (pascalOscillationTrailingColumn d) (pascalOscillationTrailingColumn e)) hQ
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      pascalOscillationTrailingColumn, Fin.ext_iff] using hc
  have hvzero : v = 0 := by
    funext d
    have hz : (∑ x : Fin (q + l + 1),
        Q x (pascalOscillationTrailingColumn d) * X x) = 0 := by
      simp [hXzero]
    simp only [X] at hz
    simp_rw [Finset.mul_sum] at hz
    rw [Finset.sum_comm] at hz
    have heq : (∑ e : Fin l,
        (∑ x : Fin (q + l + 1),
          Q x (pascalOscillationTrailingColumn d) * Q x (pascalOscillationTrailingColumn e)) * v e) =
        v d := by
      simp_rw [htailOrth]
      simp
    have hz' : (∑ e : Fin l,
        (∑ x : Fin (q + l + 1),
          Q x (pascalOscillationTrailingColumn d) * Q x (pascalOscillationTrailingColumn e)) * v e) = 0 := by
      convert hz using 1
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [heq] at hz'
    exact hz'
  exact hvne hvzero

theorem pascalOscillation_checkerTrailing_local_orientation {q l : ℕ}
    (Q : Matrix (Fin (q + l + 1)) (Fin (q + l + 1)) ℝ)
    (hQ : Q.transpose * Q = 1)
    (hlead : ∃ ε : ℝ, ∀ (u : Fin (q + 1) → Fin (q + l + 1)),
      StrictMono u → 0 < ε * Matrix.det (fun a b : Fin (q + 1) =>
        Q (u a) (pascalOscillationLeadingColumn b)))
    (f : Fin (l + 1) → Fin (q + l + 1)) (hf : StrictMono f) :
    ∃ η : ℝ, ∀ r : Fin (l + 1),
      0 < η * Matrix.det (fun a b : Fin l =>
        (-1 : ℝ) ^ (f (r.succAbove a)).val *
          Q (f (r.succAbove a)) (pascalOscillationTrailingColumn b)) := by
  let B : Fin (l + 1) → Fin l → ℝ := fun r c =>
    (-1 : ℝ) ^ (f r).val * Q (f r) (pascalOscillationTrailingColumn c)
  let y : Fin (q + l + 1) → ℝ :=
    pascalOscillationLeadingCofactorVector Q f hf
  let z : Fin (l + 1) → ℝ := fun r => (-1 : ℝ) ^ (f r).val * y (f r)
  have hzsign : ∃ ε : ℝ, ∀ r : Fin (l + 1),
      0 < ε * (-1 : ℝ) ^ r.val * z r := by
    simpa [z, y] using pascalOscillationLeadingCofactorVector_sign Q hlead f hf
  have hsum : ∀ c : Fin l,
      (∑ r : Fin (l + 1), y (f r) * Q (f r) (pascalOscillationTrailingColumn c)) = 0 := by
    intro c
    have horth := pascalOscillationLeadingCofactorVector_orthogonal_trailing Q hQ f hf c
    have hpart := pascalOscillation_sum_fRange_complement f hf
      (fun x => y x * Q x (pascalOscillationTrailingColumn c))
    rw [horth] at hpart
    have hcomp : (∑ j : Fin q,
        y (pascalOscillationComplementRows f hf j) *
          Q (pascalOscillationComplementRows f hf j) (pascalOscillationTrailingColumn c)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [show y (pascalOscillationComplementRows f hf j) = 0 by
        exact pascalOscillationLeadingCofactorVector_complement_zero Q f hf j, zero_mul]
    rw [hcomp, add_zero] at hpart
    exact hpart.symm
  have hzker : ∀ c : Fin l, (∑ r : Fin (l + 1), z r * B r c) = 0 := by
    intro c
    calc
      (∑ r : Fin (l + 1), z r * B r c) =
        ∑ r : Fin (l + 1), y (f r) * Q (f r) (pascalOscillationTrailingColumn c) := by
          apply Finset.sum_congr rfl
          intro r _
          have hp : (-1 : ℝ) ^ (f r).val * (-1 : ℝ) ^ (f r).val = 1 := by
            rw [← pow_add]
            exact Even.neg_one_pow (Even.add_self (f r).val)
          simp only [z, B]
          calc
            (-1 : ℝ) ^ (f r).val * y (f r) *
                ((-1 : ℝ) ^ (f r).val *
                  Q (f r) (pascalOscillationTrailingColumn c)) =
              (((-1 : ℝ) ^ (f r).val) *
                ((-1 : ℝ) ^ (f r).val)) *
                  (y (f r) * Q (f r) (pascalOscillationTrailingColumn c)) := by ring
            _ = _ := by rw [hp, one_mul]
      _ = 0 := hsum c
  have hminor₀ : Matrix.det (fun a b : Fin l => B (Fin.succ a) b) ≠ 0 := by
    have hM := pascalOscillationTrailingMinor_ne_zero Q hQ hlead f hf (0 : Fin (l + 1))
    let vrow : Fin l → ℝ := fun a => (-1 : ℝ) ^ (f (Fin.succ a)).val
    let M : Matrix (Fin l) (Fin l) ℝ := fun a b =>
      Q (f (Fin.succ a)) (pascalOscillationTrailingColumn b)
    have heq := Matrix.det_mul_column vrow M
    have heq' : Matrix.det (fun a b : Fin l => B (Fin.succ a) b) =
        (∏ a : Fin l, vrow a) * Matrix.det M := by
      simpa [B, vrow, M] using heq
    rw [heq']
    apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro a _
      exact pow_ne_zero _ (by norm_num)
    · simpa [M] using hM
  simpa [B] using pascalOscillation_leftKernel_orients_maximal_minors B z hzker hzsign hminor₀

end NumStability
