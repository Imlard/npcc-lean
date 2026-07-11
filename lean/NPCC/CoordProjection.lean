import Mathlib
import NPCC.Defs

/-! # Coordinate projection (paper lem:coord-projection), typed form. -/

namespace NPCC

-- CLAIM-BEGIN lem:coord-projection
/-- Paper `lem:coord-projection` (Coordinate projection), typed form.

Paper: for an `m × n` matrix, `p ≥ 1`, `Q ⊆ [p]` with `|Q| = r ≥ 1`,
`0 < y ≤ 1`, `T ≥ 1`, a submatrix `N` of the `p`-fold interlace whose row set
is `(Q,T)`-equipartitioned and whose column set has size ≥ `n^p·y` contains a
member of `⟨M, r, x, y⟩` whenever `0 < x ≤ 1` and `⌈m·x⌉ ≤ T`.

Typed rendering: the submatrix is its extraction data `(R, C)`; the bijection
`Q → [r]` of the paper is the explicit equivalence `e : Fin r ≃ {q // q ∈ Q}`
(its existence pins `r = |Q|`); "contains a member of the `r`-fold bracket" is
an `RC' ∈ bracketGE X Y r x y` whose rows come from `R` (each row `(j, v)` of
`RC'` arises from the row `((e j : Fin p), v) ∈ R`) and whose columns are
`Q`-projections of columns of `C` (each `c' ∈ RC'.2` agrees with some `c ∈ C`
on all of `Q` via `e`). Side conditions `p ≥ 1`, `T ≥ 1`, `0 < x,y ≤ 1` are
use-site hypotheses (not needed for truth here); `r ≥ 1` is kept — for `r = 0`
with `Y` empty the paper's claim degenerates falsely, matching the paper's
`|Q| = r ≥ 1`. -/
theorem coord_projection {X Y : Type*} [Fintype X] [Fintype Y]
    {p r : ℕ} (hr : 0 < r) {Q : Finset (Fin p)} (e : Fin r ≃ {q // q ∈ Q})
    {R : Finset (Fin p × X)} {C : Finset (Fin p → Y)} {T : ℕ} {x y : ℝ}
    (hrow : IsEquipartitionedGE R Q T)
    (hcol : ⌈((Fintype.card Y : ℝ) ^ p) * y⌉₊ ≤ C.card)
    (hxT : ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ T) :
    ∃ RC' : Finset (Fin r × X) × Finset (Fin r → Y),
      RC' ∈ bracketGE X Y r x y ∧
      (∀ a ∈ RC'.1, ((e a.1).val, a.2) ∈ R) ∧
      (∀ c' ∈ RC'.2, ∃ c ∈ C, ∀ j : Fin r, c' j = c (e j).val) :=
-- CLAIM-END lem:coord-projection
  by
  classical
  -- abbreviations
  set K : ℕ := ⌈(Fintype.card X : ℝ) * x⌉₊ with hK
  -- ROWS: for each j, pick K rows in the fiber over (e j).val
  have hch : ∀ j : Fin r, ∃ t : Finset (Fin p × X),
      t ⊆ R.filter (fun a => a.1 = (e j).val) ∧ t.card = K := by
    intro j
    apply Finset.exists_subset_card_eq
    exact le_trans hxT (hrow (e j).val (e j).property)
  choose t hsub hcard using hch
  -- the row set of RC'
  set Rows : Finset (Fin r × X) :=
    Finset.univ.biUnion (fun j => (t j).image (fun a => (j, a.2))) with hRows
  -- key: membership fact.  Every a ∈ t j has a.1 = (e j).val
  have hmemfst : ∀ (j : Fin r) (a : Fin p × X), a ∈ t j → a.1 = (e j).val := by
    intro j a ha
    have := hsub j ha
    rw [Finset.mem_filter] at this
    exact this.2
  have hmemR : ∀ (j : Fin r) (a : Fin p × X), a ∈ t j → a ∈ R := by
    intro j a ha
    have := hsub j ha
    rw [Finset.mem_filter] at this
    exact this.1
  -- the fiber of Rows over j0 equals (t j0).image (fun a => (j0, a.2))
  have hfiber : ∀ j0 : Fin r,
      (Rows.filter (fun q => q.1 = j0)) = (t j0).image (fun a => ((j0, a.2) : Fin r × X)) := by
    intro j0
    ext q
    simp only [hRows, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j, a, ha, rfl⟩, hq⟩
      -- hq : (j, a.2).1 = j0  i.e. j = j0
      simp only at hq
      subst hq
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨j0, a, ha, rfl⟩, rfl⟩
  -- injectivity of the image map on t j0
  have hinj : ∀ j0 : Fin r, Set.InjOn (fun a : Fin p × X => ((j0, a.2) : Fin r × X)) (t j0) := by
    intro j0 a ha b hb hab
    simp only [Prod.mk.injEq] at hab
    -- a.1 = (e j0).val = b.1, and a.2 = b.2 from hab
    have h1 := hmemfst j0 a ha
    have h2 := hmemfst j0 b hb
    apply Prod.ext
    · rw [h1, h2]
    · exact hab.2
  -- each fiber card = K
  have hfibercard : ∀ j0 : Fin r, (Rows.filter (fun q => q.1 = j0)).card = K := by
    intro j0
    rw [hfiber j0, Finset.card_image_of_injOn (hinj j0), hcard j0]
  -- Rows is (univ, K)-equipartitioned ≥
  have hRowsEq : IsEquipartitionedGE Rows (Finset.univ : Finset (Fin r)) K := by
    intro q _
    rw [hfibercard q]
  -- provenance of rows
  have hRowsProv : ∀ a ∈ Rows, ((e a.1).val, a.2) ∈ R := by
    intro a ha
    rw [hRows, Finset.mem_biUnion] at ha
    obtain ⟨j, _, hj⟩ := ha
    rw [Finset.mem_image] at hj
    obtain ⟨b, hb, rfl⟩ := hj
    -- a = (j, b.2), a.1 = j, so (e j).val = b.1 and (e j).val, b.2 ∈ R
    simp only
    have h1 := hmemfst j b hb
    have hbR := hmemR j b hb
    -- b = (b.1, b.2), and b.1 = (e j).val
    have : ((e j).val, b.2) = b := by
      rw [← h1]
    rw [this]
    exact hbR
  -- COLUMNS
  set proj : (Fin p → Y) → (Fin r → Y) := fun c j => c (e j).val with hproj
  set Cols : Finset (Fin r → Y) := C.image proj with hCols
  -- provenance of columns
  have hColsProv : ∀ c' ∈ Cols, ∃ c ∈ C, ∀ j : Fin r, c' j = c (e j).val := by
    intro c' hc'
    rw [hCols, Finset.mem_image] at hc'
    obtain ⟨c, hc, rfl⟩ := hc'
    exact ⟨c, hc, fun j => rfl⟩
  -- r ≤ p
  have hrp : r ≤ p := by
    have hQcard : Q.card = r := by
      have : Fintype.card (Fin r) = Fintype.card {q // q ∈ Q} := Fintype.card_congr e
      rw [Fintype.card_fin, Fintype.card_coe] at this
      omega
    have : Q.card ≤ p := by
      have h1 : Q.card ≤ Fintype.card (Fin p) := Finset.card_le_card (Finset.subset_univ Q) |>.trans (le_of_eq (Finset.card_univ))
      rw [Fintype.card_fin] at h1
      exact h1
    omega
  -- fiber bound: each proj-fiber inside C has ≤ (card Y)^(p-r) elements
  have hfiberbound : ∀ c0 ∈ Cols,
      (C.filter (fun c => proj c = c0)).card ≤ (Fintype.card Y) ^ (p - r) := by
    intro c0 _
    -- map fiber into functions on Qᶜ (as subtype), injectively
    apply le_trans (Finset.card_le_card_of_injOn
      (f := fun (c : Fin p → Y) => (fun s : {q : Fin p // q ∈ Qᶜ} => c s.val))
      (t := (Finset.univ : Finset ({q : Fin p // q ∈ Qᶜ} → Y))) ?_ ?_)
    · -- card univ = (card Y)^(Qᶜ.card) = (card Y)^(p-r)
      rw [Finset.card_univ, Fintype.card_fun]
      have : Fintype.card {q : Fin p // q ∈ Qᶜ} = p - r := by
        rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
        have hQcard : Q.card = r := by
          have : Fintype.card (Fin r) = Fintype.card {q // q ∈ Q} := Fintype.card_congr e
          rw [Fintype.card_fin, Fintype.card_coe] at this
          omega
        rw [hQcard]
      rw [this]
    · -- MapsTo: everything maps to univ
      intro c _
      exact Finset.mem_univ _
    · -- InjOn: two members of the fiber agreeing on Qᶜ and on Q agree everywhere
      intro c1 hc1 c2 hc2 hres
      rw [Finset.mem_coe, Finset.mem_filter] at hc1 hc2
      -- they agree on Q: proj c1 = c0 = proj c2, and for q ∈ Q,
      -- c1 q = proj c1 (e.symm ⟨q,hq⟩) = proj c2 (e.symm ⟨q,hq⟩) = c2 q
      have hprojeq : proj c1 = proj c2 := by rw [hc1.2, hc2.2]
      funext q
      by_cases hq : q ∈ Q
      · -- agree via Q
        have hval : (e (e.symm ⟨q, hq⟩)).val = q := by
          rw [Equiv.apply_symm_apply]
        have h1 : c1 q = proj c1 (e.symm ⟨q, hq⟩) := by
          simp only [hproj]; rw [hval]
        have h2 : c2 q = proj c2 (e.symm ⟨q, hq⟩) := by
          simp only [hproj]; rw [hval]
        rw [h1, h2, hprojeq]
      · -- agree via Qᶜ via hres
        have hqc : q ∈ Qᶜ := by rw [Finset.mem_compl]; exact hq
        have := congrFun hres ⟨q, hqc⟩
        simpa using this
  -- global bound
  have hglobal : C.card ≤ (Fintype.card Y) ^ (p - r) * Cols.card := by
    have hn : ∀ b ∈ Finset.image proj C, (C.filter (fun c => proj c = b)).card ≤ (Fintype.card Y) ^ (p - r) :=
      fun b hb => hfiberbound b (by rw [hCols]; exact hb)
    have := Finset.card_le_mul_card_image (f := proj) C ((Fintype.card Y) ^ (p - r)) hn
    rw [hCols]
    exact this
  -- real-arithmetic finish: cardY^r * y ≤ Cols.card, hence ceiling ≤ Cols.card
  set cY : ℕ := Fintype.card Y with hcY
  have hcolcard : ⌈((cY : ℝ) ^ r) * y⌉₊ ≤ Cols.card := by
    rcases Nat.eq_zero_or_pos cY with h0 | hpos
    · -- cardY = 0: ceiling is 0
      rw [h0]
      have : ((0 : ℕ) : ℝ) ^ r = 0 := by
        rw [Nat.cast_zero, zero_pow hr.ne']
      rw [this, zero_mul, Nat.ceil_zero]
      exact Nat.zero_le _
    · -- 0 < cardY
      -- from hcol and Nat.le_ceil: cardY^p * y ≤ C.card
      have hle_ceil : ((cY : ℝ) ^ p) * y ≤ (C.card : ℝ) := by
        calc ((cY : ℝ) ^ p) * y ≤ (⌈((cY : ℝ) ^ p) * y⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (C.card : ℝ) := by
              rw [hcY] at hcol ⊢
              exact_mod_cast hcol
      -- cardY^p = cardY^r * cardY^(p-r)
      have hpow : (cY : ℝ) ^ p = (cY : ℝ) ^ r * (cY : ℝ) ^ (p - r) := by
        rw [← pow_add, Nat.add_sub_cancel' hrp]
      -- C.card ≤ cardY^(p-r) * Cols.card as reals
      have hglobalR : (C.card : ℝ) ≤ (cY : ℝ) ^ (p - r) * (Cols.card : ℝ) := by
        rw [hcY]; exact_mod_cast hglobal
      -- combine: (cardY^r * y) * cardY^(p-r) = cardY^p * y ≤ C.card ≤ cardY^(p-r)*Cols.card
      have hpospow : (0 : ℝ) < (cY : ℝ) ^ (p - r) := by
        apply pow_pos
        exact_mod_cast hpos
      have hchain : ((cY : ℝ) ^ r * y) * (cY : ℝ) ^ (p - r) ≤ (Cols.card : ℝ) * (cY : ℝ) ^ (p - r) := by
        calc ((cY : ℝ) ^ r * y) * (cY : ℝ) ^ (p - r)
            = ((cY : ℝ) ^ p) * y := by rw [hpow]; ring
          _ ≤ (C.card : ℝ) := hle_ceil
          _ ≤ (cY : ℝ) ^ (p - r) * (Cols.card : ℝ) := hglobalR
          _ = (Cols.card : ℝ) * (cY : ℝ) ^ (p - r) := by ring
      -- divide by cardY^(p-r)
      have hfinal : (cY : ℝ) ^ r * y ≤ (Cols.card : ℝ) :=
        le_of_mul_le_mul_right hchain hpospow
      -- ceiling
      rw [Nat.ceil_le]
      exact hfinal
  -- ASSEMBLE
  refine ⟨(Rows, Cols), ⟨?_, ?_⟩, ?_, ?_⟩
  · -- IsEquipartitionedGE Rows univ ⌈card X * x⌉
    exact hRowsEq
  · -- ⌈cardY^r * y⌉ ≤ Cols.card
    exact hcolcard
  · exact hRowsProv
  · exact hColsProv

end NPCC
