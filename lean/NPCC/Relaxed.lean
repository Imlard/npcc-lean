import Mathlib
import NPCC.Defs

/-! # Relaxed interlacing (paper §4), typed definitions.
The column family is INDEXED (`Fin L → (Fin q → Y)`) — repeats allowed and
counted, per the paper. Existence of balanced families is the AGHP citation
axiom (`NPCC.Axioms`); these definitions only fix the predicate and the game. -/

namespace NPCC

-- CLAIM-BEGIN def:balanced-family
/-- Paper `def:balanced-columns` ((q,t)-balanced column family with accuracy
`ε`), typed over an INDEXED family `S : Fin L → (Fin q → Y)` (multiplicity
counts: the probability is over the uniform index `j : Fin L`). The paper's
two-sided bound `Pr[𝐲|_J = 𝐚] = |Y|^{-|J|} ± ε·|Y|^{-|J|}` is the absolute-
value inequality below; patterns are quantified as total functions read only
on `J`. `L > 0` is carried by the predicate so the probability is
well-formed. -/
def IsBalancedFamily {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q L : ℕ} (t : ℕ) (S : Fin L → Fin q → Y) (ε : ℝ) : Prop :=
  0 < L ∧
  ∀ J : Finset (Fin q), J.card ≤ t → ∀ a : Fin q → Y,
    |((Finset.univ.filter
          (fun j : Fin L => ∀ γ ∈ J, S j γ = a γ)).card : ℝ) / (L : ℝ)
      - 1 / (Fintype.card Y : ℝ) ^ J.card|
    ≤ ε / (Fintype.card Y : ℝ) ^ J.card
-- CLAIM-END def:balanced-family

-- CLAIM-BEGIN def:relaxed-interlace
/-- Paper `def:relaxed-interlace`: the relaxed interlace of `f : X → Y → Bool`
by an indexed column family `S : Fin L → (Fin q → Y)` is the game whose rows
are the classical interlace rows `Fin q × X` and whose columns are the FAMILY
INDICES `Fin L` (so repeated tuples give genuinely distinct columns), with
value `f x (S j i)` at row `(i, x)` and column `j`. With `S` enumerating the
full product this recovers the classical interlace up to column relabeling.
The paper uses a balanced family as a succinct substitute; its exact
cardinality bound and the external asymptotic wrapper are tracked separately. -/
def relaxedInterlace {X Y : Type*} (f : X → Y → Bool)
    {q L : ℕ} (S : Fin L → Fin q → Y) :
    (Fin q × X) → Fin L → Bool :=
  fun a j => f a.2 (S j a.1)
-- CLAIM-END def:relaxed-interlace

-- CLAIM-BEGIN lem:balanced-projection
/-- Paper `lem:balanced-projection` (Projection closure of balanced
families): pulling an indexed `(q,t)`-balanced family back along an
injection of coordinates `e : Fin q₀ → Fin q` yields a `(q₀,t)`-balanced
family with the SAME accuracy. The paper phrases this for subsets
`J ⊆ [q]` and their projections; the injection form subsumes it (take `e`
enumerating `J`) and composes with the reindexings used downstream. -/
theorem IsBalancedFamily.projection {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q q₀ L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (h : IsBalancedFamily t S ε)
    (e : Fin q₀ → Fin q) (he : Function.Injective e) :
    IsBalancedFamily t (fun j i₀ => S j (e i₀)) ε :=
-- CLAIM-END lem:balanced-projection
  by
  refine ⟨h.1, ?_⟩
  intro J0 hcard a
  -- Handle the empty J0 case directly, otherwise Y is inhabited.
  rcases J0.eq_empty_or_nonempty with hJ0 | hJ0ne
  · -- J0 = ∅: the filter event is vacuous (= univ), value is 1; need 0 ≤ ε,
    -- extracted from the hypothesis at ∅ with the ready-made pattern S j0.
    subst hJ0
    -- L > 0 gives an index j0, hence a total pattern S j0 : Fin q → Y.
    have hLpos : 0 < L := h.1
    obtain ⟨j0⟩ : Nonempty (Fin L) := ⟨⟨0, hLpos⟩⟩
    have hbal := h.2 (∅ : Finset (Fin q)) (by simp) (S j0)
    have heps : 0 ≤ ε := by
      have := le_trans (abs_nonneg _) hbal
      simpa using this
    -- Now the projected empty case: filter = univ, value 1, |1-1| = 0 ≤ ε.
    have hfilter : (Finset.univ.filter
        (fun j : Fin L => ∀ γ ∈ (∅ : Finset (Fin q₀)),
          S j (e γ) = a γ)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro j _ γ hγ
      simp at hγ
    rw [hfilter]
    simp only [Finset.card_empty, pow_zero, Finset.card_univ, Fintype.card_fin]
    have hL : (0:ℝ) < L := by exact_mod_cast hLpos
    rw [div_self (ne_of_gt hL)]
    simpa using heps
  · -- J0 nonempty: Y inhabited.
    obtain ⟨γ0, hγ0⟩ := hJ0ne
    have hYne : Nonempty Y := ⟨a γ0⟩
    haveI : Nonempty Y := hYne
    -- Build the total extension a2 along e.
    classical
    let a2 : Fin q → Y := fun γ =>
      if hg : ∃ γ0 : Fin q₀, γ0 ∈ J0 ∧ e γ0 = γ then a hg.choose
      else Classical.arbitrary Y
    -- Key fact: for γ0 ∈ J0, a2 (e γ0) = a γ0.
    have ha2 : ∀ γ0 ∈ J0, a2 (e γ0) = a γ0 := by
      intro δ hδ
      have hex : ∃ γ0 : Fin q₀, γ0 ∈ J0 ∧ e γ0 = e δ := ⟨δ, hδ, rfl⟩
      simp only [a2, dif_pos hex]
      -- hex.choose satisfies e hex.choose = e δ, so by injectivity = δ.
      have hspec := hex.choose_spec
      have : e hex.choose = e δ := hspec.2
      have hchoose : hex.choose = δ := he this
      rw [hchoose]
    -- The two filter events coincide.
    have hevent : (Finset.univ.filter
        (fun j : Fin L => ∀ γ ∈ J0, S j (e γ) = a γ))
      = (Finset.univ.filter
        (fun j : Fin L => ∀ γ ∈ J0.image e, S j γ = a2 γ)) := by
      apply Finset.filter_congr
      intro j _
      constructor
      · intro hj γ hγ
        rw [Finset.mem_image] at hγ
        obtain ⟨δ, hδJ0, hδeq⟩ := hγ
        subst hδeq
        rw [ha2 δ hδJ0]
        exact hj δ hδJ0
      · intro hj δ hδJ0
        have hmem : e δ ∈ J0.image e := Finset.mem_image_of_mem e hδJ0
        have := hj (e δ) hmem
        rw [ha2 δ hδJ0] at this
        exact this
    -- Card of image = card of J0 by injectivity.
    have hcardimg : (J0.image e).card = J0.card :=
      Finset.card_image_of_injective J0 he
    -- Apply the hypothesis at J := J0.image e, pattern a2.
    have hbal := h.2 (J0.image e) (by rw [hcardimg]; exact hcard) a2
    rw [hcardimg] at hbal
    rw [hevent]
    exact hbal

-- CLAIM-BEGIN lem:block-balancing
/-- Paper `lem:block-balancing` (Balancing-by-blocks): a typed interlace row
set of total density `β = |R| / (q·m) ≥ x` (with `0 < x < 1`, `m = |X|`)
admits at least `⌈q(β−x)/(1−x)⌉` full blocks — a coordinate set `J` on which
`R` is `(J, ⌈m·x⌉)`-equipartitioned in the `≥`-sense. Callers trim `J` to any
exact size with `IsEquipartitionedGE.mono_Q`. Degenerate `q·m = 0` is vacuous
(real division by zero is `0`, contradicting `0 < x ≤ β`). -/
theorem block_balancing {X : Type*} [Fintype X] {q : ℕ}
    {R : Finset (Fin q × X)} {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hβ : x ≤ (R.card : ℝ) / ((q : ℝ) * (Fintype.card X : ℝ))) :
    ∃ J : Finset (Fin q),
      ⌈(q : ℝ) * ((R.card : ℝ) / ((q : ℝ) * (Fintype.card X : ℝ)) - x)
          / (1 - x)⌉₊ ≤ J.card ∧
      IsEquipartitionedGE R J ⌈(Fintype.card X : ℝ) * x⌉₊ :=
-- CLAIM-END lem:block-balancing
  by
  classical
  set m : ℕ := Fintype.card X with hm
  set T : ℕ := ⌈(m : ℝ) * x⌉₊ with hT
  -- fiber cardinalities
  set r : Fin q → ℕ := fun i => (R.filter (fun p => p.1 = i)).card with hr
  -- full blocks
  set J : Finset (Fin q) := Finset.univ.filter (fun i => T ≤ r i) with hJ
  refine ⟨J, ?_, ?_⟩
  · -- the ceiling bound on |J|
    -- Degenerate guard: 0 < q*m.
    have hqm_pos : 0 < (q : ℝ) * (m : ℝ) := by
      rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ (q:ℝ) * (m:ℝ)) with h0 | hpos
      · exfalso
        rw [← h0] at hβ
        simp only [div_zero] at hβ
        exact absurd (lt_of_lt_of_le hx0 hβ) (lt_irrefl 0)
      · exact hpos
    have hq_pos : 0 < (q : ℝ) := by
      by_contra hqle
      push Not at hqle
      have : (q : ℝ) = 0 := le_antisymm hqle (by positivity)
      rw [this] at hqm_pos; simp at hqm_pos
    have hm_pos : 0 < (m : ℝ) := by
      by_contra hmle
      push Not at hmle
      have : (m : ℝ) = 0 := le_antisymm hmle (by positivity)
      rw [this] at hqm_pos; simp at hqm_pos
    have h1mx : (0:ℝ) < 1 - x := by linarith
    -- Fiberwise sum: R.card = Σ i, r i
    have hsum : (R.card : ℕ) = ∑ i, r i := by
      rw [hr]
      exact Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ a.1)
    -- each fiber ≤ m
    have hfib_le : ∀ i, r i ≤ m := by
      intro i
      rw [hr, hm]
      apply Finset.card_le_card_of_injOn (fun a => a.2)
      · intro a _; exact Finset.mem_univ _
      · intro a ha b hb hab
        have ha1 : a.1 = i := (Finset.mem_filter.mp ha).2
        have hb1 : b.1 = i := (Finset.mem_filter.mp hb).2
        exact Prod.ext (ha1.trans hb1.symm) hab
    -- for i ∉ J: r i ≤ T - 1, hence (r i : ℝ) ≤ (m:ℝ)*x
    have hdef_le : ∀ i ∉ J, (r i : ℝ) ≤ (m : ℝ) * x := by
      intro i hi
      have hlt : r i < T := by
        by_contra hge
        push Not at hge
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hge⟩)
      -- r i ≤ T - 1, and T ≤ m*x + 1 so r i ≤ m*x
      have hle : (r i : ℝ) ≤ (T : ℝ) - 1 := by
        have : r i + 1 ≤ T := hlt
        have := (Nat.cast_le (α := ℝ)).mpr this
        push_cast at this ⊢
        linarith
      have hTle : (T : ℝ) ≤ (m : ℝ) * x + 1 := by
        rw [hT]
        exact le_trans (Nat.ceil_lt_add_one (by positivity)).le (by linarith [Nat.ceil_lt_add_one (le_of_lt (by positivity : (0:ℝ) < (m:ℝ)*x))])
      linarith
    -- Bound the total sum in ℝ.
    -- Σ i, r i = Σ_{i∈J} r i + Σ_{i∉J} r i
    have hsplit : (R.card : ℝ) = (∑ i ∈ J, (r i : ℝ)) + (∑ i ∈ Jᶜ, (r i : ℝ)) := by
      rw [hsum]
      push_cast
      rw [← Finset.sum_add_sum_compl J (fun i => (r i : ℝ))]
    -- Σ_{i∈J} r i ≤ |J| * m
    have hJbound : (∑ i ∈ J, (r i : ℝ)) ≤ (J.card : ℝ) * (m : ℝ) := by
      calc (∑ i ∈ J, (r i : ℝ)) ≤ ∑ _i ∈ J, (m : ℝ) := by
            apply Finset.sum_le_sum
            intro i _
            exact_mod_cast hfib_le i
        _ = (J.card : ℝ) * (m : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    -- Σ_{i∉J} r i ≤ |Jᶜ| * (m*x) ≤ q * (m*x)
    have hJcbound : (∑ i ∈ Jᶜ, (r i : ℝ)) ≤ (Jᶜ.card : ℝ) * ((m : ℝ) * x) := by
      calc (∑ i ∈ Jᶜ, (r i : ℝ)) ≤ ∑ i ∈ Jᶜ, ((m : ℝ) * x) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hdef_le i (Finset.mem_compl.mp hi)
        _ = (Jᶜ.card : ℝ) * ((m : ℝ) * x) := by rw [Finset.sum_const, nsmul_eq_mul]
    -- |Jᶜ| = q - |J|, and |J| ≤ q
    have hJcard_le : J.card ≤ q := by
      calc J.card ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_le_univ _
        _ = q := by rw [Finset.card_univ, Fintype.card_fin]
    have hJc_card : (Jᶜ.card : ℝ) = (q : ℝ) - (J.card : ℝ) := by
      have : Jᶜ.card = Fintype.card (Fin q) - J.card := by
        rw [Finset.card_compl]
      rw [this, Fintype.card_fin]
      rw [Nat.cast_sub hJcard_le]
    -- Combine: R.card ≤ |J|*m + (q - |J|)*(m*x)
    have hmain : (R.card : ℝ) ≤ (J.card : ℝ) * (m : ℝ)
        + ((q : ℝ) - (J.card : ℝ)) * ((m : ℝ) * x) := by
      rw [hsplit]
      rw [hJc_card] at hJcbound
      linarith
    -- β := R.card / (q*m) ≥ x. From hmain derive |J| ≥ q*(β - x)/(1 - x).
    set β : ℝ := (R.card : ℝ) / ((q : ℝ) * (m : ℝ)) with hβdef
    -- R.card = β * (q * m)
    have hRβ : (R.card : ℝ) = β * ((q : ℝ) * (m : ℝ)) := by
      rw [hβdef]; field_simp
    -- Substitute and divide out m. First: β*q*m ≤ |J|*m + (q-|J|)*m*x
    -- ⟺ β*q ≤ |J| + (q-|J|)*x = |J|*(1-x) + q*x  (divide by m>0)
    have hstep : β * (q : ℝ) ≤ (J.card : ℝ) * (1 - x) + (q : ℝ) * x := by
      have hdivm : β * ((q : ℝ) * (m : ℝ))
          ≤ (J.card : ℝ) * (m : ℝ) + ((q : ℝ) - (J.card : ℝ)) * ((m : ℝ) * x) := by
        rw [← hRβ]; exact hmain
      -- divide both sides by m
      have := (div_le_div_iff_of_pos_right hm_pos).mpr hdivm
      -- messy; instead: use that m > 0 to cancel
      have hcancel : β * (q : ℝ) * (m:ℝ) ≤ ((J.card : ℝ) * (1 - x) + (q : ℝ) * x) * (m:ℝ) := by
        ring_nf
        ring_nf at hdivm
        nlinarith [hdivm]
      exact le_of_mul_le_mul_right (by linarith [hcancel]) hm_pos
    -- rearrange to |J| ≥ q*(β-x)/(1-x)
    have hJge : (q : ℝ) * (β - x) / (1 - x) ≤ (J.card : ℝ) := by
      rw [div_le_iff₀ h1mx]
      nlinarith [hstep]
    -- β from hβ
    have hβge : x ≤ β := by rw [hβdef]; exact hβ
    -- ceiling bound
    rw [Nat.ceil_le]
    -- goal: (q:ℝ)*(R.card/(q*m) - x)/(1-x) ≤ |J|
    -- rewrite R.card/(q*m) as β
    show (q : ℝ) * ((R.card : ℝ) / ((q : ℝ) * (m : ℝ)) - x) / (1 - x) ≤ (J.card : ℝ)
    rw [← hβdef]
    exact hJge
  · -- equipartition: immediate from mem_filter
    intro i hi
    have := (Finset.mem_filter.mp hi).2
    rw [hr] at this
    rw [hT] at this ⊢
    exact this

-- CLAIM-BEGIN lem:relaxed-to-classical
/-- Paper `lem:relaxed-to-classical` (THE bridge of Section 4): a submatrix of
the relaxed interlace that keeps a `(Q,T)`-equipartitioned row set (`|Q| = u`,
`1 <= u <= t`, realized by the equivalence `e`) and an index set `C'` of density
`>= y` yields a member of the classical `u`-fold bracket at column density
`y / (1 + eps)`: project the family to the `Q`-coordinates; balancedness (upper
side) bounds every projected pattern's index-fiber by `(1+eps)L/|Y|^u`, so at
least `y|Y|^u/(1+eps)` distinct patterns appear among `C'`; choosing one
representative index per pattern gives the bracket columns. Provenance mirrors
`coord_projection`: bracket rows come from `R` through `e`; every bracket
column is the `Q`-projection of an ACTUAL family member with index in `C'`
(the representative), which is what lets the protocol subtree transfer at the
separation theorem's handoff point. The paper's `T := ceil(m x)` is the
use-site hypothesis `hxT`; `eps >= 0` suffices here (the paper's
`eps_{q,t} < 1` matters only for later size lower bounds). -/
theorem relaxed_to_classical {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {q u t L : ℕ} (hu : 0 < u) (hut : u ≤ t)
    {S : Fin L → Fin q → Y} {ε : ℝ} (hS : IsBalancedFamily t S ε) (hε : 0 ≤ ε)
    {Q : Finset (Fin q)} (e : Fin u ≃ {i // i ∈ Q})
    {R : Finset (Fin q × X)} {C' : Finset (Fin L)} {T : ℕ} {x y : ℝ}
    (hrow : IsEquipartitionedGE R Q T)
    (hcol : y * (L : ℝ) ≤ (C'.card : ℝ))
    (hxT : ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ T) :
    ∃ RC' : Finset (Fin u × X) × Finset (Fin u → Y),
      RC' ∈ bracketGE X Y u x (y / (1 + ε)) ∧
      (∀ a ∈ RC'.1, ((e a.1).val, a.2) ∈ R) ∧
      (∀ c' ∈ RC'.2, ∃ j ∈ C', ∀ i : Fin u, c' i = S j (e i).val) :=
-- CLAIM-END lem:relaxed-to-classical
  by
  classical
  -- The coordinate map Fin u → Fin q, injective.
  set ecoord : Fin u → Fin q := fun i => (e i).val with hecoord
  have hecoord_inj : Function.Injective ecoord := by
    intro i1 i2 h12
    have : (e i1 : {i // i ∈ Q}) = e i2 := Subtype.ext h12
    exact e.injective this
  -- ================= ROWS (mirror coord_projection) =================
  set K : ℕ := ⌈(Fintype.card X : ℝ) * x⌉₊ with hK
  have hch : ∀ i : Fin u, ∃ s : Finset (Fin q × X),
      s ⊆ R.filter (fun a => a.1 = (e i).val) ∧ s.card = K := by
    intro i
    apply Finset.exists_subset_card_eq
    exact le_trans hxT (hrow (e i).val (e i).property)
  choose s hsub hcard using hch
  set Rows : Finset (Fin u × X) :=
    Finset.univ.biUnion (fun i => (s i).image (fun a => (i, a.2))) with hRows
  have hmemfst : ∀ (i : Fin u) (a : Fin q × X), a ∈ s i → a.1 = (e i).val := by
    intro i a ha
    have := hsub i ha
    rw [Finset.mem_filter] at this
    exact this.2
  have hmemR : ∀ (i : Fin u) (a : Fin q × X), a ∈ s i → a ∈ R := by
    intro i a ha
    have := hsub i ha
    rw [Finset.mem_filter] at this
    exact this.1
  have hfiber : ∀ i0 : Fin u,
      (Rows.filter (fun q => q.1 = i0)) = (s i0).image (fun a => ((i0, a.2) : Fin u × X)) := by
    intro i0
    ext p
    simp only [hRows, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, a, ha, rfl⟩, hp⟩
      simp only at hp
      subst hp
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨i0, a, ha, rfl⟩, rfl⟩
  have hinj : ∀ i0 : Fin u, Set.InjOn (fun a : Fin q × X => ((i0, a.2) : Fin u × X)) (s i0) := by
    intro i0 a ha b hb hab
    simp only [Prod.mk.injEq] at hab
    have h1 := hmemfst i0 a ha
    have h2 := hmemfst i0 b hb
    apply Prod.ext
    · rw [h1, h2]
    · exact hab.2
  have hfibercard : ∀ i0 : Fin u, (Rows.filter (fun q => q.1 = i0)).card = K := by
    intro i0
    rw [hfiber i0, Finset.card_image_of_injOn (hinj i0), hcard i0]
  have hRowsEq : IsEquipartitionedGE Rows (Finset.univ : Finset (Fin u)) K := by
    intro i _
    rw [hfibercard i]
  have hRowsProv : ∀ a ∈ Rows, ((e a.1).val, a.2) ∈ R := by
    intro a ha
    rw [hRows, Finset.mem_biUnion] at ha
    obtain ⟨i, _, hi⟩ := ha
    rw [Finset.mem_image] at hi
    obtain ⟨b, hb, rfl⟩ := hi
    simp only
    have h1 := hmemfst i b hb
    have hbR := hmemR i b hb
    have : ((e i).val, b.2) = b := by rw [← h1]
    rw [this]
    exact hbR
  -- ================= COLUMNS (the new content) =================
  set proj : Fin L → (Fin u → Y) := fun j i => S j (e i).val with hproj
  set Cols : Finset (Fin u → Y) := C'.image proj with hCols
  have hColsProv : ∀ c' ∈ Cols, ∃ j ∈ C', ∀ i : Fin u, c' i = S j (e i).val := by
    intro c' hc'
    rw [hCols, Finset.mem_image] at hc'
    obtain ⟨j, hj, rfl⟩ := hc'
    exact ⟨j, hj, fun i => rfl⟩
  -- Balancedness of the projected family (Fin u coordinates).
  have hSproj : IsBalancedFamily t (fun j i => S j (ecoord i)) ε :=
    hS.projection ecoord hecoord_inj
  have hLpos : 0 < L := hS.1
  have hLR : (0:ℝ) < (L:ℝ) := by exact_mod_cast hLpos
  set cY : ℕ := Fintype.card Y with hcY
  -- 1 + ε > 0
  have hεpos : (0:ℝ) < 1 + ε := by linarith
  -- ================= main column count =================
  -- Target threshold: ⌈(cY^u) * (y/(1+ε))⌉₊ ≤ Cols.card
  have hcolcard : ⌈((cY : ℝ) ^ u) * (y / (1 + ε))⌉₊ ≤ Cols.card := by
    -- Split on the sign of y.
    rcases le_or_gt y 0 with hy0 | hypos
    · -- y ≤ 0: the threshold is 0.
      have hle0 : ((cY : ℝ) ^ u) * (y / (1 + ε)) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos
        · positivity
        · exact div_nonpos_of_nonpos_of_nonneg hy0 (le_of_lt hεpos)
      have : ⌈((cY : ℝ) ^ u) * (y / (1 + ε))⌉₊ = 0 := by
        rw [Nat.ceil_eq_zero]; exact hle0
      rw [this]; exact Nat.zero_le _
    · -- y > 0.  Now C' is nonempty (from hcol, L>0), so Cols nonempty, Y inhabited.
      have hC'card_pos : (0:ℝ) < (C'.card : ℝ) := lt_of_lt_of_le (by positivity) hcol
      have hC'ne : C'.Nonempty := by
        rw [← Finset.card_pos]
        exact_mod_cast hC'card_pos
      obtain ⟨j0, hj0⟩ := hC'ne
      -- Y inhabited from proj j0 (u > 0).
      have hYne : Nonempty Y := ⟨proj j0 ⟨0, hu⟩⟩
      haveI : Nonempty Y := hYne
      have hcYpos : 0 < cY := by
        rw [hcY]; exact Fintype.card_pos
      have hcYR : (0:ℝ) < (cY : ℝ) := by exact_mod_cast hcYpos
      -- FIBER BOUND: every proj-fiber inside C' has real card ≤ (1+ε)*L/cY^u.
      -- univ : Finset (Fin u), card = u ≤ t.
      have hunivcard : (Finset.univ : Finset (Fin u)).card = u := by
        rw [Finset.card_univ, Fintype.card_fin]
      have hfiberbound : ∀ c0 : Fin u → Y,
          ((C'.filter (fun j => proj j = c0)).card : ℝ)
            ≤ (1 + ε) * (L:ℝ) / (cY:ℝ) ^ u := by
        intro c0
        -- Apply projected balancedness at J = univ, pattern c0.
        have hbal := hSproj.2 (Finset.univ : Finset (Fin u))
          (by rw [hunivcard]; exact hut) c0
        rw [hunivcard] at hbal
        -- From |filtercard/L - 1/cY^u| ≤ ε/cY^u, get filtercard ≤ (1+ε)L/cY^u.
        set Ffull : ℕ := (Finset.univ.filter
            (fun j : Fin L => ∀ γ ∈ (Finset.univ : Finset (Fin u)),
              S j (ecoord γ) = c0 γ)).card with hFfull
        have hcYuR : (0:ℝ) < (cY:ℝ) ^ u := by positivity
        -- upper bound on Ffull
        have habs := hbal
        rw [abs_le] at habs
        have hupper : (Ffull : ℝ) / (L:ℝ) ≤ 1 / (cY:ℝ) ^ u + ε / (cY:ℝ) ^ u := by
          have := habs.2
          rw [hFfull]
          linarith [this]
        have hFfull_le : (Ffull : ℝ) ≤ (1 + ε) * (L:ℝ) / (cY:ℝ) ^ u := by
          have hne : (cY:ℝ) ^ u ≠ 0 := ne_of_gt hcYuR
          -- multiply hupper by L > 0
          rw [div_le_iff₀ hLR] at hupper
          -- hupper : Ffull ≤ (1/cY^u + ε/cY^u) * L
          have hexp : ((1:ℝ) / (cY:ℝ) ^ u + ε / (cY:ℝ) ^ u) * (L:ℝ)
              = (1 + ε) * (L:ℝ) / (cY:ℝ) ^ u := by
            field_simp
          rw [hexp] at hupper
          exact hupper
        -- the C'-restricted fiber sits inside Ffull (C' ⊆ univ, predicate matches).
        have hsubfiber : (C'.filter (fun j => proj j = c0))
            ⊆ (Finset.univ.filter
              (fun j : Fin L => ∀ γ ∈ (Finset.univ : Finset (Fin u)),
                S j (ecoord γ) = c0 γ)) := by
          intro j hj
          rw [Finset.mem_filter] at hj ⊢
          refine ⟨Finset.mem_univ j, ?_⟩
          intro γ _
          have hpeq := hj.2
          have := congrFun hpeq γ
          rw [hproj] at this
          rw [hecoord]
          exact this
        have hcardle : (C'.filter (fun j => proj j = c0)).card ≤ Ffull := by
          rw [hFfull]; exact Finset.card_le_card hsubfiber
        calc ((C'.filter (fun j => proj j = c0)).card : ℝ)
            ≤ (Ffull : ℝ) := by exact_mod_cast hcardle
          _ ≤ (1 + ε) * (L:ℝ) / (cY:ℝ) ^ u := hFfull_le
      -- GLOBAL count: C'.card = Σ over Cols of fiber cards, each ≤ bound.
      -- C'.card = Σ_{c0 ∈ image proj C'} (fiber card)
      have hcYuR : (0:ℝ) < (cY:ℝ) ^ u := by positivity
      have hsumfib : (C'.card : ℝ)
          = ∑ c0 ∈ C'.image proj, ((C'.filter (fun j => proj j = c0)).card : ℝ) := by
        have hnat : C'.card = ∑ c0 ∈ C'.image proj, (C'.filter (fun j => proj j = c0)).card :=
          Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_image_of_mem proj (by assumption))
        rw [hnat]; push_cast; rfl
      -- each summand ≤ bound
      have hsumbound : (C'.card : ℝ)
          ≤ (Cols.card : ℝ) * ((1 + ε) * (L:ℝ) / (cY:ℝ) ^ u) := by
        rw [hsumfib]
        calc ∑ c0 ∈ C'.image proj, ((C'.filter (fun j => proj j = c0)).card : ℝ)
            ≤ ∑ _c0 ∈ C'.image proj, ((1 + ε) * (L:ℝ) / (cY:ℝ) ^ u) := by
              apply Finset.sum_le_sum
              intro c0 _
              exact hfiberbound c0
          _ = ((C'.image proj).card : ℝ) * ((1 + ε) * (L:ℝ) / (cY:ℝ) ^ u) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = (Cols.card : ℝ) * ((1 + ε) * (L:ℝ) / (cY:ℝ) ^ u) := by rw [hCols]
      -- Chain: y*L ≤ C'.card ≤ Cols.card * (1+ε)*L/cY^u
      -- ⟹ y*cY^u/(1+ε) ≤ Cols.card, i.e. cY^u * (y/(1+ε)) ≤ Cols.card.
      have hchain : y * (L:ℝ) ≤ (Cols.card : ℝ) * ((1 + ε) * (L:ℝ) / (cY:ℝ) ^ u) :=
        le_trans hcol hsumbound
      -- rearrange: from hchain, multiply by cY^u/((1+ε)*L) > 0.
      have hfinal : (cY:ℝ) ^ u * (y / (1 + ε)) ≤ (Cols.card : ℝ) := by
        have hne : (cY:ℝ) ^ u ≠ 0 := ne_of_gt hcYuR
        -- Clear the /cY^u in hchain: y*L*cY^u ≤ Cols.card*(1+ε)*L.
        have hchainR : (Cols.card : ℝ) * ((1 + ε) * (L:ℝ) / (cY:ℝ) ^ u)
            = (Cols.card : ℝ) * ((1 + ε) * (L:ℝ)) / (cY:ℝ) ^ u := by ring
        rw [hchainR, le_div_iff₀ hcYuR] at hchain
        -- hchain : y*L*cY^u ≤ Cols.card*(1+ε)*L
        -- goal: cY^u*(y/(1+ε)) ≤ Cols.card
        rw [← mul_div_assoc, div_le_iff₀ hεpos]
        -- goal: cY^u*y ≤ Cols.card*(1+ε)
        -- from hchain, divide by L>0:  cY^u*y ≤ Cols.card*(1+ε).
        have hstep : (cY:ℝ) ^ u * y * (L:ℝ) ≤ ((Cols.card : ℝ) * (1 + ε)) * (L:ℝ) := by
          nlinarith [hchain]
        exact le_of_mul_le_mul_right hstep hLR
      rw [Nat.ceil_le]
      exact hfinal
  -- ================= ASSEMBLE =================
  refine ⟨(Rows, Cols), ⟨?_, ?_⟩, ?_, ?_⟩
  · exact hRowsEq
  · exact hcolcard
  · exact hRowsProv
  · exact hColsProv

end NPCC
