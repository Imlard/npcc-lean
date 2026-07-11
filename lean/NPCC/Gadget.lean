import Mathlib
import NPCC.Scaffold
import NPCC.Stage1
import NPCC.VBP

/-! Scratch harness for `lem:C2FiberSurvival` (ledger `NPCC.C2_fiber_survival`,
NEW file `NPCC/Gadget.lean`). Balancedness of the Stage-2 family `C₂` bounds
every coordinate fibre within `(1 ± ε₂)|C₂|/|R₁|`; hence a `(1 − 8h₂)`-dense
(more precisely: strictly-larger-than-the-deletion-threshold) subset cannot
delete a fibre — every value of `R₁` survives in every coordinate.

Vehicle: `IsBalancedFamily` at `|J| = 1` (a coordinate fibre is the one-
coordinate pattern count), instantiated at the concrete Stage-2 family
`S2fam d` (whose alphabet is the ACTUAL `R₁ = Fin q₁ × Fin 1`, per the
rulings trap: the extract witness must retain the actual `R₁`). -/

namespace NPCC

open Finset

/-! ## Core counting: coordinate fibres of a balanced family (`|J| = 1`) -/

/-- The coordinate fibre `F_{β,r} = {j : S j β = r}` of an indexed family. -/
def coordFiber {Y : Type*} [DecidableEq Y] {q L : ℕ} (S : Fin L → Fin q → Y)
    (β : Fin q) (r : Y) : Finset (Fin L) :=
  Finset.univ.filter (fun j => S j β = r)

/-- Fibre two-sided bound from balancedness at a singleton coordinate set.
For a `(q,t)`-balanced family with `1 ≤ t` (so singletons are admissible) and
accuracy `ε`, every coordinate fibre `F_{β,r}` has
`(1−ε)/|Y| · L ≤ |F_{β,r}| ≤ (1+ε)/|Y| · L`. -/
theorem coordFiber_bounds {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (hS : IsBalancedFamily t S ε) (ht : 1 ≤ t) (β : Fin q) (r : Y) :
    (1 - ε) / (Fintype.card Y : ℝ) * (L : ℝ) ≤ ((coordFiber S β r).card : ℝ) ∧
      ((coordFiber S β r).card : ℝ) ≤ (1 + ε) / (Fintype.card Y : ℝ) * (L : ℝ) := by
  classical
  obtain ⟨hL, hbal⟩ := hS
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  -- Use the singleton J = {β}, pattern a := (fun _ => r).
  have hJcard : ({β} : Finset (Fin q)).card ≤ t := by
    simpa using ht
  have h := hbal {β} hJcard (fun _ => r)
  -- The filter event over J = {β} is exactly coordFiber S β r.
  have hevent : (Finset.univ.filter
      (fun j : Fin L => ∀ γ ∈ ({β} : Finset (Fin q)), S j γ = r))
      = coordFiber S β r := by
    unfold coordFiber
    apply Finset.filter_congr
    intro j _
    constructor
    · intro hj; exact hj β (Finset.mem_singleton_self β)
    · intro hj γ hγ; rw [Finset.mem_singleton] at hγ; subst hγ; exact hj
  rw [hevent] at h
  -- |J| = 1 so |Y|^{|J|} = |Y|.
  have hcardJ : ({β} : Finset (Fin q)).card = 1 := Finset.card_singleton β
  rw [hcardJ, pow_one] at h
  -- Extract the two sides of the absolute value bound.
  rw [abs_le] at h
  obtain ⟨hlo, hhi⟩ := h
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with hY0 | hYpos
  · -- |Y| = 0 is impossible: r : Y inhabits Y.
    exact absurd (Fintype.card_pos_iff.mpr ⟨r⟩) (by omega)
  · have hcY : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hYpos
    constructor
    · -- lower: from hlo, |F|/L ≥ 1/|Y| - ε/|Y| = (1-ε)/|Y|.
      have hstep : (1 - ε) / (Fintype.card Y : ℝ)
          ≤ ((coordFiber S β r).card : ℝ) / (L : ℝ) := by
        have : (1 - ε) / (Fintype.card Y : ℝ)
            = 1 / (Fintype.card Y : ℝ) - ε / (Fintype.card Y : ℝ) := by ring
        rw [this]; linarith
      calc (1 - ε) / (Fintype.card Y : ℝ) * (L : ℝ)
          ≤ ((coordFiber S β r).card : ℝ) / (L : ℝ) * (L : ℝ) := by
            apply mul_le_mul_of_nonneg_right hstep (le_of_lt hLR)
        _ = ((coordFiber S β r).card : ℝ) := by field_simp
    · -- upper: from hhi, |F|/L ≤ 1/|Y| + ε/|Y| = (1+ε)/|Y|.
      have hstep : ((coordFiber S β r).card : ℝ) / (L : ℝ)
          ≤ (1 + ε) / (Fintype.card Y : ℝ) := by
        have : (1 + ε) / (Fintype.card Y : ℝ)
            = 1 / (Fintype.card Y : ℝ) + ε / (Fintype.card Y : ℝ) := by ring
        rw [this]; linarith
      calc ((coordFiber S β r).card : ℝ)
          = ((coordFiber S β r).card : ℝ) / (L : ℝ) * (L : ℝ) := by field_simp
        _ ≤ (1 + ε) / (Fintype.card Y : ℝ) * (L : ℝ) := by
            apply mul_le_mul_of_nonneg_right hstep (le_of_lt hLR)

/-! ## Fibre survival: a dense subset hits every value in every coordinate -/

/-- Fibre survival (core form). If `S ⊆ univ` (a subset of the family indices)
is larger than `(1 − (1−ε)/|Y|)·L`, then for every coordinate `β` the set of
values `{S j β : j ∈ S}` is ALL of `Y`: no value's fibre can be entirely
deleted, because each fibre has `> (1−ε)/|Y|·L` elements and the complement of
`𝒮` has fewer than that many. -/
theorem fiber_survival {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (hS : IsBalancedFamily t S ε) (ht : 1 ≤ t)
    (𝒮 : Finset (Fin L))
    (hbig : (1 - (1 - ε) / (Fintype.card Y : ℝ)) * (L : ℝ) < (𝒮.card : ℝ))
    (β : Fin q) (r : Y) :
    ∃ j ∈ 𝒮, S j β = r := by
  classical
  by_contra hcon
  push Not at hcon
  -- Then 𝒮 avoids the fibre F_{β,r}; so 𝒮 ⊆ univ \ F, giving |𝒮| ≤ L - |F|.
  have hdisj : Disjoint 𝒮 (coordFiber S β r) := by
    rw [Finset.disjoint_left]
    intro j hj hjF
    unfold coordFiber at hjF
    exact hcon j hj (Finset.mem_filter.mp hjF).2
  have hsub : 𝒮 ⊆ Finset.univ \ coordFiber S β r := by
    intro j hj
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ j, ?_⟩
    intro hjF
    exact (Finset.disjoint_left.mp hdisj) hj hjF
  have hcardle : 𝒮.card ≤ L - (coordFiber S β r).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin] at this
  -- Numeric contradiction: |𝒮| ≤ L - |F| but |F| ≥ (1-ε)/|Y| · L.
  have hFlow := (coordFiber_bounds hS ht β r).1
  have hFle : (coordFiber S β r).card ≤ L := by
    have := Finset.card_le_card (Finset.subset_univ (coordFiber S β r))
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hcardR : (𝒮.card : ℝ) ≤ (L : ℝ) - ((coordFiber S β r).card : ℝ) := by
    have h1 : (𝒮.card : ℝ) ≤ ((L - (coordFiber S β r).card : ℕ) : ℝ) := by
      exact_mod_cast hcardle
    rwa [Nat.cast_sub hFle] at h1
  -- Combine: |𝒮| ≤ L - |F| ≤ L - (1-ε)/|Y|·L = (1 - (1-ε)/|Y|)·L < |𝒮|.
  have hchain : (𝒮.card : ℝ) ≤ (1 - (1 - ε) / (Fintype.card Y : ℝ)) * (L : ℝ) := by
    have : (L : ℝ) - ((coordFiber S β r).card : ℝ)
        ≤ (1 - (1 - ε) / (Fintype.card Y : ℝ)) * (L : ℝ) := by
      have hexp : (1 - (1 - ε) / (Fintype.card Y : ℝ)) * (L : ℝ)
          = (L : ℝ) - (1 - ε) / (Fintype.card Y : ℝ) * (L : ℝ) := by ring
      rw [hexp]; linarith
    linarith
  linarith

/-- Fibre survival, value-cover form: under the same density hypothesis, for
every coordinate `β` the value set `{S j β : j ∈ 𝒮}` (as a `Finset Y`) is the
whole alphabet. This is the paper's `{c_β : c ∈ 𝒮} = R₁`. -/
theorem fiber_value_cover {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (hS : IsBalancedFamily t S ε) (ht : 1 ≤ t)
    (𝒮 : Finset (Fin L))
    (hbig : (1 - (1 - ε) / (Fintype.card Y : ℝ)) * (L : ℝ) < (𝒮.card : ℝ))
    (β : Fin q) :
    (𝒮.image (fun j => S j β)) = (Finset.univ : Finset Y) := by
  apply Finset.eq_univ_of_forall
  intro r
  obtain ⟨j, hj𝒮, hjr⟩ := fiber_survival hS ht 𝒮 hbig β r
  rw [Finset.mem_image]
  exact ⟨j, hj𝒮, hjr⟩

/-! ## Concrete instantiation at the Stage-2 family `C₂ = S_{q₂,I₂}(R₁)` -/

-- CLAIM-BEGIN lem:C2FiberSurvival
/-- Paper `lem:C2FiberSurvival` (arXiv:2508.05597, fibre survival after
Stage-3 row loss) at the concrete Stage-2 objects. `C₂ := S2fam d`
(alphabet `R₁ = Fin q₁ × Fin 1`, retained EXACTLY per the rulings trap:
the witness ranges over the ACTUAL `R₁`), `ε₂ := ε_{q₂,I₂} = epsQT q₂ t₂`,
`|C₂| = L₂`, `|R₁| = q₁`.  Balancedness of `C₂` bounds every coordinate fibre
`F_{β,r} = {c ∈ C₂ : c_β = r}` within `(1 ± ε₂)|C₂|/|R₁|`; consequently any
index subset `𝒮 ⊆ C₂` with `|𝒮| > (1 − (1−ε₂)/|R₁|)|C₂|` has, in every
coordinate `β`, value set `{c_β : c ∈ 𝒮}` equal to all of `R₁` — a
`(1−8h₂)`-dense subset (whose size clears this threshold under the audited
parameter regime) cannot delete a fibre. -/
theorem C2_fiber_survival (d : ℕ)
    (h : Params.t2 d ≤ Params.q2 d) (hq1 : 1 ≤ Params.q1 d)
    (𝒮 : Finset (Fin (L2 d)))
    (hbig : (1 - (1 - epsQT (Params.q2 d) (Params.t2 d))
              / (Fintype.card (Fin (Params.q1 d) × Fin 1) : ℝ)) * (L2 d : ℝ)
            < (𝒮.card : ℝ))
    (β : Fin (Params.q2 d)) :
    -- fibre two-sided bound
    (∀ r : Fin (Params.q1 d) × Fin 1,
      (1 - epsQT (Params.q2 d) (Params.t2 d))
          / (Fintype.card (Fin (Params.q1 d) × Fin 1) : ℝ) * (L2 d : ℝ)
        ≤ ((coordFiber (S2fam d) β r).card : ℝ) ∧
      ((coordFiber (S2fam d) β r).card : ℝ)
        ≤ (1 + epsQT (Params.q2 d) (Params.t2 d))
            / (Fintype.card (Fin (Params.q1 d) × Fin 1) : ℝ) * (L2 d : ℝ)) ∧
    -- value cover: {c_β : c ∈ 𝒮} = R₁
    (𝒮.image (fun j => S2fam d j β)) = (Finset.univ : Finset (Fin (Params.q1 d) × Fin 1)) :=
-- CLAIM-END lem:C2FiberSurvival
  by
  have hbal : IsBalancedFamily (Params.t2 d) (S2fam d)
      (epsQT (Params.q2 d) (Params.t2 d)) := S2fam_balanced d h hq1
  have ht : 1 ≤ Params.t2 d := Params.t2_pos d
  refine ⟨fun r => coordFiber_bounds hbal ht β r, ?_⟩
  exact fiber_value_cover hbal ht 𝒮 hbig β

open Workspace.Types.Interlace
open Workspace.Types.CommComplexity

/-! # `lem:MFourDiagonalCopy` — the canonical diagonal copy `X̂_{p,α}`

Paper `lem:MFourDiagonalCopy` (arXiv:2508.05597, "Canonical diagonal copy").
For a fixed bin `p`, the tail-compatible fully-diagonal columns
`X̂_{p,α} = { (tail(γ), ((α,γ),(α,γ),(α,γ),(α,γ))) : γ ∈ C₁ } ⊆ X_{p,α}` and
`D̂_p = ⋃_α X̂_{p,α}`; after identifying each such column with the Stage-2
column `(α,γ) ∈ R₂`, the restriction of `M₄` to the template rows `{p}×C₂`
and the columns `D̂_p` is EXACTLY `M₂ᵀ`.

Design authority: the Stage-4 scaffold (`NPCC.M4`, `NPCC.compatCol`,
`NPCC.diagEmbed`) anticipates this lemma; the diagonal copy is
`compatCol d p α (fun _ => γ)` — a diagonal column of dimension `α` with the
CONSTANT Stage-1 tuple `γ` (all four `R₂` entries equal to `(α,γ)`) and gadget
coordinate pinned to the bin-`p` tail pattern `tail(γ)`.  On the template
rows `M₄` copies `M₃`, and the `p`-th Stage-3 branch of `M₃` reads only the
`p`-th component `(α,γ)`, giving `M₃((p,c),(…)) = M₂ᵀ(c,(α,γ)) = M₂((α,γ),c)`
— a pure definitional computation over the transposed-interlace `M₃`. -/

/-- The canonical diagonal column `ĵ_{α,γ} ∈ X̂_{p,α}` (independent of the bin
`p`): the diagonal Stage-4 column of dimension `α` with the constant Stage-1
tuple `γ`, gadget coordinate pinned to `tail(γ)`.  Equals
`(tail γ, fun _ => (α,γ))`. -/
noncomputable def diagCopyCol (d : ℕ) (α : Fin (Params.q2 d)) (γ : C1 d) :
    C4 d :=
  compatCol d 0 α (fun _ => γ)

/-- Companion: the diagonal copy column in explicit coordinates. -/
theorem diagCopyCol_eq (d : ℕ) (α : Fin (Params.q2 d)) (γ : C1 d) :
    diagCopyCol d α γ = (tail d γ, fun _ => (α, γ)) := rfl

/-- Companion: `diagCopyCol` is injective in the Stage-1 column `γ` (so the
family `X̂_{p,α}` has one column per `γ ∈ C₁`). -/
theorem diagCopyCol_injective (d : ℕ) (α : Fin (Params.q2 d)) :
    Function.Injective (diagCopyCol d α) := by
  intro γ γ' h
  have h2 := congrArg (fun z : C4 d => (z.2 0).2) h
  simpa [diagCopyCol_eq] using h2

/-- Canonical diagonal copy (core pointwise identity): on the template row
`(p,c)` and the canonical diagonal column `ĵ_{α,γ}`, `M₄` equals
`M₂ᵀ(c,(α,γ)) = M₂((α,γ),c)`.  Pure `rfl` computation:
`M₄ template → M₃ → interlaceFun (M₂ᵀ) 4 → M₂`. -/
theorem M4_diagonal_copy_apply (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4) (c : C2 d)
    (α : Fin (Params.q2 d)) (γ : C1 d) :
    M4 d v (Sum.inl (p, c)) (diagCopyCol d α γ) = M2 d (α, γ) c := rfl

-- CLAIM-BEGIN lem:MFourDiagonalCopy
/-- Paper `lem:MFourDiagonalCopy` (arXiv:2508.05597, Canonical diagonal copy),
game form.  Identifying each canonical diagonal column `ĵ_{α,γ}` of `X̂_{p,α}`
with the Stage-2 column `(α,γ) ∈ [q₂]×C₁ = R₂`, the restriction of `M₄` to the
template rows `{p}×C₂` (indexed by `c ∈ C₂`) and the columns
`D̂_p = ⋃_α X̂_{p,α}` (indexed by `r = (α,γ) ∈ R₂`) is EXACTLY the transpose
`M₂ᵀ`, i.e. `(c, r) ↦ M₂(r, c)`.  Holds for every attached vector family `v`
(the template rows ignore the vector rows and the gadget coordinate). -/
theorem M4_diagonal_copy (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4) :
    (fun (c : C2 d) (r : R2 d) =>
      M4 d v (Sum.inl (p, c)) (diagCopyCol d r.1 r.2))
      = (fun (c : C2 d) (r : R2 d) => M2 d r c) :=
-- CLAIM-END lem:MFourDiagonalCopy
  by
  funext c r
  obtain ⟨α, γ⟩ := r
  exact M4_diagonal_copy_apply d v p c α γ

/-! # `lem:compat-slice-retention` — the shifted compatibility slices

Paper `lem:compat-slice-retention` (arXiv:2508.05597).  Fix a bin `p` and a
dimension `α`.  The diagonal outer-block family
`D_{p,α} = { (k,(j₁,…,j₄)) ∈ C₄ : jₘ = (α,γₘ) ∈ {α}×C₁ ∀ m }` is the disjoint
union of the `2⁵` EQUAL shifted compatibility slices
`X^{(s)}_{p,α} = { (k,·) ∈ D_{p,α} : k = tail(γ_p) ⊕ s }`.  Consequently
(pigeonhole) a `(1−η)`-dense subset retains `(1−2⁵η)`-density in some slice;
and replacing `k` by `k ⊕ s` is a column permutation of the 5-row local
gadget, so the shift-`s` subgame is isomorphic to the shift-`0` subgame.

Representation details used by the proof:
* The tail-shift acts on the explicit `[2⁵]` gadget factor with no
  AGHP shift-closure assumption — `shiftK` is the bit-vector XOR transported
  through the SAME `finFunctionFinEquiv` packing that `localGadget` uses, so
  the "column permutation" claim is literally the gadget-column reindexing
  (`localGadget_shiftPerm`), not an appeal to any family symmetry.
* `D_{p,α}` is modelled as a tagged family (via `dCol = diagEmbed ∘ section` on the tagged
  index type `DIdx = [2⁵] × ([4]→C₁)` at fixed dimension `α`), never an
  untyped union; `dCol` and `diagEmbed` are injective, so the counting is
  honest set-cardinality.
* AGHP families are transported, never re-chosen: nothing here selects a new
  balanced family — `D_{p,α}` and the slices are cut out of the fixed
  Stage-1/Stage-4 objects by the deterministic shift read-off `sliceIdx`. -/

/-- Bit-vector XOR shift on the `[2⁵]` gadget coordinate: transport pointwise
`Fin 2` addition (= XOR) through the SAME `finFunctionFinEquiv` packing used
by `localGadget`.  Paper `k ⊕ s`; acts on the EXPLICIT `[2⁵]` factor. -/
noncomputable def shiftK (k s : Fin (2 ^ 5)) : Fin (2 ^ 5) :=
  finFunctionFinEquiv
    (fun i => finFunctionFinEquiv.symm k i + finFunctionFinEquiv.symm s i)

/-- For a fixed shift `s`, `k ↦ k ⊕ s` is a bijection of `[2⁵]` (adding a
fixed bit-vector is a permutation). -/
theorem shiftK_bijective (s : Fin (2 ^ 5)) :
    Function.Bijective (fun k => shiftK k s) := by
  classical
  constructor
  · intro k k' h
    unfold shiftK at h
    have h2 := finFunctionFinEquiv.injective h
    have : finFunctionFinEquiv.symm k = finFunctionFinEquiv.symm k' := by
      funext i
      have := congrFun h2 i
      simpa using add_right_cancel this
    exact finFunctionFinEquiv.symm.injective this
  · intro k
    refine ⟨finFunctionFinEquiv
      (fun i => finFunctionFinEquiv.symm k i - finFunctionFinEquiv.symm s i), ?_⟩
    unfold shiftK
    apply finFunctionFinEquiv.symm.injective
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    funext i
    simp

/-- The index type of the diagonal outer-block family `D_{p,α}`: a gadget
coordinate `k ∈ [2⁵]` together with a Stage-1 tuple `γ : [4] → C₁`.  The
realised column is `diagEmbed d (α,k,γ)`; `diagEmbed` is injective, so this
type is in bijection with `D_{p,α} ⊆ C₄`. -/
abbrev DIdx (d : ℕ) : Type := Fin (2 ^ 5) × (Fin 4 → C1 d)

/-- The realised diagonal column of an index at dimension `α`. -/
noncomputable def dCol (d : ℕ) (α : Fin (Params.q2 d)) (x : DIdx d) : C4 d :=
  diagEmbed d (α, x.1, x.2)

/-- The slice index of a diagonal column: the 5-bit shift `s = k ⊖ tail(γ_p)`
with `k = tail(γ_p) ⊕ s`.  Reads the shift off the column deterministically
(no choice), making the `2⁵` slices a genuine partition. -/
noncomputable def sliceIdx (d : ℕ) (p : Fin 4) (x : DIdx d) : Fin (2 ^ 5) :=
  finFunctionFinEquiv
    (fun i => finFunctionFinEquiv.symm x.1 i
      - finFunctionFinEquiv.symm (tail d (x.2 p)) i)

/-- `sliceIdx` recovers `k` from `tail(γ_p)`: `k = tail(γ_p) ⊕ sliceIdx`. -/
theorem shiftK_tail_sliceIdx (d : ℕ) (p : Fin 4) (x : DIdx d) :
    shiftK (tail d (x.2 p)) (sliceIdx d p x) = x.1 := by
  unfold shiftK sliceIdx
  apply finFunctionFinEquiv.symm.injective
  rw [Equiv.symm_apply_apply]
  funext i
  rw [Equiv.symm_apply_apply]
  simp

/-- The diagonal outer-block family `D_{p,α}` as a `Finset (C₄ d)`: the
(injective) image of ALL diagonal indices under `dCol`.  Independent of `p`. -/
noncomputable def Dfam (d : ℕ) (α : Fin (Params.q2 d)) : Finset (C4 d) :=
  Finset.univ.image (dCol d α)

/-- The `s`-th shifted compatibility slice `X^{(s)}_{p,α}`: the diagonal
columns with `sliceIdx = s`, i.e. gadget coordinate `tail(γ_p) ⊕ s`. -/
noncomputable def sliceX (d : ℕ) (p : Fin 4) (α : Fin (Params.q2 d))
    (s : Fin (2 ^ 5)) : Finset (C4 d) :=
  (Finset.univ.filter (fun x : DIdx d => sliceIdx d p x = s)).image (dCol d α)

/-- The "shift-off" reparametrisation `x ↦ (sliceIdx x, γ)` is an equivalence
`DIdx ≃ [2⁵] × ([4] → C₁)`; the inverse rebuilds `k = tail(γ_p) ⊕ s`.  Under
it, the `sliceIdx = s` fibre is exactly `{s} × (tuples)`. -/
noncomputable def shiftEquiv (d : ℕ) (p : Fin 4) :
    DIdx d ≃ Fin (2 ^ 5) × (Fin 4 → C1 d) where
  toFun x := (sliceIdx d p x, x.2)
  invFun sγ := (shiftK (tail d (sγ.2 p)) sγ.1, sγ.2)
  left_inv x := by
    apply Prod.ext
    · exact shiftK_tail_sliceIdx d p x
    · rfl
  right_inv sγ := by
    obtain ⟨s, γ⟩ := sγ
    apply Prod.ext
    · show sliceIdx d p (shiftK (tail d (γ p)) s, γ) = s
      unfold sliceIdx shiftK
      apply finFunctionFinEquiv.symm.injective
      rw [Equiv.symm_apply_apply]
      funext i
      simp only [Equiv.symm_apply_apply]
      show finFunctionFinEquiv.symm (tail d (γ p)) i
          + finFunctionFinEquiv.symm s i - finFunctionFinEquiv.symm (tail d (γ p)) i
        = finFunctionFinEquiv.symm s i
      abel
    · rfl

/-- `dCol d α` is injective (it is `diagEmbed` precomposed with a section). -/
theorem dCol_injective (d : ℕ) (α : Fin (Params.q2 d)) :
    Function.Injective (dCol d α) := by
  intro x y h
  unfold dCol at h
  have := diagEmbed_injective d h
  have h1 : x.1 = y.1 := congrArg (fun z : DiagColumns d => z.2.1) this
  have h2 : x.2 = y.2 := congrArg (fun z : DiagColumns d => z.2.2) this
  exact Prod.ext h1 h2

/-- The index-level slice fibre `{x : sliceIdx x = s}`. -/
noncomputable def sliceIdxFib (d : ℕ) (p : Fin 4) (s : Fin (2 ^ 5)) :
    Finset (DIdx d) :=
  Finset.univ.filter (fun x : DIdx d => sliceIdx d p x = s)

/-- Every index-level slice fibre has the same cardinality `(L₁)⁴` (via the
shift reparametrisation `shiftEquiv`, sending it bijectively onto the tuples
`[4] → C₁`). -/
theorem sliceIdxFib_card (d : ℕ) (p : Fin 4) (s : Fin (2 ^ 5)) :
    (sliceIdxFib d p s).card = (L1 d) ^ 4 := by
  classical
  have himg : (sliceIdxFib d p s).image (shiftEquiv d p)
      = ({s} : Finset (Fin (2 ^ 5))) ×ˢ (Finset.univ : Finset (Fin 4 → C1 d)) := by
    ext sγ
    simp only [Finset.mem_image, sliceIdxFib, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, trivial⟩
    · rintro ⟨hs, -⟩
      refine ⟨(shiftEquiv d p).symm sγ, ?_, by rw [Equiv.apply_symm_apply]⟩
      have : (shiftEquiv d p ((shiftEquiv d p).symm sγ)).1 = s := by
        rw [Equiv.apply_symm_apply]; exact hs
      simpa [shiftEquiv] using this
  have hcard := congrArg Finset.card himg
  rw [Finset.card_image_of_injective _ (shiftEquiv d p).injective] at hcard
  rw [hcard, Finset.card_product, Finset.card_singleton, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, one_mul]

/-- `sliceX` card equals the index-fibre card (image under injective `dCol`). -/
theorem sliceX_card (d : ℕ) (p : Fin 4) (α : Fin (Params.q2 d))
    (s : Fin (2 ^ 5)) :
    (sliceX d p α s).card = (L1 d) ^ 4 := by
  unfold sliceX
  rw [Finset.card_image_of_injective _ (dCol_injective d α)]
  exact sliceIdxFib_card d p s

/-- The `2⁵` slices are pairwise disjoint. -/
theorem sliceX_disjoint (d : ℕ) (p : Fin 4) (α : Fin (Params.q2 d))
    {s s' : Fin (2 ^ 5)} (hss : s ≠ s') :
    Disjoint (sliceX d p α s) (sliceX d p α s') := by
  classical
  rw [Finset.disjoint_left]
  rintro c hc hc'
  unfold sliceX at hc hc'
  rw [Finset.mem_image] at hc hc'
  obtain ⟨x, hx, hxc⟩ := hc
  obtain ⟨y, hy, hyc⟩ := hc'
  rw [Finset.mem_filter] at hx hy
  have hxy : x = y := dCol_injective d α (hxc.trans hyc.symm)
  subst hxy
  exact hss (hx.2.symm.trans hy.2)

/-- The `2⁵` slices cover `D_{p,α}`. -/
theorem Dfam_eq_biUnion (d : ℕ) (p : Fin 4) (α : Fin (Params.q2 d)) :
    Dfam d α = (Finset.univ : Finset (Fin (2 ^ 5))).biUnion (sliceX d p α) := by
  classical
  ext c
  simp only [Dfam, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and,
    sliceX, Finset.mem_filter]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨sliceIdx d p x, x, rfl, rfl⟩
  · rintro ⟨s, x, -, rfl⟩
    exact ⟨x, rfl⟩

/-- `|D_{p,α}| = 2⁵ · (L₁)⁴` — all slices equal, summed. -/
theorem Dfam_card (d : ℕ) (p : Fin 4) (α : Fin (Params.q2 d)) :
    (Dfam d α).card = 2 ^ 5 * (L1 d) ^ 4 := by
  classical
  rw [Dfam_eq_biUnion d p α,
    Finset.card_biUnion (fun s _ s' _ hss => sliceX_disjoint d p α hss)]
  rw [Finset.sum_congr rfl (fun s _ => sliceX_card d p α s)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

set_option maxHeartbeats 1600000 in
/-- Density-retention pigeonhole. If `C ⊆ D_{p,α}` is `(1−η)`-dense in
`D_{p,α}`, then some shift `s` retains `(1−2⁵η)`-density inside its slice
`X^{(s)}_{p,α}`. -/
theorem sliceX_retention (d : ℕ) (p : Fin 4) (α : Fin (Params.q2 d))
    {η : ℝ} (hη : 0 ≤ η) (C : Finset (C4 d)) (hCsub : C ⊆ Dfam d α)
    (hCdense : (1 - η) * ((Dfam d α).card : ℝ) ≤ (C.card : ℝ)) :
    ∃ s : Fin (2 ^ 5),
      (1 - 2 ^ 5 * η) * ((sliceX d p α s).card : ℝ)
        ≤ ((C ∩ sliceX d p α s).card : ℝ) := by
  classical
  by_contra hcon
  push Not at hcon
  -- `C` splits over the slices (as `C ⊆ Dfam = ⨆ sliceX`).
  have hCsplit : C.card = ∑ s : Fin (2 ^ 5), (C ∩ sliceX d p α s).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext c
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
      constructor
      · intro hcC
        have hcD : c ∈ Dfam d α := hCsub hcC
        rw [Dfam_eq_biUnion d p α, Finset.mem_biUnion] at hcD
        obtain ⟨s, -, hcs⟩ := hcD
        exact ⟨s, hcC, hcs⟩
      · rintro ⟨s, hcC, -⟩; exact hcC
    · intro s _ s' _ hss
      exact Finset.disjoint_left.mpr (fun a ha ha' =>
        (Finset.disjoint_left.mp (sliceX_disjoint d p α hss))
          (Finset.mem_of_mem_inter_right ha) (Finset.mem_of_mem_inter_right ha'))
  -- Abstract the common slice size `L := (L₁)⁴` as an opaque nat `Lnat`.
  obtain ⟨Lnat, hLnat⟩ : ∃ N : ℕ, (L1 d) ^ 4 = N := ⟨(L1 d) ^ 4, rfl⟩
  set Lr : ℝ := (Lnat : ℝ) with hLr
  have hLrnn : (0 : ℝ) ≤ Lr := Nat.cast_nonneg _
  have hLs : ∀ s : Fin (2 ^ 5), ((sliceX d p α s).card : ℝ) = Lr := by
    intro s; rw [sliceX_card, hLnat, hLr]
  have hDcard : ((Dfam d α).card : ℝ) = ((2 ^ 5 : ℕ) : ℝ) * Lr := by
    rw [Dfam_card d p α, hLnat, Nat.cast_mul, hLr]
  -- Sum bound: every slice has < (1−2⁵η)·Lr, so total < 2⁵(1−2⁵η)·Lr.
  have hsumlt : (C.card : ℝ) < ((2 ^ 5 : ℕ) : ℝ) * ((1 - 2 ^ 5 * η) * Lr) := by
    have hsplit : (C.card : ℝ)
        = ∑ s : Fin (2 ^ 5), ((C ∩ sliceX d p α s).card : ℝ) := by
      rw [hCsplit, Nat.cast_sum]
    have hlt : (C.card : ℝ)
        < ∑ _s : Fin (2 ^ 5), (1 - 2 ^ 5 * η) * Lr := by
      rw [hsplit]
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro s _
      have := hcon s
      rwa [hLs s] at this
    rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  -- Combine with the density hypothesis: (1−η)|D| ≤ |C| < (1−2⁵η)|D| ≤ (1−η)|D|.
  rw [hDcard] at hCdense
  have hc : ((2 ^ 5 : ℕ) : ℝ) = 32 := by norm_num
  rw [hc] at hCdense hsumlt
  have hmono : 32 * ((1 - 2 ^ 5 * η) * Lr) ≤ 32 * ((1 - η) * Lr) := by
    have h32 : (2 ^ 5 : ℝ) = 32 := by norm_num
    rw [h32]
    have hstep : (1 - 32 * η) * Lr ≤ (1 - η) * Lr :=
      mul_le_mul_of_nonneg_right (by linarith) hLrnn
    linarith
  have h1 : (1 - η) * (32 * Lr) = 32 * ((1 - η) * Lr) := by ring
  rw [h1] at hCdense
  linarith [hCdense, hsumlt, hmono]

/-- Shift isomorphism (column-permutation form). For each shift `s`, the map
`k ↦ k ⊕ s` is a permutation (`Equiv.Perm`) of the `[2⁵]` gadget columns. -/
noncomputable def shiftPerm (s : Fin (2 ^ 5)) : Equiv.Perm (Fin (2 ^ 5)) :=
  Equiv.ofBijective (fun k => shiftK k s) (shiftK_bijective s)

/-- The shift is a genuine column permutation of the 5-row local gadget: the
gadget on the shifted column equals the gadget reindexed by `shiftPerm s`.
This is the "subgame on `X^{(s)}` ≅ subgame on `X^{(0)}`" content. -/
theorem localGadget_shiftPerm (slot : Fin 5) (s k : Fin (2 ^ 5)) :
    localGadget slot (shiftPerm s k) = localGadget slot (shiftK k s) := rfl

-- CLAIM-BEGIN lem:compat-slice-retention
/-- Paper `lem:compat-slice-retention` (arXiv:2508.05597), packaged.  Fix a
bin `p` and a dimension `α`.  The diagonal outer-block family `D_{p,α}`
(`Dfam`, independent of `p`) is the disjoint union of the `2⁵` EQUAL shifted
compatibility slices `X^{(s)}_{p,α}` (`sliceX`).  Hence: (i) equal-cardinality
disjoint cover, (ii) density-retention pigeonhole — a `(1−η)`-dense subset
keeps `(1−2⁵η)`-density in some slice, and (iii) the shift `k ↦ k ⊕ s` is a
column permutation of the 5-row local gadget, so the shift-`s` subgame is
isomorphic to the shift-`0` subgame. -/
theorem compat_slice_retention (d : ℕ) (p : Fin 4) (α : Fin (Params.q2 d)) :
    (Dfam d α = (Finset.univ : Finset (Fin (2 ^ 5))).biUnion (sliceX d p α)) ∧
    (∀ s s' : Fin (2 ^ 5), s ≠ s' →
      Disjoint (sliceX d p α s) (sliceX d p α s')) ∧
    (∀ s : Fin (2 ^ 5), (sliceX d p α s).card = (L1 d) ^ 4) ∧
    (Dfam d α).card = 2 ^ 5 * (L1 d) ^ 4 ∧
    (∀ {η : ℝ}, 0 ≤ η → ∀ C : Finset (C4 d), C ⊆ Dfam d α →
      (1 - η) * ((Dfam d α).card : ℝ) ≤ (C.card : ℝ) →
      ∃ s : Fin (2 ^ 5),
        (1 - 2 ^ 5 * η) * ((sliceX d p α s).card : ℝ)
          ≤ ((C ∩ sliceX d p α s).card : ℝ)) ∧
    (∀ s : Fin (2 ^ 5), Function.Bijective (fun k => shiftK k s)) ∧
    (∀ (slot : Fin 5) (s k : Fin (2 ^ 5)),
      localGadget slot (shiftPerm s k) = localGadget slot (shiftK k s)) :=
-- CLAIM-END lem:compat-slice-retention
  by
  refine ⟨Dfam_eq_biUnion d p α, ?_, sliceX_card d p α, Dfam_card d p α,
    ?_, shiftK_bijective, localGadget_shiftPerm⟩
  · intro s s' hss; exact sliceX_disjoint d p α hss
  · intro η hη C hCsub hCdense; exact sliceX_retention d p α hη C hCsub hCdense

/-! # `lem:M1PlusVectorsIsInterlace` and
`cor:M1PlusVectorsCanonicalDense`

The formal vehicle below is the canonical-transversal form required by the
Stage-4 audit.  The full branch may contain duplicate vector rows and duplicate
compatibility columns; lower bounds are transported through the subgame that
keeps all active vector rows, at most one inactive vector row, and one canonical
diagonal column for each Stage-1 family index.
-/

/-- The canonical row-coordinate set for the local Stage-1 game: the first
`q₁` template coordinates, plus the vector-row transversal at `α`. -/
abbrev M1PlusOuter (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) (α : Fin (Params.q2 d))
    (B : Finset (Fin n)) : Type :=
  Fin (Params.q1 d) ⊕ {i // i ∈ transversalAt v α B}

/-- The canonical diagonal block `X̂_{p,α}`, as a finset of Stage-4 columns
(independent of `p` in the current encoding). -/
noncomputable def diagCopySet (d : ℕ) (α : Fin (Params.q2 d)) : Finset (C4 d) :=
  Finset.univ.image (diagCopyCol d α)

/-- Pull a subset of the canonical diagonal block back to Stage-1 family
indices. -/
noncomputable def diagPullback (d : ℕ) (α : Fin (Params.q2 d))
    (Y : Finset (C4 d)) : Finset (C1 d) :=
  Finset.univ.filter (fun γ => diagCopyCol d α γ ∈ Y)

theorem diagCopySet_card (d : ℕ) (α : Fin (Params.q2 d)) :
    (diagCopySet d α).card = L1 d := by
  classical
  unfold diagCopySet
  rw [Finset.card_image_of_injective _ (diagCopyCol_injective d α),
    Finset.card_univ, Fintype.card_fin]

theorem diagPullback_image_eq (d : ℕ) (α : Fin (Params.q2 d))
    {Y : Finset (C4 d)} (hY : Y ⊆ diagCopySet d α) :
    (diagPullback d α Y).image (diagCopyCol d α) = Y := by
  classical
  ext c
  constructor
  · intro hc
    rw [Finset.mem_image] at hc
    rcases hc with ⟨γ, hγ, rfl⟩
    exact (Finset.mem_filter.mp hγ).2
  · intro hc
    have hcX := hY hc
    unfold diagCopySet at hcX
    rw [Finset.mem_image] at hcX
    rcases hcX with ⟨γ, -, rfl⟩
    rw [Finset.mem_image]
    exact ⟨γ, Finset.mem_filter.mpr ⟨Finset.mem_univ γ, hc⟩, rfl⟩

theorem diagPullback_card (d : ℕ) (α : Fin (Params.q2 d))
    {Y : Finset (C4 d)} (hY : Y ⊆ diagCopySet d α) :
    (diagPullback d α Y).card = Y.card := by
  classical
  have h := congrArg Finset.card (diagPullback_image_eq d α hY)
  rw [Finset.card_image_of_injective _ (diagCopyCol_injective d α)] at h
  exact h

/-- Balancedness of the Stage-2 family supplies a representative column-family
index for any desired Stage-1 row at a fixed dimension. -/
theorem S2fam_coord_surj (d : ℕ)
    (h₂ : Params.t2 d ≤ Params.q2 d) (hq1 : 1 ≤ Params.q1 d)
    (α : Fin (Params.q2 d)) (a : R1 d) :
    ∃ c : C2 d, S2fam d c α = a := by
  classical
  have hbal : IsBalancedFamily (Params.t2 d) (S2fam d)
      (epsQT (Params.q2 d) (Params.t2 d)) :=
    S2fam_balanced d h₂ hq1
  have hε : epsQT (Params.q2 d) (Params.t2 d) < 1 :=
    epsQT_lt_one (Params.q2_pos d) (Params.t2_pos d)
  have hJ : ({α} : Finset (Fin (Params.q2 d))).card ≤ Params.t2 d := by
    simpa using (Params.t2_pos d)
  obtain ⟨c, hc⟩ := hbal.pattern_occurs hε hJ (fun _ => a)
  exact ⟨c, hc α (Finset.mem_singleton_self α)⟩

/-- A fixed representative Stage-2 index for a requested Stage-1 row. -/
noncomputable def S2coordPreimage (d : ℕ)
    (h₂ : Params.t2 d ≤ Params.q2 d) (hq1 : 1 ≤ Params.q1 d)
    (α : Fin (Params.q2 d)) (a : R1 d) : C2 d :=
  Classical.choose (S2fam_coord_surj d h₂ hq1 α a)

theorem S2coordPreimage_spec (d : ℕ)
    (h₂ : Params.t2 d ≤ Params.q2 d) (hq1 : 1 ≤ Params.q1 d)
    (α : Fin (Params.q2 d)) (a : R1 d) :
    S2fam d (S2coordPreimage d h₂ hq1 α a) α = a :=
  Classical.choose_spec (S2fam_coord_surj d h₂ hq1 α a)

/-- The outer-coordinate map into the full `(q₁+5)` Stage-1 coordinate set. -/
def m1PlusCoord (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) (α : Fin (Params.q2 d))
    (B : Finset (Fin n)) :
    M1PlusOuter d v α B → Fin (Params.q1 d + 5)
  | Sum.inl q => baseIdx d q
  | Sum.inr i => slotIdx d (gadgetSlot v α i.val)

theorem transversalAt_inactive_unique {n q : ℕ}
    (v : Fin n → Fin q → Bool) (α : Fin q) (B : Finset (Fin n))
    {i j : Fin n} (hiT : i ∈ transversalAt v α B)
    (hjT : j ∈ transversalAt v α B)
    (hi : i ∉ activeSet v α) (hj : j ∉ activeSet v α) :
    i = j := by
  classical
  by_cases h : (B \ activeSet v α).Nonempty
  · have hi' : i = (B \ activeSet v α).min' h := by
      rw [transversalAt, dif_pos h] at hiT
      rcases Finset.mem_union.mp hiT with hiA | hiS
      · exact False.elim (hi (Finset.mem_of_mem_inter_right hiA))
      · simpa using hiS
    have hj' : j = (B \ activeSet v α).min' h := by
      rw [transversalAt, dif_pos h] at hjT
      rcases Finset.mem_union.mp hjT with hjA | hjS
      · exact False.elim (hj (Finset.mem_of_mem_inter_right hjA))
      · simpa using hjS
    exact hi'.trans hj'.symm
  · rw [transversalAt, dif_neg h, Finset.union_empty] at hiT
    exact False.elim (hi (Finset.mem_of_mem_inter_right hiT))

theorem m1PlusCoord_injective (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) (α : Fin (Params.q2 d))
    (B : Finset (Fin n)) (hA : (activeSet v α).card ≤ 4) :
    Function.Injective (m1PlusCoord d v α B) := by
  classical
  intro x y hxy
  cases x with
  | inl q =>
      cases y with
      | inl q' =>
          have hq : q = q' := baseIdx_injective d (by simpa [m1PlusCoord] using hxy)
          exact congrArg Sum.inl hq
      | inr j =>
          have hbad : baseIdx d q = slotIdx d (gadgetSlot v α j.val) := by
            simpa [m1PlusCoord] using hxy
          exact False.elim ((baseIdx_ne_slotIdx d q (gadgetSlot v α j.val)) hbad)
  | inr i =>
      cases y with
      | inl q =>
          have hbad : slotIdx d (gadgetSlot v α i.val) = baseIdx d q := by
            simpa [m1PlusCoord] using hxy
          exact False.elim ((baseIdx_ne_slotIdx d q (gadgetSlot v α i.val)) hbad.symm)
      | inr j =>
          have hslot : gadgetSlot v α i.val = gadgetSlot v α j.val :=
            slotIdx_injective d (by simpa [m1PlusCoord] using hxy)
          have hij : i.val = j.val := by
            by_cases hiA : i.val ∈ activeSet v α <;>
              by_cases hjA : j.val ∈ activeSet v α
            · exact gadgetSlot_injOn_active v α hA
                (mem_activeSet.mp hiA) (mem_activeSet.mp hjA) hslot
            · have hi_neutral :
                  gadgetSlot v α i.val ≠ (4 : Fin 5) :=
                gadgetSlot_active_ne_neutral v α hA (mem_activeSet.mp hiA)
              have hjfalse : v j.val α = false :=
                Bool.eq_false_iff.mpr (fun ht => hjA (mem_activeSet.mpr ht))
              rw [gadgetSlot_inactive v α j.val hjfalse] at hslot
              exact False.elim (hi_neutral hslot)
            · have hifalse : v i.val α = false :=
                Bool.eq_false_iff.mpr (fun ht => hiA (mem_activeSet.mpr ht))
              have hj_neutral :
                  gadgetSlot v α j.val ≠ (4 : Fin 5) :=
                gadgetSlot_active_ne_neutral v α hA (mem_activeSet.mp hjA)
              rw [gadgetSlot_inactive v α i.val hifalse] at hslot
              exact False.elim (hj_neutral hslot.symm)
            · exact transversalAt_inactive_unique v α B i.property j.property hiA hjA
          exact congrArg Sum.inr (Subtype.ext hij)

/-- The same coordinate map, reindexed over `Fin (card outer)` for
`stage1_chosen_dense_threshold`. -/
noncomputable def m1PlusCoordEnum (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) (α : Fin (Params.q2 d))
    (B : Finset (Fin n)) :
    Fin (Fintype.card (M1PlusOuter d v α B)) → Fin (Params.q1 d + 5) :=
  fun k => m1PlusCoord d v α B
    ((Fintype.equivFin (M1PlusOuter d v α B)).symm k)

theorem m1PlusCoordEnum_injective (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) (α : Fin (Params.q2 d))
    (B : Finset (Fin n)) (hA : (activeSet v α).card ≤ 4) :
    Function.Injective (m1PlusCoordEnum d v α B) := by
  intro x y hxy
  have houter := m1PlusCoord_injective d v α B hA hxy
  exact (Fintype.equivFin (M1PlusOuter d v α B)).symm.injective houter

theorem M1PlusOuter_card (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) (α : Fin (Params.q2 d))
    (B : Finset (Fin n)) :
    Fintype.card (M1PlusOuter d v α B)
      = Params.q1 d + (transversalAt v α B).card := by
  classical
  simp [M1PlusOuter]

theorem transversalAt_card_ge_of_inactive {n q : ℕ}
    (v : Fin n → Fin q → Bool) (α : Fin q) (B : Finset (Fin n))
    (h : (B \ activeSet v α).Nonempty) :
    (B ∩ activeSet v α).card + 1 ≤ (transversalAt v α B).card := by
  classical
  rw [transversalAt, dif_pos h]
  have hdisj : Disjoint (B ∩ activeSet v α)
      ({(B \ activeSet v α).min' h} : Finset (Fin n)) := by
    rw [Finset.disjoint_left]
    intro x hx hxrep
    rw [Finset.mem_singleton] at hxrep
    subst hxrep
    exact (Finset.mem_sdiff.mp ((B \ activeSet v α).min'_mem h)).2
      (Finset.mem_of_mem_inter_right hx)
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton]

theorem m1PlusCoordEnum_large (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) (α : Fin (Params.q2 d))
    (B : Finset (Fin n))
    (hinact : (B \ activeSet v α).Nonempty)
    (hell : 2 ≤ (B ∩ activeSet v α).card) :
    Params.q1 d + 3 ≤ Fintype.card (M1PlusOuter d v α B) := by
  have hT := transversalAt_card_ge_of_inactive v α B hinact
  rw [M1PlusOuter_card d v α B]
  omega

/-- The canonical branch subgame, with template rows represented by chosen
Stage-2 indices and vector rows represented by the transversal. -/
noncomputable def m1PlusBranchCoreSub (d : ℕ)
    (h₂ : Params.t2 d ≤ Params.q2 d) (hq1 : 1 ≤ Params.q1 d)
    {n : ℕ} (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4)
    (α : Fin (Params.q2 d)) (B : Finset (Fin n)) (S' : Finset (C1 d)) :
    (M1PlusOuter d v α B × Fin 1) → {γ // γ ∈ S'} → Bool :=
  fun x γ =>
    match x.1 with
    | Sum.inl q =>
        M4 d v (Sum.inl (p, S2coordPreimage d h₂ hq1 α (q, x.2)))
          (diagCopyCol d α γ.val)
    | Sum.inr i =>
        M4 d v (Sum.inr i.val) (diagCopyCol d α γ.val)

theorem m1PlusBranchCoreSub_eq_stage (d : ℕ)
    (h₂ : Params.t2 d ≤ Params.q2 d) (hq1 : 1 ≤ Params.q1 d)
    {n : ℕ} (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4)
    (α : Fin (Params.q2 d)) (B : Finset (Fin n)) (S' : Finset (C1 d))
    (x : M1PlusOuter d v α B × Fin 1) (γ : {γ // γ ∈ S'}) :
    m1PlusBranchCoreSub d h₂ hq1 v p α B S' x γ =
      HlocalAtSub d (S1fam d) S' (m1PlusCoordEnum d v α B)
        (((Fintype.equivFin (M1PlusOuter d v α B)) x.1), x.2) γ := by
  classical
  cases x with
  | mk outer row0 =>
      cases outer with
      | inl q =>
          simp only [m1PlusBranchCoreSub]
          rw [M4_diagonal_copy_apply, M2_apply,
            S2coordPreimage_spec d h₂ hq1 α (q, row0), M1_apply]
          simp [HlocalAtSub, HlocalAt, m1PlusCoordEnum, m1PlusCoord,
            relaxedInterlace]
      | inr i =>
          simp only [m1PlusBranchCoreSub, diagCopyCol_eq]
          rw [M4_vector_diag d v i.val (tail d γ.val)
            (fun _ : Fin 4 => (α, γ.val)) (by intro m; rfl)]
          rw [localGadget_tail, M1hat_apply]
          have hrow : row0 = (0 : Fin 1) := Subsingleton.elim _ _
          simp [HlocalAtSub, HlocalAt, m1PlusCoordEnum, m1PlusCoord,
            relaxedInterlace, hrow]

/-- The canonical branch subgame is isomorphic to the chosen-coordinate
Stage-1 local game. -/
noncomputable def m1PlusBranchIso (d : ℕ)
    (h₂ : Params.t2 d ≤ Params.q2 d) (hq1 : 1 ≤ Params.q1 d)
    {n : ℕ} (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4)
    (α : Fin (Params.q2 d)) (B : Finset (Fin n)) (S' : Finset (C1 d)) :
    GameIso (m1PlusBranchCoreSub d h₂ hq1 v p α B S')
      (HlocalAtSub d (S1fam d) S' (m1PlusCoordEnum d v α B)) where
  eX := (Fintype.equivFin (M1PlusOuter d v α B)).prodCongr (Equiv.refl (Fin 1))
  eY := Equiv.refl _
  hval := fun x γ => m1PlusBranchCoreSub_eq_stage d h₂ hq1 v p α B S' x γ

theorem m1PlusBranchCoreSub_lower (d : ℕ) (hd : 2 ≤ d)
    (hbal : Params.t1 d ≤ Params.q1 d + 5)
    (hta : Params.a d + 2 ≤ Params.t1 d)
    (h₂ : Params.t2 d ≤ Params.q2 d) (hq1 : 1 ≤ Params.q1 d)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hρ : ρ < (1 - epsQT (Params.q1 d + 5) (Params.t1 d)) / 2)
    {n : ℕ} (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4)
    (α : Fin (Params.q2 d)) (B : Finset (Fin n))
    (hA : (activeSet v α).card ≤ 4) (S' : Finset (C1 d))
    (hS' : (1 - ρ) * (L1 d : ℝ) ≤ (S'.card : ℝ))
    (hinact : (B \ activeSet v α).Nonempty)
    (hell : 2 ≤ (B ∩ activeSet v α).card) :
    Params.a d + 2 ≤ D (m1PlusBranchCoreSub d h₂ hq1 v p α B S') := by
  classical
  have he := m1PlusCoordEnum_injective d v α B hA
  have hu := m1PlusCoordEnum_large d v α B hinact hell
  have hstage := stage1_chosen_dense_threshold d hd hbal hta
    hρ0 hρ1 hρ S' hS' (m1PlusCoordEnum d v α B) he hu
  have hD := GameIso.D_eq (m1PlusBranchIso d h₂ hq1 v p α B S')
  rw [hD]
  exact hstage

-- CLAIM-BEGIN lem:M1PlusVectorsIsInterlace
/-- Paper `lem:M1PlusVectorsIsInterlace`, canonical-transversal formalization.
The selected `(p, α)` branch restricted to canonical diagonal columns and to
the vector transversal is isomorphic to a chosen-coordinate Stage-1 local
game.  Consequently, if the branch has an inactive vector row and at least two
active vector rows at `α`, then its canonical local subgame has complexity at
least `B_cap+1 = a+2`. -/
theorem M1_plus_vectors_is_interlace (d : ℕ) (hd : 2 ≤ d)
    (hbal : Params.t1 d ≤ Params.q1 d + 5)
    (hta : Params.a d + 2 ≤ Params.t1 d)
    (h₂ : Params.t2 d ≤ Params.q2 d) (hq1 : 1 ≤ Params.q1 d)
    {n : ℕ} (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4)
    (α : Fin (Params.q2 d)) (B : Finset (Fin n))
    (hA : (activeSet v α).card ≤ 4) :
    Nonempty
      (GameIso (m1PlusBranchCoreSub d h₂ hq1 v p α B (Finset.univ : Finset (C1 d)))
        (HlocalAtSub d (S1fam d) (Finset.univ : Finset (C1 d))
          (m1PlusCoordEnum d v α B))) ∧
      ((B \ activeSet v α).Nonempty →
        2 ≤ (B ∩ activeSet v α).card →
        Params.a d + 2 ≤
          D (m1PlusBranchCoreSub d h₂ hq1 v p α B
            (Finset.univ : Finset (C1 d)))) :=
-- CLAIM-END lem:M1PlusVectorsIsInterlace
  by
  constructor
  · exact ⟨m1PlusBranchIso d h₂ hq1 v p α B (Finset.univ : Finset (C1 d))⟩
  · intro hinact hell
    have hε : epsQT (Params.q1 d + 5) (Params.t1 d) < 1 :=
      epsQT_lt_one (by omega) (Params.t1_pos d)
    have hρ : (0 : ℝ) < (1 - epsQT (Params.q1 d + 5) (Params.t1 d)) / 2 := by
      linarith
    have hS' :
        (1 - (0 : ℝ)) * (L1 d : ℝ)
          ≤ (((Finset.univ : Finset (C1 d)).card : ℕ) : ℝ) := by
      simp [C1]
    exact m1PlusBranchCoreSub_lower d hd hbal hta h₂ hq1
      (ρ := 0) (by norm_num) (by norm_num) hρ v p α B hA
      (Finset.univ : Finset (C1 d)) hS' hinact hell

-- CLAIM-BEGIN cor:M1PlusVectorsCanonicalDense
/-- Paper `cor:M1PlusVectorsCanonicalDense`, canonical diagonal-block
formalization.  A dense subset of the canonical diagonal block pulls back to a
dense Stage-1 subfamily `S'`; the same canonical-transversal branch subgame is
isomorphic to `HlocalAtSub` over `S'`, and the chosen-coordinate threshold
gives the advertised lower bound under the same active/inactive hypotheses. -/
theorem M1_plus_vectors_canonical_dense (d : ℕ) (hd : 2 ≤ d)
    (hbal : Params.t1 d ≤ Params.q1 d + 5)
    (hta : Params.a d + 2 ≤ Params.t1 d)
    (h₂ : Params.t2 d ≤ Params.q2 d) (hq1 : 1 ≤ Params.q1 d)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hρ : ρ < (1 - epsQT (Params.q1 d + 5) (Params.t1 d)) / 2)
    {n : ℕ} (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4)
    (α : Fin (Params.q2 d)) (B : Finset (Fin n))
    (hA : (activeSet v α).card ≤ 4)
    (Y : Finset (C4 d)) (hYsub : Y ⊆ diagCopySet d α)
    (hYdense : (1 - ρ) * ((diagCopySet d α).card : ℝ) ≤ (Y.card : ℝ)) :
    ∃ S' : Finset (C1 d),
      (1 - ρ) * (L1 d : ℝ) ≤ (S'.card : ℝ) ∧
      Nonempty
        (GameIso (m1PlusBranchCoreSub d h₂ hq1 v p α B S')
          (HlocalAtSub d (S1fam d) S' (m1PlusCoordEnum d v α B))) ∧
      ((B \ activeSet v α).Nonempty →
        2 ≤ (B ∩ activeSet v α).card →
        Params.a d + 2 ≤ D (m1PlusBranchCoreSub d h₂ hq1 v p α B S')) :=
-- CLAIM-END cor:M1PlusVectorsCanonicalDense
  by
  classical
  let S' : Finset (C1 d) := diagPullback d α Y
  have hcardS : S'.card = Y.card := by
    simpa [S'] using diagPullback_card d α hYsub
  have hcardX : (diagCopySet d α).card = L1 d := diagCopySet_card d α
  have hS' : (1 - ρ) * (L1 d : ℝ) ≤ (S'.card : ℝ) := by
    rw [← hcardS, hcardX] at hYdense
    exact hYdense
  refine ⟨S', hS', ⟨m1PlusBranchIso d h₂ hq1 v p α B S'⟩, ?_⟩
  intro hinact hell
  exact m1PlusBranchCoreSub_lower d hd hbal hta h₂ hq1
    hρ0 hρ1 hρ v p α B hA S' hS' hinact hell

end NPCC
