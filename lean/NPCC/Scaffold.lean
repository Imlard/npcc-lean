import Mathlib
import NPCC.Defs
import NPCC.Relaxed
import NPCC.VBP
import Workspace.Types.Interlace

/-! # Stage-4 scaffold and source attachment

This module first derives elementary lower bounds on balanced-family sizes.
It then defines `M₄` by attaching the preprocessed source vectors to the
three-stage template matrix. The source promise controls how vector rows enter
the local gadgets, while the tagged diagonal column family keeps the four bin
coordinates distinguishable. -/

namespace NPCC

/-- Companion (unregistered): with accuracy `ε < 1`, the lower side of
balancedness forces every pattern on every coordinate set of size at most `t`
to occur in the family — the matching-index count is at least
`(1-ε)L/|Y|^{|J|} > 0`, hence positive. -/
theorem IsBalancedFamily.pattern_occurs {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (hS : IsBalancedFamily t S ε) (hε : ε < 1)
    {J : Finset (Fin q)} (hJ : J.card ≤ t) (a : Fin q → Y) :
    ∃ j : Fin L, ∀ γ ∈ J, S j γ = a γ := by
  classical
  obtain ⟨hL, hbal⟩ := hS
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with hY0 | hYpos
  · -- `Y` empty: the pattern `a` itself refutes any constrained coordinate.
    haveI : IsEmpty Y := Fintype.card_eq_zero_iff.mp hY0
    exact ⟨⟨0, hL⟩, fun γ _ => (IsEmpty.false (a γ)).elim⟩
  · -- `Y` inhabited: the balancedness lower side makes the fiber nonempty.
    have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hcY : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hYpos
    have h := hbal J hJ a
    set F : Finset (Fin L) :=
      Finset.univ.filter (fun j : Fin L => ∀ γ ∈ J, S j γ = a γ) with hF
    have hpow : (0 : ℝ) < (Fintype.card Y : ℝ) ^ J.card := by positivity
    have hlow : (1 - ε) / (Fintype.card Y : ℝ) ^ J.card
        ≤ (F.card : ℝ) / (L : ℝ) := by
      have habs := (abs_le.mp h).1
      have hsplit : (1 - ε) / (Fintype.card Y : ℝ) ^ J.card
          = 1 / (Fintype.card Y : ℝ) ^ J.card
            - ε / (Fintype.card Y : ℝ) ^ J.card := by
        ring
      rw [hsplit]
      linarith
    have hposR : (0 : ℝ) < (F.card : ℝ) := by
      have hnum : (0 : ℝ) < (1 - ε) / (Fintype.card Y : ℝ) ^ J.card :=
        div_pos (by linarith) hpow
      have hq := lt_of_lt_of_le hnum hlow
      rcases div_pos_iff.mp hq with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact h1
      · linarith
    have hpos : 0 < F.card := by exact_mod_cast hposR
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    rw [hF] at hj
    exact ⟨j, (Finset.mem_filter.mp hj).2⟩

-- CLAIM-BEGIN aux:family-lower
/-- Counting lower bound for balanced families (scaffold prose fact, no paper
label). For a `(q,t)`-balanced family `S : Fin L → Fin q → Y` with accuracy
`ε < 1` and `t ≤ q` (so a `t`-element coordinate set exists), the lower side
of balancedness makes every pattern on a fixed `t`-element coordinate set
occur among the `S j`; the restriction map to those coordinates is therefore
onto, giving `|Y|^t ≤ L` and in particular the form the scaffold consumes,
stated division-safely as `|Y|^t / (1+ε) ≤ L`. (Balancedness at the empty
coordinate set forces `ε ≥ 0`, so the division is by a positive number.)
Instantiated at the Stage-1/Stage-2 families this yields the size facts
`|C₁| ≥ 2^{t₁}/(1+ε) ≥ 2^{t₁-1}` and `|C₂| ≥ |R₁|^{t₂}/(1+ε) ≥ |R₁|^{t₂}/2`. -/
theorem balanced_family_card_lower {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (hS : IsBalancedFamily t S ε) (hε : ε < 1) (htq : t ≤ q) :
    ((Fintype.card Y : ℝ) ^ t) / (1 + ε) ≤ (L : ℝ) :=
-- CLAIM-END aux:family-lower
  by
  classical
  have hL : 0 < L := hS.1
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  -- `ε ≥ 0`, extracted from balancedness at the empty coordinate set.
  have hε0 : 0 ≤ ε := by
    have h := hS.2 (∅ : Finset (Fin q)) (Nat.zero_le t) (S ⟨0, hL⟩)
    have hfil : (Finset.univ.filter
        (fun j : Fin L => ∀ γ ∈ (∅ : Finset (Fin q)), S j γ = S ⟨0, hL⟩ γ))
          = (Finset.univ : Finset (Fin L)) := by
      apply Finset.filter_true_of_mem
      intro j _ γ hγ
      simp at hγ
    rw [hfil] at h
    simp only [Finset.card_empty, pow_zero, Finset.card_univ, Fintype.card_fin] at h
    rw [div_self (ne_of_gt hLR)] at h
    simpa using h
  -- Main counting bound: `|Y|^t ≤ L` (restriction to a `t`-set is onto).
  have hmain : (Fintype.card Y : ℝ) ^ t ≤ (L : ℝ) := by
    rcases Nat.eq_zero_or_pos (Fintype.card Y) with hY0 | hYpos
    · rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · subst ht0
        simpa using hL1
      · rw [hY0]
        push_cast
        rw [zero_pow htpos.ne']
        positivity
    · haveI : Nonempty Y := Fintype.card_pos_iff.mp hYpos
      -- A coordinate set of size exactly `t`.
      obtain ⟨J, -, hJcard⟩ : ∃ J ⊆ (Finset.univ : Finset (Fin q)), J.card = t := by
        apply Finset.exists_subset_card_eq
        simpa using htq
      -- The restriction map `Fin L → ({γ // γ ∈ J} → Y)` is onto.
      have hsurj : Function.Surjective
          (fun (j : Fin L) (γ : {γ // γ ∈ J}) => S j γ.val) := by
        intro b
        obtain ⟨j, hj⟩ := hS.pattern_occurs hε (le_of_eq hJcard)
          (fun γ => if h : γ ∈ J then b ⟨γ, h⟩ else Classical.arbitrary Y)
        refine ⟨j, funext fun γ => ?_⟩
        show S j γ.val = b γ
        exact (hj γ.val γ.property).trans (dif_pos γ.property)
      have hcard : Fintype.card ({γ // γ ∈ J} → Y) ≤ Fintype.card (Fin L) :=
        Fintype.card_le_of_surjective _ hsurj
      rw [Fintype.card_fun, Fintype.card_coe, hJcard, Fintype.card_fin] at hcard
      exact_mod_cast hcard
  calc ((Fintype.card Y : ℝ) ^ t) / (1 + ε)
      ≤ (Fintype.card Y : ℝ) ^ t := div_le_self (by positivity) (by linarith)
    _ ≤ (L : ℝ) := hmain

end NPCC

/-! # Stage 4: attach the source instance

The final matrix has row type `R₄ = R₃ ⊕ [n]`: template rows and source-vector
rows remain distinguished by a tagged sum. For each source coordinate `α`, the
active vectors are ranked into four gadget slots; the source promise proves
that this rank is injective and lies in `[4]`. A fifth slot represents all
inactive vectors.

Several details are explicit because they are load-bearing later:

* gadget coordinates use the same bit-vector encoding as the Stage-1 tail;
* duplicate inactive rows are retained, and lower bounds first select a
  canonical transversal before applying a game isomorphism;
* diagonal column slices carry their dimension tags, so distinct slices are
  disjoint by construction;
* the neutral-row flag records presence of an inactive vector, not uniqueness;
* `Bcap = a+1` and `Byes = 2 + clog₂(q₂) + Bcap` record the exact residual
  communication budget after the two announcement phases. -/

namespace NPCC

open Workspace.Types.Interlace

-- CLAIM-BEGIN def:stage4-matrix
/-- Paper Stage 4: the active support set `A_α := {i ∈ [n] : v_i(α) = 1}` of
a dimension `α`, for the attached vector family `v` (the preprocessed,
power-of-two-normalised source instance; the set-builder tests `v i α = true`
explicitly, per the Bool-coercion ruling). The source-side screen — the
`VBPInstance.Promise` of the attached instance — is exactly
`(activeSet v α).card ≤ 4` for every `α` (companion
`activeSet_card_le_of_promise`). -/
def activeSet {n q : ℕ} (v : Fin n → Fin q → Bool) (α : Fin q) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => v i α = true)

/-- The injection `π_α : A_α ↪ [4]`, represented by the order-preserving
rank of `i` inside `A_α`, i.e. the number of strictly smaller active rows.
It is total, with a harmless fallback value outside `A_α`; on `A_α` it is
strictly increasing
(`piAlpha_lt_of_lt`), hence injective (`piAlpha_injOn`), and under the
source-side screen `|A_α| ≤ 4` it lands in `[4]` (`piAlpha_lt_four`). -/
def piAlpha {n q : ℕ} (v : Fin n → Fin q → Bool) (α : Fin q) (i : Fin n) :
    ℕ :=
  ((activeSet v α).filter (fun i' => i' < i)).card

/-- The Stage-4 slot of row `i` at dimension `α` in the 5-row local gadget:
the active slot `π_α(i) ∈ {0,1,2,3}` when `v_i(α) = 1` (falling back to the
neutral slot if the promise-supplied range bound `π_α(i) < 4` fails — the
fallback branch is dead under the screen and no lemma exposes it), and the
neutral slot `4` when `v_i(α) = 0` (paper slot `q₁+5`, 1-based). The slot
values follow the `slotIdx` typed-separator convention: four active slots
`0,1,2,3` and the neutral slot `4`. -/
def gadgetSlot {n q : ℕ} (v : Fin n → Fin q → Bool) (α : Fin q) (i : Fin n) :
    Fin 5 :=
  if h : v i α = true ∧ piAlpha v α i < 4 then ⟨piAlpha v α i, by omega⟩
  else (4 : Fin 5)

/-- The 5-row local gadget `⟨M₀⟩⁵(s, k)`: the classical 5-fold interlace of
the seed, with its column tuples `Fin 5 → Fin 2` packed into `k ∈ [2⁵]` by
the SAME equivalence `finFunctionFinEquiv` that packs the Stage-1 `tail`
patterns — the two encodings must stay aligned (`localGadget_tail`). -/
def localGadget (s : Fin 5) (k : Fin (2 ^ 5)) : Bool :=
  interlaceFun M0 5 (s, 0) (finFunctionFinEquiv.symm k)

/-- The Stage-4 row carrier `R₄ = R₃ ⊕ [n]` is a tagged sum.
`Sum.inl` carries the template rows `R₃ = [4]×C₂`,
`Sum.inr` the vector rows `[n]` of the attached instance (including its four
zero anchors). -/
abbrev R4 (d n : ℕ) : Type := R3 d ⊕ Fin n

/-- The Stage-4 column carrier `C₄ = [2⁵] × R₂⁴` (the second factor is the
Stage-3 column carrier `C₃ = R₂⁴`; the first is the local-gadget
coordinate). -/
abbrev C4 (d : ℕ) : Type := Fin (2 ^ 5) × C3 d

/-- The outer (dimension) coordinate a column tuple proposes: the outer
component of its first entry. A tuple lies on the diagonal outer-block slice
`α₁ = α₂ = α₃ = α₄ = α` iff ALL FOUR entries have outer component `α`, and
then `α` is forced to equal `diagCoord`; reading the candidate dimension off
the tuple makes the Stage-4 case split deterministic (no choice, no `∃`
elimination in the definition). -/
def diagCoord (d : ℕ) (y : C3 d) : Fin (Params.q2 d) := (y 0).1

/-- Template half of Stage 4: the rows `R₃` copy the Stage-3 template `M₃`,
reading only the `R₂⁴` component of the column (the gadget coordinate `k` is
invisible to template rows). -/
noncomputable def M4template (d : ℕ) : R3 d → C4 d → Bool :=
  fun r j => M3 d r j.2

/-- Vector half of Stage 4: on the diagonal outer-block slice
`α₁ = α₂ = α₃ = α₄ = α` the row `i` plays its Stage-4 slot in the 5-row
local gadget — the `π_α(i)`-th active row exactly when `v_i(α) = 1`, the
neutral row otherwise — and off the diagonal it is neutral. Zero rows (in
particular the four zero anchors of the preprocessed instance) are neutral
on every column (`M4_zero_row_neutral`). -/
def M4vector (d : ℕ) {n : ℕ} (v : Fin n → Fin (Params.q2 d) → Bool) :
    Fin n → C4 d → Bool :=
  fun i j =>
    if (∀ m : Fin 4, (j.2 m).1 = diagCoord d j.2) then
      localGadget (gadgetSlot v (diagCoord d j.2) i) j.1
    else localGadget (4 : Fin 5) j.1

/-- Paper Stage 4, the matrix `M₄` (`def:stage4-matrix`): template rows carry
`M₃`, vector rows carry the diagonal-gated 5-row local gadget. Authored in
the exact `Sum.elim` shape consumed by `GameIso.sumAttachCongr`. The
attached family `v` is the vector family of the preprocessed,
power-of-two-normalised source instance over the `q₂` padded source
dimensions (`q₂ = d` on the normalised regime, `Params.q2_eq_self`); its row
index set `[n]` includes the four zero anchors of
`lem:zero-anchor-preprocessing`, whose rows are neutral on every column. -/
noncomputable def M4 (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) : R4 d n → C4 d → Bool :=
  fun r j =>
    Sum.elim (fun x => M4template d x j) (fun i => M4vector d v i j) r

/-- The local capacity budget `B_cap := a + 1` (the Stage-1 threshold budget
available on a successful branch). -/
def Bcap (d : ℕ) : ℕ := Params.a d + 1

/-- The YES-case target budget
`B_yes := log 4 + ⌈log q₂⌉ + B_cap = 2 + ⌈log q₂⌉ + B_cap` — choose a bin,
choose a dimension, then solve the local Stage-1 subproblem. `log 4 = 2` is
exact; the ceiling log is the exact `Nat.clog 2`, which agrees with
`Nat.log 2` on the (power-of-two) normalised regime (`clog_q2_eq_log`). -/
def Byes (d : ℕ) : ℕ := 2 + Nat.clog 2 (Params.q2 d) + Bcap d
-- CLAIM-END def:stage4-matrix

/-! ## Companions: definitional transparency of `M₄` -/

/-- Companion: membership in the active support is exactly activity. -/
theorem mem_activeSet {n q : ℕ} {v : Fin n → Fin q → Bool} {α : Fin q}
    {i : Fin n} : i ∈ activeSet v α ↔ v i α = true := by
  simp [activeSet]

/-- Companion: `M₄` is definitionally the `Sum.elim` attachment shape of
`GameIso.sumAttachCongr` (the Stage-4 congruence step applies without any
reshaping). -/
theorem M4_eq_sumElim (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) :
    M4 d v = fun (r : R4 d n) (j : C4 d) =>
      Sum.elim (fun x => M4template d x j) (fun i => M4vector d v i j) r :=
  rfl

/-- Companion: template rows copy `M₃`, ignoring the gadget coordinate. -/
theorem M4_template_apply (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) (r : R3 d) (j : C4 d) :
    M4 d v (Sum.inl r) j = M3 d r j.2 := rfl

/-- Companion: the local gadget evaluates as the seed at the `s`-th packed
column digit. -/
theorem localGadget_apply (s : Fin 5) (k : Fin (2 ^ 5)) :
    localGadget s k = M0 0 (finFunctionFinEquiv.symm k s) := rfl

/-- Companion (encoding alignment): the gadget value at slot `s` of a
`tail`-encoded Stage-1 column is the full Stage-1 matrix `M̂₁` at the
reserved coordinate `slotIdx s`. This pins the `tail`/`localGadget` packing
to the SAME `finFunctionFinEquiv` convention; the Stage-4 local-subgame
lemmas consume exactly this identity. -/
theorem localGadget_tail (d : ℕ) (s : Fin 5) (γ : C1 d) :
    localGadget s (tail d γ) = M1hat d (slotIdx d s, 0) γ := by
  simp only [localGadget, tail, Equiv.symm_apply_apply]
  rfl

/-- Companion: vector-row value on the diagonal slice of dimension `α`. -/
theorem M4_vector_diag (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) (i : Fin n) (k : Fin (2 ^ 5))
    (y : C3 d) {α : Fin (Params.q2 d)} (hy : ∀ m : Fin 4, (y m).1 = α) :
    M4 d v (Sum.inr i) (k, y) = localGadget (gadgetSlot v α i) k := by
  have hα : diagCoord d y = α := hy 0
  have hdiag : ∀ m : Fin 4, (y m).1 = diagCoord d y := by
    intro m
    rw [hα]
    exact hy m
  show M4vector d v i (k, y) = localGadget (gadgetSlot v α i) k
  rw [M4vector]
  simp only
  rw [if_pos hdiag, hα]

/-- Companion: vector-row value off the diagonal slice — neutral. -/
theorem M4_vector_offdiag (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) (i : Fin n) (k : Fin (2 ^ 5))
    (y : C3 d) (hy : ¬ ∀ m : Fin 4, (y m).1 = diagCoord d y) :
    M4 d v (Sum.inr i) (k, y) = localGadget (4 : Fin 5) k := by
  show M4vector d v i (k, y) = localGadget (4 : Fin 5) k
  rw [M4vector]
  simp only
  rw [if_neg hy]

/-- Companion: an inactive row's slot is neutral. -/
theorem gadgetSlot_inactive {n q : ℕ} (v : Fin n → Fin q → Bool) (α : Fin q)
    (i : Fin n) (hi : v i α = false) : gadgetSlot v α i = (4 : Fin 5) := by
  rw [gadgetSlot, dif_neg]
  rintro ⟨h1, -⟩
  rw [hi] at h1
  cases h1

/-- Companion: a zero row — in particular each zero anchor of the
preprocessed instance (`anchor_zero`) — is neutral on EVERY column of `M₄`
(paper: "every zero-anchor row remains neutral on every branch"). -/
theorem M4_zero_row_neutral (d : ℕ) {n : ℕ}
    (v : Fin n → Fin (Params.q2 d) → Bool) (i : Fin n)
    (hz : ∀ α, v i α = false) (j : C4 d) :
    M4 d v (Sum.inr i) j = localGadget (4 : Fin 5) j.1 := by
  obtain ⟨k, y⟩ := j
  by_cases hdiag : ∀ m : Fin 4, (y m).1 = diagCoord d y
  · rw [M4_vector_diag d v i k y hdiag,
      gadgetSlot_inactive v (diagCoord d y) i (hz (diagCoord d y))]
  · exact M4_vector_offdiag d v i k y hdiag

/-! ## Companions: `π_α` under the source-side screen (Promise-gated) -/

/-- Companion: the source-side screen of the attached instance
(`VBPInstance.Promise`) is exactly the `|A_α| ≤ 4` gate on active sets. -/
theorem activeSet_card_le_of_promise (I : VBPInstance) (h : I.Promise)
    (α : Fin I.d) : (activeSet I.v α).card ≤ 4 :=
  h α

/-- Companion: an active row's rank is below the active count. -/
theorem piAlpha_lt_card {n q : ℕ} (v : Fin n → Fin q → Bool) (α : Fin q)
    {i : Fin n} (hi : i ∈ activeSet v α) :
    piAlpha v α i < (activeSet v α).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨i, hi, by simp⟩

/-- Companion (D4 range bound, Promise-gated): under the source-side screen
`|A_α| ≤ 4`, every active row's `π_α` value lies in `[4]` — the active slots
never collide with the neutral slot. -/
theorem piAlpha_lt_four {n q : ℕ} (v : Fin n → Fin q → Bool) (α : Fin q)
    (hA : (activeSet v α).card ≤ 4) {i : Fin n} (hi : i ∈ activeSet v α) :
    piAlpha v α i < 4 :=
  lt_of_lt_of_le (piAlpha_lt_card v α hi) hA

/-- Companion: `π_α` is strictly increasing along active rows (the
order-preserving half of D4; the second row need not be active). -/
theorem piAlpha_lt_of_lt {n q : ℕ} (v : Fin n → Fin q → Bool) (α : Fin q)
    {i i' : Fin n} (hi : i ∈ activeSet v α) (hii' : i < i') :
    piAlpha v α i < piAlpha v α i' := by
  have hsub : (activeSet v α).filter (fun i₀ => i₀ < i)
      ⊆ (activeSet v α).filter (fun i₀ => i₀ < i') := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 hii'⟩
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset hsub]
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, hii'⟩, by simp⟩

/-- Companion (D4 injectivity, Promise-irrelevant on the set itself): `π_α`
is injective on the active set `A_α`. -/
theorem piAlpha_injOn {n q : ℕ} (v : Fin n → Fin q → Bool) (α : Fin q)
    {i i' : Fin n} (hi : i ∈ activeSet v α) (hi' : i' ∈ activeSet v α)
    (h : piAlpha v α i = piAlpha v α i') : i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (piAlpha_lt_of_lt v α hi hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (piAlpha_lt_of_lt v α hi' hgt))

/-- Companion (Promise-gated): an active row's slot is its `π_α` rank — the
fallback branch of `gadgetSlot` is dead under the screen. -/
theorem gadgetSlot_active {n q : ℕ} (v : Fin n → Fin q → Bool) (α : Fin q)
    (hA : (activeSet v α).card ≤ 4) {i : Fin n} (hi : v i α = true) :
    (gadgetSlot v α i).val = piAlpha v α i := by
  have hmem : i ∈ activeSet v α :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  rw [gadgetSlot, dif_pos ⟨hi, piAlpha_lt_four v α hA hmem⟩]

/-- Companion (Promise-gated): an active row's slot is never the neutral
slot (the four active slots and the neutral slot are disjoint). -/
theorem gadgetSlot_active_ne_neutral {n q : ℕ} (v : Fin n → Fin q → Bool)
    (α : Fin q) (hA : (activeSet v α).card ≤ 4) {i : Fin n}
    (hi : v i α = true) : gadgetSlot v α i ≠ (4 : Fin 5) := by
  intro hcon
  have hval := congrArg Fin.val hcon
  rw [gadgetSlot_active v α hA hi] at hval
  have hmem : i ∈ activeSet v α :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  have := piAlpha_lt_four v α hA hmem
  omega

/-- Companion (Promise-gated): distinct active rows occupy distinct slots. -/
theorem gadgetSlot_injOn_active {n q : ℕ} (v : Fin n → Fin q → Bool)
    (α : Fin q) (hA : (activeSet v α).card ≤ 4) {i i' : Fin n}
    (hi : v i α = true) (hi' : v i' α = true)
    (h : gadgetSlot v α i = gadgetSlot v α i') : i = i' := by
  have hmem : i ∈ activeSet v α :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  have hmem' : i' ∈ activeSet v α :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i', hi'⟩
  have hval := congrArg Fin.val h
  rw [gadgetSlot_active v α hA hi, gadgetSlot_active v α hA hi'] at hval
  exact piAlpha_injOn v α hmem hmem' hval

/-! ## Companions: the tagged diagonal column family -/

/-- Companion: the diagonal outer-block column family (the paper's
`D_{p,α}`, which is independent of the bin `p`), tagged by its dimension: a
dimension `α`, a gadget coordinate `k`, and one Stage-1 column per bin. -/
abbrev DiagColumns (d : ℕ) : Type :=
  Fin (Params.q2 d) × Fin (2 ^ 5) × (Fin 4 → C1 d)

/-- Companion: the (injective) realisation of a tagged diagonal column as a
Stage-4 column — all four `R₂` entries ride the tagged dimension. -/
def diagEmbed (d : ℕ) : DiagColumns d → C4 d :=
  fun x => (x.2.1, fun m => (x.1, x.2.2 m))

/-- Companion: `diagEmbed` is injective; in particular the diagonal slices
of two distinct dimensions are DISJOINT (the proved-disjointness half of the
tagged-family ruling). -/
theorem diagEmbed_injective (d : ℕ) : Function.Injective (diagEmbed d) := by
  intro x y h
  have hk : x.2.1 = y.2.1 := congrArg (fun z : C4 d => z.1) h
  have hsnd := congrArg (fun z : C4 d => z.2) h
  have hα : x.1 = y.1 :=
    congrArg (fun r : R2 d => r.1) (congrFun hsnd 0)
  have hγ : x.2.2 = y.2.2 :=
    funext fun m => congrArg (fun r : R2 d => r.2) (congrFun hsnd m)
  exact Prod.ext_iff.mpr ⟨hα, Prod.ext_iff.mpr ⟨hk, hγ⟩⟩

/-- Companion: the realised column is diagonal at its tag. -/
theorem diagEmbed_diag (d : ℕ) (x : DiagColumns d) (m : Fin 4) :
    ((diagEmbed d x).2 m).1 = x.1 := rfl

/-- Companion: every diagonal Stage-4 column is a realised tagged column. -/
theorem eq_diagEmbed_of_diag (d : ℕ) (k : Fin (2 ^ 5)) (y : C3 d)
    {α : Fin (Params.q2 d)} (hy : ∀ m : Fin 4, (y m).1 = α) :
    (k, y) = diagEmbed d (α, k, fun m => (y m).2) := by
  refine Prod.ext_iff.mpr ⟨rfl, funext fun m => ?_⟩
  exact Prod.ext_iff.mpr ⟨hy m, rfl⟩

/-- Companion: the Stage-4 compatibility column of the local-gadget lemmas
(`X_{p,α}` in the paper): the diagonal column of dimension `α` with Stage-1
tuple `γ`, gadget coordinate pinned to the bin-`p` tail pattern
`tail(γ_p)`. The slice `X_{p,α}` is the (injective) range of
`compatCol d p α` over `γ ∈ C₁⁴`; for a fixed tuple exactly one gadget
coordinate is compatible, which is what the shift/retention argument
counts. -/
noncomputable def compatCol (d : ℕ) (p : Fin 4) (α : Fin (Params.q2 d))
    (γ : Fin 4 → C1 d) : C4 d :=
  diagEmbed d (α, tail d (γ p), γ)

/-- Companion: `compatCol` is injective in the Stage-1 tuple. -/
theorem compatCol_injective (d : ℕ) (p : Fin 4) (α : Fin (Params.q2 d)) :
    Function.Injective (compatCol d p α) := by
  intro γ γ' h
  have := diagEmbed_injective d h
  exact congrArg (fun x : DiagColumns d => x.2.2) this

/-! ## Companions: the canonical transversal -/

/-- Companion: the canonical transversal
of a branch row set `B` at dimension `α` — every active row of `B`, plus the
LEAST inactive row of `B` as the one canonical neutral representative (when
`B \ A_α` is nonempty; this is the presence-form `ν_α(B) = 1`, never an
exactly-one-zero condition). Restricting the vector rows to this transversal
collapses the duplicate neutral rows to a single representative, after which
the local identification is honestly bijective; `M₄` itself keeps every
duplicate row. -/
def transversalAt {n q : ℕ} (v : Fin n → Fin q → Bool) (α : Fin q)
    (B : Finset (Fin n)) : Finset (Fin n) :=
  (B ∩ activeSet v α) ∪
    (if h : (B \ activeSet v α).Nonempty then {(B \ activeSet v α).min' h}
     else ∅)

/-- Companion: the transversal stays inside the branch row set. -/
theorem transversalAt_subset {n q : ℕ} (v : Fin n → Fin q → Bool)
    (α : Fin q) (B : Finset (Fin n)) : transversalAt v α B ⊆ B := by
  intro x hx
  by_cases h : (B \ activeSet v α).Nonempty
  · rw [transversalAt, dif_pos h] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_of_mem_inter_left hx
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact (Finset.mem_sdiff.mp ((B \ activeSet v α).min'_mem h)).1
  · rw [transversalAt, dif_neg h, Finset.union_empty] at hx
    exact Finset.mem_of_mem_inter_left hx

/-- Companion: every active row of the branch survives in the transversal
(`A_α(B) = B ∩ A_α` is kept whole — `ℓ_α(B)` is not reduced). -/
theorem inter_active_subset_transversalAt {n q : ℕ}
    (v : Fin n → Fin q → Bool) (α : Fin q) (B : Finset (Fin n)) :
    B ∩ activeSet v α ⊆ transversalAt v α B :=
  Finset.subset_union_left

/-- Companion: the neutral representative is in the transversal whenever the
branch has an inactive row (`ν_α(B) = 1` in presence form). -/
theorem transversalAt_rep_mem {n q : ℕ} (v : Fin n → Fin q → Bool)
    (α : Fin q) (B : Finset (Fin n)) (h : (B \ activeSet v α).Nonempty) :
    (B \ activeSet v α).min' h ∈ transversalAt v α B := by
  rw [transversalAt, dif_pos h]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- Companion: the neutral representative is genuinely inactive. -/
theorem transversalAt_rep_inactive {n q : ℕ} (v : Fin n → Fin q → Bool)
    (α : Fin q) (B : Finset (Fin n)) (h : (B \ activeSet v α).Nonempty) :
    v ((B \ activeSet v α).min' h) α = false := by
  have hmem := (Finset.mem_sdiff.mp ((B \ activeSet v α).min'_mem h)).2
  exact Bool.eq_false_iff.mpr fun hc => hmem (mem_activeSet.mpr hc)

/-- Companion: the transversal costs at most one extra row over the active
part. -/
theorem transversalAt_card_le {n q : ℕ} (v : Fin n → Fin q → Bool)
    (α : Fin q) (B : Finset (Fin n)) :
    (transversalAt v α B).card ≤ (B ∩ activeSet v α).card + 1 := by
  by_cases h : (B \ activeSet v α).Nonempty
  · rw [transversalAt, dif_pos h]
    exact le_trans (Finset.card_union_le _ _) (by simp)
  · rw [transversalAt, dif_neg h, Finset.union_empty]
    exact Nat.le_add_right _ 1

/-- Companion (Promise-gated): under the source-side screen the transversal
has at most five rows — matching the five slots of the local gadget. -/
theorem transversalAt_card_le_five {n q : ℕ} (v : Fin n → Fin q → Bool)
    (α : Fin q) (hA : (activeSet v α).card ≤ 4) (B : Finset (Fin n)) :
    (transversalAt v α B).card ≤ 5 := by
  have h1 := transversalAt_card_le v α B
  have h2 : (B ∩ activeSet v α).card ≤ (activeSet v α).card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

/-! ## Companions: budget arithmetic -/

/-- Companion: `q₂` is a power of two by construction, so the ceiling log in
`B_yes` is exact — `Nat.clog 2 q₂ = Nat.log 2 q₂` (no large-`d` gate
needed). -/
theorem clog_q2_eq_log (d : ℕ) :
    Nat.clog 2 (Params.q2 d) = Nat.log 2 (Params.q2 d) := by
  have hq : Params.q2 d = 2 ^ Nat.clog 2 d := rfl
  rw [hq, Nat.clog_pow 2 _ one_lt_two, Nat.log_pow one_lt_two]

/-- Companion: the floor-log form of the YES budget. -/
theorem Byes_eq_log (d : ℕ) :
    Byes d = 2 + Nat.log 2 (Params.q2 d) + Bcap d := by
  rw [Byes, clog_q2_eq_log]

end NPCC
