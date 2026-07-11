import Mathlib
import NPCC.Defs
import NPCC.Relaxed
import NPCC.Axioms
import NPCC.Complexity
import Workspace.Types.Interlace

/-! # Source instances and staged matrix construction

This module defines the objects used by the reduction before the final Stage-4
attachment. It contains:

* the promised four-bin `{0,1}` vector-packing source instance;
* zero-anchor preprocessing and power-of-two dimension padding;
* the explicit parameter regime and the two balanced column families;
* the typed carriers and matrices `M₀`, `M̂₁`, `M₁`, `M₂`, and `M₃`.

The source promise is a separate predicate rather than a structure field. The
balanced families are selected once from
`finite_alphabet_balanced_family_exists` and then
transported through later identifications; no stage silently chooses a fresh
family. The final matrix `M₄` is defined in `NPCC.Scaffold`. -/

namespace NPCC

open Workspace.Types.Interlace

/-! ## Source instance encoding -/

-- CLAIM-BEGIN def:vbp-instance
/-- Paper source problem (`sec:encoding-interface`, `\DefineProblemNoPara`):
a `{0,1}`-`d`-Dimension Vector Bin Packing instance, restricted as the
reduction consumes it. The capacity `c = 1` and the bin count `m = 4` are
hard-wired: they appear only through `IsYes` quantifying over `Fin 4`
bins with per-bin/per-coordinate load at most `1`. The structure carries
exactly the data `n` vectors in `{0,1}^d`; the promise is a SEPARATE
predicate (`VBPInstance.Promise`), never a field, so the final wrapper can
feed unpromised instances through the preprocessor. -/
structure VBPInstance where
  /-- Ambient dimension `d`. -/
  d : ℕ
  /-- Number of vectors `n`. -/
  n : ℕ
  /-- The vectors `v_1, …, v_n ∈ {0,1}^d`, as Boolean coordinate functions. -/
  v : Fin n → Fin d → Bool

/-- YES-instance predicate, `c = 1`, `m = 4`: a total bin assignment
`σ : Fin n → Fin 4` such that every bin `p` and coordinate `α` receive at
most one vector with a `1` at `α` (the `‖Σ_{v ∈ B_p} v‖_∞ ≤ 1` condition,
per-coordinate). Set-builders test `v i α = true` explicitly. -/
def VBPInstance.IsYes (I : VBPInstance) : Prop :=
  ∃ σ : Fin I.n → Fin 4, ∀ (p : Fin 4) (α : Fin I.d),
    (Finset.univ.filter (fun i => σ i = p ∧ I.v i α = true)).card ≤ 1

/-- The source-side promise (paper: `Σ_i v_i(α) ≤ 4` for every coordinate):
at most four vectors carry a `1` in any coordinate. Kept SEPARATE from the
structure; instances violating it are immediate NO-instances and the
reduction pre-screens them. Stage-4's `π_α` injections are gated on this. -/
def VBPInstance.Promise (I : VBPInstance) : Prop :=
  ∀ α : Fin I.d, (Finset.univ.filter (fun i => I.v i α = true)).card ≤ 4
-- CLAIM-END def:vbp-instance

/-- Companion (unregistered; D1's "separate preprocessed-instance record"):
a VBP instance together with the four distinguished zero-anchor rows
`z_1, …, z_4` produced by the zero-anchor preprocessing
(`lem:zero-anchor-preprocessing`). The anchors are REMEMBERED here, outside
the source type: `VBPInstance` itself never carries them. -/
structure PreprocessedInstance extends VBPInstance where
  /-- The four distinguished zero-anchor row indices `z_p ∈ [n]`. -/
  anchor : Fin 4 → Fin n
  /-- The four anchors are pairwise distinct rows. -/
  anchor_injective : Function.Injective anchor
  /-- Every anchor row is the all-zero vector `0^d`. -/
  anchor_zero : ∀ (p : Fin 4) (β : Fin d), v (anchor p) β = false

/-- Companion: the typed row index of the replicated padded instance
`I∘` — five slab copies `(t, i) : Fin 5 × Fin n` plus four anchors
`Fin 4`, as a TAGGED sum (never an untagged `[5n+4]` with raw offsets),
identified with `Fin (5n+4)` only through this equivalence. -/
def preprocessRowEquiv (n : ℕ) : ((Fin 5 × Fin n) ⊕ Fin 4) ≃ Fin (5 * n + 4) :=
  (finProdFinEquiv.sumCongr (Equiv.refl (Fin 4))).trans finSumFinEquiv

/-- Companion: the typed coordinate index of `I∘` — slab `t`'s copy of
source coordinate `α` is `(t, α) : Fin 5 × Fin d`, identified with
`Fin (5d)` through this equivalence. -/
def preprocessCoordEquiv (d : ℕ) : (Fin 5 × Fin d) ≃ Fin (5 * d) :=
  finProdFinEquiv

/-- Companion (the `I∘` construction of `lem:zero-anchor-preprocessing`):
five disjoint-coordinate slab copies `ι_t(v_i)` plus the four zero anchors
`z_1 = ⋯ = z_4 = 0^{5d}`. Row `(t, i)` has a `1` at coordinate `(s, α)` iff
`s = t` and `v_i(α) = 1`; anchor rows are identically `false`. All indexing
goes through the tagged equivalences above. -/
def preprocess (I : VBPInstance) : PreprocessedInstance where
  d := 5 * I.d
  n := 5 * I.n + 4
  v := fun r β =>
    Sum.elim
      (fun ti : Fin 5 × Fin I.n =>
        if ((preprocessCoordEquiv I.d).symm β).1 = ti.1 then
          I.v ti.2 ((preprocessCoordEquiv I.d).symm β).2
        else false)
      (fun _ => false)
      ((preprocessRowEquiv I.n).symm r)
  anchor := fun p => preprocessRowEquiv I.n (Sum.inr p)
  anchor_injective := fun p p' h =>
    Sum.inr_injective ((preprocessRowEquiv I.n).injective h)
  anchor_zero := by
    intro p β
    simp [Equiv.symm_apply_apply]

/-- Companion: the slab-copy row `(t, i)` of the preprocessed instance. -/
def slabRow (I : VBPInstance) (t : Fin 5) (i : Fin I.n) :
    Fin ((preprocess I).n) :=
  preprocessRowEquiv I.n (Sum.inl (t, i))

/-- Companion: slab `s`'s copy of source coordinate `α`. -/
def slabCoord (I : VBPInstance) (s : Fin 5) (α : Fin I.d) :
    Fin ((preprocess I).d) :=
  preprocessCoordEquiv I.d (s, α)

/-- Companion sanity: the preprocessed matrix at a slab row and a slab
coordinate is the paper's `ι_t(v_i)`: the value of `v_i` at `α` when the
slabs agree, `false` otherwise. -/
theorem preprocess_v_slab (I : VBPInstance) (t s : Fin 5) (i : Fin I.n)
    (α : Fin I.d) :
    (preprocess I).v (slabRow I t i) (slabCoord I s α)
      = if s = t then I.v i α else false := by
  simp [preprocess, slabRow, slabCoord, Equiv.symm_apply_apply]

/-- Companion sanity: anchor rows evaluate to `false` everywhere (field
`anchor_zero`, restated for term-style use). -/
theorem preprocess_anchor_zero (I : VBPInstance) (p : Fin 4)
    (β : Fin ((preprocess I).d)) :
    (preprocess I).v ((preprocess I).anchor p) β = false :=
  (preprocess I).anchor_zero p β

/-! ## Power-of-two normalisation -/

-- CLAIM-BEGIN def:powtwo-normalise
/-- `ceilpowtwo(z)`: the least power of two that is at least `z`, rendered
EXACTLY over ℕ as `2 ^ Nat.clog 2 z` (so `ceilPowTwo 0 = 1`; the paper only
consumes it at `z ≥ 1`). The two defining facts are the companions
`le_ceilPowTwo` and `ceilPowTwo_le_pow` below. -/
def ceilPowTwo (z : ℕ) : ℕ := 2 ^ Nat.clog 2 z

/-- `z ≤ ceilPowTwo z` (upper adjoint side of `Nat.clog`). -/
theorem le_ceilPowTwo (z : ℕ) : z ≤ ceilPowTwo z :=
  Nat.le_pow_clog one_lt_two z

/-- The typed padding equivalence keeps padded coordinates distinguishable
from original coordinates in the type: the coordinate set
of a `d`-dimensional instance padded to `D ≥ d` dimensions is the tagged sum
of the original `Fin d` and the padding block `Fin (D − d)`. -/
def padCoordEquiv {d D : ℕ} (h : d ≤ D) : (Fin d ⊕ Fin (D - d)) ≃ Fin D :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))

/-- Power-of-two normalisation (paper `sec:encoding-interface`): pad the
preprocessed instance to ambient dimension `D := ceilpowtwo(max{d, dstar})`
by trailing zero coordinates. Original coordinates enter through
`Sum.inl`, padding through `Sum.inr` (identically `false`); the anchors are
carried over unchanged and stay all-zero.

`dstar` is an explicit argument so this elementary normaliser remains separate
from the large-parameter proof. The final construction instantiates it with
`d_star`, selected from `large_d_checklist`. -/
def normalizeInstance (dstar : ℕ) (I : PreprocessedInstance) :
    PreprocessedInstance where
  d := ceilPowTwo (max I.d dstar)
  n := I.n
  v := fun i β =>
    Sum.elim (fun α => I.v i α) (fun _ => false)
      ((padCoordEquiv
        (le_trans (le_max_left I.d dstar) (le_ceilPowTwo _))).symm β)
  anchor := I.anchor
  anchor_injective := I.anchor_injective
  anchor_zero := by
    intro p β
    rcases (padCoordEquiv
        (le_trans (le_max_left I.d dstar) (le_ceilPowTwo _))).symm β
      with α | γ
    · simp [I.anchor_zero]
    · simp
-- CLAIM-END def:powtwo-normalise

/-- `ceilPowTwo z` is minimal among powers of two that dominate `z`. -/
theorem ceilPowTwo_le_pow {z k : ℕ} (h : z ≤ 2 ^ k) : ceilPowTwo z ≤ 2 ^ k :=
  Nat.pow_le_pow_right (by norm_num) (Nat.clog_le_of_le_pow h)

/-- `ceilPowTwo` is positive. -/
theorem ceilPowTwo_pos (z : ℕ) : 0 < ceilPowTwo z :=
  pow_pos (by norm_num) _

/-- `ceilPowTwo` fixes powers of two. -/
theorem ceilPowTwo_two_pow (k : ℕ) : ceilPowTwo (2 ^ k) = 2 ^ k :=
  le_antisymm (ceilPowTwo_le_pow le_rfl) (le_ceilPowTwo _)

/-- The normalised dimension is a power of two. -/
theorem normalizeInstance_d_two_pow (dstar : ℕ) (I : PreprocessedInstance) :
    ∃ k, (normalizeInstance dstar I).d = 2 ^ k :=
  ⟨Nat.clog 2 (max I.d dstar), rfl⟩

/-- The normalised dimension dominates the threshold. -/
theorem dstar_le_normalizeInstance_d (dstar : ℕ) (I : PreprocessedInstance) :
    dstar ≤ (normalizeInstance dstar I).d :=
  le_trans (le_max_right _ _) (le_ceilPowTwo _)

/-- The normalised dimension dominates the original dimension. -/
theorem d_le_normalizeInstance_d (dstar : ℕ) (I : PreprocessedInstance) :
    I.d ≤ (normalizeInstance dstar I).d :=
  le_trans (le_max_left _ _) (le_ceilPowTwo _)

/-- Companion accessor: on an ORIGINAL coordinate (a `Sum.inl` under the
typed padding equivalence) the normalised instance agrees with `I`. -/
theorem normalizeInstance_v_orig (dstar : ℕ) (I : PreprocessedInstance)
    (i : Fin I.n) (α : Fin I.d) :
    (normalizeInstance dstar I).v i
      (padCoordEquiv (le_trans (le_max_left I.d dstar) (le_ceilPowTwo _))
        (Sum.inl α)) = I.v i α := by
  simp [normalizeInstance, Equiv.symm_apply_apply]

/-- Companion accessor: on a PADDING coordinate (a `Sum.inr`) the normalised
instance is identically `false`. -/
theorem normalizeInstance_v_pad (dstar : ℕ) (I : PreprocessedInstance)
    (i : Fin I.n)
    (γ : Fin (ceilPowTwo (max I.d dstar) - I.d)) :
    (normalizeInstance dstar I).v i
      (padCoordEquiv (le_trans (le_max_left I.d dstar) (le_ceilPowTwo _))
        (Sum.inr γ)) = false := by
  simp [normalizeInstance, Equiv.symm_apply_apply]

/-! ## Parameter regime -/

-- CLAIM-BEGIN def:scaffold-params
/-! Paper `sec:scaffold`, the audited parameter regime as functions of the
(normalised, power-of-two) ambient dimension `d` — every discrete parameter
is an EXACT ℕ-def (`Nat.log 2` for the paper's `log`, `ceilPowTwo` for
`ceilpowtwo`, ceiling division rendered as `(x + y − 1) / y`), and the real
densities are derived from the ℕ exponents. Divisibility/power-of-two facts
(`q₁+2 = r₁t₁`, `q₂ = r₂t₂`, `q₂ = d`, …) are NOT baked into the defs: they
hold for large powers of two `d` and are delivered by `lem:large-d-checklist`
as gated accessor lemmas. Nat truncation notes: `q1` truncates at small `d`
(`ceilPowTwo … − 2`), `t2`'s inner division truncates when
`Nat.log 2 (Nat.log 2 d) = 0` (i.e. `d < 4`) — both junk regions sit far
below `d_star` and are never consumed. -/
namespace Params

/-- Global density margin `δ := 0.1`. -/
noncomputable def delta : ℝ := 0.1

/-- Global surplus-copy parameter `j := 5` (paper `\deltaDep`), fed to the
Stage-2 application of the hard-seed lemma. -/
def jSurplus : ℕ := 5

/-- `q₁ := ceilpowtwo(2 log² d) − 2` (Stage-1 outer-coordinate count). -/
def q1 (d : ℕ) : ℕ := ceilPowTwo (2 * Nat.log 2 d ^ 2) - 2

/-- The Stage-1 threshold exponent `a`, defined structurally so that
`2 ^ a = ceilpowtwo(2 log² d) = q₁ + 2` (companion `two_pow_a`, gated on
`2 ≤ d` against the ℕ-truncation of `q1`). -/
def a (d : ℕ) : ℕ := Nat.clog 2 (2 * Nat.log 2 d ^ 2)

/-- Stage-1 independence `t₁ := ceilpowtwo(64 log d)` (paper `\Independence_1`). -/
def t1 (d : ℕ) : ℕ := ceilPowTwo (64 * Nat.log 2 d)

/-- Stage-1 fiber count `r₁ := (q₁+2)/t₁` (exact division for `d ≥ d_star`). -/
def r1 (d : ℕ) : ℕ := (q1 d + 2) / t1 d

/-- Base Stage-1 robustness margin `b₀ := 64 log(64 log d)` (paper
`\Robustness_0`), used to initialise the passage `M₀ → M₁`. -/
def b0 (d : ℕ) : ℕ := 64 * Nat.log 2 (64 * Nat.log 2 d)

/-- Stage-1 core robustness `b′₁ := 3 log d` (paper `\CoreRobustness_1`). -/
def b1' (d : ℕ) : ℕ := 3 * Nat.log 2 d

/-- Stage-1 robustness `b₁ := 2 log d` (paper `\Robustness_1`). -/
def b1 (d : ℕ) : ℕ := 2 * Nat.log 2 d

/-- `q₂ := ceilpowtwo(d)` (`= d` once `d` is a power of two — gated
companion `q2_eq_self`). -/
def q2 (d : ℕ) : ℕ := ceilPowTwo d

/-- Stage-2 independence `t₂ := ceilpowtwo(3 log d / loglog d)` (paper
`\Independence_2`); the inner real division enters through its ℕ ceiling
`(3 log d + loglog d − 1) / loglog d`, which agrees with the real form since
a power-of-two threshold only sees the integer ceiling. -/
def t2 (d : ℕ) : ℕ :=
  ceilPowTwo
    ((3 * Nat.log 2 d + Nat.log 2 (Nat.log 2 d) - 1) /
      Nat.log 2 (Nat.log 2 d))

/-- Stage-2 fiber count `r₂ := q₂/t₂` (exact division for `d ≥ d_star`). -/
def r2 (d : ℕ) : ℕ := q2 d / t2 d

/-- Stage-2 core robustness `b′₂ := 8 loglog d` (paper `\CoreRobustness_2`). -/
def b2' (d : ℕ) : ℕ := 8 * Nat.log 2 (Nat.log 2 d)

/-- Stage-2 robustness `b₂ := 3 loglog d` (paper `\Robustness_2`). -/
def b2 (d : ℕ) : ℕ := 3 * Nat.log 2 (Nat.log 2 d)

/-- Stage-2 density `h₂ := 2^{−b₂}` (`= (log d)^{−3}` for powers of two),
derived from the ℕ exponent. -/
noncomputable def h2 (d : ℕ) : ℝ := (2 : ℝ) ^ (-(b2 d : ℤ))

/-- Stage-2 core density `h′₂ := 2^{−b′₂}` (`= (log d)^{−8}`), derived from
the ℕ exponent. -/
noncomputable def h2' (d : ℕ) : ℝ := (2 : ℝ) ^ (-(b2' d : ℤ))

end Params
-- CLAIM-END def:scaffold-params

namespace Params

/-- Companion: the defining identity `2 ^ a = q₁ + 2`, available as soon as
`2 ≤ d` (which forces `2 log² d ≥ 2` so the ℕ-truncation in `q1` is inert;
the full large-`d` regime is far above this). -/
theorem two_pow_a {d : ℕ} (hd : 2 ≤ d) : 2 ^ a d = q1 d + 2 := by
  have hlog : 0 < Nat.log 2 d := Nat.log_pos one_lt_two hd
  have h2z : 2 ≤ 2 * Nat.log 2 d ^ 2 := by nlinarith
  have hle : 2 ≤ ceilPowTwo (2 * Nat.log 2 d ^ 2) :=
    le_trans h2z (le_ceilPowTwo _)
  have : q1 d + 2 = ceilPowTwo (2 * Nat.log 2 d ^ 2) :=
    Nat.sub_add_cancel hle
  rw [this]
  rfl

/-- Companion: `a = log(q₁+2)` — the exponent is recoverable by the exact
`Nat.log 2` (depth arithmetic stays structural). -/
theorem a_eq_log {d : ℕ} (hd : 2 ≤ d) : a d = Nat.log 2 (q1 d + 2) := by
  rw [← two_pow_a hd, Nat.log_pow one_lt_two]

/-- Companion: once `d` is a power of two (the normalised regime),
`q₂ = d`. -/
theorem q2_eq_self {d k : ℕ} (h : d = 2 ^ k) : q2 d = d := by
  rw [q2, h, ceilPowTwo_two_pow]

/-- Companion: `t₁` is positive (it is a power of two). -/
theorem t1_pos (d : ℕ) : 0 < t1 d := ceilPowTwo_pos _

/-- Companion: `t₂` is positive (it is a power of two). -/
theorem t2_pos (d : ℕ) : 0 < t2 d := ceilPowTwo_pos _

/-- Companion: `q₂` is positive. -/
theorem q2_pos (d : ℕ) : 0 < q2 d := ceilPowTwo_pos _

end Params

/-! ## Balanced column families -/

/-- The absolute constant from the finite-alphabet balanced-family citation
interface, choice-extracted once. -/
noncomputable def balancedFamilyConstant : ℕ :=
  finite_alphabet_balanced_family_exists.choose

/-- The balanced-family constant is positive. -/
theorem balancedFamilyConstant_pos : 0 < balancedFamilyConstant :=
  finite_alphabet_balanced_family_exists.choose_spec.1

/-- The citation interface's universal clause, specialised to
`balancedFamilyConstant`. -/
theorem balancedFamily_spec :
    ∀ (q t : ℕ) (Y : Type) [Fintype Y] [DecidableEq Y] (ε : ℝ),
      1 ≤ t → t ≤ q → 0 < ε → ε < 1 → 1 ≤ Fintype.card Y →
      ∃ (L : ℕ) (S : Fin L → Fin q → Y),
        0 < L ∧
        (L : ℝ) ≤ ((q + 2 : ℕ) : ℝ) ^ balancedFamilyConstant
                    * ((Fintype.card Y + 2 : ℕ) : ℝ) ^ (balancedFamilyConstant * t)
                    * ((⌈1 / ε⌉₊ : ℕ) : ℝ) ^ balancedFamilyConstant ∧
        ∀ J : Finset (Fin q), J.card ≤ t → ∀ a : Fin q → Y,
          |((Finset.univ.filter
                (fun j : Fin L => ∀ γ ∈ J, S j γ = a γ)).card : ℝ) / (L : ℝ)
            - 1 / (Fintype.card Y : ℝ) ^ J.card|
          ≤ ε / (Fintype.card Y : ℝ) ^ J.card :=
  finite_alphabet_balanced_family_exists.choose_spec.2

/-- Companion: the total-fallback existential behind the extractor (the D1
total-fallback pattern). SOME indexed family satisfies the axiom's
conclusion conditionally on the side conditions: the cited witness when they
hold, the empty family (vacuously) when they fail. -/
theorem balancedFamilyData_exists (q t : ℕ) (Y : Type) [Fintype Y]
    [DecidableEq Y] (ε : ℝ) :
    ∃ (L : ℕ) (S : Fin L → Fin q → Y),
      (1 ≤ t ∧ t ≤ q ∧ 0 < ε ∧ ε < 1 ∧ 1 ≤ Fintype.card Y) →
        (0 < L ∧
          (L : ℝ) ≤ ((q + 2 : ℕ) : ℝ) ^ balancedFamilyConstant
                      * ((Fintype.card Y + 2 : ℕ) : ℝ) ^ (balancedFamilyConstant * t)
                      * ((⌈1 / ε⌉₊ : ℕ) : ℝ) ^ balancedFamilyConstant ∧
          ∀ J : Finset (Fin q), J.card ≤ t → ∀ a : Fin q → Y,
            |((Finset.univ.filter
                  (fun j : Fin L => ∀ γ ∈ J, S j γ = a γ)).card : ℝ) / (L : ℝ)
              - 1 / (Fintype.card Y : ℝ) ^ J.card|
            ≤ ε / (Fintype.card Y : ℝ) ^ J.card) := by
  by_cases h : 1 ≤ t ∧ t ≤ q ∧ 0 < ε ∧ ε < 1 ∧ 1 ≤ Fintype.card Y
  · obtain ⟨L, S, hs⟩ :=
      balancedFamily_spec q t Y ε h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    exact ⟨L, S, fun _ => hs⟩
  · exact ⟨0, fun j => j.elim0, fun hc => absurd hc h⟩

/-- Total choice-extractor for a cited balanced family. Under the axiom's
side conditions it selects a witnessing indexed family; outside them it
degrades to the (vacuous) empty-family witness, whose properties are never
exposed — every property lemma is gated on the side conditions. -/
noncomputable def balancedFamilyData (q t : ℕ) (Y : Type) [Fintype Y]
    [DecidableEq Y] (ε : ℝ) : (L : ℕ) × (Fin L → Fin q → Y) :=
  ⟨(balancedFamilyData_exists q t Y ε).choose,
   (balancedFamilyData_exists q t Y ε).choose_spec.choose⟩

/-- Companion: the extractor's specification under the side conditions —
the selected family is `(q,t)`-balanced at accuracy `ε` and satisfies the
axiom's explicit size bound. -/
theorem balancedFamilyData_spec (q t : ℕ) (Y : Type) [Fintype Y]
    [DecidableEq Y] {ε : ℝ}
    (h1 : 1 ≤ t) (h2 : t ≤ q) (h3 : 0 < ε) (h4 : ε < 1)
    (h5 : 1 ≤ Fintype.card Y) :
    IsBalancedFamily t (balancedFamilyData q t Y ε).2 ε ∧
      ((balancedFamilyData q t Y ε).1 : ℝ)
        ≤ ((q + 2 : ℕ) : ℝ) ^ balancedFamilyConstant
            * ((Fintype.card Y + 2 : ℕ) : ℝ) ^ (balancedFamilyConstant * t)
            * ((⌈1 / ε⌉₊ : ℕ) : ℝ) ^ balancedFamilyConstant := by
  obtain ⟨hL, hsize, hbal⟩ :=
    (balancedFamilyData_exists q t Y ε).choose_spec.choose_spec
      ⟨h1, h2, h3, h4, h5⟩
  exact ⟨⟨hL, hbal⟩, hsize⟩

-- CLAIM-BEGIN def:S-family
/-- Paper `rem:balanced-columns-exist`: the accuracy at which every scaffold
family is drawn, `ε_{q,t} := (2qt)^{−c}`. The exponent is the constant
`c := balancedFamilyConstant` supplied by the balanced-family citation
interface. All downstream
large-parameter gates use this same choice. -/
noncomputable def epsQT (q t : ℕ) : ℝ :=
  ((2 * q * t : ℕ) : ℝ) ^ (-(balancedFamilyConstant : ℤ))

/-- The scaffold's balanced-family selector `S_{q,t}(Y)`: the cited family
over alphabet `Y` at accuracy `ε_{q,t}`, selected once inside
`balancedFamilyData`. Downstream stage isomorphisms transport this same family
rather than selecting a new one. -/
noncomputable def scaffoldFamily (q t : ℕ) (Y : Type) [Fintype Y]
    [DecidableEq Y] : (L : ℕ) × (Fin L → Fin q → Y) :=
  balancedFamilyData q t Y (epsQT q t)

/-- The size of the Stage-1 column family `C₁ = S_{q₁+5,t₁}(Cols M₀)`
(alphabet `Fin 2 = Cols M₀`). -/
noncomputable def L1 (d : ℕ) : ℕ :=
  (scaffoldFamily (Params.q1 d + 5) (Params.t1 d) (Fin 2)).1

/-- The Stage-1 column family `C₁` itself, as an indexed family (repeats
allowed and counted; columns of `M̂₁` are the family INDICES). -/
noncomputable def S1fam (d : ℕ) :
    Fin (L1 d) → Fin (Params.q1 d + 5) → Fin 2 :=
  (scaffoldFamily (Params.q1 d + 5) (Params.t1 d) (Fin 2)).2

/-- The size of the Stage-2 column family `S_{q₂,t₂}(R₁)` (alphabet
`Fin q₁ × Fin 1 = R₁`, the row set of `M₁`). -/
noncomputable def L2 (d : ℕ) : ℕ :=
  (scaffoldFamily (Params.q2 d) (Params.t2 d)
    (Fin (Params.q1 d) × Fin 1)).1

/-- The Stage-2 column family `S_{q₂,t₂}(R₁)` itself. -/
noncomputable def S2fam (d : ℕ) :
    Fin (L2 d) → Fin (Params.q2 d) → Fin (Params.q1 d) × Fin 1 :=
  (scaffoldFamily (Params.q2 d) (Params.t2 d)
    (Fin (Params.q1 d) × Fin 1)).2
-- CLAIM-END def:S-family

/-- Companion: `ε_{q,t}` is positive (for positive `q`, `t`). -/
theorem epsQT_pos {q t : ℕ} (hq : 0 < q) (ht : 0 < t) : 0 < epsQT q t := by
  have hbase : (0 : ℝ) < ((2 * q * t : ℕ) : ℝ) := by
    have : 0 < 2 * q * t := by positivity
    exact_mod_cast this
  exact zpow_pos hbase _

/-- Companion: `ε_{q,t} < 1` (for positive `q`, `t`; uses
`balancedFamilyConstant ≥ 1`). -/
theorem epsQT_lt_one {q t : ℕ} (hq : 0 < q) (ht : 0 < t) : epsQT q t < 1 := by
  have hbase : (1 : ℝ) < ((2 * q * t : ℕ) : ℝ) := by
    have : 2 ≤ 2 * q * t := by nlinarith
    have h2 : (2 : ℝ) ≤ ((2 * q * t : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hC : balancedFamilyConstant ≠ 0 :=
    Nat.pos_iff_ne_zero.mp balancedFamilyConstant_pos
  rw [epsQT, zpow_neg, zpow_natCast]
  have hpow : (1 : ℝ) < ((2 * q * t : ℕ) : ℝ) ^ balancedFamilyConstant :=
    one_lt_pow₀ hbase hC
  exact inv_lt_one_of_one_lt₀ hpow

/-- Companion: the Stage-1 family is `(q₁+5, t₁)`-balanced at its accuracy,
exposed under the single large-`d` side condition `t₁ ≤ q₁+5` (delivered
downstream by `lem:large-d-checklist`). -/
theorem S1fam_balanced (d : ℕ) (h : Params.t1 d ≤ Params.q1 d + 5) :
    IsBalancedFamily (Params.t1 d) (S1fam d)
      (epsQT (Params.q1 d + 5) (Params.t1 d)) := by
  have hq : 0 < Params.q1 d + 5 := by omega
  exact (balancedFamilyData_spec (Params.q1 d + 5) (Params.t1 d) (Fin 2)
    (Params.t1_pos d) h (epsQT_pos hq (Params.t1_pos d))
    (epsQT_lt_one hq (Params.t1_pos d)) (by simp)).1

/-- Companion: the Stage-2 family is `(q₂, t₂)`-balanced at its accuracy,
exposed under the large-`d` side conditions `t₂ ≤ q₂` and `1 ≤ q₁`. -/
theorem S2fam_balanced (d : ℕ) (h : Params.t2 d ≤ Params.q2 d)
    (hq1 : 1 ≤ Params.q1 d) :
    IsBalancedFamily (Params.t2 d) (S2fam d)
      (epsQT (Params.q2 d) (Params.t2 d)) := by
  have hcard : 1 ≤ Fintype.card (Fin (Params.q1 d) × Fin 1) := by
    simpa using hq1
  exact (balancedFamilyData_spec (Params.q2 d) (Params.t2 d)
    (Fin (Params.q1 d) × Fin 1)
    (Params.t2_pos d) h (epsQT_pos (Params.q2_pos d) (Params.t2_pos d))
    (epsQT_lt_one (Params.q2_pos d) (Params.t2_pos d)) hcard).1

/-- Companion: the Stage-1 family is nonempty under the gate. -/
theorem L1_pos (d : ℕ) (h : Params.t1 d ≤ Params.q1 d + 5) : 0 < L1 d :=
  (S1fam_balanced d h).1

/-- Companion: the Stage-2 family is nonempty under the gate. -/
theorem L2_pos (d : ℕ) (h : Params.t2 d ≤ Params.q2 d)
    (hq1 : 1 ≤ Params.q1 d) : 0 < L2 d :=
  (S2fam_balanced d h hq1).1

/-! ## The stage matrices `M₀`, `M̂₁`, `M₁`, `M₂`, and `M₃` -/

-- CLAIM-BEGIN def:stage-matrices
/-- Stage 0 (paper `sec:scaffold`): the seed matrix `M₀ := [1 0]` — one row,
two columns, value `1` exactly at the first column. -/
def M0 : Fin 1 → Fin 2 → Bool := fun _ y => decide (y = 0)

/-- The Stage-1 column carrier `C₁ = S_{q₁+5,t₁}(Cols M₀)`: columns of the
relaxed interlace are the family INDICES (repeats counted). -/
abbrev C1 (d : ℕ) : Type := Fin (L1 d)

/-- The full Stage-1 row carrier `R₁^full = [q₁+5] × Rows(M₀)`. -/
abbrev R1full (d : ℕ) : Type := Fin (Params.q1 d + 5) × Fin 1

/-- The Stage-1 row carrier `R₁ = [q₁] × Rows(M₀)` (first `q₁` outer
blocks; the final five subgame coordinates are reserved for the Stage-4
local gadget). -/
abbrev R1 (d : ℕ) : Type := Fin (Params.q1 d) × Fin 1

/-- D4 typed separator, base side: the embedding of the `q₁` ambient
Stage-1 coordinates into the `q₁+5` full coordinates (`Fin.castAdd`, never
a raw ℕ offset). -/
def baseIdx (d : ℕ) (i : Fin (Params.q1 d)) : Fin (Params.q1 d + 5) :=
  Fin.castAdd 5 i

/-- D4 typed separator, slot side: the embedding of the five reserved
Stage-4 coordinates (four vector slots `s = 0,1,2,3` and one neutral slot
`s = 4`; paper indexing `q₁+1, …, q₁+5`). -/
def slotIdx (d : ℕ) (s : Fin 5) : Fin (Params.q1 d + 5) :=
  Fin.natAdd (Params.q1 d) s

/-- Stage 1, full form: `M̂₁ := ⟨M₀⟩^{q₁+5, C₁}`, the relaxed interlace of
the seed by the Stage-1 balanced family. -/
noncomputable def M1hat (d : ℕ) : R1full d → C1 d → Bool :=
  relaxedInterlace M0 (S1fam d)

/-- Stage 1: `M₁ := M̂₁[R₁; C₁]`, the row restriction of `M̂₁` to its first
`q₁` outer blocks, as a total game on the restricted row type (rows embed
through `baseIdx`; all columns kept). -/
noncomputable def M1 (d : ℕ) : R1 d → C1 d → Bool :=
  fun a j => M1hat d (baseIdx d a.1, a.2) j

/-- The tail pattern `tail(γ) ∈ [2⁵]`: the 5-bit pattern a Stage-1 column
carries on the five reserved slot coordinates. -/
noncomputable def tail (d : ℕ) (j : C1 d) : Fin (2 ^ 5) :=
  finFunctionFinEquiv (fun s : Fin 5 => S1fam d j (slotIdx d s))

/-- The Stage-2 row carrier `R₂ = [q₂] × C₁` (outer blocks = padded source
dimensions). -/
abbrev R2 (d : ℕ) : Type := Fin (Params.q2 d) × C1 d

/-- The Stage-2 column carrier `C₂` (indices of the Stage-2 family). -/
abbrev C2 (d : ℕ) : Type := Fin (L2 d)

/-- Stage 2 (the dimension gadget): `M₂ := ⟨M₁ᵀ⟩^{q₂, S_{q₂,t₂}(R₁)}`, the
relaxed interlace of the TRANSPOSE of `M₁` by the Stage-2 family (transpose
in the same orientation as `GameIso.transpose` / `D_swap`). -/
noncomputable def M2 (d : ℕ) : R2 d → C2 d → Bool :=
  relaxedInterlace (fun (j : C1 d) (a : R1 d) => M1 d a j) (S2fam d)

/-- The Stage-3 row carrier `R₃ = [4] × C₂` (outer blocks = bins; `m = 4`
hard-wired). -/
abbrev R3 (d : ℕ) : Type := Fin 4 × C2 d

/-- The Stage-3 column carrier `C₃ = R₂⁴`. -/
abbrev C3 (d : ℕ) : Type := Fin 4 → R2 d

/-- Stage 3 (the bin gadget): `M₃ := ⟨M₂ᵀ⟩^4`, the CLASSICAL 4-fold
interlace of the transpose of `M₂`. -/
noncomputable def M3 (d : ℕ) : R3 d → C3 d → Bool :=
  interlaceFun (fun (c : C2 d) (r : R2 d) => M2 d r c) 4
-- CLAIM-END def:stage-matrices

/-- Companion (D4): the base coordinates and the reserved slot coordinates
are DISJOINT — the typed separator never aliases. -/
theorem baseIdx_ne_slotIdx (d : ℕ) (i : Fin (Params.q1 d)) (s : Fin 5) :
    baseIdx d i ≠ slotIdx d s := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [baseIdx, slotIdx, Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

/-- Companion (D4): distinct reserved slots are distinct coordinates. -/
theorem slotIdx_injective (d : ℕ) : Function.Injective (slotIdx d) := by
  intro s s' h
  have hv := congrArg Fin.val h
  simp only [slotIdx, Fin.val_natAdd] at hv
  exact Fin.ext (by omega)

/-- Companion (D4): the base embedding is injective. -/
theorem baseIdx_injective (d : ℕ) : Function.Injective (baseIdx d) := by
  intro i i' h
  have hv := congrArg Fin.val h
  simp only [baseIdx, Fin.val_castAdd] at hv
  exact Fin.ext hv

/-- Companion: `M̂₁` evaluates as the seed at the family entry (definitional
transparency of the Stage-1 construction). -/
theorem M1hat_apply (d : ℕ) (a : R1full d) (j : C1 d) :
    M1hat d a j = M0 a.2 (S1fam d j a.1) := rfl

/-- Companion: `M₁` evaluates as the seed at the base-embedded coordinate. -/
theorem M1_apply (d : ℕ) (a : R1 d) (j : C1 d) :
    M1 d a j = M0 a.2 (S1fam d j (baseIdx d a.1)) := rfl

/-- Companion: `M₂` evaluates as `M₁` transposed at the Stage-2 family
entry: row `(α, γ)`, column `c` reads `M₁` at row `S₂(c)(α)`, column `γ`. -/
theorem M2_apply (d : ℕ) (r : R2 d) (c : C2 d) :
    M2 d r c = M1 d (S2fam d c r.1) r.2 := rfl

/-- Companion: `M₃` evaluates as `M₂` transposed at the selected bin
component: row `(p, c)`, column `y : Fin 4 → R₂` reads `M₂` at row `y(p)`,
column `c`. -/
theorem M3_apply (d : ℕ) (r : R3 d) (y : C3 d) :
    M3 d r y = M2 d (y r.1) r.2 := rfl

/-- Companion sanity: the seed matrix is `[1 0]`. -/
theorem M0_apply_zero (x : Fin 1) : M0 x 0 = true := rfl

/-- Companion sanity: the seed matrix vanishes at its second column. -/
theorem M0_apply_one (x : Fin 1) : M0 x 1 = false := rfl



open Finset

/-! ## General evaluation of the preprocessed matrix (helper companions) -/

/-- General value of the preprocessed matrix at a slab-row `(t,i)` and an
arbitrary coordinate `β`, decomposed through the coordinate equivalence. -/
theorem preprocess_v_slabRow (I : VBPInstance) (t : Fin 5) (i : Fin I.n)
    (β : Fin ((preprocess I).d)) :
    (preprocess I).v (slabRow I t i) β
      = (if ((preprocessCoordEquiv I.d).symm β).1 = t then
          I.v i ((preprocessCoordEquiv I.d).symm β).2 else false) := by
  simp [preprocess, slabRow, Equiv.symm_apply_apply]

/-- Every row of `preprocess I` is either a slab copy `(t,i)` or an anchor. -/
theorem preprocess_row_cases (I : VBPInstance) (r : Fin ((preprocess I).n)) :
    (∃ t i, r = slabRow I t i) ∨ (∃ p, r = (preprocess I).anchor p) := by
  rcases hr : (preprocessRowEquiv I.n).symm r with ⟨t, i⟩ | p
  · left
    refine ⟨t, i, ?_⟩
    rw [slabRow, ← hr, Equiv.apply_symm_apply]
  · right
    refine ⟨p, ?_⟩
    show r = preprocessRowEquiv I.n (Sum.inr p)
    rw [← hr, Equiv.apply_symm_apply]

/-- The 5 slabs of `preprocess I` use disjoint coordinate blocks: a slab-`t`
copy is `0` at any coordinate that lies in slab `s ≠ t`. -/
theorem slabRow_off_slab (I : VBPInstance) (t s : Fin 5) (i : Fin I.n)
    (α : Fin I.d) (hst : s ≠ t) :
    (preprocess I).v (slabRow I t i) (slabCoord I s α) = false := by
  rw [preprocess_v_slab]; simp [hst]

/-- Anchors are all-zero (restated for term use). -/
theorem anchor_val_false (I : VBPInstance) (p : Fin 4)
    (β : Fin ((preprocess I).d)) :
    (preprocess I).v ((preprocess I).anchor p) β = false :=
  (preprocess I).anchor_zero p β

/-- Slab rows and anchors are distinct rows. -/
theorem slabRow_ne_anchor (I : VBPInstance) (t : Fin 5) (i : Fin I.n)
    (p : Fin 4) : slabRow I t i ≠ (preprocess I).anchor p := by
  intro h
  have : (preprocessRowEquiv I.n).symm (slabRow I t i)
      = (preprocessRowEquiv I.n).symm ((preprocess I).anchor p) := by rw [h]
  rw [slabRow, Equiv.symm_apply_apply] at this
  change _ = (preprocessRowEquiv I.n).symm (preprocessRowEquiv I.n (Sum.inr p)) at this
  rw [Equiv.symm_apply_apply] at this
  exact Sum.inl_ne_inr this

/-- Distinct slabs give distinct rows (for the same or different `i`). -/
theorem slabRow_inj (I : VBPInstance) {t t' : Fin 5} {i i' : Fin I.n}
    (h : slabRow I t i = slabRow I t' i') : t = t' ∧ i = i' := by
  have h2 : (Sum.inl (t, i) : (Fin 5 × Fin I.n) ⊕ Fin 4) = Sum.inl (t', i') := by
    apply (preprocessRowEquiv I.n).injective
    exact h
  have h3 := Sum.inl_injective h2
  exact ⟨(Prod.ext_iff.mp h3).1, (Prod.ext_iff.mp h3).2⟩

/-! ## Clause (i), forward: `I` YES ⟹ `I∘` YES -/

/-- The canonical lift of a source packing `σ` to `I∘`: replicate `σ` across
all five slab copies of each vector and drop the four anchors into bin `0`. -/
def liftAssign (I : VBPInstance) (σ : Fin I.n → Fin 4) :
    Fin ((preprocess I).n) → Fin 4 :=
  fun r => Sum.elim (fun ti : Fin 5 × Fin I.n => σ ti.2) (fun _ => 0)
    ((preprocessRowEquiv I.n).symm r)

/-- `liftAssign` on a slab row reads off `σ` of the source index. -/
theorem liftAssign_slabRow (I : VBPInstance) (σ : Fin I.n → Fin 4)
    (t : Fin 5) (i : Fin I.n) :
    liftAssign I σ (slabRow I t i) = σ i := by
  simp [liftAssign, slabRow, Equiv.symm_apply_apply]

/-- `liftAssign` sends every anchor to bin `0`. -/
theorem liftAssign_anchor (I : VBPInstance) (σ : Fin I.n → Fin 4) (p : Fin 4) :
    liftAssign I σ ((preprocess I).anchor p) = 0 := by
  show Sum.elim _ _ ((preprocessRowEquiv I.n).symm
    (preprocessRowEquiv I.n (Sum.inr p))) = 0
  rw [Equiv.symm_apply_apply]; rfl

theorem preprocess_isYes_of_isYes (I : VBPInstance) (h : I.IsYes) :
    (preprocess I).IsYes := by
  classical
  obtain ⟨σ, hσ⟩ := h
  refine ⟨liftAssign I σ, ?_⟩
  intro p β
  -- Decode β into its slab `s` and source coordinate `α`.
  set s : Fin 5 := ((preprocessCoordEquiv I.d).symm β).1 with hs
  set α : Fin I.d := ((preprocessCoordEquiv I.d).symm β).2 with hα
  -- The preprocess filter set is contained in the image of the source filter
  -- set under `slabRow I s` (every 1-valued row in a bin is a slab-`s` copy).
  have hsub : (Finset.univ.filter
        (fun r => liftAssign I σ r = p ∧ (preprocess I).v r β = true))
      ⊆ (Finset.univ.filter (fun i => σ i = p ∧ I.v i α = true)).image
          (slabRow I s) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨-, hassign, hval⟩ := hr
    rw [Finset.mem_image]
    rcases preprocess_row_cases I r with ⟨t, i, rfl⟩ | ⟨q, rfl⟩
    · rw [preprocess_v_slabRow] at hval
      by_cases hst : s = t
      · subst hst
        rw [if_pos rfl] at hval
        rw [liftAssign_slabRow] at hassign
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hassign, hval⟩, rfl⟩
      · rw [if_neg (by simpa [eq_comm] using hst)] at hval
        exact absurd hval (by simp)
    · rw [anchor_val_false] at hval
      exact absurd hval (by simp)
  calc (Finset.univ.filter
        (fun r => liftAssign I σ r = p ∧ (preprocess I).v r β = true)).card
      ≤ ((Finset.univ.filter (fun i => σ i = p ∧ I.v i α = true)).image
          (slabRow I s)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun i => σ i = p ∧ I.v i α = true)).card :=
          Finset.card_image_le
    _ ≤ 1 := hσ p α

/-! ## Clause (i), backward: `I∘` YES ⟹ `I` YES -/

theorem isYes_of_preprocess_isYes (I : VBPInstance) (h : (preprocess I).IsYes) :
    I.IsYes := by
  classical
  obtain ⟨σ, hσ⟩ := h
  -- Restrict to slab 0.
  refine ⟨fun i => σ (slabRow I 0 i), ?_⟩
  intro p α
  -- Inject the source filter set into the preprocess filter set (at slab-0
  -- coordinate `slabCoord I 0 α`) via the injection `i ↦ slabRow I 0 i`.
  have hcard : (Finset.univ.filter (fun i => σ (slabRow I 0 i) = p ∧ I.v i α = true)).card
      ≤ (Finset.univ.filter (fun r => σ r = p ∧
          (preprocess I).v r (slabCoord I 0 α) = true)).card := by
    apply Finset.card_le_card_of_injOn (slabRow I 0)
    · intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      rw [Finset.mem_coe, Finset.mem_filter]
      obtain ⟨-, hassign, hval⟩ := hi
      refine ⟨Finset.mem_univ _, hassign, ?_⟩
      rw [preprocess_v_slab]; simpa using hval
    · intro x _ y _ hxy
      exact (slabRow_inj I hxy).2
  exact le_trans hcard (hσ p (slabCoord I 0 α))

/-! ## Clause (ii): canonical anchors `z_p ∈ B_p` for a YES `I∘` -/

/-- The anchor-canonicalised packing: keep `σ` on slab rows, but send every
anchor `z_p` to bin `p`.  Since anchors are all-zero, this changes no
coordinate count, so validity is preserved and now `z_p ∈ B_p`. -/
def canonAnchors (I : VBPInstance) (σ : Fin ((preprocess I).n) → Fin 4) :
    Fin ((preprocess I).n) → Fin 4 :=
  fun r => Sum.elim (fun _ : Fin 5 × Fin I.n => σ r) (fun p => p)
    ((preprocessRowEquiv I.n).symm r)

theorem canonAnchors_slabRow (I : VBPInstance) (σ) (t : Fin 5) (i : Fin I.n) :
    canonAnchors I σ (slabRow I t i) = σ (slabRow I t i) := by
  simp [canonAnchors, slabRow, Equiv.symm_apply_apply]

theorem canonAnchors_anchor (I : VBPInstance) (σ) (p : Fin 4) :
    canonAnchors I σ ((preprocess I).anchor p) = p := by
  show Sum.elim _ _ ((preprocessRowEquiv I.n).symm
    (preprocessRowEquiv I.n (Sum.inr p))) = p
  rw [Equiv.symm_apply_apply]; rfl

theorem preprocess_isYes_canonical (I : VBPInstance) (h : (preprocess I).IsYes) :
    ∃ σ : Fin ((preprocess I).n) → Fin 4,
      (∀ (p : Fin 4) (β : Fin ((preprocess I).d)),
        (Finset.univ.filter
          (fun r => σ r = p ∧ (preprocess I).v r β = true)).card ≤ 1) ∧
      (∀ p : Fin 4, σ ((preprocess I).anchor p) = p) := by
  classical
  obtain ⟨σ, hσ⟩ := h
  refine ⟨canonAnchors I σ, ?_, fun p => canonAnchors_anchor I σ p⟩
  intro p β
  -- The 1-valued rows are the same for `canonAnchors I σ` and `σ`, and on those
  -- rows the two assignments agree (they are slab rows).
  have hset : (Finset.univ.filter
        (fun r => canonAnchors I σ r = p ∧ (preprocess I).v r β = true))
      = (Finset.univ.filter (fun r => σ r = p ∧ (preprocess I).v r β = true)) := by
    apply Finset.filter_congr
    intro r _
    rcases preprocess_row_cases I r with ⟨t, i, rfl⟩ | ⟨q, rfl⟩
    · rw [canonAnchors_slabRow]
    · -- anchors are all-zero, so both predicates fail on the value side.
      rw [anchor_val_false]
      simp
  rw [hset]
  exact hσ p β

/-! ## Clause (iii): a NO `I` forces a bad bin+coordinate in every 4-partition -/

/-- Bridge: at a slab-`t` coordinate `slabCoord I t α`, the preprocess rows in
bin `p` that are `1` there are exactly the images under `slabRow I t` of the
source rows in bin `p` (under `σ ∘ slabRow I t`) that are `1` at `α`.  Hence
the two counts agree. -/
theorem slab_ones_card (I : VBPInstance) (σ : Fin ((preprocess I).n) → Fin 4)
    (t : Fin 5) (p : Fin 4) (α : Fin I.d) :
    (Finset.univ.filter (fun i : Fin I.n =>
        σ (slabRow I t i) = p ∧ I.v i α = true)).card
      = (Finset.univ.filter (fun r =>
          σ r = p ∧ (preprocess I).v r (slabCoord I t α) = true)).card := by
  classical
  -- The RHS filter set is the image of the LHS filter set under `slabRow I t`.
  have himg : (Finset.univ.filter (fun r =>
        σ r = p ∧ (preprocess I).v r (slabCoord I t α) = true))
      = (Finset.univ.filter (fun i : Fin I.n =>
          σ (slabRow I t i) = p ∧ I.v i α = true)).image (slabRow I t) := by
    ext r
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hassign, hval⟩
      rcases preprocess_row_cases I r with ⟨s, i, rfl⟩ | ⟨q, rfl⟩
      · -- slab row: 1 at slabCoord t α forces s = t (the `if` reads `t = s`).
        rw [preprocess_v_slab] at hval
        by_cases hst : s = t
        · subst hst
          rw [if_pos rfl] at hval
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hassign, hval⟩, rfl⟩
        · rw [if_neg (fun h => hst h.symm)] at hval; exact absurd hval (by simp)
      · rw [anchor_val_false] at hval; exact absurd hval (by simp)
    · rintro ⟨i, hi, rfl⟩
      rw [Finset.mem_filter] at hi
      obtain ⟨-, hassign, hval⟩ := hi
      refine ⟨Finset.mem_univ _, hassign, ?_⟩
      rw [preprocess_v_slab, if_pos rfl]; exact hval
  rw [himg, Finset.card_image_of_injective _ (fun x y hxy => (slabRow_inj I hxy).2)]

/-- A row that is NOT a slab-`t` copy is `0` at every slab-`t` coordinate. -/
theorem non_slab_t_zero (I : VBPInstance) (t : Fin 5) (α : Fin I.d)
    (r : Fin ((preprocess I).n)) (hr : ∀ i, r ≠ slabRow I t i) :
    (preprocess I).v r (slabCoord I t α) = false := by
  rcases preprocess_row_cases I r with ⟨s, i, rfl⟩ | ⟨q, rfl⟩
  · rw [preprocess_v_slab]
    by_cases hst : s = t
    · subst hst; exact absurd rfl (hr i)
    · rw [if_neg (fun h => hst h.symm)]
  · exact anchor_val_false I q _

/-- The three-clause zero-anchor preprocessing lemma, clause (iii). -/
theorem preprocess_no_bad_bin (I : VBPInstance) (hno : ¬ I.IsYes)
    (σ : Fin ((preprocess I).n) → Fin 4) :
    ∃ (p : Fin 4) (β : Fin ((preprocess I).d)),
      2 ≤ (Finset.univ.filter
            (fun r => σ r = p ∧ (preprocess I).v r β = true)).card ∧
      1 ≤ (Finset.univ.filter
            (fun r => σ r = p ∧ (preprocess I).v r β = false)).card := by
  classical
  by_contra hcon
  push Not at hcon
  -- hcon : ∀ p β, 2 ≤ ones → (zeros count) < 1, i.e. zeros = 0.
  -- For each slab t, σ∘slabRow t is not a YES-packing, so some (p,α) has ≥2 ones.
  have hslab : ∀ t : Fin 5, ∃ (p : Fin 4) (α : Fin I.d),
      2 ≤ (Finset.univ.filter (fun r =>
        σ r = p ∧ (preprocess I).v r (slabCoord I t α) = true)).card := by
    intro t
    -- σ_t := σ ∘ slabRow I t is not valid for I (I is NO).
    have hnotvalid : ¬ ∀ (p : Fin 4) (α : Fin I.d),
        (Finset.univ.filter (fun i => σ (slabRow I t i) = p ∧ I.v i α = true)).card ≤ 1 := by
      intro hv; exact hno ⟨fun i => σ (slabRow I t i), hv⟩
    push Not at hnotvalid
    obtain ⟨p, α, hpα⟩ := hnotvalid
    refine ⟨p, α, ?_⟩
    rw [← slab_ones_card]; omega
  -- For each slab t pick such a bin p_t and coord α_t; deduce bin p_t is all slab-t.
  choose pbin acoord hcount using hslab
  -- From hcon: since ones ≥ 2 at (p_t, slabCoord t α_t), the zero count is 0.
  have hzero : ∀ t : Fin 5, (Finset.univ.filter (fun r =>
      σ r = pbin t ∧ (preprocess I).v r (slabCoord I t (acoord t)) = false)).card = 0 := by
    intro t
    have := hcon (pbin t) (slabCoord I t (acoord t)) (hcount t)
    omega
  -- Hence every row in bin p_t at coord slabCoord t α_t must be a 1 there, so it
  -- is a slab-t copy: bin p_t contains only slab-t rows.
  have honly : ∀ t : Fin 5, ∀ r, σ r = pbin t → ∃ i, r = slabRow I t i := by
    intro t r hr
    by_contra hcontra
    push Not at hcontra
    -- r is not any slab-t copy, so it is 0 at slabCoord t (acoord t).
    have hval0 : (preprocess I).v r (slabCoord I t (acoord t)) = false :=
      non_slab_t_zero I t (acoord t) r hcontra
    -- Then r is in the (empty) zero filter set — contradiction.
    have hmem : r ∈ (Finset.univ.filter (fun r =>
        σ r = pbin t ∧ (preprocess I).v r (slabCoord I t (acoord t)) = false)) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ r, hr, hval0⟩
    rw [Finset.card_eq_zero.mp (hzero t)] at hmem
    exact absurd hmem (Finset.notMem_empty r)
  -- Each bin p_t is nonempty (it has ≥2 one-rows), giving a witness slab-t row.
  have hwit : ∀ t : Fin 5, ∃ i, σ (slabRow I t i) = pbin t := by
    intro t
    have hpos : 0 < (Finset.univ.filter (fun r =>
        σ r = pbin t ∧ (preprocess I).v r (slabCoord I t (acoord t)) = true)).card := by
      have := hcount t; omega
    obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hr
    obtain ⟨-, hassign, -⟩ := hr
    obtain ⟨i, rfl⟩ := honly t r hassign
    exact ⟨i, hassign⟩
  -- The map t ↦ pbin t is injective: distinct slabs land in distinct bins.
  have hinj : Function.Injective pbin := by
    intro t t' hpp
    by_contra hne
    -- witness slab-t row lies in bin pbin t = pbin t', so honly t' forces it slab-t'.
    obtain ⟨i, hi⟩ := hwit t
    have hin' : σ (slabRow I t i) = pbin t' := by rw [hi, hpp]
    obtain ⟨i', hi'⟩ := honly t' (slabRow I t i) hin'
    -- slabRow I t i = slabRow I t' i' ⟹ t = t', contradicting hne.
    exact hne (slabRow_inj I hi').1
  -- But `Fin 5 ↪ Fin 4` is impossible.
  have := Fintype.card_le_of_injective pbin hinj
  simp at this

/-! ## The registered lemma: three-clause zero-anchor preprocessing -/

-- CLAIM-BEGIN lem:zero-anchor-preprocessing
/-- Paper `lem:zero-anchor-preprocessing` (arXiv:2508.05597 §5): for a `c = 1`,
`m = 4` `{0,1}`-`d`-Dimension Vector Bin Packing instance `I`, the replicated
padded instance `I∘` (five disjoint-coordinate slab copies `ι_t(v_i)` plus four
zero anchors `z_1 = ⋯ = z_4 = 0^{5d}`), rendered here as the companion
`preprocess I`, satisfies:

1. **YES iff YES** — `I.IsYes ↔ (preprocess I).IsYes`.
2. **Canonical anchors** — whenever `I∘` is YES it has a feasible packing
   `σ : rows → Fin 4` (per-bin/per-coordinate load `≤ 1`) with each anchor in
   its own bin, `σ (z_p) = p` for every `p ∈ [4]`.
3. **NO ⟹ bad bin** — whenever `I` is a NO-instance (`¬ I.IsYes`), every
   4-partition `σ` of the rows of `I∘` has a bin `p` and a coordinate `β` with
   at least two rows carrying a `1` at `β` and at least one row carrying a `0`
   at `β` (the `ℓ ≥ 2` and neutral-slot presence at the SAME coordinate the
   final NoWasteLift contradiction consumes).

(The paper also says this preprocessing is computable in polynomial time. The
Lean theorem records the combinatorial specification above, not a machine or
running-time statement.) -/
theorem zero_anchor_preprocessing (I : VBPInstance) :
    (I.IsYes ↔ (preprocess I).IsYes) ∧
    (((preprocess I).IsYes) →
      ∃ σ : Fin ((preprocess I).n) → Fin 4,
        (∀ (p : Fin 4) (β : Fin ((preprocess I).d)),
          (Finset.univ.filter
            (fun r => σ r = p ∧ (preprocess I).v r β = true)).card ≤ 1) ∧
        (∀ p : Fin 4, σ ((preprocess I).anchor p) = p)) ∧
    ((¬ I.IsYes) →
      ∀ σ : Fin ((preprocess I).n) → Fin 4,
        ∃ (p : Fin 4) (β : Fin ((preprocess I).d)),
          2 ≤ (Finset.univ.filter
                (fun r => σ r = p ∧ (preprocess I).v r β = true)).card ∧
          1 ≤ (Finset.univ.filter
                (fun r => σ r = p ∧ (preprocess I).v r β = false)).card) :=
-- CLAIM-END lem:zero-anchor-preprocessing
  ⟨⟨preprocess_isYes_of_isYes I, isYes_of_preprocess_isYes I⟩,
   preprocess_isYes_canonical I,
   preprocess_no_bad_bin I⟩

-- CLAIM-BEGIN aux:vbp-wrapper-support
theorem preprocess_promise (I : VBPInstance) (hI : I.Promise) :
    (preprocess I).Promise := by
  classical
  intro beta
  set s : Fin 5 := ((preprocessCoordEquiv I.d).symm beta).1 with hs
  set alpha : Fin I.d := ((preprocessCoordEquiv I.d).symm beta).2 with halpha
  have hsub : (Finset.univ.filter
        (fun r => (preprocess I).v r beta = true))
      ⊆ (Finset.univ.filter (fun i => I.v i alpha = true)).image
          (slabRow I s) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨-, hval⟩ := hr
    rw [Finset.mem_image]
    rcases preprocess_row_cases I r with ⟨t, i, rfl⟩ | ⟨q, rfl⟩
    · rw [preprocess_v_slabRow] at hval
      by_cases hst : s = t
      · subst hst
        rw [if_pos rfl] at hval
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hval⟩, rfl⟩
      · rw [if_neg (by simpa [eq_comm] using hst)] at hval
        exact absurd hval (by simp)
    · rw [anchor_val_false] at hval
      exact absurd hval (by simp)
  calc (Finset.univ.filter
        (fun r => (preprocess I).v r beta = true)).card
      ≤ ((Finset.univ.filter (fun i => I.v i alpha = true)).image
          (slabRow I s)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun i => I.v i alpha = true)).card :=
          Finset.card_image_le
    _ ≤ 4 := hI alpha

theorem normalizeInstance_promise (dstar : Nat) (I : PreprocessedInstance)
    (hI : I.Promise) : (normalizeInstance dstar I).Promise := by
  classical
  intro beta
  rcases hbeta :
      (padCoordEquiv
        (le_trans (le_max_left I.d dstar) (le_ceilPowTwo _))).symm beta with
    alpha | gamma
  · simpa [normalizeInstance, hbeta] using hI alpha
  · have hempty : (Finset.univ.filter
        (fun i => (normalizeInstance dstar I).v i beta = true)) = ∅ := by
      ext i
      simp [normalizeInstance, hbeta]
    rw [hempty]
    norm_num

theorem normalizeInstance_feasible_of_feasible
    (dstar : Nat) (I : PreprocessedInstance) (sigma : Fin I.n -> Fin 4)
    (hfeas : forall p alpha,
      (Finset.univ.filter (fun i => sigma i = p ∧ I.v i alpha = true)).card ≤ 1) :
    forall p beta,
      (Finset.univ.filter
        (fun i => sigma i = p ∧
          (normalizeInstance dstar I).v i beta = true)).card ≤ 1 := by
  classical
  intro p beta
  rcases hbeta :
      (padCoordEquiv
        (le_trans (le_max_left I.d dstar) (le_ceilPowTwo _))).symm beta with
    alpha | gamma
  · simpa [normalizeInstance, hbeta] using hfeas p alpha
  · simp [normalizeInstance, hbeta]

theorem normalizeInstance_isYes_iff (dstar : Nat) (I : PreprocessedInstance) :
    I.IsYes ↔ (normalizeInstance dstar I).IsYes := by
  constructor
  · intro h
    obtain ⟨sigma, hsigma⟩ := h
    exact ⟨sigma, normalizeInstance_feasible_of_feasible dstar I sigma hsigma⟩
  · intro h
    obtain ⟨sigma, hsigma⟩ := h
    refine ⟨sigma, ?_⟩
    intro p alpha
    have h :=
      hsigma p
        (padCoordEquiv
          (le_trans (le_max_left I.d dstar) (le_ceilPowTwo _))
          (Sum.inl alpha))
    simpa [normalizeInstance, Equiv.symm_apply_apply] using h

theorem normalizeInstance_bad_bin_of_bad_bin
    (dstar : Nat) (I : PreprocessedInstance) (sigma : Fin I.n -> Fin 4) :
    (∃ p alpha,
      2 ≤ (Finset.univ.filter
        (fun i => sigma i = p ∧ I.v i alpha = true)).card ∧
      1 ≤ (Finset.univ.filter
        (fun i => sigma i = p ∧ I.v i alpha = false)).card) ->
    ∃ p beta,
      2 ≤ (Finset.univ.filter
        (fun i => sigma i = p ∧
          (normalizeInstance dstar I).v i beta = true)).card ∧
      1 ≤ (Finset.univ.filter
        (fun i => sigma i = p ∧
          (normalizeInstance dstar I).v i beta = false)).card := by
  intro h
  rcases h with ⟨p, alpha, htrue, hfalse⟩
  refine ⟨p,
    padCoordEquiv
      (le_trans (le_max_left I.d dstar) (le_ceilPowTwo _))
      (Sum.inl alpha), ?_, ?_⟩
  · simpa [normalizeInstance, Equiv.symm_apply_apply] using htrue
  · simpa [normalizeInstance, Equiv.symm_apply_apply] using hfalse

theorem not_isYes_of_not_promise (I : VBPInstance) :
    ¬ I.Promise -> ¬ I.IsYes := by
  classical
  intro hnp hyes
  obtain ⟨alpha, halpha⟩ : ∃ alpha : Fin I.d,
      4 < (Finset.univ.filter (fun i => I.v i alpha = true)).card := by
    simpa [VBPInstance.Promise] using hnp
  obtain ⟨sigma, hsigma⟩ := hyes
  let active : Finset (Fin I.n) :=
    Finset.univ.filter (fun i => I.v i alpha = true)
  have hfiber : forall p : Fin 4,
      (active.filter (fun i => sigma i = p)).card ≤ 1 := by
    intro p
    have hset : active.filter (fun i => sigma i = p)
        = Finset.univ.filter (fun i => sigma i = p ∧ I.v i alpha = true) := by
      ext i
      simp [active, and_comm]
    rw [hset]
    exact hsigma p alpha
  have hinj : Function.Injective (fun x : {i // i ∈ active} => sigma x.1) := by
    intro x y hxy
    apply Subtype.ext
    have hxmem : x.1 ∈ active.filter (fun i => sigma i = sigma x.1) := by
      rw [Finset.mem_filter]
      exact ⟨x.2, rfl⟩
    have hymem : y.1 ∈ active.filter (fun i => sigma i = sigma x.1) := by
      rw [Finset.mem_filter]
      exact ⟨y.2, hxy.symm⟩
    exact (Finset.card_le_one.mp (hfiber (sigma x.1)) x.1 hxmem y.1 hymem)
  have hcardSubtype :
      Fintype.card {i // i ∈ active} ≤ Fintype.card (Fin 4) :=
    Fintype.card_le_of_injective (fun x : {i // i ∈ active} => sigma x.1) hinj
  have hactive : active.card ≤ 4 := by
    simpa [active, Fintype.card_subtype] using hcardSubtype
  exact not_lt_of_ge hactive halpha
-- CLAIM-END aux:vbp-wrapper-support

end NPCC
