import Mathlib
import NPCC.Defs
import NPCC.Relaxed
import NPCC.Complexity
import Workspace.Types.CommComplexity
import Workspace.Types.Interlace
import Workspace.UpperBound

/-! # Protocol upper bounds and game isomorphisms

Two layers:

1. **GameIso:** a bundled isomorphism of two-party games, its
   `D`-invariance (via the proved `NPCC.D_equiv_invariance`), transport of
   `bracketGE` membership and of induced subgames, and the congruence
   constructors the stage lemmas consume (transpose, `interlaceFun`,
   `relaxedInterlace`, sum-attachment of extra rows). This is the typed
   rendering of the paper's "canonically identified with" steps.

2. **Protocol constructions:** the row-identification
   protocol and the announce-then-subprotocol composition bound, both built on
   the artifact's `announceTree` machinery through
   `Workspace.UpperBound.D_le_announce`. -/

namespace NPCC

open Workspace.Types.CommComplexity
open Workspace.Types.Protocol
open Workspace.Types.Interlace

/-! ## GameIso: bundled isomorphism of two-party games -/

/-- An isomorphism of two-party games `f : X → Y → Bool` and
`f' : X' → Y' → Bool`: equivalences of the two input spaces that carry the
value of `f` to the value of `f'` pointwise. This is the typed vehicle for the
paper's "canonically identified with" steps; deterministic communication
complexity is invariant along it (`GameIso.D_eq`). -/
structure GameIso {X Y X' Y' : Type*} (f : X → Y → Bool) (f' : X' → Y' → Bool) where
  /-- Equivalence of the row (Alice) input spaces. -/
  eX : X ≃ X'
  /-- Equivalence of the column (Bob) input spaces. -/
  eY : Y ≃ Y'
  /-- The equivalences transport values: `f x y = f' (eX x) (eY y)`. -/
  hval : ∀ x y, f x y = f' (eX x) (eY y)

namespace GameIso

variable {X Y X' Y' X'' Y'' : Type*}

/-- Every game is isomorphic to itself. -/
def refl (f : X → Y → Bool) : GameIso f f :=
  ⟨Equiv.refl X, Equiv.refl Y, fun _ _ => rfl⟩

/-- Game isomorphism is symmetric. -/
def symm {f : X → Y → Bool} {f' : X' → Y' → Bool} (h : GameIso f f') :
    GameIso f' f where
  eX := h.eX.symm
  eY := h.eY.symm
  hval := fun x' y' => by
    rw [h.hval (h.eX.symm x') (h.eY.symm y'), h.eX.apply_symm_apply,
      h.eY.apply_symm_apply]

/-- Game isomorphism is transitive. -/
def trans {f : X → Y → Bool} {f' : X' → Y' → Bool} {f'' : X'' → Y'' → Bool}
    (h₁ : GameIso f f') (h₂ : GameIso f' f'') : GameIso f f'' where
  eX := h₁.eX.trans h₂.eX
  eY := h₁.eY.trans h₂.eY
  hval := fun x y => by
    rw [Equiv.trans_apply, Equiv.trans_apply, h₁.hval, h₂.hval]

/-- Deterministic communication complexity is invariant along a game
isomorphism (the game-level bridge device `D_equiv_invariance`, packaged). -/
theorem D_eq [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    {f : X → Y → Bool} {f' : X' → Y' → Bool} (h : GameIso f f') :
    D f = D f' := by
  have hfun : f = fun x y => f' (h.eX x) (h.eY y) :=
    funext fun x => funext fun y => h.hval x y
  rw [hfun]
  exact D_equiv_invariance f' h.eX h.eY

/-- Transpose congruence: an isomorphism of games induces an isomorphism of
the transposed games (swap the two parties; the artifact's protocol-transpose
`Workspace.UpperBound.D_swap` supplies the matching `D`-invariance). -/
def transpose {f : X → Y → Bool} {f' : X' → Y' → Bool} (h : GameIso f f') :
    GameIso (fun y x => f x y) (fun y' x' => f' x' y') where
  eX := h.eY
  eY := h.eX
  hval := fun y x => h.hval x y

/-- The induced equivalence on `p`-fold interlace rows `Fin p × X`. -/
def rowsEquiv {f : X → Y → Bool} {f' : X' → Y' → Bool} (h : GameIso f f')
    (p : ℕ) : (Fin p × X) ≃ (Fin p × X') :=
  (Equiv.refl (Fin p)).prodCongr h.eX

/-- The induced equivalence on `p`-fold interlace columns `Fin p → Y`. -/
def colsEquiv {f : X → Y → Bool} {f' : X' → Y' → Bool} (h : GameIso f f')
    (p : ℕ) : (Fin p → Y) ≃ (Fin p → Y') :=
  (Equiv.refl (Fin p)).arrowCongr h.eY

/-- Interlace congruence: an isomorphism of base games lifts to an isomorphism
of their `p`-fold interlaces, with rows and columns mapped by the induced
equivalences. -/
def interlaceCongr {f : X → Y → Bool} {f' : X' → Y' → Bool} (h : GameIso f f')
    (p : ℕ) : GameIso (interlaceFun f p) (interlaceFun f' p) where
  eX := h.rowsEquiv p
  eY := h.colsEquiv p
  hval := fun a c => by
    show f a.2 (c a.1) = f' (h.eX a.2) (h.eY (c a.1))
    exact h.hval a.2 (c a.1)

/-- Relaxed-interlace congruence: an isomorphism of base games together with a
reindexing of the coordinate set and of the column family (compatible with the
value equivalence) lifts to an isomorphism of the relaxed interlaces. -/
def relaxedInterlaceCongr {f : X → Y → Bool} {f' : X' → Y' → Bool}
    (h : GameIso f f') {q q' L L' : ℕ} (eQ : Fin q ≃ Fin q') (eL : Fin L ≃ Fin L')
    {S : Fin L → Fin q → Y} {S' : Fin L' → Fin q' → Y'}
    (hS : ∀ j i, S' (eL j) (eQ i) = h.eY (S j i)) :
    GameIso (relaxedInterlace f S) (relaxedInterlace f' S') where
  eX := eQ.prodCongr h.eX
  eY := eL
  hval := fun a j => by
    show f a.2 (S j a.1) = f' (h.eX a.2) (S' (eL j) (eQ a.1))
    rw [hS j a.1]
    exact h.hval a.2 (S j a.1)

/-- Sum-attachment congruence (the Stage-4 `R₄ = R₃ ∪ [n]` shape): attaching
extra rows `v : Z → Y → Bool` to a game `f` on the same columns is congruent
along an isomorphism of `f` plus a compatible equivalence of the attached row
sets. The column equivalence of the result is the one of the base isomorphism. -/
def sumAttachCongr {Z Z' : Type*} {f : X → Y → Bool} {f' : X' → Y' → Bool}
    (h : GameIso f f') {v : Z → Y → Bool} {v' : Z' → Y' → Bool} (eZ : Z ≃ Z')
    (hv : ∀ z y, v z y = v' (eZ z) (h.eY y)) :
    GameIso (fun (s : X ⊕ Z) (y : Y) => Sum.elim (fun x => f x y) (fun z => v z y) s)
      (fun (s : X' ⊕ Z') (y : Y') => Sum.elim (fun x => f' x y) (fun z => v' z y) s) where
  eX := h.eX.sumCongr eZ
  eY := h.eY
  hval := fun s y => by
    cases s with
    | inl x =>
        show f x y = f' (h.eX x) (h.eY y)
        exact h.hval x y
    | inr z =>
        show v z y = v' (eZ z) (h.eY y)
        exact hv z y

/-- Subgame congruence: an isomorphism of ambient games restricts to an
isomorphism of the induced subgames, with the selected rows and columns mapped
by the bundled equivalences. Together with `GameIso.D_eq` this transports
`D (subgame · · ·)` facts across "canonically identified" games. -/
def subgameCongr {f : X → Y → Bool} {f' : X' → Y' → Bool} (h : GameIso f f')
    (R : Finset X) (C : Finset Y) :
    GameIso (subgame f R C)
      (subgame f' (R.map h.eX.toEmbedding) (C.map h.eY.toEmbedding)) where
  eX := h.eX.subtypeEquiv fun _ => (Finset.mem_map' h.eX.toEmbedding).symm
  eY := h.eY.subtypeEquiv fun _ => (Finset.mem_map' h.eY.toEmbedding).symm
  hval := fun a c => h.hval a.val c.val

/-- Transport of `bracketGE` membership along a game isomorphism: mapping the
extraction data by the induced row/column equivalences of the `p`-fold
interlace preserves membership in the bracket family (the two thresholds only
see the cardinalities of `X` and `Y`, which the equivalences preserve). -/
theorem bracketGE_map [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    {f : X → Y → Bool} {f' : X' → Y' → Bool} (h : GameIso f f')
    {p : ℕ} {x y : ℝ} {RC : Finset (Fin p × X) × Finset (Fin p → Y)}
    (hRC : RC ∈ bracketGE X Y p x y) :
    (RC.1.map (h.rowsEquiv p).toEmbedding, RC.2.map (h.colsEquiv p).toEmbedding)
      ∈ bracketGE X' Y' p x y := by
  classical
  obtain ⟨hrow, hcol⟩ := hRC
  refine ⟨?_, ?_⟩
  · -- row condition: the induced row map preserves first components, so each
    -- fiber of the mapped row set is the (injective) image of the old fiber.
    intro qb _hqb
    have hXcard : Fintype.card X' = Fintype.card X :=
      (Fintype.card_congr h.eX).symm
    have hfil : (RC.1.map (h.rowsEquiv p).toEmbedding).filter (fun r => r.1 = qb)
        = (RC.1.filter (fun r => r.1 = qb)).map (h.rowsEquiv p).toEmbedding := by
      rw [Finset.filter_map]
      -- the induced row map fixes first components, so the two filter
      -- predicates agree definitionally
      congr 1
    rw [hfil, Finset.card_map, hXcard]
    exact hrow qb (Finset.mem_univ qb)
  · -- column condition: `map` preserves the cardinality.
    rw [Finset.card_map]
    have hYcard : Fintype.card Y' = Fintype.card Y :=
      (Fintype.card_congr h.eY).symm
    rw [hYcard]
    exact hcol

end GameIso

/-! ## Upper-bound lemmas (`aux:upper-row-id`, `aux:upper-partition`) -/

/-- One-row games cost at most one bit: Bob announces the value
(`bNode β (leaf false) (leaf true)`). Helper for the `a + 1` row-type bound. -/
theorem D_le_one_of_unit_row {B : Type*} [Fintype B] (β : B → Bool) :
    D (fun (_ : Unit) (y : B) => β y) ≤ 1 := by
  have hmem : (1 : ℕ) ∈ AchievableCosts (fun (_ : Unit) (y : B) => β y) := by
    refine ⟨Protocol.bNode β (Protocol.leaf false) (Protocol.leaf true), rfl, ?_⟩
    intro _x y
    cases hb : β y <;> simp [Protocol.eval, hb]
  exact Nat.sInf_le hmem

-- CLAIM-BEGIN aux:upper-row-id
/-- Row-identification upper bound (the reduction's "direct protocol"; no
paper label). If the rows of `g : A → B → Bool` factor through at most `2 ^ a`
distinct row behaviours — a row-type map `τ : A → Fin (2 ^ a)` and a table
`ρ : Fin (2 ^ a) → B → Bool` of class behaviours with `g x y = ρ (τ x) y` —
and each class behaviour, viewed as the one-row game
`fun (_ : Unit) y => ρ k y`, admits a protocol of depth at most `c`, then
`D g ≤ a + c`: Alice announces the `a` bits of her row type, then the parties
run the class subprotocol. The ledger's `a + 1` headline is the `c = 1`
instance (Bob answers the single bit), `comp_le_of_row_types_succ`. -/
theorem comp_le_of_row_types {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B → Bool) (a c : ℕ) (τ : A → Fin (2 ^ a)) (ρ : Fin (2 ^ a) → B → Bool)
    (hτ : ∀ x y, g x y = ρ (τ x) y)
    (hρ : ∀ k, D (fun (_ : Unit) (y : B) => ρ k y) ≤ c) :
    D g ≤ a + c :=
-- CLAIM-END aux:upper-row-id
  by
  classical
  -- Realize each class bound by a protocol, pulled back from `Unit` to `A`.
  have hex : ∀ k : Fin (2 ^ a), ∃ P : Protocol A B Bool,
      P.cost ≤ c ∧ ∀ x y, P.eval x y = ρ k y := by
    intro k
    have hne : (AchievableCosts (fun (_ : Unit) (y : B) => ρ k y)).Nonempty :=
      Workspace.UpperBound.AchievableCosts_nonempty _
    have hmem : D (fun (_ : Unit) (y : B) => ρ k y)
        ∈ AchievableCosts (fun (_ : Unit) (y : B) => ρ k y) := by
      have := Nat.sInf_mem hne
      simpa [D] using this
    obtain ⟨Pk, hcost, hcomp⟩ := hmem
    refine ⟨Workspace.UpperBound.Protocol.comap (fun _ : A => ()) (fun y : B => y) Pk,
      ?_, ?_⟩
    · rw [Workspace.UpperBound.Protocol.comap_cost, hcost]
      exact hρ k
    · intro x y
      rw [Workspace.UpperBound.Protocol.comap_eval]
      exact hcomp () y
  choose P hPcost hPeval using hex
  refine Workspace.UpperBound.D_le_announce g (Fin (2 ^ a)) τ P a c ?_ ?_ hPcost
  · simp
  · intro k x y hk
    rw [hPeval k x y, hτ x y, hk]

/-- The ledger's `a + 1` headline instance of `comp_le_of_row_types`: a game
whose rows factor through at most `2 ^ a` distinct row behaviours has
`D g ≤ a + 1` (Alice names her row class, Bob answers the bit). -/
theorem comp_le_of_row_types_succ {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B → Bool) (a : ℕ) (τ : A → Fin (2 ^ a))
    (hτ : ∀ x₁ x₂, τ x₁ = τ x₂ → g x₁ = g x₂) :
    D g ≤ a + 1 := by
  classical
  refine comp_le_of_row_types g a 1 τ
    (fun k => if h : ∃ x, τ x = k then g h.choose else fun _ => false) ?_ ?_
  · intro x y
    have hex : ∃ x', τ x' = τ x := ⟨x, rfl⟩
    simp only [dif_pos hex]
    rw [hτ hex.choose x hex.choose_spec]
  · intro k
    exact D_le_one_of_unit_row _

-- CLAIM-BEGIN aux:upper-partition
/-- Partition composition upper bound, row side (no paper label). If the rows
of `g : A → B → Bool` split into `2 ^ s` classes via `σ : A → Fin (2 ^ s)` and
every class-submatrix — the game restricted to the rows of one class, all
columns kept — admits a protocol of depth at most `c`, then `D g ≤ s + c`: an
`s`-deep Alice announce tree names the class and the class subprotocol runs at
its leaves. The column-side twin (Bob announces) is `comp_le_partition_cols`. -/
theorem comp_le_partition {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B → Bool) (s c : ℕ) (σ : A → Fin (2 ^ s))
    (hc : ∀ k : Fin (2 ^ s), D (fun (x : {x : A // σ x = k}) (y : B) => g x.val y) ≤ c) :
    D g ≤ s + c :=
-- CLAIM-END aux:upper-partition
  by
  classical
  -- For each class, a protocol on all of `A × B` correct on that class.
  have hex : ∀ k : Fin (2 ^ s), ∃ P : Protocol A B Bool,
      P.cost ≤ c ∧ ∀ x y, σ x = k → P.eval x y = g x y := by
    intro k
    by_cases hk : ∃ x₀, σ x₀ = k
    · obtain ⟨x₀, hx₀⟩ := hk
      have hne : (AchievableCosts
          (fun (x : {x : A // σ x = k}) (y : B) => g x.val y)).Nonempty :=
        Workspace.UpperBound.AchievableCosts_nonempty _
      have hmem : D (fun (x : {x : A // σ x = k}) (y : B) => g x.val y)
          ∈ AchievableCosts (fun (x : {x : A // σ x = k}) (y : B) => g x.val y) := by
        have := Nat.sInf_mem hne
        simpa [D] using this
      obtain ⟨Pk, hcost, hcomp⟩ := hmem
      refine ⟨Workspace.UpperBound.Protocol.comap
          (fun x : A => if h : σ x = k then (⟨x, h⟩ : {x : A // σ x = k}) else ⟨x₀, hx₀⟩)
          (fun y : B => y) Pk, ?_, ?_⟩
      · rw [Workspace.UpperBound.Protocol.comap_cost, hcost]
        exact hc k
      · intro x y hxk
        rw [Workspace.UpperBound.Protocol.comap_eval, dif_pos hxk]
        exact hcomp ⟨x, hxk⟩ y
    · exact ⟨Protocol.leaf false, Nat.zero_le c, fun x _y hxk => absurd ⟨x, hxk⟩ hk⟩
  choose P hPcost hPeval using hex
  refine Workspace.UpperBound.D_le_announce g (Fin (2 ^ s)) σ P s c ?_ hPeval hPcost
  simp

/-- Partition composition upper bound, column side: if the columns of `g`
split into `2 ^ s` classes via `σ : B → Fin (2 ^ s)` and every class-submatrix
(all rows, the columns of one class) admits a protocol of depth at most `c`,
then `D g ≤ s + c` — Bob announces his class; formally by transposing
(`Workspace.UpperBound.D_swap`) and applying the row side. -/
theorem comp_le_partition_cols {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B → Bool) (s c : ℕ) (σ : B → Fin (2 ^ s))
    (hc : ∀ k : Fin (2 ^ s), D (fun (x : A) (y : {y : B // σ y = k}) => g x y.val) ≤ c) :
    D g ≤ s + c := by
  rw [Workspace.UpperBound.D_swap g]
  refine comp_le_partition (fun y x => g x y) s c σ (fun k => ?_)
  show D (fun (y : {y : B // σ y = k}) (x : A) => g x y.val) ≤ c
  exact (Workspace.UpperBound.D_swap
    (fun (x : A) (y : {y : B // σ y = k}) => g x y.val)).symm.trans_le (hc k)

-- CLAIM-BEGIN lem:transposeComp
/-- Transpose symmetry (paper `lem:transposeComp`, arXiv:2508.05597 §2):
for every Boolean matrix `M`, `comp(Mᵀ) = comp(M)`. Under the depth
convention `comp = D` (the paper's deterministic communication complexity is
the artifact's protocol-tree depth `D`), a Boolean matrix is its game
`M : X → Y → Bool` and its transpose `Mᵀ` is the party-swapped game
`fun y x => M x y`; the equality is `D` of a game equals `D` of its swap.
Vehicle: the artifact's protocol-transpose bijection on achievable costs
(`Workspace.UpperBound.D_swap`), repackaged so the two orientations agree as
`GameIso.transpose` would apply. -/
theorem comp_transpose {X Y : Type*} [Fintype X] [Fintype Y] (M : X → Y → Bool) :
    D (fun y x => M x y) = D M :=
-- CLAIM-END lem:transposeComp
  (Workspace.UpperBound.D_swap M).symm

end NPCC
