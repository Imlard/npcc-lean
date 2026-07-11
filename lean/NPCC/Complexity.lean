import Mathlib
import NPCC.Defs
import Workspace.Types.CommComplexity
import Workspace.UpperBound

/-! # Typed communication-complexity layer
Typed family complexity over the artifact's polymorphic `D` (protocol-tree
depth, `Workspace.Types.CommComplexity`). The game-level bridge device
(`D_equiv_invariance`) and `D_subgame_le` live in this file below the defs. -/

namespace NPCC

open Workspace.Types.CommComplexity

-- CLAIM-BEGIN def:subgame
/-- Induced subgame of a two-party game `f : A → B → Bool` by extraction data
`(R, C)`: the game on the subtypes of the selected rows and columns,
`(a, c) ↦ f a c`. Typed analogue of the artifact's `extract`; with
`f = interlaceFun M p` and `(R, C) ∈ bracketGE X Y p x y` this realizes the
paper's "submatrix of the `p`-fold interlace". The subtype domains are
`Fintype` via `FinsetCoe`, so the artifact's polymorphic complexity `D`
applies directly. -/
def subgame {A B : Type*} (f : A → B → Bool) (R : Finset A) (C : Finset B) :
    {a // a ∈ R} → {c // c ∈ C} → Bool :=
  fun a c => f a.val c.val
-- CLAIM-END def:subgame

-- CLAIM-BEGIN def:Dfamily
/-- Family complexity `comp{Φ}` (paper §2 preamble: the minimum deterministic
communication complexity over a nonempty family of submatrices). For an
ambient game `f` and a family `Φ` of extraction-data pairs, this is the
infimum over members of the depth-complexity `D` of the induced subgame.
`sInf` on `ℕ` yields `0` for the empty family — the paper's convention makes
`Φ` nonempty at every use site (cf. `bracketGE.nonempty`). Instantiated at
`f = interlaceFun M p`, `Φ = bracketGE X Y p x y` this is the paper's
`comp⟨M,p,x,y⟩`. -/
noncomputable def Dfamily {A B : Type*} (f : A → B → Bool)
    (Φ : Set (Finset A × Finset B)) : ℕ :=
  sInf { d : ℕ | ∃ RC ∈ Φ, d = D (subgame f RC.1 RC.2) }
-- CLAIM-END def:Dfamily

/-! Helper section (unregistered, compiled): protocol transport. Provers add
`Protocol.reindex` / `Protocol.restrict` and their cost/eval lemmas here. -/

open Workspace.Types.Protocol

/-- Reindex a protocol along equivalences on both parties' input spaces:
transport each node predicate through the equivalences, preserving the tree
shape. `leaf` is unchanged; an Alice node `a : A → Bool` becomes
`fun x => a (e₁ x) : A' → Bool`, and analogously for Bob. -/
def Protocol.reindex {A B A' B' Z : Type*} (e₁ : A' ≃ A) (e₂ : B' ≃ B) :
    Protocol A B Z → Protocol A' B' Z
  | Protocol.leaf z => Protocol.leaf z
  | Protocol.aNode a l r =>
      Protocol.aNode (fun x => a (e₁ x)) (Protocol.reindex e₁ e₂ l) (Protocol.reindex e₁ e₂ r)
  | Protocol.bNode b l r =>
      Protocol.bNode (fun y => b (e₂ y)) (Protocol.reindex e₁ e₂ l) (Protocol.reindex e₁ e₂ r)

/-- Reindexing preserves the tree depth (cost): the transform changes only node
predicates, never the tree shape. -/
theorem Protocol.cost_reindex {A B A' B' Z : Type*} (e₁ : A' ≃ A) (e₂ : B' ≃ B)
    (P : Protocol A B Z) : (Protocol.reindex e₁ e₂ P).cost = P.cost := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr =>
      simp only [Protocol.reindex, Protocol.cost, ihl, ihr]
  | bNode b l r ihl ihr =>
      simp only [Protocol.reindex, Protocol.cost, ihl, ihr]

/-- Evaluating the reindexed protocol at `(x, y)` agrees with evaluating the
original at the transported point `(e₁ x, e₂ y)`. -/
theorem Protocol.eval_reindex {A B A' B' Z : Type*} (e₁ : A' ≃ A) (e₂ : B' ≃ B)
    (P : Protocol A B Z) (x : A') (y : B') :
    (Protocol.reindex e₁ e₂ P).eval x y = P.eval (e₁ x) (e₂ y) := by
  induction P generalizing x y with
  | leaf z => rfl
  | aNode a l r ihl ihr =>
      simp only [Protocol.reindex, Protocol.eval, ihl, ihr]
  | bNode b l r ihl ihr =>
      simp only [Protocol.reindex, Protocol.eval, ihl, ihr]

/-- Transport of the `Computes` relation: if `P` computes `f`, then its reindex
computes the reindexed function `fun a b => f (e₁ a) (e₂ b)`. -/
theorem Protocol.computes_reindex {A B A' B' Z : Type*} (e₁ : A' ≃ A) (e₂ : B' ≃ B)
    (P : Protocol A B Z) (f : A → B → Z) (h : P.Computes f) :
    (Protocol.reindex e₁ e₂ P).Computes (fun a b => f (e₁ a) (e₂ b)) := by
  intro x y
  rw [Protocol.eval_reindex]
  exact h (e₁ x) (e₂ y)

/-- The achievable-cost sets of `f` and its reindexing coincide: reindexing
along equivalences is a cost-preserving bijection on computing protocols. -/
theorem achievableCosts_reindex {A B A' B' Z : Type*}
    (f : A → B → Z) (e₁ : A' ≃ A) (e₂ : B' ≃ B) :
    AchievableCosts (fun a b => f (e₁ a) (e₂ b)) = AchievableCosts f := by
  apply Set.ext
  intro c
  constructor
  · rintro ⟨P, hcost, hcomp⟩
    refine ⟨Protocol.reindex e₁.symm e₂.symm P, ?_, ?_⟩
    · rw [Protocol.cost_reindex]; exact hcost
    · have := Protocol.computes_reindex e₁.symm e₂.symm P _ hcomp
      simpa only [Equiv.apply_symm_apply] using this
  · rintro ⟨P, hcost, hcomp⟩
    refine ⟨Protocol.reindex e₁ e₂ P, ?_, ?_⟩
    · rw [Protocol.cost_reindex]; exact hcost
    · exact Protocol.computes_reindex e₁ e₂ P f hcomp


/-! Helpers from the D_subgame_le prover (merge-safe suffixes). -/
/-! Helper section (unregistered, compiled): protocol transport. Provers add
`Protocol.reindex` / `Protocol.restrict` and their cost/eval lemmas here. -/

open Workspace.Types.Protocol

/-- Restrict a protocol on `A × B` to the subtypes of a row selection `R` and a
column selection `C`, precomposing every node predicate with the subtype
inclusion `Subtype.val`. The tree shape is preserved verbatim, hence so is the
cost. (Merge-safe helper name: `restrictSub`.) -/
def Protocol.restrictSub {A B Z : Type*} (R : Finset A) (C : Finset B) :
    Protocol A B Z → Protocol {a // a ∈ R} {c // c ∈ C} Z
  | Protocol.leaf z => Protocol.leaf z
  | Protocol.aNode a l r =>
      Protocol.aNode (fun x => a x.val) (Protocol.restrictSub R C l)
        (Protocol.restrictSub R C r)
  | Protocol.bNode b l r =>
      Protocol.bNode (fun y => b y.val) (Protocol.restrictSub R C l)
        (Protocol.restrictSub R C r)

/-- Restricting a protocol to selected rows/columns preserves its cost (tree
depth), since it preserves the tree shape node-for-node. -/
theorem Protocol.cost_restrictSub {A B Z : Type*} (R : Finset A) (C : Finset B)
    (P : Protocol A B Z) : (Protocol.restrictSub R C P).cost = P.cost := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr =>
      simp only [Protocol.restrictSub, Protocol.cost, ihl, ihr]
  | bNode b l r ihl ihr =>
      simp only [Protocol.restrictSub, Protocol.cost, ihl, ihr]

/-- The restricted protocol evaluates pointwise as the original protocol on the
underlying elements. -/
theorem Protocol.eval_restrictSub {A B Z : Type*} (R : Finset A) (C : Finset B)
    (P : Protocol A B Z) (a : {a // a ∈ R}) (c : {c // c ∈ C}) :
    (Protocol.restrictSub R C P).eval a c = P.eval a.val c.val := by
  induction P with
  | leaf z => rfl
  | aNode f l r ihl ihr =>
      simp only [Protocol.restrictSub, Protocol.eval]
      by_cases h : f a.val = true
      · rw [if_pos h, if_pos h, ihr]
      · rw [if_neg h, if_neg h, ihl]
  | bNode f l r ihl ihr =>
      simp only [Protocol.restrictSub, Protocol.eval]
      by_cases h : f c.val = true
      · rw [if_pos h, if_pos h, ihr]
      · rw [if_neg h, if_neg h, ihl]

/-- If `P` computes the ambient game `f`, its restriction computes the induced
subgame on the selected rows/columns. -/
theorem Protocol.computes_restrictSub {A B : Type*} (f : A → B → Bool)
    (R : Finset A) (C : Finset B) (P : Protocol A B Bool)
    (hP : Protocol.Computes P f) :
    Protocol.Computes (Protocol.restrictSub R C P) (subgame f R C) := by
  intro a c
  rw [Protocol.eval_restrictSub]
  exact hP a.val c.val

/-- Every cost achievable for `f` is achievable for its subgame: transport a
witnessing protocol through `restrictSub` (equal cost, computes the subgame). -/
theorem achievableCosts_subgame_subset {A B : Type*}
    (f : A → B → Bool) (R : Finset A) (C : Finset B) :
    AchievableCosts f ⊆ AchievableCosts (subgame f R C) := by
  rintro c ⟨P, hcost, hcomp⟩
  refine ⟨Protocol.restrictSub R C P, ?_, ?_⟩
  · rw [Protocol.cost_restrictSub]; exact hcost
  · exact Protocol.computes_restrictSub f R C P hcomp

-- CLAIM-BEGIN lem:D-equiv-invariance
/-- Deterministic communication complexity is invariant under reindexing both
inputs by equivalences: relabeling Alice's and Bob's input spaces changes
neither protocols (transport node predicates through the equivalences,
preserving tree shape, hence cost) nor computed functions. This is the
game-level bridge device: the reduction's "canonically identified with" steps
and the typed↔flattened complexity transfer both consume it. Output type `Z`
arbitrary (covers Bool and tuple-valued direct sums alike). -/
theorem D_equiv_invariance {A B A' B' Z : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (f : A → B → Z) (e₁ : A' ≃ A) (e₂ : B' ≃ B) :
    D (fun a b => f (e₁ a) (e₂ b)) = D f :=
-- CLAIM-END lem:D-equiv-invariance
  by
    unfold D
    exact congrArg sInf (achievableCosts_reindex f e₁ e₂)

-- CLAIM-BEGIN lem:D-subgame-le
/-- Subgames are easier, typed form: restricting a game to selected rows and
columns cannot increase its deterministic communication complexity (the same
protocol tree, with node predicates precomposed with the subtype inclusions,
computes the restriction at equal cost). Typed analogue of the artifact's
`subgames_are_easier`. -/
theorem D_subgame_le {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → Bool) (R : Finset A) (C : Finset B) :
    D (subgame f R C) ≤ D f :=
-- CLAIM-END lem:D-subgame-le
  by
  -- `D f = sInf (AchievableCosts f)`; the achievable set of `f` is nonempty,
  -- so its inf is attained, and every achievable cost of `f` is achievable
  -- for the subgame. Hence `sInf` of the (larger) subgame set is `≤` it.
  have hne : (AchievableCosts f).Nonempty :=
    Workspace.UpperBound.AchievableCosts_nonempty f
  have hmem : D f ∈ AchievableCosts f := by
    have := Nat.sInf_mem hne
    simpa [D] using this
  have hmem' : D f ∈ AchievableCosts (subgame f R C) :=
    achievableCosts_subgame_subset f R C hmem
  have := Nat.sInf_le hmem'
  simpa [D] using this

end NPCC
