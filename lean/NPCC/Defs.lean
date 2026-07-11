import Mathlib

/-! # Paper-facing definitions

The native definitions use typed indices such as `Finset (ι × X)`, with fibers
taken by the first component. The reused `Workspace` library uses flattened
natural-number blocks; `NPCC.Bridge` and `NPCC.Twin` prove the row, column, and
communication-value correspondences between the two representations. -/

namespace NPCC

-- CLAIM-BEGIN def:equipartition-ge
/-- Paper `def:equipartition` ((Q,T)-Equipartitioned Row Set), `≥`-form, typed.

The paper's row set `R ⊆ [k] × X` (X a finite set) is a `Finset (ι × X)` over
an index type `ι` playing the role of `[k]` (the paper's `k` only scopes `Q`;
taking an arbitrary index type is the standard faithful generalization, and
`X` may be any type since `R : Finset _` already makes the engaged rows
finite). The paper's slice `R_q = {x ∈ X : (q,x) ∈ R}` is the fiber of `R`
over first component `q`; filtering pairs with `p.1 = q` counts exactly
`|R_q|` (the first component is fixed, so pairs biject with their second
components). `R` is `(Q,T)`-equipartitioned iff every `q ∈ Q` has fiber of
size at least `T`. The paper's side conditions `T ≥ 1` and `Q ⊆ [k]` are
hypotheses at use sites, not baked into the predicate. -/
def IsEquipartitionedGE {ι X : Type*} [DecidableEq ι]
    (R : Finset (ι × X)) (Q : Finset ι) (T : ℕ) : Prop :=
  ∀ q ∈ Q, T ≤ (R.filter (fun p => p.1 = q)).card
-- CLAIM-END def:equipartition-ge

-- CLAIM-BEGIN def:bracket-ge
/-- Paper `def:bracket` (Bracket family `⟨M,p,x,y⟩`), `≥`-form, typed.

For an `m × n` matrix `M : X → Y → Bool` (`m = Fintype.card X`,
`n = Fintype.card Y`) the `p`-fold interlace has rows `Fin p × X` and columns
`Fin p → Y` (the paper's `Y^p`); cf. `Workspace.Types.Interlace.interlaceFun`.
A member of the bracket family is recorded by its extraction data: the pair
`(R, C)` of a row subset and a column subset of the interlace. The paper's
two conditions: the row set is `([p], T)`-equipartitioned with `T = ⌈m·x⌉`
(here `IsEquipartitionedGE` over `Q = Finset.univ`), and the column set has
size at least `S = ⌈n^p·y⌉` (note `Fintype.card (Fin p → Y) = n^p`). The
submatrix itself is the subgame of `interlaceFun M p` induced by `(R, C)`,
and the family complexity `comp ⟨M,p,x,y⟩ = min` over members is a
downstream definition; the family itself depends only on the row/column
TYPES of `M`, not its entries — matching the paper, whose two conditions
constrain only the extracted row and column sets. Side conditions `p ≥ 1`,
`0 < x, y ≤ 1` are use-site hypotheses. -/
def bracketGE (X Y : Type*) [Fintype X] [Fintype Y] (p : ℕ) (x y : ℝ) :
    Set (Finset (Fin p × X) × Finset (Fin p → Y)) :=
  { RC | IsEquipartitionedGE RC.1 (Finset.univ : Finset (Fin p))
           ⌈(Fintype.card X : ℝ) * x⌉₊
         ∧ ⌈((Fintype.card Y : ℝ) ^ p) * y⌉₊ ≤ RC.2.card }
-- CLAIM-END def:bracket-ge

end NPCC
