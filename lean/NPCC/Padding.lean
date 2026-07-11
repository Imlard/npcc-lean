import Mathlib
import NPCC.Complexity
import NPCC.VBP
import Workspace.ProofLemmas.SublemmaPrecompNoIncrease

/-!
# Square truth-table padding

The communication problem is conventionally encoded as a square Boolean
matrix whose two input sets both have power-of-two size. The reduction itself
produces a typed rectangular matrix. This module closes that representation
gap: duplicate rows and columns are added through surjective projections, and
the resulting pullback game has exactly the same deterministic communication
complexity.
-/

namespace NPCC

open Workspace.Types.CommComplexity

/-- Pulling a finite game back along surjections on both input sets preserves
deterministic communication complexity. One inequality simulates a protocol
for `f` on the larger input sets. For the reverse inequality, choose sections
of the two surjections and simulate a protocol for the pullback on the original
inputs. -/
theorem D_precomp_eq_of_surjective
    {A B A' B' Z : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (f : A -> B -> Z) (alpha : A' -> A) (beta : B' -> B)
    (halpha : Function.Surjective alpha) (hbeta : Function.Surjective beta) :
    D (fun a' b' => f (alpha a') (beta b')) = D f := by
  apply le_antisymm
  · exact Workspace.ProofLemmas.SublemmaPrecompNoIncrease f alpha beta
  · let sectionA : A -> A' := Function.surjInv halpha
    let sectionB : B -> B' := Function.surjInv hbeta
    have h := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
      (fun a' b' => f (alpha a') (beta b')) sectionA sectionB
    simpa [sectionA, sectionB, Function.surjInv_eq halpha,
      Function.surjInv_eq hbeta] using h

/-- A surjective projection from a sufficiently large finite interval onto a
nonempty finite type. Indices below `card A` enumerate `A`; the remaining
indices duplicate one default element. -/
noncomputable def padProjection (A : Type*) [Fintype A] [Nonempty A]
    {n : Nat} (_hcard : Fintype.card A <= n) : Fin n -> A :=
  fun i =>
    if hi : i.val < Fintype.card A then
      (Fintype.equivFin A).symm ⟨i.val, hi⟩
    else
      Classical.choice (inferInstance : Nonempty A)

/-- `padProjection` reaches every original input. -/
theorem padProjection_surjective (A : Type*) [Fintype A] [Nonempty A]
    {n : Nat} (hcard : Fintype.card A <= n) :
    Function.Surjective (padProjection A hcard) := by
  intro a
  let i0 : Fin (Fintype.card A) := Fintype.equivFin A a
  let i : Fin n := ⟨i0.val, lt_of_lt_of_le i0.isLt hcard⟩
  refine ⟨i, ?_⟩
  have hi : i.val < Fintype.card A := i0.isLt
  rw [padProjection, dif_pos hi]
  have hfin : (⟨i.val, hi⟩ : Fin (Fintype.card A)) = i0 := by
    apply Fin.ext
    rfl
  rw [hfin]
  exact (Fintype.equivFin A).symm_apply_apply a

/-- Common power-of-two side length used to square-pad a finite game. -/
def squarePadSize (A B : Type*) [Fintype A] [Fintype B] : Nat :=
  ceilPowTwo (max (Fintype.card A) (Fintype.card B))

theorem card_le_squarePadSize_left (A B : Type*) [Fintype A] [Fintype B] :
    Fintype.card A <= squarePadSize A B := by
  exact le_trans (Nat.le_max_left _ _) (le_ceilPowTwo _)

theorem card_le_squarePadSize_right (A B : Type*) [Fintype A] [Fintype B] :
    Fintype.card B <= squarePadSize A B := by
  exact le_trans (Nat.le_max_right _ _) (le_ceilPowTwo _)

/-- The square power-of-two truth-table padding of a typed finite game. -/
noncomputable def squarePad
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A -> B -> Bool) :
    Fin (squarePadSize A B) -> Fin (squarePadSize A B) -> Bool :=
  fun i j =>
    f (padProjection A (card_le_squarePadSize_left A B) i)
      (padProjection B (card_le_squarePadSize_right A B) j)

/-- Square padding does not change deterministic communication complexity. -/
theorem D_squarePad
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A -> B -> Bool) :
    D (squarePad f) = D f := by
  exact D_precomp_eq_of_surjective f
    (padProjection A (card_le_squarePadSize_left A B))
    (padProjection B (card_le_squarePadSize_right A B))
    (padProjection_surjective A (card_le_squarePadSize_left A B))
    (padProjection_surjective B (card_le_squarePadSize_right A B))

/-- The padded side length is literally a power of two. -/
theorem squarePadSize_eq_two_pow (A B : Type*) [Fintype A] [Fintype B] :
    ∃ k : Nat, squarePadSize A B = 2 ^ k := by
  exact ⟨Nat.clog 2 (max (Fintype.card A) (Fintype.card B)), rfl⟩

end NPCC
