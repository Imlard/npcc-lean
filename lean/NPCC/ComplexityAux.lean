import Mathlib
import NPCC.Complexity

/-! # Communication-complexity regression lemmas -/

namespace NPCC

open Workspace.Types.CommComplexity

-- CLAIM-BEGIN aux:Dfamily-singleton
/-- Family complexity of a singleton family collapses to the depth-complexity
of the single induced subgame: `comp{RC} = D (subgame f R C)`. The existential
membership constraint `∃ RC' ∈ {RC}, d = D (subgame f RC'.1 RC'.2)` forces
`RC' = RC`, so the index set is the singleton `{D (subgame f RC.1 RC.2)}` and
`sInf` of a singleton returns its element. -/
theorem Dfamily.singleton {A B : Type*} (f : A → B → Bool) (RC : Finset A × Finset B) :
    Dfamily f {RC} = D (subgame f RC.1 RC.2) :=
-- CLAIM-END aux:Dfamily-singleton
  by
  unfold Dfamily
  have hset :
      { d : ℕ | ∃ RC' ∈ ({RC} : Set (Finset A × Finset B)),
          d = D (subgame f RC'.1 RC'.2) }
        = {D (subgame f RC.1 RC.2)} := by
    ext d
    constructor
    · rintro ⟨RC', hRC', rfl⟩
      rw [Set.mem_singleton_iff] at hRC'
      subst hRC'
      rfl
    · intro hd
      rw [Set.mem_singleton_iff] at hd
      exact ⟨RC, Set.mem_singleton RC, hd⟩
  rw [hset, csInf_singleton]

-- CLAIM-BEGIN aux:Dfamily-anti-mono
/-- Unit test for `Dfamily`: family complexity is antitone in the family `Φ`.
Enlarging the family of extraction-data pairs can only make the minimum
depth-complexity smaller (more submatrices to choose from). Formally, for
`Φ₁ ⊆ Φ₂` with `Φ₁` nonempty, `Dfamily f Φ₂ ≤ Dfamily f Φ₁`. The cost-set of
`Φ₁` is a nonempty subset of the cost-set of `Φ₂` (each `∃`-witness in `Φ₁`
sits in `Φ₂` via `hsub`), so `Nat.sInf` is antitone: `sInf S₂ ≤ sInf S₁`. The
nonemptiness of `Φ₁` guarantees `sInf S₁` is actually attained (`Nat.sInf_mem`),
placing it inside `S₂` where `Nat.sInf_le` applies. -/
theorem Dfamily.anti_mono {A B : Type*} (f : A → B → Bool)
    {Φ₁ Φ₂ : Set (Finset A × Finset B)} (hsub : Φ₁ ⊆ Φ₂) (hne : Φ₁.Nonempty) :
    Dfamily f Φ₂ ≤ Dfamily f Φ₁ :=
-- CLAIM-END aux:Dfamily-anti-mono
  by
  -- Cost-sets of the two families.
  set S₁ : Set ℕ := { d : ℕ | ∃ RC ∈ Φ₁, d = D (subgame f RC.1 RC.2) } with hS₁
  set S₂ : Set ℕ := { d : ℕ | ∃ RC ∈ Φ₂, d = D (subgame f RC.1 RC.2) } with hS₂
  -- `S₁ ⊆ S₂`: an existence witness in `Φ₁` is also a witness in `Φ₂`.
  have hSsub : S₁ ⊆ S₂ := by
    intro d hd
    obtain ⟨RC, hRC, hdeq⟩ := hd
    exact ⟨RC, hsub hRC, hdeq⟩
  -- `S₁` is nonempty: pick any member of `Φ₁` and read off its cost.
  have hS₁ne : S₁.Nonempty := by
    obtain ⟨RC, hRC⟩ := hne
    exact ⟨D (subgame f RC.1 RC.2), RC, hRC, rfl⟩
  -- `sInf S₁ ∈ S₁` (attained since `S₁` nonempty), hence `sInf S₁ ∈ S₂`.
  have hmem : sInf S₁ ∈ S₂ := hSsub (Nat.sInf_mem hS₁ne)
  -- `sInf S₂ ≤ sInf S₁` by the lower-bound property of `sInf` on `ℕ`.
  have : sInf S₂ ≤ sInf S₁ := Nat.sInf_le hmem
  simpa only [Dfamily, hS₁, hS₂] using this

end NPCC
