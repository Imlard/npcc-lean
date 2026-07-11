import Mathlib
import NPCC.Defs

/-! # Definition laws

Small lemmas record the monotonicity, nonemptiness, and boundary behavior of
the paper-facing definitions. They serve as regression tests and as reusable
facts for later proofs. -/

namespace NPCC

-- CLAIM-BEGIN aux:equipartition-mono-T
/-- Unit test for `IsEquipartitionedGE`: the equipartition fiber-size threshold is
antitone in the target `T`. If every fiber over `Q` has size at least `T`, then in
particular every such fiber has size at least any `T2 ≤ T`. This verifies that
`IsEquipartitionedGE R Q T` is a monotone (downward-closed) family in `T`, matching
the paper's use where lowering the required per-part count preserves the property. -/
theorem IsEquipartitionedGE.mono_T {ι X : Type*} [DecidableEq ι]
    {R : Finset (ι × X)} {Q : Finset ι} {T T2 : ℕ}
    (h : IsEquipartitionedGE R Q T) (hT : T2 ≤ T) :
    IsEquipartitionedGE R Q T2 :=
-- CLAIM-END aux:equipartition-mono-T
  by
  intro q hq
  exact le_trans hT (h q hq)

-- CLAIM-BEGIN aux:equipartition-subset-Q
/-- Unit test for `IsEquipartitionedGE`: the predicate is antitone in its index
set `Q`. If a row set `R` is `(Q, T)`-equipartitioned (every `q ∈ Q` has fiber
of size at least `T`) and `Q2 ⊆ Q`, then `R` is also `(Q2, T)`-equipartitioned,
since every `q ∈ Q2` is in `Q` and hence inherits the fiber-size bound. This
verifies that shrinking the index set never invalidates the equipartition
property — a sanity check on the `∀ q ∈ Q` binder shape. -/
theorem IsEquipartitionedGE.mono_Q {ι X : Type*} [DecidableEq ι]
    {R : Finset (ι × X)} {Q Q2 : Finset ι} {T : ℕ}
    (h : IsEquipartitionedGE R Q T) (hsub : Q2 ⊆ Q) :
    IsEquipartitionedGE R Q2 T :=
-- CLAIM-END aux:equipartition-subset-Q
  by
  intro q hq
  exact h q (hsub hq)

-- CLAIM-BEGIN aux:equipartition-full
/-- Unit test for `IsEquipartitionedGE`: the full row set `Finset.univ` over a
finite index type `ι` and finite payload type `X` is `(Q, T)`-equipartitioned for
every `Q` and every threshold `T ≤ Fintype.card X`. The point is that the fiber of
`univ` over any first component `q` bijects with `X` (the second component ranges
freely), so it has exactly `Fintype.card X` elements; the threshold hypothesis then
gives the required lower bound uniformly over `Q`. -/
theorem IsEquipartitionedGE.univ {ι X : Type*} [DecidableEq ι] [Fintype ι]
    [Fintype X] (Q : Finset ι) (T : ℕ) (hT : T ≤ Fintype.card X) :
    IsEquipartitionedGE (Finset.univ : Finset (ι × X)) Q T :=
-- CLAIM-END aux:equipartition-full
  by
  intro q _hq
  have hfilter :
      (Finset.univ : Finset (ι × X)).filter (fun p => p.1 = q)
        = ({q} : Finset ι) ×ˢ (Finset.univ : Finset X) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true]
  rw [hfilter, Finset.card_product, Finset.card_singleton, Finset.card_univ, one_mul]
  exact hT

-- CLAIM-BEGIN aux:bracket-top
/-- Unit test for `bracketGE`: the full pair `(univ, univ)` is a member of the
`x = y = 1` bracket. This checks the two membership conditions at their tightest
thresholds. Row side: every fiber of `univ : Finset (Fin p × X)` over a fixed
first component has card `Fintype.card X`, and the required threshold is
`⌈(card X : ℝ) * 1⌉₊ = card X` (by `mul_one` then `Nat.ceil_natCast`), so the
`≥` holds with equality. Column side: `(univ : Finset (Fin p → Y)).card =
Fintype.card (Fin p → Y) = (card Y) ^ p` (`Fintype.card_pi_const`), and the
required threshold is `⌈((card Y : ℝ) ^ p) * 1⌉₊ = (card Y) ^ p`, again meeting
it with equality. This pins down that `bracketGE` at `x = y = 1` demands full
fibers and the full column type, exercising both `IsEquipartitionedGE` and the
column-count clause of the definition. -/
theorem bracketGE.self_mem {X Y : Type*} [Fintype X] [Fintype Y]
    (p : ℕ) [DecidableEq (Fin p → Y)] :
    ((Finset.univ : Finset (Fin p × X)), (Finset.univ : Finset (Fin p → Y)))
      ∈ bracketGE X Y p 1 1 :=
-- CLAIM-END aux:bracket-top
  by
  refine ⟨?_, ?_⟩
  · intro q _hq
    have hceil : ⌈(Fintype.card X : ℝ) * 1⌉₊ = Fintype.card X := by
      rw [mul_one, Nat.ceil_natCast]
    rw [hceil]
    have hmap : (Finset.univ : Finset (Fin p × X)).filter (fun r => r.1 = q)
        = Finset.univ.map ⟨fun x => (q, x), by intro a b h; simpa using h⟩ := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · intro h; exact ⟨r.2, by ext <;> simp [h]⟩
      · rintro ⟨x, rfl⟩; rfl
    rw [hmap, Finset.card_map, Finset.card_univ]
  · have hcard : (Finset.univ : Finset (Fin p → Y)).card = Fintype.card Y ^ p := by
      rw [Finset.card_univ, Fintype.card_pi_const]
    have hceil : ⌈((Fintype.card Y : ℝ) ^ p) * 1⌉₊ = Fintype.card Y ^ p := by
      rw [mul_one, ← Nat.cast_pow, Nat.ceil_natCast]
    rw [hcard, hceil]

-- CLAIM-BEGIN aux:bracket-mono
/-- Unit test: parameter monotonicity of the bracket family in SUBSET form.
Because both defining conditions of `bracketGE` are `≥`-thresholds whose
thresholds `⌈card X · x⌉₊` and `⌈card Y ^ p · y⌉₊` are *monotone* in the
real parameters `x` and `y` (the cardinalities are nonnegative, so scaling
by a smaller factor gives a smaller ceiling), lowering the parameters to
`x2 ≤ x` and `y2 ≤ y` only weakens the membership requirements. Hence every
member of the tighter family `bracketGE X Y p x y` is still a member of the
looser family `bracketGE X Y p x2 y2`, i.e. the family is monotone under
parameter decrease. -/
theorem bracketGE.anti_mono_params {X Y : Type*} [Fintype X] [Fintype Y]
    (p : ℕ) {x y x2 y2 : ℝ} (hx : x2 ≤ x) (hy : y2 ≤ y) :
    bracketGE X Y p x y ⊆ bracketGE X Y p x2 y2 :=
-- CLAIM-END aux:bracket-mono
  by
  intro RC hRC
  obtain ⟨hR, hC⟩ := hRC
  constructor
  · -- row condition: smaller threshold ⌈card X · x2⌉₊ ≤ ⌈card X · x⌉₊
    intro q hq
    refine le_trans ?_ (hR q hq)
    apply Nat.ceil_le_ceil
    exact mul_le_mul_of_nonneg_left hx (by positivity)
  · -- column condition: smaller threshold ⌈card Y ^ p · y2⌉₊ ≤ ⌈card Y ^ p · y⌉₊
    refine le_trans ?_ hC
    apply Nat.ceil_le_ceil
    exact mul_le_mul_of_nonneg_left hy (by positivity)

-- CLAIM-BEGIN aux:bracket-nonempty
/-- Unit test for `bracketGE`: whenever `x ≤ 1`, `y ≤ 1` and `X` is nonempty
(`1 ≤ Fintype.card X`), the bracket family is nonempty. The witness is
`(Finset.univ, Finset.univ)`: every fiber of the full row set over a fixed first
component bijects with `X`, so it has size exactly `Fintype.card X`, and `x ≤ 1`
forces `⌈(card X)·x⌉₊ ≤ card X`; symmetrically the full column set has size
`Fintype.card (Fin p → Y) = (card Y)^p` and `y ≤ 1` forces
`⌈(card Y)^p·y⌉₊ ≤ (card Y)^p`. This verifies the two membership conditions are
simultaneously satisfiable, so the defined set is nonempty. -/
theorem bracketGE.nonempty {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (p : ℕ) (x y : ℝ) (hx1 : x ≤ 1) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) :
    (bracketGE X Y p x y).Nonempty :=
-- CLAIM-END aux:bracket-nonempty
  by
  refine ⟨(Finset.univ, Finset.univ), ?_, ?_⟩
  · -- row side: full row set is equipartitioned at threshold ⌈(card X)*x⌉₊
    intro q _hq
    have hfilter :
        (Finset.univ : Finset (Fin p × X)).filter (fun r => r.1 = q)
          = ({q} : Finset (Fin p)) ×ˢ (Finset.univ : Finset X) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        Finset.mem_singleton, and_true]
    rw [hfilter, Finset.card_product, Finset.card_singleton, Finset.card_univ, one_mul]
    -- ⌈(card X)*x⌉₊ ≤ card X
    rw [Nat.ceil_le]
    calc (Fintype.card X : ℝ) * x ≤ (Fintype.card X : ℝ) * 1 := by
            apply mul_le_mul_of_nonneg_left hx1 (by positivity)
      _ = (Fintype.card X : ℝ) := by ring
  · -- column side: full column set has size (card Y)^p ≥ ⌈(card Y)^p*y⌉₊
    have hcard : (Finset.univ : Finset (Fin p → Y)).card = Fintype.card Y ^ p := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    rw [hcard, Nat.ceil_le]
    push_cast
    calc ((Fintype.card Y : ℝ) ^ p) * y ≤ ((Fintype.card Y : ℝ) ^ p) * 1 := by
            apply mul_le_mul_of_nonneg_left hy1 (by positivity)
      _ = (Fintype.card Y : ℝ) ^ p := by ring

end NPCC
