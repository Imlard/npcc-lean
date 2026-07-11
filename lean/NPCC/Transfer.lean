import Mathlib
import NPCC.Defs
import NPCC.Complexity
import NPCC.Robust
import NPCC.RobustAux
import NPCC.Engine
import NPCC.Relaxed
import NPCC.Control

/-! # §4 transfer layer (paper "Lower Bounds After Column Loss").
This file hosts `def:column-loss-resilient` now and the extension/separation
theorems later. Rendering conventions: powers of two by exponent
(`q = 2^Q`, `t = 2^T`, so the paper's `log q = Q`, `log t = T`, `log = log₂`);
the balanced-family error `ε` is an explicit parameter (the paper fixes
`ε_{q,t}` contextually; consumers instantiate it with the AGHP error term).
Range conditions (`q ≥ t ≥ 1`, `t ≤ 2^b`, `h ∈ (0,1]`, `1 ≤ b`, `0 ≤ ε`) are
use-site hypotheses, not baked into the Prop — the standing convention of
`IsRobust`/`IsBalancedFamily`. -/

namespace NPCC

open Workspace.Types.CommComplexity Workspace.Types.Interlace

/-- The paper's `y_c(h) := ((h·2^{−c})/(1+ε))^{1/t}` — the one-copy classical
density surviving after a branch has spent `c` column bits on a relaxed
subgame of initial column density `h`, bridged on one coordinate.
Unregistered supporting definition — judged with
`def:column-loss-resilient`, whose statement depends on it. `t` is passed as
the actual copy count (callers use `2^T`). -/
noncomputable def yLoss (ε : ℝ) (t : ℕ) (h : ℝ) (c : ℕ) : ℝ :=
  ((h * (2 : ℝ) ^ (-(c : ℝ))) / (1 + ε)) ^ (1 / (t : ℝ))

-- CLAIM-BEGIN def:column-loss-resilient
/-- Paper `def:column-loss-resilient`: `(f, b)` is `(q,t,h)`-column-loss
resilient (with `q = 2^Q ≥ t = 2^T` powers of two, error term `ε`) iff
(i) the one-copy family at row density `2^{−b}` and column density
`y_{log q + comp f}(h)` is nontrivial (`comp ≥ 1`), and
(ii) for all `0 ≤ k ≤ comp f` and `0 ≤ c ≤ log t + k`,
`Λ_f(1, 2^{−b}, y_c(h)) ≥ comp f − k` (ℕ-subtraction exact under `k ≤ D f`).
`Λ` is the typed `LambdaGE`; `y_c(h)` is `yLoss ε (2^T) h c`. -/
def IsColumnLossResilient {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (b ε : ℝ) (Q T : ℕ) (h : ℝ) : Prop :=
  1 ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 ((2 : ℝ) ^ (-b)) (yLoss ε (2 ^ T) h (Q + D f))) ∧
  ∀ k ≤ D f, ∀ c ≤ T + k,
    D f - k ≤ LambdaGE f 1 ((2 : ℝ) ^ (-b)) (yLoss ε (2 ^ T) h c)
-- CLAIM-END def:column-loss-resilient

/-! ## Private toolkit for `thm:Extension` / `cor:localized-extension`

The paper's proof (§4) is a root-to-leaf chain in the protocol tree.  It is
formalized below as ONE structural induction over the artifact `Protocol`
tree (`extension_chain`), maintaining the paper's chain invariant
(eq. extension-invariant, localized form) in the frozen shape

* `2^(R'e − s) · pseed ≤ |Qc|`                          (surviving blocks),
* every `Qc`-fiber of the current row set holds `≥ ⌈2^(R'e−s)·x_seed·m⌉`
  rows (equipartition at the CURRENT threshold — the paper's recursive
  ledger `T_{i+1} = ⌈T_i/2⌉` is folded into the threshold itself via
  `2·⌈u⌉ ≤ ⌈2u⌉ + 1`),
* `h·L ≤ 2^(a+c) · |Cc|`                                (column density),
* `cost + s + c < D f + R'e + T`                        (budget),

for `s ≤ R'e` row bits and `c` column bits spent.  Closing lemmas:
`extension_seed_step` = the paper's Case 2, fired at the FIRST node with
`s = R'e` regardless of its shape (`relaxed_to_classical` hands a
`bracketGE … x_seed h_seed` member to the seed bound `hseedbd`, and the
residual protocol — of cost `< D f + T` by the budget — would compute that
member through `Protocol.pullback`; contradiction).  `extension_leaf_step`
= Case 1, a leaf reached with `s < R'e`: the leaf rectangle still holds
`t = 2^T` blocks of `≥ ⌈2^{−b}m⌉` rows; `relaxed_to_classical` at `u = t`
plus a one-coordinate maximum projection (`exists_dense_coordinate`,
the typed `lem:max-projection` at `ℓ = 1`) produce a CONSTANT member of the
one-copy family at density `y_{log q + D f}(h)`, contradicting resilience
clause (i).  Clause (ii) of `IsColumnLossResilient` is not consumed here —
exactly as in the paper, whose Extension/localized proofs use only clause
(i) plus the seed bound.  Deviations from the paper's ledger (both safe
strengthenings): the chain keeps ALL blocks whose chosen half is heavy
(at least half of them) instead of trimming to exactly `⌈|Q_i|/2⌉`, and
`extension_theorem` is derived as the `a = 0`, `r' = r` instance of the
localized chain rather than by a separate run. -/

open Workspace.Types.Protocol

/-- Fiber counting transports along `Subtype.val`: filtering the
`val`-image of a subtype selection by an ambient predicate counts the same
as filtering the selection by the pulled-back predicate. -/
private theorem card_filter_image_val {α : Type*} [DecidableEq α] {s : Finset α}
    (u : Finset {x // x ∈ s}) (pr : α → Prop) [DecidablePred pr] :
    ((u.image Subtype.val).filter pr).card
      = (u.filter (fun x => pr x.val)).card := by
  rw [← Finset.card_image_of_injective (u.filter (fun x => pr x.val))
    Subtype.val_injective]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hpr⟩
    exact ⟨w, ⟨hw, hpr⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hpr⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, hpr⟩

/-- `2^(−K) ≤ (2^k)⁻¹` (rpow left, monoid pow right) whenever `k ≤ K`. -/
private theorem rpow_neg_le_inv_npow {k K : ℕ} (hkK : k ≤ K) :
    (2 : ℝ) ^ (-(K : ℝ)) ≤ ((2 : ℝ) ^ k)⁻¹ := by
  rw [← Real.rpow_natCast 2 k, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact neg_le_neg (by exact_mod_cast hkK)

/-- Degenerate guard: clause (i) of column-loss resilience forces `Y`
nonempty — with `card Y = 0` the pair `(univ, ∅)` would be a one-copy
bracket member of complexity `0`. -/
private theorem card_Y_pos_of_clause_one {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {b z₀ : ℝ} (hxb1 : (2 : ℝ) ^ (-b) ≤ 1)
    (hone : 1 ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 ((2 : ℝ) ^ (-b)) z₀)) :
    0 < Fintype.card Y := by
  by_contra hY
  have hY0 : Fintype.card Y = 0 := by omega
  have hmem : ((Finset.univ : Finset (Fin 1 × X)), (∅ : Finset (Fin 1 → Y)))
      ∈ bracketGE X Y 1 ((2 : ℝ) ^ (-b)) z₀ := by
    refine ⟨?_, ?_⟩
    · intro i _
      have hfill : (Finset.univ : Finset (Fin 1 × X)).filter (fun p => p.1 = i)
          = Finset.univ := by
        apply Finset.filter_true_of_mem
        intro p _
        have h1 := p.1.2
        have h2 := i.2
        exact Fin.ext (by omega)
      rw [hfill, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, one_mul,
        Nat.ceil_le]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) hxb1
    · simp [hY0]
  have hcomp : (Protocol.leaf true).Computes
      (subgame (interlaceFun f 1) (Finset.univ : Finset (Fin 1 × X))
        (∅ : Finset (Fin 1 → Y))) := by
    intro x y
    exact absurd y.2 (Finset.notMem_empty _)
  have hD0 : D (subgame (interlaceFun f 1) (Finset.univ : Finset (Fin 1 × X))
      (∅ : Finset (Fin 1 → Y))) ≤ 0 := by
    have h0 : (0 : ℕ) ∈ AchievableCosts (subgame (interlaceFun f 1)
        (Finset.univ : Finset (Fin 1 × X)) (∅ : Finset (Fin 1 → Y))) :=
      ⟨Protocol.leaf true, rfl, hcomp⟩
    simpa [D] using Nat.sInf_le h0
  have hfam : Dfamily (interlaceFun f 1) (bracketGE X Y 1 ((2 : ℝ) ^ (-b)) z₀)
      ≤ D (subgame (interlaceFun f 1) (Finset.univ : Finset (Fin 1 × X))
        (∅ : Finset (Fin 1 → Y))) := by
    have hm : D (subgame (interlaceFun f 1) (Finset.univ : Finset (Fin 1 × X))
        (∅ : Finset (Fin 1 → Y)))
        ∈ { d : ℕ | ∃ RC ∈ bracketGE X Y 1 ((2 : ℝ) ^ (-b)) z₀,
            d = D (subgame (interlaceFun f 1) RC.1 RC.2) } := ⟨_, hmem, rfl⟩
    simpa [Dfamily] using Nat.sInf_le hm
  omega

/-- Typed `lem:max-projection` at one copy: a `t`-fold column set of size
`≥ n^t·y'` projects, on SOME coordinate, to `≥ n·y'^{1/t}` distinct values
(`|C| ≤ ∏ᵢ |projᵢ C|`, so the max factor is `≥ |C|^{1/t}`). -/
private theorem exists_dense_coordinate {Y : Type*} [Fintype Y] [DecidableEq Y]
    {t : ℕ} (ht : 0 < t) (hY : 0 < Fintype.card Y)
    (Cols : Finset (Fin t → Y)) {y' : ℝ} (hy' : 0 < y')
    (hcols : ⌈((Fintype.card Y : ℝ) ^ t) * y'⌉₊ ≤ Cols.card) :
    ∃ i₀ : Fin t, (Fintype.card Y : ℝ) * y' ^ (1 / (t : ℝ))
      ≤ ((Cols.image (fun c => c i₀)).card : ℝ) := by
  classical
  by_contra hnone
  simp only [not_exists, not_le] at hnone
  have hroot_pos : 0 < y' ^ (1 / (t : ℝ)) := Real.rpow_pos_of_pos hy' _
  have hnR : (0:ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hlow : ((Fintype.card Y : ℝ) ^ t) * y' ≤ (Cols.card : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hcols)
  have hColsNe : Cols.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hc
    have hc0 : Cols.card = 0 := by omega
    rw [hc0] at hlow
    have : (0:ℝ) < ((Fintype.card Y : ℝ) ^ t) * y' := by positivity
    norm_num at hlow
    linarith
  have hsub : Cols ⊆ Fintype.piFinset (fun i => Cols.image (fun c => c i)) := by
    intro c hc
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image_of_mem _ hc
  have hprod : (Cols.card : ℝ)
      ≤ ∏ i : Fin t, ((Cols.image (fun c => c i)).card : ℝ) := by
    have h1 : Cols.card ≤ ∏ i : Fin t, (Cols.image (fun c => c i)).card := by
      calc Cols.card
          ≤ (Fintype.piFinset (fun i => Cols.image (fun c => c i))).card :=
            Finset.card_le_card hsub
        _ = ∏ i : Fin t, (Cols.image (fun c => c i)).card :=
            Fintype.card_piFinset _
    exact_mod_cast h1
  have hlt : ∏ i : Fin t, ((Cols.image (fun c => c i)).card : ℝ)
      < ∏ _i : Fin t, ((Fintype.card Y : ℝ) * y' ^ (1 / (t : ℝ))) := by
    haveI : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
    apply Finset.prod_lt_prod_of_nonempty
    · intro i _
      have hne : (Cols.image (fun c => c i)).Nonempty := hColsNe.image _
      have hpos : 0 < (Cols.image (fun c => c i)).card := Finset.card_pos.mpr hne
      exact_mod_cast hpos
    · intro i _
      exact hnone i
    · exact Finset.univ_nonempty
  have hBt : ∏ _i : Fin t, ((Fintype.card Y : ℝ) * y' ^ (1 / (t : ℝ)))
      = ((Fintype.card Y : ℝ) ^ t) * y' := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
    congr 1
    rw [← Real.rpow_natCast (y' ^ (1 / (t : ℝ))) t, ← Real.rpow_mul hy'.le,
      one_div, inv_mul_cancel₀ (by exact_mod_cast ht.ne' : (t:ℝ) ≠ 0),
      Real.rpow_one]
  rw [hBt] at hlt
  linarith

/-- Case 2 of the paper's Extension proof, fired at the first chain node
with all `R'e` row bits spent: the rectangle still holds `pseed` blocks at
threshold `⌈x_seed·m⌉` and column density `h·2^{−(a+c)}` with
`a + c ≤ log t + D f`; `relaxed_to_classical` produces a
`bracketGE … x_seed h_seed` member inside it (via the theorem-level bridge
`h_seed ≤ h·2^{−(log t + D f)}/(1+ε)`), the seed bound prices it at
`≥ D f + T`, and the residual protocol of cost `< D f + T` would compute it
through `Protocol.pullback` — contradiction. -/
private theorem extension_seed_step {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {ε : ℝ} (hε : 0 ≤ ε)
    (T R : ℕ) {L : ℕ} (S : Fin L → Fin (2 ^ (R + T)) → Y)
    (hS : IsBalancedFamily (2 ^ T) S ε)
    (pseed : ℕ) {xseed h hseed : ℝ}
    (hh0 : 0 < h)
    (hp1 : 2 ^ T ≤ 2 * pseed) (hp2 : pseed ≤ 2 ^ T)
    (hseedbd : D f + T ≤ Dfamily (interlaceFun f pseed)
        (bracketGE X Y pseed xseed hseed))
    (hbridge : hseed ≤ h * (2 : ℝ) ^ (-((T + D f : ℕ) : ℝ)) / (1 + ε))
    (a : ℕ) (Rs : Finset (Fin (2 ^ (R + T)) × X)) (Cs : Finset (Fin L))
    (P : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool)
    (c : ℕ) (Qc : Finset (Fin (2 ^ (R + T))))
    (Rc : Finset {p // p ∈ Rs}) (Cc : Finset {j // j ∈ Cs})
    (hcomp : ∀ x ∈ Rc, ∀ y ∈ Cc,
      P.eval x y = subgame (relaxedInterlace f S) Rs Cs x y)
    (hQcard : pseed ≤ Qc.card)
    (hQfib : ∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ) * xseed⌉₊
        ≤ (Rc.filter (fun p => p.val.1 = qq)).card)
    (hCcard : h * (L : ℝ) ≤ (2 : ℝ) ^ (a + c) * (Cc.card : ℝ))
    (hac : a + c ≤ T + D f)
    (hPcost : P.cost < D f + T) : False := by
  classical
  have hεpos : (0:ℝ) < 1 + ε := by linarith
  have hpseed : 0 < pseed := by
    have h1 : 0 < 2 ^ T := Nat.two_pow_pos T
    omega
  have h2pow_pos : (0:ℝ) < (2 : ℝ) ^ (a + c) := by positivity
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hQcard
  set e : Fin pseed ≃ {i // i ∈ J} := (J.orderIsoOfFin hJcard).toEquiv with he
  have hrow : IsEquipartitionedGE (Rc.image Subtype.val) J
      ⌈(Fintype.card X : ℝ) * xseed⌉₊ := by
    intro qq hqq
    rw [card_filter_image_val]
    exact hQfib qq (hJsub hqq)
  have hcol : (h * ((2 : ℝ) ^ (a + c))⁻¹) * (L : ℝ)
      ≤ ((Cc.image Subtype.val).card : ℝ) := by
    rw [Finset.card_image_of_injective Cc Subtype.val_injective]
    have hrw : (h * ((2 : ℝ) ^ (a + c))⁻¹) * (L : ℝ)
        = h * (L : ℝ) / (2 : ℝ) ^ (a + c) := by
      rw [div_eq_mul_inv]; ring
    rw [hrw, div_le_iff₀ h2pow_pos]
    calc h * (L : ℝ) ≤ (2 : ℝ) ^ (a + c) * (Cc.card : ℝ) := hCcard
      _ = (Cc.card : ℝ) * (2 : ℝ) ^ (a + c) := mul_comm _ _
  obtain ⟨RC', hmem, hRowsProv, hColsProv⟩ :=
    relaxed_to_classical (x := xseed) hpseed hp2 hS hε e hrow hcol (le_refl _)
  -- upgrade the member to density `hseed`
  have hseed_le : hseed ≤ (h * ((2 : ℝ) ^ (a + c))⁻¹) / (1 + ε) := by
    refine le_trans hbridge ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hεpos.le)
    exact mul_le_mul_of_nonneg_left (rpow_neg_le_inv_npow hac) hh0.le
  have hmem' : RC' ∈ bracketGE X Y pseed xseed hseed := by
    refine ⟨hmem.1, le_trans ?_ hmem.2⟩
    apply Nat.ceil_le_ceil
    exact mul_le_mul_of_nonneg_left hseed_le (by positivity)
  have hDlow : D f + T ≤ D (subgame (interlaceFun f pseed) RC'.1 RC'.2) := by
    refine le_trans hseedbd ?_
    have hm : D (subgame (interlaceFun f pseed) RC'.1 RC'.2)
        ∈ { d : ℕ | ∃ RC ∈ bracketGE X Y pseed xseed hseed,
            d = D (subgame (interlaceFun f pseed) RC.1 RC.2) } := ⟨RC', hmem', rfl⟩
    simpa [Dfamily] using Nat.sInf_le hm
  -- transport the residual protocol onto the member
  have hρex : ∀ p : {p // p ∈ RC'.1}, ∃ w, w ∈ Rc ∧
      (w : Fin (2 ^ (R + T)) × X) = ((e p.val.1).val, p.val.2) := by
    intro p
    have hm2 := hRowsProv p.val p.2
    rw [Finset.mem_image] at hm2
    obtain ⟨w, hw, hweq⟩ := hm2
    exact ⟨w, hw, hweq⟩
  choose ρ hρmem hρval using hρex
  have hσex : ∀ cc : {c' // c' ∈ RC'.2}, ∃ w, w ∈ Cc ∧
      ∀ i : Fin pseed, cc.val i = S (w : Fin L) (e i).val := by
    intro cc
    obtain ⟨j, hj, hjeq⟩ := hColsProv cc.val cc.2
    rw [Finset.mem_image] at hj
    obtain ⟨w, hw, hweq⟩ := hj
    refine ⟨w, hw, ?_⟩
    intro i
    rw [← hweq] at hjeq
    exact hjeq i
  choose σ hσmem hσval using hσex
  have hPb : (Protocol.pullback ρ σ P).Computes
      (subgame (interlaceFun f pseed) RC'.1 RC'.2) := by
    intro p cc
    rw [Protocol.pullback_eval]
    rw [hcomp (ρ p) (hρmem p) (σ cc) (hσmem cc)]
    simp only [subgame, relaxedInterlace, interlaceFun]
    rw [hρval p, hσval cc p.val.1]
  have hDup : D (subgame (interlaceFun f pseed) RC'.1 RC'.2) ≤ P.cost := by
    have hmem2 : P.cost
        ∈ AchievableCosts (subgame (interlaceFun f pseed) RC'.1 RC'.2) :=
      ⟨Protocol.pullback ρ σ P, Protocol.pullback_cost ρ σ P, hPb⟩
    simpa [D] using Nat.sInf_le hmem2
  omega

/-- Case 1 of the paper's Extension proof: a leaf reached with `s < R'e`
row bits spent.  The (monochromatic) leaf rectangle still holds `t = 2^T`
blocks of `≥ ⌈2^{−b}m⌉` rows and columns of density `h·2^{−(a+c)}` with
`a + c ≤ log q + D f`; `relaxed_to_classical` at `u = t` plus the
one-coordinate maximum projection produce a CONSTANT one-copy bracket
member at density `y_{log q + D f}(h)`, contradicting clause (i). -/
private theorem extension_leaf_step {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {b ε : ℝ} (hε : 0 ≤ ε)
    (T R : ℕ) {L : ℕ} (S : Fin L → Fin (2 ^ (R + T)) → Y)
    (hS : IsBalancedFamily (2 ^ T) S ε)
    {h : ℝ} (hh0 : 0 < h)
    (hY : 0 < Fintype.card Y)
    (hone : 1 ≤ Dfamily (interlaceFun f 1)
        (bracketGE X Y 1 ((2 : ℝ) ^ (-b)) (yLoss ε (2 ^ T) h (R + T + D f))))
    (a : ℕ) (Rs : Finset (Fin (2 ^ (R + T)) × X)) (Cs : Finset (Fin L))
    (z : Bool) (c : ℕ) (Qc : Finset (Fin (2 ^ (R + T))))
    (Rc : Finset {p // p ∈ Rs}) (Cc : Finset {j // j ∈ Cs})
    (hconst : ∀ x ∈ Rc, ∀ y ∈ Cc,
      subgame (relaxedInterlace f S) Rs Cs x y = z)
    (hQcard : 2 ^ T ≤ Qc.card)
    (hQfib : ∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ (-b))⌉₊
        ≤ (Rc.filter (fun p => p.val.1 = qq)).card)
    (hCcard : h * (L : ℝ) ≤ (2 : ℝ) ^ (a + c) * (Cc.card : ℝ))
    (hac : a + c ≤ R + T + D f) : False := by
  classical
  have hεpos : (0:ℝ) < 1 + ε := by linarith
  have ht : 0 < 2 ^ T := Nat.two_pow_pos T
  have h2pow_pos : (0:ℝ) < (2 : ℝ) ^ (a + c) := by positivity
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hQcard
  set e : Fin (2 ^ T) ≃ {i // i ∈ J} := (J.orderIsoOfFin hJcard).toEquiv with he
  have hrow : IsEquipartitionedGE (Rc.image Subtype.val) J
      ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ (-b))⌉₊ := by
    intro qq hqq
    rw [card_filter_image_val]
    exact hQfib qq (hJsub hqq)
  have hcol : (h * ((2 : ℝ) ^ (a + c))⁻¹) * (L : ℝ)
      ≤ ((Cc.image Subtype.val).card : ℝ) := by
    rw [Finset.card_image_of_injective Cc Subtype.val_injective]
    have hrw : (h * ((2 : ℝ) ^ (a + c))⁻¹) * (L : ℝ)
        = h * (L : ℝ) / (2 : ℝ) ^ (a + c) := by
      rw [div_eq_mul_inv]; ring
    rw [hrw, div_le_iff₀ h2pow_pos]
    calc h * (L : ℝ) ≤ (2 : ℝ) ^ (a + c) * (Cc.card : ℝ) := hCcard
      _ = (Cc.card : ℝ) * (2 : ℝ) ^ (a + c) := mul_comm _ _
  obtain ⟨RC', hmem, hRowsProv, hColsProv⟩ :=
    relaxed_to_classical (x := (2 : ℝ) ^ (-b)) ht (le_refl (2 ^ T)) hS hε e
      hrow hcol (le_refl _)
  -- the member is monochromatic with value `z`
  have hmono : ∀ p ∈ RC'.1, ∀ c' ∈ RC'.2, f p.2 (c' p.1) = z := by
    intro p hp c' hc'
    have hr := hRowsProv p hp
    rw [Finset.mem_image] at hr
    obtain ⟨w, hw, hweq⟩ := hr
    obtain ⟨j, hj, hjeq⟩ := hColsProv c' hc'
    rw [Finset.mem_image] at hj
    obtain ⟨jc, hjc, hjceq⟩ := hj
    rw [← hjceq] at hjeq
    have hval : f (w : Fin (2 ^ (R + T)) × X).2
        (S (jc : Fin L) (w : Fin (2 ^ (R + T)) × X).1) = z := hconst w hw jc hjc
    rw [hweq] at hval
    rw [hjeq p.1]
    exact hval
  -- max projection to one copy
  have hy'pos : 0 < (h * ((2 : ℝ) ^ (a + c))⁻¹) / (1 + ε) :=
    div_pos (mul_pos hh0 (inv_pos.mpr h2pow_pos)) hεpos
  obtain ⟨i₀, hi₀⟩ := exists_dense_coordinate ht hY RC'.2 hy'pos hmem.2
  set R₀ : Finset (Fin 1 × X) :=
    (RC'.1.filter (fun p => p.1 = i₀)).image (fun p => ((0 : Fin 1), p.2)) with hR₀
  set C₀ : Finset (Fin 1 → Y) :=
    ((RC'.2.image (fun c' => c' i₀)).image (fun yv => (fun _ : Fin 1 => yv))) with hC₀
  have hR₀card : R₀.card = (RC'.1.filter (fun p => p.1 = i₀)).card := by
    rw [hR₀]
    apply Finset.card_image_of_injOn
    intro p hp p' hp' hpp
    have h1 : p.1 = i₀ := (Finset.mem_filter.mp hp).2
    have h2 : p'.1 = i₀ := (Finset.mem_filter.mp hp').2
    simp only [Prod.mk.injEq] at hpp
    exact Prod.ext (h1.trans h2.symm) hpp.2
  have hC₀card : C₀.card = (RC'.2.image (fun c' => c' i₀)).card := by
    rw [hC₀]
    apply Finset.card_image_of_injective
    intro y1 y2 h12
    exact congrFun h12 ⟨0, Nat.one_pos⟩
  -- density comparison against `y_{log q + D f}(h)`
  have hz₀le : yLoss ε (2 ^ T) h (R + T + D f)
      ≤ ((h * ((2 : ℝ) ^ (a + c))⁻¹) / (1 + ε)) ^ (1 / ((2 ^ T : ℕ) : ℝ)) := by
    unfold yLoss
    apply Real.rpow_le_rpow
    · exact div_nonneg (mul_nonneg hh0.le
        (Real.rpow_nonneg (by norm_num) _)) hεpos.le
    · rw [div_eq_mul_inv, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hεpos.le)
      exact mul_le_mul_of_nonneg_left (rpow_neg_le_inv_npow hac) hh0.le
    · positivity
  have hrows₀ : IsEquipartitionedGE R₀ (Finset.univ : Finset (Fin 1))
      ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ (-b))⌉₊ := by
    intro i _
    have hall : ∀ p ∈ R₀, p.1 = i := by
      intro p _
      have h1 := p.1.2
      have h2 := i.2
      exact Fin.ext (by omega)
    rw [Finset.filter_true_of_mem hall, hR₀card]
    exact hmem.1 i₀ (Finset.mem_univ i₀)
  have hcols₀ : ⌈((Fintype.card Y : ℝ) ^ 1)
      * yLoss ε (2 ^ T) h (R + T + D f)⌉₊ ≤ C₀.card := by
    rw [pow_one, Nat.ceil_le]
    calc (Fintype.card Y : ℝ) * yLoss ε (2 ^ T) h (R + T + D f)
        ≤ (Fintype.card Y : ℝ)
            * (((h * ((2 : ℝ) ^ (a + c))⁻¹) / (1 + ε)) ^ (1 / ((2 ^ T : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hz₀le (Nat.cast_nonneg _)
      _ ≤ ((RC'.2.image (fun c' => c' i₀)).card : ℝ) := hi₀
      _ = (C₀.card : ℝ) := by rw [hC₀card]
  have hmem₀ : (R₀, C₀) ∈ bracketGE X Y 1 ((2 : ℝ) ^ (-b))
      (yLoss ε (2 ^ T) h (R + T + D f)) := ⟨hrows₀, hcols₀⟩
  -- the induced subgame is the constant `z`
  have hcz : (Protocol.leaf z).Computes (subgame (interlaceFun f 1) R₀ C₀) := by
    intro aa cc
    have haa : (aa : Fin 1 × X)
        ∈ (RC'.1.filter (fun p => p.1 = i₀)).image (fun p => ((0 : Fin 1), p.2)) := by
      rw [← hR₀]
      exact aa.2
    rw [Finset.mem_image] at haa
    obtain ⟨p, hpf, hpeq⟩ := haa
    rw [Finset.mem_filter] at hpf
    have hcc : (cc : Fin 1 → Y)
        ∈ (RC'.2.image (fun c' => c' i₀)).image (fun yv => (fun _ : Fin 1 => yv)) := by
      rw [← hC₀]
      exact cc.2
    rw [Finset.mem_image] at hcc
    obtain ⟨yv, hyv, hyveq⟩ := hcc
    rw [Finset.mem_image] at hyv
    obtain ⟨c', hc', hc'eq⟩ := hyv
    show z = subgame (interlaceFun f 1) R₀ C₀ aa cc
    have hgoal : subgame (interlaceFun f 1) R₀ C₀ aa cc
        = f (aa : Fin 1 × X).2 ((cc : Fin 1 → Y) (aa : Fin 1 × X).1) := rfl
    rw [hgoal, ← hpeq, ← hyveq, ← hc'eq]
    have hz := hmono p hpf.1 c' hc'
    rw [hpf.2] at hz
    exact hz.symm
  have hD0 : D (subgame (interlaceFun f 1) R₀ C₀) ≤ 0 := by
    have h0 : (0 : ℕ) ∈ AchievableCosts (subgame (interlaceFun f 1) R₀ C₀) :=
      ⟨Protocol.leaf z, rfl, hcz⟩
    simpa [D] using Nat.sInf_le h0
  have hfam : Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 ((2 : ℝ) ^ (-b)) (yLoss ε (2 ^ T) h (R + T + D f)))
      ≤ D (subgame (interlaceFun f 1) R₀ C₀) := by
    have hm : D (subgame (interlaceFun f 1) R₀ C₀)
        ∈ { d : ℕ | ∃ RC ∈ bracketGE X Y 1 ((2 : ℝ) ^ (-b))
              (yLoss ε (2 ^ T) h (R + T + D f)),
            d = D (subgame (interlaceFun f 1) RC.1 RC.2) } := ⟨(R₀, C₀), hmem₀, rfl⟩
    simpa [Dfamily] using Nat.sInf_le hm
  omega

set_option maxHeartbeats 1000000 in
/-- The paper's root-to-leaf chain, as a structural induction over the
protocol tree with the frozen invariant (see the section docstring).
Bob nodes halve the surviving column set (`c ↦ c+1`); Alice nodes halve
each block fiber and keep the half of the blocks whose heavy side agrees
(`s ↦ s+1`); the FIRST node with `s = R'e` fires `extension_seed_step`,
and a leaf with `s < R'e` fires `extension_leaf_step`. -/
private theorem extension_chain {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {b ε : ℝ} (hε : 0 ≤ ε)
    (T R : ℕ) {L : ℕ} (S : Fin L → Fin (2 ^ (R + T)) → Y)
    (hS : IsBalancedFamily (2 ^ T) S ε)
    (pseed : ℕ) {xseed h hseed : ℝ}
    (hx1 : (2 : ℝ) ^ (-b) ≤ xseed)
    (hh0 : 0 < h)
    (hp1 : 2 ^ T ≤ 2 * pseed) (hp2 : pseed ≤ 2 ^ T)
    (hres : IsColumnLossResilient f b ε (R + T) T h)
    (hseedbd : D f + T ≤ Dfamily (interlaceFun f pseed)
        (bracketGE X Y pseed xseed hseed))
    (hbridge : hseed ≤ h * (2 : ℝ) ^ (-((T + D f : ℕ) : ℝ)) / (1 + ε))
    (a R'e : ℕ) (ha : a ≤ 1) (hR'R : R'e ≤ R)
    (Rs : Finset (Fin (2 ^ (R + T)) × X)) (Cs : Finset (Fin L))
    (hY : 0 < Fintype.card Y)
    (P : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool)
    (s c : ℕ) (Qc : Finset (Fin (2 ^ (R + T))))
    (Rc : Finset {p // p ∈ Rs}) (Cc : Finset {j // j ∈ Cs})
    (hs : s ≤ R'e)
    (hcomp : ∀ x ∈ Rc, ∀ y ∈ Cc,
      P.eval x y = subgame (relaxedInterlace f S) Rs Cs x y)
    (hQcard : 2 ^ (R'e - s) * pseed ≤ Qc.card)
    (hQfib : ∀ qq ∈ Qc, ⌈(2 : ℝ) ^ (R'e - s) * xseed * (Fintype.card X : ℝ)⌉₊
        ≤ (Rc.filter (fun p => p.val.1 = qq)).card)
    (hCcard : h * (L : ℝ) ≤ (2 : ℝ) ^ (a + c) * (Cc.card : ℝ))
    (hcost : P.cost + s + c < D f + R'e + T) : False := by
  have hxseed0 : 0 < xseed :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) (-b)) hx1
  -- Case-2 firing wrapper, protocol-shape agnostic.
  have hfire : ∀ (P' : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool) (c' : ℕ)
      (Qc' : Finset (Fin (2 ^ (R + T)))) (Rc' : Finset {p // p ∈ Rs})
      (Cc' : Finset {j // j ∈ Cs}),
      (∀ x ∈ Rc', ∀ y ∈ Cc',
        P'.eval x y = subgame (relaxedInterlace f S) Rs Cs x y) →
      2 ^ (R'e - R'e) * pseed ≤ Qc'.card →
      (∀ qq ∈ Qc', ⌈(2 : ℝ) ^ (R'e - R'e) * xseed * (Fintype.card X : ℝ)⌉₊
          ≤ (Rc'.filter (fun p => p.val.1 = qq)).card) →
      h * (L : ℝ) ≤ (2 : ℝ) ^ (a + c') * (Cc'.card : ℝ) →
      P'.cost + R'e + c' < D f + R'e + T →
      False := by
    intro P' c' Qc' Rc' Cc' hcomp' hQcard' hQfib' hCcard' hcost'
    rw [Nat.sub_self, pow_zero, one_mul] at hQcard'
    have hQfib'' : ∀ qq ∈ Qc', ⌈(Fintype.card X : ℝ) * xseed⌉₊
        ≤ (Rc'.filter (fun p => p.val.1 = qq)).card := by
      intro qq hqq
      refine le_trans (Nat.ceil_le_ceil (le_of_eq ?_)) (hQfib' qq hqq)
      rw [Nat.sub_self, pow_zero]
      ring
    exact extension_seed_step f hε T R S hS pseed hh0 hp1 hp2 hseedbd hbridge
      a Rs Cs P' c' Qc' Rc' Cc' hcomp' hQcard' hQfib'' hCcard'
      (by omega) (by omega)
  induction P generalizing s c Qc Rc Cc with
  | leaf z =>
    rcases eq_or_lt_of_le hs with heq | hslt
    · subst heq
      exact hfire (Protocol.leaf z) c Qc Rc Cc hcomp hQcard hQfib hCcard hcost
    · -- Case 1: monochromatic leaf before the row bits are exhausted.
      have hconst : ∀ x ∈ Rc, ∀ y ∈ Cc,
          subgame (relaxedInterlace f S) Rs Cs x y = z := by
        intro x hx y hy
        exact (hcomp x hx y hy).symm
      have hQcard' : 2 ^ T ≤ Qc.card := by
        have h1 : 1 ≤ R'e - s := by omega
        have h2 : 2 ≤ 2 ^ (R'e - s) := by
          calc 2 = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ (R'e - s) := Nat.pow_le_pow_right (by norm_num) h1
        have h3 : 2 * pseed ≤ 2 ^ (R'e - s) * pseed :=
          Nat.mul_le_mul_right pseed h2
        omega
      have hQfib' : ∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ (-b))⌉₊
          ≤ (Rc.filter (fun p => p.val.1 = qq)).card := by
        intro qq hqq
        refine le_trans (Nat.ceil_le_ceil ?_) (hQfib qq hqq)
        have hone2 : (1:ℝ) ≤ (2 : ℝ) ^ (R'e - s) := one_le_pow₀ (by norm_num)
        have hxx : (2 : ℝ) ^ (-b) ≤ (2 : ℝ) ^ (R'e - s) * xseed := by
          calc (2 : ℝ) ^ (-b) ≤ xseed := hx1
            _ = 1 * xseed := (one_mul _).symm
            _ ≤ (2 : ℝ) ^ (R'e - s) * xseed :=
                mul_le_mul_of_nonneg_right hone2 hxseed0.le
        calc (Fintype.card X : ℝ) * ((2 : ℝ) ^ (-b))
            ≤ (Fintype.card X : ℝ) * ((2 : ℝ) ^ (R'e - s) * xseed) :=
              mul_le_mul_of_nonneg_left hxx (Nat.cast_nonneg _)
          _ = (2 : ℝ) ^ (R'e - s) * xseed * (Fintype.card X : ℝ) := by ring
      have hac : a + c ≤ R + T + D f := by
        have hc0 : (Protocol.leaf z : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool).cost
            = 0 := rfl
        omega
      exact extension_leaf_step f hε T R S hS hh0 hY hres.1 a Rs Cs z c Qc Rc Cc
        hconst hQcard' hQfib' hCcard hac
  | aNode pred l r ihl ihr =>
    rcases eq_or_lt_of_le hs with heq | hslt
    · subst heq
      exact hfire (Protocol.aNode pred l r) c Qc Rc Cc hcomp hQcard hQfib hCcard hcost
    · -- Alice (row) bit: halve the fibers, keep the majority half of the blocks.
      set Rt : Finset {p // p ∈ Rs} := Rc.filter (fun p => pred p = true) with hRt
      set Rf : Finset {p // p ∈ Rs} := Rc.filter (fun p => ¬ (pred p = true)) with hRf
      have hsum : ∀ qq : Fin (2 ^ (R + T)),
          (Rt.filter (fun p => p.val.1 = qq)).card
            + (Rf.filter (fun p => p.val.1 = qq)).card
          = (Rc.filter (fun p => p.val.1 = qq)).card := by
        intro qq
        have e1 : Rt.filter (fun p => p.val.1 = qq)
            = (Rc.filter (fun p => p.val.1 = qq)).filter (fun p => pred p = true) := by
          rw [hRt, Finset.filter_comm]
        have e2 : Rf.filter (fun p => p.val.1 = qq)
            = (Rc.filter (fun p => p.val.1 = qq)).filter
                (fun p => ¬ (pred p = true)) := by
          rw [hRf, Finset.filter_comm]
        rw [e1, e2]
        exact Finset.card_filter_add_card_filter_not (fun p => pred p = true)
      -- threshold halving: 2·⌈u⌉ ≤ ⌈2u⌉ + 1
      have hkey : 2 * ⌈(2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ)⌉₊
          ≤ ⌈(2 : ℝ) ^ (R'e - s) * xseed * (Fintype.card X : ℝ)⌉₊ + 1 := by
        have hu0 : (0:ℝ) ≤ (2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ) :=
          mul_nonneg (mul_nonneg (by positivity) hxseed0.le) (Nat.cast_nonneg _)
        have hsplit2 : (2 : ℝ) ^ (R'e - s) * xseed * (Fintype.card X : ℝ)
            = 2 * ((2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ)) := by
          have hexp : R'e - s = (R'e - (s+1)) + 1 := by omega
          rw [hexp, pow_succ]
          ring
        rw [hsplit2]
        have h1 : (⌈(2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ)⌉₊ : ℝ)
            < (2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ) + 1 :=
          Nat.ceil_lt_add_one hu0
        have h2 : 2 * ((2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ))
            ≤ (⌈2 * ((2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ))⌉₊ : ℝ) :=
          Nat.le_ceil _
        have h3 : ((2 * ⌈(2 : ℝ) ^ (R'e - (s+1)) * xseed
              * (Fintype.card X : ℝ)⌉₊ : ℕ) : ℝ)
            < ((⌈2 * ((2 : ℝ) ^ (R'e - (s+1)) * xseed
              * (Fintype.card X : ℝ))⌉₊ + 2 : ℕ) : ℝ) := by
          push_cast
          linarith
        have h4 := Nat.cast_lt.mp h3
        omega
      set QT : Finset (Fin (2 ^ (R + T))) := Qc.filter (fun qq =>
        ⌈(2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ)⌉₊
          ≤ (Rt.filter (fun p => p.val.1 = qq)).card) with hQT
      set QF : Finset (Fin (2 ^ (R + T))) := Qc.filter (fun qq =>
        ¬ (⌈(2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ)⌉₊
          ≤ (Rt.filter (fun p => p.val.1 = qq)).card)) with hQF
      have hQTF : QT.card + QF.card = Qc.card := by
        rw [hQT, hQF]
        exact Finset.card_filter_add_card_filter_not _
      have hQFfib : ∀ qq ∈ QF,
          ⌈(2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ)⌉₊
            ≤ (Rf.filter (fun p => p.val.1 = qq)).card := by
        intro qq hqq
        rw [hQF, Finset.mem_filter] at hqq
        obtain ⟨hqqQ, hlight⟩ := hqq
        have hfib := hQfib qq hqqQ
        have hsq := hsum qq
        omega
      have hhalf : 2 ^ (R'e - (s+1)) * pseed ≤ QT.card
          ∨ 2 ^ (R'e - (s+1)) * pseed ≤ QF.card := by
        have hexp : R'e - s = (R'e - (s+1)) + 1 := by omega
        rw [hexp, pow_succ] at hQcard
        have h2 : 2 * (2 ^ (R'e - (s+1)) * pseed) ≤ QT.card + QF.card := by
          rw [hQTF]
          calc 2 * (2 ^ (R'e - (s+1)) * pseed)
              = 2 ^ (R'e - (s+1)) * 2 * pseed := by ring
            _ ≤ Qc.card := hQcard
        omega
      have hcost' : max l.cost r.cost + (s + 1) + c < D f + R'e + T := by
        have hc1 : (Protocol.aNode pred l r).cost = 1 + max l.cost r.cost := rfl
        omega
      rcases hhalf with hhT | hhF
      · -- keep the `pred = true` side; the residual subtree is `r`
        refine ihr (s+1) c QT Rt Cc (by omega) ?_ hhT ?_ hCcard ?_
        · intro x hx y hy
          rw [hRt, Finset.mem_filter] at hx
          have hev := hcomp x hx.1 y hy
          simp only [Protocol.eval] at hev
          rw [if_pos hx.2] at hev
          exact hev
        · intro qq hqq
          rw [hQT, Finset.mem_filter] at hqq
          exact hqq.2
        · have hle : r.cost ≤ max l.cost r.cost := le_max_right _ _
          omega
      · -- keep the `pred = false` side; the residual subtree is `l`
        refine ihl (s+1) c QF Rf Cc (by omega) ?_ hhF hQFfib hCcard ?_
        · intro x hx y hy
          rw [hRf, Finset.mem_filter] at hx
          have hev := hcomp x hx.1 y hy
          simp only [Protocol.eval] at hev
          rw [if_neg hx.2] at hev
          exact hev
        · have hle : l.cost ≤ max l.cost r.cost := le_max_left _ _
          omega
  | bNode pred l r ihl ihr =>
    rcases eq_or_lt_of_le hs with heq | hslt
    · subst heq
      exact hfire (Protocol.bNode pred l r) c Qc Rc Cc hcomp hQcard hQfib hCcard hcost
    · -- Bob (column) bit: one child keeps at least half the columns.
      set Ct : Finset {j // j ∈ Cs} := Cc.filter (fun j => pred j = true) with hCt
      set Cf : Finset {j // j ∈ Cs} := Cc.filter (fun j => ¬ (pred j = true)) with hCf
      have hCTF : Ct.card + Cf.card = Cc.card := by
        rw [hCt, hCf]
        exact Finset.card_filter_add_card_filter_not _
      have h2pos : (0:ℝ) < (2 : ℝ) ^ (a + c) := by positivity
      have hchoice : h * (L : ℝ) ≤ (2 : ℝ) ^ (a + (c+1)) * (Ct.card : ℝ)
          ∨ h * (L : ℝ) ≤ (2 : ℝ) ^ (a + (c+1)) * (Cf.card : ℝ) := by
        by_contra hno
        simp only [not_or, not_le] at hno
        obtain ⟨h1, h2⟩ := hno
        have hpe : (2 : ℝ) ^ (a + (c+1)) = (2 : ℝ) ^ (a + c) * 2 := by
          rw [show a + (c+1) = (a+c) + 1 from rfl, pow_succ]
        rw [hpe] at h1 h2
        have hcast : ((Ct.card : ℝ) + (Cf.card : ℝ)) = (Cc.card : ℝ) := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hCTF
        have hXC : (2 : ℝ) ^ (a + c) * (Cc.card : ℝ)
            = (2 : ℝ) ^ (a + c) * (Ct.card : ℝ)
              + (2 : ℝ) ^ (a + c) * (Cf.card : ℝ) := by
          rw [← hcast]
          ring
        linarith [hCcard]
      have hcost' : max l.cost r.cost + s + (c + 1) < D f + R'e + T := by
        have hc1 : (Protocol.bNode pred l r).cost = 1 + max l.cost r.cost := rfl
        omega
      rcases hchoice with hct | hcf
      · refine ihr s (c+1) Qc Rc Ct hs ?_ hQcard hQfib hct ?_
        · intro x hx y hy
          rw [hCt, Finset.mem_filter] at hy
          have hev := hcomp x hx y hy.1
          simp only [Protocol.eval] at hev
          rw [if_pos hy.2] at hev
          exact hev
        · have hle : r.cost ≤ max l.cost r.cost := le_max_right _ _
          omega
      · refine ihl s (c+1) Qc Rc Cf hs ?_ hQcard hQfib hcf ?_
        · intro x hx y hy
          rw [hCf, Finset.mem_filter] at hy
          have hev := hcomp x hx y hy.1
          simp only [Protocol.eval] at hev
          rw [if_neg hy.2] at hev
          exact hev
        · have hle : l.cost ≤ max l.cost r.cost := le_max_left _ _
          omega

/-- The master induction: the localized Extension statement, proved by
running `extension_chain` from the root of a depth-`< D f + (R'e + T)`
protocol (obtained from `Nat.sInf_mem` on the achievable-cost set). Both
frozen claims below are instances (`thm:Extension` at `a = 0, R'e = R`). -/
private theorem extension_master {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {b ε : ℝ} (hε : 0 ≤ ε)
    (T R : ℕ)
    {L : ℕ} (S : Fin L → Fin (2 ^ (R + T)) → Y)
    (hS : IsBalancedFamily (2 ^ T) S ε)
    (pseed : ℕ) {xseed h hseed : ℝ}
    (hx1 : (2 : ℝ) ^ (-b) ≤ xseed) (hx2 : xseed ≤ 1)
    (hh0 : 0 < h)
    (hp1 : 2 ^ T ≤ 2 * pseed) (hp2 : pseed ≤ 2 ^ T)
    (hres : IsColumnLossResilient f b ε (R + T) T h)
    (hseedbd : D f + T ≤ Dfamily (interlaceFun f pseed)
        (bracketGE X Y pseed xseed hseed))
    (hbridge : hseed ≤ h * (2 : ℝ) ^ (-((T + D f : ℕ) : ℝ)) / (1 + ε))
    (a R'e : ℕ) (ha : a ≤ 1) (hR'R : R'e ≤ R)
    (Rs : Finset (Fin (2 ^ (R + T)) × X)) (Cs : Finset (Fin L))
    (hRs : ∃ Qs : Finset (Fin (2 ^ (R + T))), Qs.card = 2 ^ R'e * pseed ∧
        IsEquipartitionedGE Rs Qs
          ⌈(2 : ℝ) ^ (R'e : ℕ) * xseed * (Fintype.card X : ℝ)⌉₊)
    (hCs : h * (2 : ℝ) ^ (-(a : ℝ)) * (L : ℝ) ≤ (Cs.card : ℝ)) :
    D f + (R'e + T) ≤ D (subgame (relaxedInterlace f S) Rs Cs) := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨Qs, hQscard, hQseq⟩ := hRs
  have hxb1 : (2 : ℝ) ^ (-b) ≤ 1 := le_trans hx1 hx2
  have hY : 0 < Fintype.card Y := card_Y_pos_of_clause_one f hxb1 hres.1
  have hne : (AchievableCosts (subgame (relaxedInterlace f S) Rs Cs)).Nonempty :=
    Workspace.UpperBound.AchievableCosts_nonempty _
  have hDmem : D (subgame (relaxedInterlace f S) Rs Cs)
      ∈ AchievableCosts (subgame (relaxedInterlace f S) Rs Cs) := by
    simpa [D] using Nat.sInf_mem hne
  obtain ⟨P₀, hP₀cost, hP₀comp⟩ := hDmem
  -- base invariant
  have hQbase : 2 ^ (R'e - 0) * pseed ≤ Qs.card := by
    rw [Nat.sub_zero, hQscard]
  have hQfibbase : ∀ qq ∈ Qs,
      ⌈(2 : ℝ) ^ (R'e - 0) * xseed * (Fintype.card X : ℝ)⌉₊
        ≤ (Rs.attach.filter (fun p => p.val.1 = qq)).card := by
    intro qq hqq
    calc ⌈(2 : ℝ) ^ (R'e - 0) * xseed * (Fintype.card X : ℝ)⌉₊
        ≤ (Rs.filter (fun p => p.1 = qq)).card := hQseq qq hqq
      _ = (Rs.attach.filter (fun p => p.val.1 = qq)).card := by
          have h1 := card_filter_image_val (s := Rs) Rs.attach (fun p => p.1 = qq)
          rw [Finset.attach_image_val] at h1
          exact h1
  have hCbase : h * (L : ℝ) ≤ (2 : ℝ) ^ (a + 0) * ((Cs.attach.card : ℕ) : ℝ) := by
    rw [Finset.card_attach, Nat.add_zero]
    have hpp : (2 : ℝ) ^ a * ((2 : ℝ) ^ (-(a : ℝ))) = 1 := by
      rw [← Real.rpow_natCast 2 a, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      simp
    calc h * (L : ℝ)
        = ((2 : ℝ) ^ a * ((2 : ℝ) ^ (-(a : ℝ)))) * (h * (L : ℝ)) := by
          rw [hpp, one_mul]
      _ = (2 : ℝ) ^ a * (h * (2 : ℝ) ^ (-(a : ℝ)) * (L : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ a * ((Cs.card : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hCs (by positivity)
  exact extension_chain f hε T R S hS pseed hx1 hh0 hp1 hp2 hres hseedbd hbridge
    a R'e ha hR'R Rs Cs hY P₀ 0 0 Qs Rs.attach Cs.attach
    (Nat.zero_le _) (fun x _ y _ => hP₀comp x y) hQbase hQfibbase hCbase
    (by omega)

-- CLAIM-BEGIN thm:Extension
/-- Paper `thm:Extension` (Extension theorem, §4 black box #1). Renderings:
`t = 2^T`, `r = 2^R` powers of two (`q = r·t = 2^(R+T)`, so `log q = R + T`,
`log t = T`, `log = log₂`); `t ≤ 2^b` is `(T:ℝ) ≤ b`; `t/2 ≤ p_seed` is
`2^T ≤ 2·p_seed` (exact integer form, correct at `T = 0`). The relaxed
interlace `Ŝ = ⟨M⟩_{q,S}` is `relaxedInterlace f S` for an ARBITRARY
`(q,t)`-balanced family `S : Fin L → Fin q → Y` with accuracy `ε`
(the paper's selected family `S_{q,t}(Cols M)` is one instance; its exact
AGHP/Bshouty citation boundary is documented separately;
`|Cols Ŝ| = L`, family-index columns per
`def:relaxed-interlace`). Submatrix condition (i) is GE-equipartition at
threshold `⌈r·x_seed·m⌉` over an EXACT-size block set `|Q| = r·p_seed`;
(ii) is `h·L ≤ |C'|`. Conclusion: `comp N ≥ comp M + log q` with
`N = subgame (relaxedInterlace f S) R' C'` and `comp N = D N`. -/
theorem extension_theorem {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {b ε : ℝ} (hb : 1 ≤ b) (hε : 0 ≤ ε)
    (T R : ℕ) (hTb : (T : ℝ) ≤ b)
    {L : ℕ} (S : Fin L → Fin (2 ^ (R + T)) → Y)
    (hS : IsBalancedFamily (2 ^ T) S ε)
    (pseed : ℕ) {xseed h hseed : ℝ}
    (hx1 : (2 : ℝ) ^ (-b) ≤ xseed) (hx2 : xseed ≤ 1)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs0 : 0 < hseed) (hs1 : hseed ≤ 1)
    (hp1 : 2 ^ T ≤ 2 * pseed) (hp2 : pseed ≤ 2 ^ T)
    (hres : IsColumnLossResilient f b ε (R + T) T h)
    (hseedbd : D f + T ≤ Dfamily (interlaceFun f pseed)
        (bracketGE X Y pseed xseed hseed))
    (hbridge : hseed ≤ h * (2 : ℝ) ^ (-((T + D f : ℕ) : ℝ)) / (1 + ε))
    (R' : Finset (Fin (2 ^ (R + T)) × X)) (C' : Finset (Fin L))
    (hR' : ∃ Qs : Finset (Fin (2 ^ (R + T))), Qs.card = 2 ^ R * pseed ∧
        IsEquipartitionedGE R' Qs
          ⌈(2 : ℝ) ^ (R : ℕ) * xseed * (Fintype.card X : ℝ)⌉₊)
    (hC' : h * (L : ℝ) ≤ (C'.card : ℝ)) :
    D f + (R + T) ≤ D (subgame (relaxedInterlace f S) R' C') :=
-- CLAIM-END thm:Extension
  by
  have _guards : (1 ≤ b) ∧ ((T : ℝ) ≤ b) ∧ (h ≤ 1) ∧ (0 < hseed) ∧ (hseed ≤ 1) :=
    ⟨hb, hTb, hh1, hs0, hs1⟩
  exact extension_master f hε T R S hS pseed hx1 hx2 hh0 hp1 hp2 hres hseedbd
    hbridge 0 R (Nat.zero_le 1) (le_refl R) R' C' hR' (by simpa using hC')

-- CLAIM-BEGIN cor:localized-extension
/-- Paper `cor:localized-extension`: under the Extension theorem's
hypotheses, a localized submatrix — `r' = 2^R'` with `R' ≤ R`, block set of
exact size `r'·p_seed`, equipartition threshold `⌈r'·x_seed·m⌉`, and column
fraction `h·2^{−a}` for `a ∈ {0,1}` — has `comp ≥ comp M + log(r'·t)
= D f + (R' + T)`. Same renderings as `thm:Extension`. -/
theorem localized_extension {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {b ε : ℝ} (hb : 1 ≤ b) (hε : 0 ≤ ε)
    (T R : ℕ) (hTb : (T : ℝ) ≤ b)
    {L : ℕ} (S : Fin L → Fin (2 ^ (R + T)) → Y)
    (hS : IsBalancedFamily (2 ^ T) S ε)
    (pseed : ℕ) {xseed h hseed : ℝ}
    (hx1 : (2 : ℝ) ^ (-b) ≤ xseed) (hx2 : xseed ≤ 1)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs0 : 0 < hseed) (hs1 : hseed ≤ 1)
    (hp1 : 2 ^ T ≤ 2 * pseed) (hp2 : pseed ≤ 2 ^ T)
    (hres : IsColumnLossResilient f b ε (R + T) T h)
    (hseedbd : D f + T ≤ Dfamily (interlaceFun f pseed)
        (bracketGE X Y pseed xseed hseed))
    (hbridge : hseed ≤ h * (2 : ℝ) ^ (-((T + D f : ℕ) : ℝ)) / (1 + ε))
    (a R'e : ℕ) (ha : a ≤ 1) (hR'R : R'e ≤ R)
    (Rs : Finset (Fin (2 ^ (R + T)) × X)) (Cs : Finset (Fin L))
    (hRs : ∃ Qs : Finset (Fin (2 ^ (R + T))), Qs.card = 2 ^ R'e * pseed ∧
        IsEquipartitionedGE Rs Qs
          ⌈(2 : ℝ) ^ (R'e : ℕ) * xseed * (Fintype.card X : ℝ)⌉₊)
    (hCs : h * (2 : ℝ) ^ (-(a : ℝ)) * (L : ℝ) ≤ (Cs.card : ℝ)) :
    D f + (R'e + T) ≤ D (subgame (relaxedInterlace f S) Rs Cs) :=
-- CLAIM-END cor:localized-extension
  by
  have _guards : (1 ≤ b) ∧ ((T : ℝ) ≤ b) ∧ (h ≤ 1) ∧ (0 < hseed) ∧ (hseed ≤ 1) :=
    ⟨hb, hTb, hh1, hs0, hs1⟩
  exact extension_master f hε T R S hS pseed hx1 hx2 hh0 hp1 hp2 hres hseedbd
    hbridge a R'e ha hR'R Rs Cs hRs hCs

/-! ## Private toolkit for `thm:SeparationTheorem`

The paper's proof (§4, three-phase protocol control) is formalized as ONE
structural induction over the artifact `Protocol` tree (`sep_main_chain`),
maintaining the uniform invariant "after `d` spent bits the surviving
rectangle still holds `≥ 2^(R+T−d)` outer blocks of `≥ ⌈m·2^(−d)⌉` rows
each, with the full column set", plus a SECOND structural induction
(`sep_chase` — the paper's Phase-2 unbalanced-row continuation) walking an
over-heavy row-split child (`> q_s/2` assigned blocks) down to the
`t/2 + 1`-block classical contradiction.  Exclusions: in the outer phase
(`d ≤ R`) leaves and column bits die by `localized_extension` at `a = 0` /
`a = 1`; in the inner phase (`d > R`) the surviving witness is bridged by
`relaxed_to_classical` and priced by `power_of_two_lower` /
`plus_one_family` / `two_copy_amplification` (`hband` feeds every
column-halving step).  Conjunct (b) is `no_waste_row_partition` at
`Q = univ`, `Rin = univ`, `T₀ = card X` (fibers of `univ` hold exactly `m`
rows; `hgap` is literally its `q·T < T₀` side condition), with `hNoTwo`
discharged by the two-copy residual-budget contradiction through
`D_prefixFiber_le_of_residual`.  The strong exponent bound
`(R+T) + 1 ≤ b` needed by every inner-phase density comparison is derived
from `hgap` (as in `classical_separation`'s `hxstrong`). -/

private theorem sep_delta_half {δ : ℝ} (hδ : δ ≤ 1 / Real.sqrt 2 - 1 / 2) :
    δ ≤ 1 / 2 := by
  have hsqrt_ge_one : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hinv : 1 / Real.sqrt 2 ≤ 1 := by
    rw [one_div]
    exact inv_le_one_of_one_le₀ hsqrt_ge_one
  linarith

/-- `(1/2+δ)² ≤ y` from the band hypothesis `2(1/2+δ)² ≤ y`. -/
private theorem sep_band_weak {δ y : ℝ} (hband : 2 * (1 / 2 + δ) ^ 2 ≤ y) :
    (1 / 2 + δ) ^ 2 ≤ y := by
  nlinarith [sq_nonneg (1 / 2 + δ)]

/-- The two consequences of `hgap`: `X` is nonempty and the strong exponent
bound `(R+T) + 1 ≤ b` (in fact `< b`). -/
private theorem sep_gap_consequences {X : Type*} [Fintype X] {b : ℝ} {R T : ℕ}
    (hgap : 2 ^ (R + T) * ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊
      < Fintype.card X) :
    1 ≤ Fintype.card X ∧ ((R + T : ℕ) : ℝ) + 1 ≤ b := by
  have hm1 : 1 ≤ Fintype.card X := by omega
  refine ⟨hm1, ?_⟩
  have hmR : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hm1
  have hceil : (2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)
      ≤ (⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hcast : ((2 ^ (R + T) * ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊ : ℕ) : ℝ)
      < (Fintype.card X : ℝ) := by exact_mod_cast hgap
  push_cast at hcast
  have hchain : ((2 : ℝ) ^ (R + T)) * ((2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ))
      < (Fintype.card X : ℝ) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hceil (by positivity)) hcast
  have hdiv : ((2 : ℝ) ^ (R + T)) * (2 : ℝ) ^ (1 - b) < 1 := by
    have h2 : ((2 : ℝ) ^ (R + T)) * (2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)
        < 1 * (Fintype.card X : ℝ) := by
      rw [one_mul]
      nlinarith [hchain]
    exact lt_of_mul_lt_mul_right h2 (le_of_lt hmR)
  have hrw : ((2 : ℝ) ^ (R + T)) * (2 : ℝ) ^ (1 - b)
      = (2 : ℝ) ^ (((R + T : ℕ) : ℝ) + (1 - b)) := by
    rw [← Real.rpow_natCast 2 (R + T),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [hrw] at hdiv
  have h0 : (2 : ℝ) ^ (((R + T : ℕ) : ℝ) + (1 - b)) < (2 : ℝ) ^ (0 : ℝ) := by
    rw [Real.rpow_zero]
    exact hdiv
  have hexp := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h0
  linarith

/-- The full-row-set fiber of block `qq` is a copy of `X`. -/
private theorem sep_fiber_univ_card {X : Type*} [Fintype X] {q : ℕ} (qq : Fin q) :
    ((Finset.univ : Finset (Fin q × X)).filter (fun p => p.1 = qq)).card
      = Fintype.card X := by
  classical
  have hset : (Finset.univ : Finset (Fin q × X)).filter (fun p => p.1 = qq)
      = {qq} ×ˢ (Finset.univ : Finset X) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_singleton, and_true]
  rw [hset, Finset.card_product]
  simp

/-- Threshold halving for the chain thresholds `⌈m·2^(−d)⌉`:
`2⌈m·2^(−(d+1))⌉ ≤ ⌈m·2^(−d)⌉ + 1`. -/
private theorem sep_ceil_halving (m d : ℕ) :
    2 * ⌈(m : ℝ) * (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ))⌉₊
      ≤ ⌈(m : ℝ) * (2 : ℝ) ^ (-(d : ℝ))⌉₊ + 1 := by
  set A : ℝ := (m : ℝ) * (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ)) with hA
  have hu0 : (0 : ℝ) ≤ A := by
    rw [hA]
    positivity
  have hsplit : (m : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) = 2 * A := by
    rw [hA]
    have hexp : (2 : ℝ) ^ (-(d : ℝ)) = 2 * (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ)) := by
      have h1 : -(d : ℝ) = 1 + (-(((d + 1 : ℕ)) : ℝ)) := by push_cast; ring
      rw [h1, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    rw [hexp]
    ring
  have h1 : (⌈A⌉₊ : ℝ) < A + 1 := Nat.ceil_lt_add_one hu0
  have h2 : 2 * A ≤ (⌈2 * A⌉₊ : ℝ) := Nat.le_ceil _
  have h3 : ((2 * ⌈A⌉₊ : ℕ) : ℝ) < ((⌈2 * A⌉₊ + 2 : ℕ) : ℝ) := by
    push_cast
    linarith
  have h4 := Nat.cast_lt.mp h3
  rw [hsplit]
  omega

/-- Density comparison for `power_of_two_lower`'s row parameter:
`2^w·2^(−b) ≤ 2^(−d)` whenever `w + d ≤ b`. -/
private theorem sep_pow_density_le {w d : ℕ} {b : ℝ}
    (hwd : ((w : ℕ) : ℝ) + (d : ℝ) ≤ b) :
    (2 : ℝ) ^ (w : ℕ) * (2 : ℝ) ^ (-b) ≤ (2 : ℝ) ^ (-(d : ℝ)) := by
  rw [← Real.rpow_natCast 2 w, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- Density comparison for `plus_one_family`'s row parameter:
`2^(k−b) ≤ 2^(−d)` whenever `k + d ≤ b`. -/
private theorem sep_rpow_density_le {d : ℕ} {k b : ℝ} (hkd : k + (d : ℝ) ≤ b) :
    (2 : ℝ) ^ (k - b) ≤ (2 : ℝ) ^ (-(d : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- One side of a Boolean split keeps at least half the set. -/
private theorem sep_half_side {α : Type*} (s : Finset α) (p : α → Bool) :
    ∃ β : Bool, s.card ≤ 2 * (s.filter fun a => p a = β).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := s)
    (p := fun a => p a = true)
  by_cases hle : (s.filter fun a => ¬ p a = true).card
      ≤ (s.filter fun a => p a = true).card
  · exact ⟨true, by omega⟩
  · refine ⟨false, ?_⟩
    have heq : (s.filter fun a => p a = false)
        = (s.filter fun a => ¬ p a = true) := by
      apply Finset.filter_congr
      intro a _
      simp
    rw [heq]
    omega

/-- Bool-filter bookkeeping: the `= false` filter is the `¬ (= true)` filter. -/
private theorem sep_filter_false_eq {α : Type*} (s : Finset α) (p : α → Bool) :
    (s.filter fun a => p a = false) = (s.filter fun a => ¬ p a = true) := by
  classical
  apply Finset.filter_congr
  intro a _
  simp

/-- The `2^(k−1)+1`-copy classical family bound at row density `2^(k−b)`,
uniform in `k ≥ 1` (the paper's `cor:plus-one-family` for `k ≥ 2`,
`cor:two-copy-amplification` at `k = 1`). -/
private theorem sep_plus_one_fam {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {δ b : ℝ}
    (hrob : IsRobust f δ b) (hb : 1 ≤ b) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hD : 2 ≤ D f) (k : ℕ) (hk1 : 1 ≤ k) (hkb : (k : ℝ) ≤ b) :
    D f + k ≤ Dfamily (interlaceFun f (2 ^ (k - 1) + 1))
      (bracketGE X Y (2 ^ (k - 1) + 1) ((2 : ℝ) ^ ((k : ℝ) - b))
        ((1 / 2 + δ) ^ 2)) := by
  rcases eq_or_lt_of_le hk1 with hk1' | hk2
  · -- k = 1: the two-copy bound
    rw [← hk1']
    have h2c := two_copy_amplification hrob hb hδ0 hδ2 hD
    have hgoal : D f + 1 ≤ Dfamily (interlaceFun f 2)
        (bracketGE X Y 2 ((2 : ℝ) ^ ((1 : ℝ) - b)) ((1 / 2 + δ) ^ 2)) := by
      exact_mod_cast h2c
    simpa using hgoal
  · exact plus_one_family hrob hb hδ0 hδ2 hD k hk2 hkb

/-- Residual upper bound: a protocol agreeing with the relaxed game on a
rectangle prices every relaxed subgame drawn from inside that rectangle at
its own cost (`Protocol.pullback` transport, cf. `extension_seed_step`). -/
private theorem sep_residual_upper {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {q L : ℕ} (S : Fin L → Fin q → Y)
    (Rs : Finset (Fin q × X)) (Cs : Finset (Fin L))
    (P' : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool)
    (Rc : Finset {p // p ∈ Rs}) (Cc : Finset {j // j ∈ Cs})
    (hcomp : ∀ x ∈ Rc, ∀ y ∈ Cc,
      P'.eval x y = subgame (relaxedInterlace f S) Rs Cs x y)
    (Rsx : Finset (Fin q × X)) (Csx : Finset (Fin L))
    (hRsub : ∀ p ∈ Rsx, ∃ w, w ∈ Rc ∧ (w : {p // p ∈ Rs}).val = p)
    (hCsub : ∀ j ∈ Csx, ∃ w, w ∈ Cc ∧ (w : {j // j ∈ Cs}).val = j) :
    D (subgame (relaxedInterlace f S) Rsx Csx) ≤ P'.cost := by
  classical
  have hρex : ∀ p : {p // p ∈ Rsx}, ∃ w, w ∈ Rc ∧ (w : {p // p ∈ Rs}).val = p.val :=
    fun p => hRsub p.val p.2
  choose ρ hρmem hρval using hρex
  have hσex : ∀ j : {j // j ∈ Csx}, ∃ w, w ∈ Cc ∧ (w : {j // j ∈ Cs}).val = j.val :=
    fun j => hCsub j.val j.2
  choose σ hσmem hσval using hσex
  have hPb : (Protocol.pullback ρ σ P').Computes
      (subgame (relaxedInterlace f S) Rsx Csx) := by
    intro p j
    rw [Protocol.pullback_eval, hcomp (ρ p) (hρmem p) (σ j) (hσmem j)]
    show relaxedInterlace f S (ρ p).val (σ j).val = relaxedInterlace f S p.val j.val
    rw [hρval p, hσval j]
  have hmem2 : (Protocol.pullback ρ σ P').cost
      ∈ AchievableCosts (subgame (relaxedInterlace f S) Rsx Csx) :=
    ⟨Protocol.pullback ρ σ P', rfl, hPb⟩
  have hle := Nat.sInf_le hmem2
  rw [Protocol.pullback_cost] at hle
  simpa [D] using hle

/-- Bridged classical lower bound: a `u ≤ t`-block relaxed witness at row
threshold `⌈m·x_w⌉` and column mass `γ·L` prices the ambient relaxed subgame
by any classical `u`-copy family bound at weaker parameters
(`relaxed_to_classical` + `bracketGE.anti_mono_params` + `D_mapNodes_le`). -/
private theorem sep_bridge_lower {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {ε : ℝ} (hε : 0 ≤ ε) {q L t : ℕ}
    {S : Fin L → Fin q → Y} (hS : IsBalancedFamily t S ε)
    {u : ℕ} (hu : 0 < u) (hut : u ≤ t)
    {w : ℕ} {xstar ystar xw γ : ℝ}
    (hfam : D f + w ≤ Dfamily (interlaceFun f u) (bracketGE X Y u xstar ystar))
    (hxstar : xstar ≤ xw) (hystar : ystar ≤ γ / (1 + ε))
    (J : Finset (Fin q)) (hJcard : J.card = u)
    (Rsx : Finset (Fin q × X)) (Csx : Finset (Fin L))
    (hfib : ∀ qq ∈ J, ⌈(Fintype.card X : ℝ) * xw⌉₊
        ≤ (Rsx.filter (fun p => p.1 = qq)).card)
    (hCsx : γ * (L : ℝ) ≤ (Csx.card : ℝ)) :
    D f + w ≤ D (subgame (relaxedInterlace f S) Rsx Csx) := by
  classical
  set e : Fin u ≃ {i // i ∈ J} := (J.orderIsoOfFin hJcard).toEquiv with he
  have hrow : IsEquipartitionedGE Rsx J ⌈(Fintype.card X : ℝ) * xw⌉₊ :=
    fun qq hqq => hfib qq hqq
  obtain ⟨RC', hmem, hRowsProv, hColsProv⟩ :=
    relaxed_to_classical hu hut hS hε e hrow hCsx (le_refl _)
  have hmem' : RC' ∈ bracketGE X Y u xstar ystar :=
    bracketGE.anti_mono_params u hxstar hystar hmem
  have hFam_le : Dfamily (interlaceFun f u) (bracketGE X Y u xstar ystar)
      ≤ D (subgame (interlaceFun f u) RC'.1 RC'.2) := by
    have hm : D (subgame (interlaceFun f u) RC'.1 RC'.2)
        ∈ { d : ℕ | ∃ RC ∈ bracketGE X Y u xstar ystar,
            d = D (subgame (interlaceFun f u) RC.1 RC.2) } := ⟨RC', hmem', rfl⟩
    simpa [Dfamily] using Nat.sInf_le hm
  have hσex : ∀ cc : {c' // c' ∈ RC'.2}, ∃ jj, jj ∈ Csx ∧
      ∀ i : Fin u, cc.val i = S jj (e i).val := by
    intro cc
    obtain ⟨j, hj, hjeq⟩ := hColsProv cc.val cc.2
    exact ⟨j, hj, hjeq⟩
  choose σj hσmem hσval using hσex
  have heq : subgame (interlaceFun f u) RC'.1 RC'.2
      = (fun (p : {p // p ∈ RC'.1}) (cc : {c' // c' ∈ RC'.2}) =>
          subgame (relaxedInterlace f S) Rsx Csx
            ⟨((e p.val.1).val, p.val.2), hRowsProv p.val p.2⟩
            ⟨σj cc, hσmem cc⟩) := by
    funext p cc
    show f p.val.2 (cc.val p.val.1) = f p.val.2 (S (σj cc) (e p.val.1).val)
    exact congrArg (fun yy => f p.val.2 yy) (hσval cc p.val.1)
  have hD_le : D (subgame (interlaceFun f u) RC'.1 RC'.2)
      ≤ D (subgame (relaxedInterlace f S) Rsx Csx) := by
    rw [heq]
    exact D_mapNodes_le (subgame (relaxedInterlace f S) Rsx Csx)
      (fun p : {p // p ∈ RC'.1} =>
        (⟨((e p.val.1).val, p.val.2), hRowsProv p.val p.2⟩ : {p // p ∈ Rsx}))
      (fun cc : {c' // c' ∈ RC'.2} =>
        (⟨σj cc, hσmem cc⟩ : {j // j ∈ Csx}))
  omega

/-- Outer-phase relaxed lower bound (`d ≤ R` spent bits): the surviving
`2^(R+T−d)`-block witness at threshold `⌈m·2^(−d)⌉` instantiates
`cor:localized-extension` at `R'e = R − d`, pricing the ambient relaxed
subgame at `D f + (R − d) + T` (column fraction `h·2^(−a)`, `a ∈ {0,1}`). -/
private theorem sep_outer_lower {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {b ε : ℝ} (hb : 1 ≤ b) (hε : 0 ≤ ε)
    (T R : ℕ) (hTb : (T : ℝ) ≤ b)
    {L : ℕ} (S : Fin L → Fin (2 ^ (R + T)) → Y)
    (hS : IsBalancedFamily (2 ^ T) S ε)
    (pseed : ℕ) {xseed h hseed : ℝ}
    (hx1 : (2 : ℝ) ^ (-b) ≤ xseed) (hx2 : xseed ≤ (2 : ℝ) ^ (-(R : ℝ)))
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs0 : 0 < hseed) (hs1 : hseed ≤ 1)
    (hp1 : 2 ^ T ≤ 2 * pseed) (hp2 : pseed ≤ 2 ^ T)
    (hres : IsColumnLossResilient f b ε (R + T) T h)
    (hseedbd : D f + T ≤ Dfamily (interlaceFun f pseed)
        (bracketGE X Y pseed xseed hseed))
    (hbridge : hseed ≤ h * (2 : ℝ) ^ (-((T + D f : ℕ) : ℝ)) / (1 + ε))
    {d a : ℕ} (hdR : d ≤ R) (ha : a ≤ 1)
    (Qc : Finset (Fin (2 ^ (R + T)))) (hQcard : 2 ^ (R + T - d) ≤ Qc.card)
    (Rsx : Finset (Fin (2 ^ (R + T)) × X)) (Csx : Finset (Fin L))
    (hfib : ∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-(d : ℝ))⌉₊
        ≤ (Rsx.filter (fun p => p.1 = qq)).card)
    (hCsx : h * (2 : ℝ) ^ (-(a : ℝ)) * (L : ℝ) ≤ (Csx.card : ℝ)) :
    D f + ((R - d) + T) ≤ D (subgame (relaxedInterlace f S) Rsx Csx) := by
  classical
  have hxseed1 : xseed ≤ 1 := by
    refine le_trans hx2 ?_
    rw [← Real.rpow_zero 2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (neg_nonpos.mpr (Nat.cast_nonneg R))
  have hsub : 2 ^ (R - d) * pseed ≤ Qc.card := by
    have h1 : 2 ^ (R - d) * pseed ≤ 2 ^ (R - d) * 2 ^ T :=
      Nat.mul_le_mul_left _ hp2
    have h2 : 2 ^ (R - d) * 2 ^ T = 2 ^ (R + T - d) := by
      rw [← pow_add]
      congr 1
      omega
    omega
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hsub
  have hthr : ⌈(2 : ℝ) ^ ((R - d : ℕ)) * xseed * (Fintype.card X : ℝ)⌉₊
      ≤ ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-(d : ℝ))⌉₊ := by
    apply Nat.ceil_le_ceil
    have hx : (2 : ℝ) ^ ((R - d : ℕ)) * xseed ≤ (2 : ℝ) ^ (-(d : ℝ)) := by
      have hcast : (2 : ℝ) ^ ((R - d : ℕ)) = (2 : ℝ) ^ ((R : ℝ) - (d : ℝ)) := by
        rw [← Real.rpow_natCast 2 (R - d), Nat.cast_sub hdR]
      rw [hcast]
      calc (2 : ℝ) ^ ((R : ℝ) - (d : ℝ)) * xseed
          ≤ (2 : ℝ) ^ ((R : ℝ) - (d : ℝ)) * (2 : ℝ) ^ (-(R : ℝ)) :=
            mul_le_mul_of_nonneg_left hx2 (by positivity)
        _ = (2 : ℝ) ^ (-(d : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            congr 1
            ring
    calc (2 : ℝ) ^ ((R - d : ℕ)) * xseed * (Fintype.card X : ℝ)
        ≤ (2 : ℝ) ^ (-(d : ℝ)) * (Fintype.card X : ℝ) :=
          mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg _)
      _ = (Fintype.card X : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) := mul_comm _ _
  have hRs : ∃ Qs : Finset (Fin (2 ^ (R + T))), Qs.card = 2 ^ (R - d) * pseed ∧
      IsEquipartitionedGE Rsx Qs
        ⌈(2 : ℝ) ^ ((R - d : ℕ)) * xseed * (Fintype.card X : ℝ)⌉₊ :=
    ⟨J, hJcard, fun qq hqq => le_trans hthr (hfib qq (hJsub hqq))⟩
  exact localized_extension f hb hε T R hTb S hS pseed hx1 hxseed1 hh0 hh1 hs0
    hs1 hp1 hp2 hres hseedbd hbridge a (R - d) ha (Nat.sub_le R d) Rsx Csx hRs
    hCsx

/-- Outer-phase budget clash (subtype level): a residual protocol of cost
`< D f + (R − d) + T` agreeing with the relaxed game on a rectangle that
still carries the `d`-level witness is impossible. -/
private theorem sep_outer_clash {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {b ε : ℝ} (hb : 1 ≤ b) (hε : 0 ≤ ε)
    (T R : ℕ) (hTb : (T : ℝ) ≤ b)
    {L : ℕ} (S : Fin L → Fin (2 ^ (R + T)) → Y)
    (hS : IsBalancedFamily (2 ^ T) S ε)
    (pseed : ℕ) {xseed h hseed : ℝ}
    (hx1 : (2 : ℝ) ^ (-b) ≤ xseed) (hx2 : xseed ≤ (2 : ℝ) ^ (-(R : ℝ)))
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs0 : 0 < hseed) (hs1 : hseed ≤ 1)
    (hp1 : 2 ^ T ≤ 2 * pseed) (hp2 : pseed ≤ 2 ^ T)
    (hres : IsColumnLossResilient f b ε (R + T) T h)
    (hseedbd : D f + T ≤ Dfamily (interlaceFun f pseed)
        (bracketGE X Y pseed xseed hseed))
    (hbridge : hseed ≤ h * (2 : ℝ) ^ (-((T + D f : ℕ) : ℝ)) / (1 + ε))
    (Rs : Finset (Fin (2 ^ (R + T)) × X)) (Cs : Finset (Fin L))
    (P' : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool)
    (Rc : Finset {p // p ∈ Rs}) (Cc : Finset {j // j ∈ Cs})
    (hcomp : ∀ x ∈ Rc, ∀ y ∈ Cc,
      P'.eval x y = subgame (relaxedInterlace f S) Rs Cs x y)
    {d a : ℕ} (hdR : d ≤ R) (ha : a ≤ 1)
    (Qc : Finset (Fin (2 ^ (R + T)))) (hQcard : 2 ^ (R + T - d) ≤ Qc.card)
    (hQfib : ∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-(d : ℝ))⌉₊
        ≤ (Rc.filter (fun p => p.val.1 = qq)).card)
    (hCcard : h * (2 : ℝ) ^ (-(a : ℝ)) * (L : ℝ)
        ≤ (((Cc.image Subtype.val).card : ℕ) : ℝ))
    (hPcost : P'.cost < D f + ((R - d) + T)) : False := by
  classical
  have hfib' : ∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-(d : ℝ))⌉₊
      ≤ ((Rc.image Subtype.val).filter (fun p => p.1 = qq)).card := by
    intro qq hqq
    rw [card_filter_image_val]
    exact hQfib qq hqq
  have hlow := sep_outer_lower f hb hε T R hTb S hS pseed hx1 hx2 hh0 hh1 hs0
    hs1 hp1 hp2 hres hseedbd hbridge hdR ha Qc hQcard (Rc.image Subtype.val)
    (Cc.image Subtype.val) hfib' hCcard
  have hup := sep_residual_upper f S Rs Cs P' Rc Cc hcomp
    (Rc.image Subtype.val) (Cc.image Subtype.val)
    (by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨wit, hw, hweq⟩ := hp
      exact ⟨wit, hw, hweq⟩)
    (by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨wit, hw, hweq⟩ := hj
      exact ⟨wit, hw, hweq⟩)
  omega

/-- Bridged classical budget clash (subtype level): a residual protocol of
cost `< D f + w` agreeing with the relaxed game on a rectangle carrying a
`u ≤ t`-block witness priced at `D f + w` by a classical family bound is
impossible. -/
private theorem sep_bridge_clash {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {ε : ℝ} (hε : 0 ≤ ε) {q L t : ℕ}
    {S : Fin L → Fin q → Y} (hS : IsBalancedFamily t S ε)
    {u : ℕ} (hu : 0 < u) (hut : u ≤ t)
    {w : ℕ} {xstar ystar xw γ : ℝ}
    (hfam : D f + w ≤ Dfamily (interlaceFun f u) (bracketGE X Y u xstar ystar))
    (hxstar : xstar ≤ xw) (hystar : ystar ≤ γ / (1 + ε))
    (Rs : Finset (Fin q × X)) (Cs : Finset (Fin L))
    (P' : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool)
    (Rc : Finset {p // p ∈ Rs}) (Cc : Finset {j // j ∈ Cs})
    (hcomp : ∀ x ∈ Rc, ∀ y ∈ Cc,
      P'.eval x y = subgame (relaxedInterlace f S) Rs Cs x y)
    (Qc : Finset (Fin q)) (hQu : u ≤ Qc.card)
    (hQfib : ∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ) * xw⌉₊
        ≤ (Rc.filter (fun p => p.val.1 = qq)).card)
    (hCcard : γ * (L : ℝ) ≤ (((Cc.image Subtype.val).card : ℕ) : ℝ))
    (hPcost : P'.cost < D f + w) : False := by
  classical
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hQu
  have hfib' : ∀ qq ∈ J, ⌈(Fintype.card X : ℝ) * xw⌉₊
      ≤ ((Rc.image Subtype.val).filter (fun p => p.1 = qq)).card := by
    intro qq hqq
    rw [card_filter_image_val]
    exact hQfib qq (hJsub hqq)
  have hlow := sep_bridge_lower f hε hS hu hut hfam hxstar hystar J hJcard
    (Rc.image Subtype.val) (Cc.image Subtype.val) hfib' hCcard
  have hup := sep_residual_upper f S Rs Cs P' Rc Cc hcomp
    (Rc.image Subtype.val) (Cc.image Subtype.val)
    (by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨wit, hw, hweq⟩ := hp
      exact ⟨wit, hw, hweq⟩)
    (by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨wit, hw, hweq⟩ := hj
      exact ⟨wit, hw, hweq⟩)
  omega

/-- Chase terminal (paper Phase 2, `j = ℓ`): a rectangle at depth `R + 1`
still holding `t/2 + 1` blocks of `≥ ⌈m·2^(−(R+1))⌉` rows each (full column
mass `h·L`) clashes with the residual budget `D f + T − 1` via the bridged
`2^(T−1)+1`-copy classical bound. -/
private theorem sep_chase_fire {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {δ b ε : ℝ} (hb : 1 ≤ b) (hε : 0 ≤ ε)
    (T R : ℕ) (hTb : (T : ℝ) ≤ b)
    {L : ℕ} {S : Fin L → Fin (2 ^ (R + T)) → Y}
    (hS : IsBalancedFamily (2 ^ T) S ε)
    {h : ℝ}
    (hrob : IsRobust f δ b) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hD : 2 ≤ D f) (hT1 : 1 ≤ T)
    (hband : 2 * (1 / 2 + δ) ^ 2 ≤ h / (1 + ε))
    (hbig : ((R + T : ℕ) : ℝ) + 1 ≤ b)
    (Rs : Finset (Fin (2 ^ (R + T)) × X)) (Cs : Finset (Fin L))
    (P' : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool)
    (Rc : Finset {p // p ∈ Rs}) (Cc : Finset {j // j ∈ Cs})
    (Qc : Finset (Fin (2 ^ (R + T))))
    (hcomp : ∀ x ∈ Rc, ∀ y ∈ Cc,
      P'.eval x y = subgame (relaxedInterlace f S) Rs Cs x y)
    (hcost : P'.cost + (R + 1) ≤ D f + (R + T))
    (hQcard : 2 ^ (T - 1) + 1 ≤ Qc.card)
    (hQfib : ∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ)
        * (2 : ℝ) ^ (-((R + 1 : ℕ) : ℝ))⌉₊
        ≤ (Rc.filter (fun p => p.val.1 = qq)).card)
    (hCcard : h * (L : ℝ) ≤ (((Cc.image Subtype.val).card : ℕ) : ℝ)) :
    False := by
  have hfam := sep_plus_one_fam hrob hb hδ0 hδ2 hD T hT1 hTb
  have hut : 2 ^ (T - 1) + 1 ≤ 2 ^ T := by
    have h2T : 2 ^ T = 2 ^ (T - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    have h1le : 1 ≤ 2 ^ (T - 1) := Nat.one_le_two_pow
    omega
  have hxstar : (2 : ℝ) ^ ((T : ℝ) - b) ≤ (2 : ℝ) ^ (-((R + 1 : ℕ) : ℝ)) := by
    apply sep_rpow_density_le
    push_cast
    push_cast at hbig
    linarith
  exact sep_bridge_clash f hε hS (Nat.succ_pos _) hut hfam hxstar
    (sep_band_weak hband) Rs Cs P' Rc Cc hcomp Qc hQcard hQfib hCcard
    (by omega)

set_option maxHeartbeats 1000000 in
/-- The paper's Phase-2 unbalanced-row continuation, as a structural
induction over the protocol tree: a rectangle at depth `d` holding
`2^(v+T−1) + 1` blocks of `≥ ⌈m·2^(−d)⌉` rows (`v + d = R + 1`, full column
mass) under the global budget is impossible.  While `v ≥ 1` a leaf / column
bit dies by `localized_extension` (`sep_outer_clash`) and a row bit sends
`2^(v+T−2) + 1` blocks to a majority child; at `v = 0` the terminal
`t/2 + 1`-block classical clash fires (`sep_chase_fire`). -/
private theorem sep_chase {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {δ b ε : ℝ} (hb : 1 ≤ b) (hε : 0 ≤ ε)
    (T R : ℕ) (hTb : (T : ℝ) ≤ b)
    {L : ℕ} (S : Fin L → Fin (2 ^ (R + T)) → Y)
    (hS : IsBalancedFamily (2 ^ T) S ε)
    (pseed : ℕ) {xseed h hseed : ℝ}
    (hx1 : (2 : ℝ) ^ (-b) ≤ xseed) (hx2 : xseed ≤ (2 : ℝ) ^ (-(R : ℝ)))
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs0 : 0 < hseed) (hs1 : hseed ≤ 1)
    (hp1 : 2 ^ T ≤ 2 * pseed) (hp2 : pseed ≤ 2 ^ T)
    (hres : IsColumnLossResilient f b ε (R + T) T h)
    (hseedbd : D f + T ≤ Dfamily (interlaceFun f pseed)
        (bracketGE X Y pseed xseed hseed))
    (hbridge : hseed ≤ h * (2 : ℝ) ^ (-((T + D f : ℕ) : ℝ)) / (1 + ε))
    (hrob : IsRobust f δ b) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hD : 2 ≤ D f) (hT1 : 1 ≤ T)
    (hband : 2 * (1 / 2 + δ) ^ 2 ≤ h / (1 + ε))
    (hbig : ((R + T : ℕ) : ℝ) + 1 ≤ b)
    (Rs : Finset (Fin (2 ^ (R + T)) × X)) (Cs : Finset (Fin L))
    (P' : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool) :
    ∀ (v d : ℕ) (Rc : Finset {p // p ∈ Rs}) (Cc : Finset {j // j ∈ Cs})
      (Qc : Finset (Fin (2 ^ (R + T)))),
      v + d = R + 1 →
      (∀ x ∈ Rc, ∀ y ∈ Cc,
        P'.eval x y = subgame (relaxedInterlace f S) Rs Cs x y) →
      P'.cost + d ≤ D f + (R + T) →
      2 ^ (v + T - 1) + 1 ≤ Qc.card →
      (∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-(d : ℝ))⌉₊
          ≤ (Rc.filter (fun p => p.val.1 = qq)).card) →
      h * (L : ℝ) ≤ (((Cc.image Subtype.val).card : ℕ) : ℝ) →
      False := by
  induction P' with
  | leaf z =>
    intro v d Rc Cc Qc hvd hcomp hcost hQcard hQfib hCcard
    rcases Nat.eq_zero_or_pos v with hv0 | hv1
    · subst hv0
      have hd : d = R + 1 := by omega
      subst hd
      exact sep_chase_fire f hb hε T R hTb hS hrob hδ0 hδ2 hD hT1 hband hbig
        Rs Cs (Protocol.leaf z) Rc Cc Qc hcomp hcost
        (by simpa using hQcard) hQfib hCcard
    · have hdR : d ≤ R := by omega
      have hQcard' : 2 ^ (R + T - d) ≤ Qc.card := by
        have hexp : R + T - d = v + T - 1 := by omega
        rw [hexp]
        omega
      have hC0 : h * (2 : ℝ) ^ (-((0 : ℕ) : ℝ)) * (L : ℝ)
          ≤ (((Cc.image Subtype.val).card : ℕ) : ℝ) := by
        have hrw : h * (2 : ℝ) ^ (-((0 : ℕ) : ℝ)) * (L : ℝ) = h * (L : ℝ) := by
          simp
        rw [hrw]
        exact hCcard
      exact sep_outer_clash f hb hε T R hTb S hS pseed hx1 hx2 hh0 hh1 hs0 hs1
        hp1 hp2 hres hseedbd hbridge Rs Cs (Protocol.leaf z) Rc Cc hcomp hdR
        (Nat.zero_le 1) Qc hQcard' hQfib hC0
        (by
          have h0 : (Protocol.leaf z :
              Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool).cost = 0 := rfl
          omega)
  | bNode bp l r ihl ihr =>
    intro v d Rc Cc Qc hvd hcomp hcost hQcard hQfib hCcard
    rcases Nat.eq_zero_or_pos v with hv0 | hv1
    · subst hv0
      have hd : d = R + 1 := by omega
      subst hd
      exact sep_chase_fire f hb hε T R hTb hS hrob hδ0 hδ2 hD hT1 hband hbig
        Rs Cs (Protocol.bNode bp l r) Rc Cc Qc hcomp hcost
        (by simpa using hQcard) hQfib hCcard
    · have hdR : d ≤ R := by omega
      have hQcard' : 2 ^ (R + T - d) ≤ Qc.card := by
        have hexp : R + T - d = v + T - 1 := by omega
        rw [hexp]
        omega
      have hcostnode : (Protocol.bNode bp l r :
          Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool).cost
          = 1 + max l.cost r.cost := rfl
      obtain ⟨β, hβ⟩ := sep_half_side Cc bp
      set Cch : Finset {j // j ∈ Cs} := Cc.filter (fun c => bp c = β) with hCch
      have hCchsub : ∀ y ∈ Cch, y ∈ Cc := by
        intro y hy
        exact (Finset.mem_filter.mp hy).1
      have hChalf : h * (2 : ℝ) ^ (-((1 : ℕ) : ℝ)) * (L : ℝ)
          ≤ (((Cch.image Subtype.val).card : ℕ) : ℝ) := by
        have himg1 : (Cc.image Subtype.val).card = Cc.card :=
          Finset.card_image_of_injective Cc Subtype.val_injective
        have himg2 : (Cch.image Subtype.val).card = Cch.card :=
          Finset.card_image_of_injective Cch Subtype.val_injective
        have hβR : ((Cc.card : ℕ) : ℝ) ≤ 2 * ((Cch.card : ℕ) : ℝ) := by
          exact_mod_cast hβ
        have hrw : (2 : ℝ) ^ (-((1 : ℕ) : ℝ)) = 2⁻¹ := by
          rw [Nat.cast_one, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
            Real.rpow_one]
        rw [hrw, himg2]
        rw [himg1] at hCcard
        nlinarith [hCcard, hβR]
      -- the child protocol keeping the heavy column half
      have hclash : ∀ Pc : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool,
          Pc.cost ≤ max l.cost r.cost →
          (∀ x ∈ Rc, ∀ y ∈ Cch,
            Pc.eval x y = subgame (relaxedInterlace f S) Rs Cs x y) →
          False := by
        intro Pc hPcc hcompc
        exact sep_outer_clash f hb hε T R hTb S hS pseed hx1 hx2 hh0 hh1 hs0
          hs1 hp1 hp2 hres hseedbd hbridge Rs Cs Pc Rc Cch hcompc hdR
          (le_refl 1) Qc hQcard' hQfib hChalf (by omega)
      cases β with
      | false =>
        refine hclash l (le_max_left _ _) ?_
        intro x hx y hy
        have hyc : bp y = false := (Finset.mem_filter.mp hy).2
        have hev := hcomp x hx y (hCchsub y hy)
        simp only [Protocol.eval] at hev
        rw [if_neg (by rw [hyc]; exact Bool.false_ne_true)] at hev
        exact hev
      | true =>
        refine hclash r (le_max_right _ _) ?_
        intro x hx y hy
        have hyc : bp y = true := (Finset.mem_filter.mp hy).2
        have hev := hcomp x hx y (hCchsub y hy)
        simp only [Protocol.eval] at hev
        rw [if_pos hyc] at hev
        exact hev
  | aNode ap l r ihl ihr =>
    intro v d Rc Cc Qc hvd hcomp hcost hQcard hQfib hCcard
    rcases Nat.eq_zero_or_pos v with hv0 | hv1
    · subst hv0
      have hd : d = R + 1 := by omega
      subst hd
      exact sep_chase_fire f hb hε T R hTb hS hrob hδ0 hδ2 hD hT1 hband hbig
        Rs Cs (Protocol.aNode ap l r) Rc Cc Qc hcomp hcost
        (by simpa using hQcard) hQfib hCcard
    · have hcostnode : (Protocol.aNode ap l r :
          Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool).cost
          = 1 + max l.cost r.cost := rfl
      have hkey := sep_ceil_halving (Fintype.card X) d
      set Rt : Finset {p // p ∈ Rs} := Rc.filter (fun p => ap p = true)
        with hRt
      set Rf : Finset {p // p ∈ Rs} := Rc.filter (fun p => ¬ (ap p = true))
        with hRf
      have hsum : ∀ qq : Fin (2 ^ (R + T)),
          (Rt.filter (fun p => p.val.1 = qq)).card
            + (Rf.filter (fun p => p.val.1 = qq)).card
          = (Rc.filter (fun p => p.val.1 = qq)).card := by
        intro qq
        have e1 : Rt.filter (fun p => p.val.1 = qq)
            = (Rc.filter (fun p => p.val.1 = qq)).filter
                (fun p => ap p = true) := by
          rw [hRt, Finset.filter_comm]
        have e2 : Rf.filter (fun p => p.val.1 = qq)
            = (Rc.filter (fun p => p.val.1 = qq)).filter
                (fun p => ¬ (ap p = true)) := by
          rw [hRf, Finset.filter_comm]
        rw [e1, e2]
        exact Finset.card_filter_add_card_filter_not
          (s := Rc.filter (fun p => p.val.1 = qq)) (p := fun p => ap p = true)
      set QT : Finset (Fin (2 ^ (R + T))) := Qc.filter (fun qq =>
        ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ))⌉₊
          ≤ (Rt.filter (fun p => p.val.1 = qq)).card) with hQT
      set QF : Finset (Fin (2 ^ (R + T))) := Qc.filter (fun qq =>
        ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ))⌉₊
          ≤ (Rf.filter (fun p => p.val.1 = qq)).card) with hQF
      have hcover : ∀ qq ∈ Qc, qq ∈ QT ∨ qq ∈ QF := by
        intro qq hqq
        have hs := hsum qq
        have hf := hQfib qq hqq
        by_cases hT' : ⌈(Fintype.card X : ℝ)
            * (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ))⌉₊
            ≤ (Rt.filter (fun p => p.val.1 = qq)).card
        · exact Or.inl (Finset.mem_filter.mpr ⟨hqq, hT'⟩)
        · refine Or.inr (Finset.mem_filter.mpr ⟨hqq, ?_⟩)
          omega
      have hQTF : Qc.card ≤ QT.card + QF.card := by
        calc Qc.card ≤ (QT ∪ QF).card :=
              Finset.card_le_card
                (fun qq hqq => Finset.mem_union.mpr (hcover qq hqq))
          _ ≤ QT.card + QF.card := Finset.card_union_le _ _
      have hmaj : 2 ^ ((v - 1) + T - 1) + 1 ≤ QT.card
          ∨ 2 ^ ((v - 1) + T - 1) + 1 ≤ QF.card := by
        by_contra hno
        push Not at hno
        have h2 : 2 ^ (v + T - 1) = 2 * 2 ^ ((v - 1) + T - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        omega
      have hcostl : l.cost + (d + 1) ≤ D f + (R + T) := by
        have hle : l.cost ≤ max l.cost r.cost := le_max_left _ _
        omega
      have hcostr : r.cost + (d + 1) ≤ D f + (R + T) := by
        have hle : r.cost ≤ max l.cost r.cost := le_max_right _ _
        omega
      rcases hmaj with hmT | hmF
      · -- majority on the `true` side: follow subtree `r`
        refine ihr (v - 1) (d + 1) Rt Cc QT (by omega) ?_ hcostr hmT ?_ hCcard
        · intro x hx y hy
          have hxc : ap x = true := (Finset.mem_filter.mp hx).2
          have hev := hcomp x ((Finset.mem_filter.mp hx).1) y hy
          simp only [Protocol.eval] at hev
          rw [if_pos hxc] at hev
          exact hev
        · intro qq hqq
          exact (Finset.mem_filter.mp hqq).2
      · -- majority on the `false` side: follow subtree `l`
        refine ihl (v - 1) (d + 1) Rf Cc QF (by omega) ?_ hcostl hmF ?_ hCcard
        · intro x hx y hy
          have hxc : ¬ (ap x = true) := (Finset.mem_filter.mp hx).2
          have hev := hcomp x ((Finset.mem_filter.mp hx).1) y hy
          simp only [Protocol.eval] at hev
          rw [if_neg hxc] at hev
          exact hev
        · intro qq hqq
          exact (Finset.mem_filter.mp hqq).2

/-- Inner-phase (`R ≤ d < R+T`) leaf/column-bit clash: the surviving
`2^(R+T−d)`-block witness bridges to a classical `2^(R+T−d)`-copy bracket
member (`u ≤ t`), priced at `D f + (R+T−d)` by `cor:power-of-two` — above
the residual budget.  `γ` is the current column fraction (`h`, or `h/2`
after a column split, fed by `hband`). -/
private theorem sep_inner_clash {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {δ b ε : ℝ} (hb : 1 ≤ b) (hε : 0 ≤ ε)
    (T R : ℕ)
    {L : ℕ} {S : Fin L → Fin (2 ^ (R + T)) → Y}
    (hS : IsBalancedFamily (2 ^ T) S ε)
    (hrob : IsRobust f δ b) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hD : 2 ≤ D f)
    (hbig : ((R + T : ℕ) : ℝ) + 1 ≤ b)
    (Rs : Finset (Fin (2 ^ (R + T)) × X)) (Cs : Finset (Fin L))
    (P' : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool)
    (Rc : Finset {p // p ∈ Rs}) (Cc : Finset {j // j ∈ Cs})
    (hcomp : ∀ x ∈ Rc, ∀ y ∈ Cc,
      P'.eval x y = subgame (relaxedInterlace f S) Rs Cs x y)
    {d : ℕ} (hRd : R ≤ d) (hdRT : d < R + T)
    {γ : ℝ} (hγ : (1 / 2 + δ) ^ 2 ≤ γ / (1 + ε))
    (Qc : Finset (Fin (2 ^ (R + T)))) (hQcard : 2 ^ (R + T - d) ≤ Qc.card)
    (hQfib : ∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-(d : ℝ))⌉₊
        ≤ (Rc.filter (fun p => p.val.1 = qq)).card)
    (hCcard : γ * (L : ℝ) ≤ (((Cc.image Subtype.val).card : ℕ) : ℝ))
    (hPcost : P'.cost + d < D f + (R + T)) : False := by
  have hdle : d ≤ R + T := le_of_lt hdRT
  have hw1 : 1 ≤ R + T - d := by omega
  have hwb : ((R + T - d : ℕ) : ℝ) ≤ b := by
    have hle : ((R + T - d : ℕ) : ℝ) ≤ ((R + T : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le (R + T) d
    linarith
  have hfam := power_of_two_lower hrob hb hδ0 hδ2 hD (R + T - d) hw1 hwb
  have hxstar : (2 : ℝ) ^ ((R + T - d : ℕ)) * (2 : ℝ) ^ (-b)
      ≤ (2 : ℝ) ^ (-(d : ℝ)) := by
    apply sep_pow_density_le
    rw [Nat.cast_sub hdle]
    push_cast
    push_cast at hbig
    linarith
  have hut : 2 ^ (R + T - d) ≤ 2 ^ T :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  exact sep_bridge_clash f hε hS (Nat.two_pow_pos _) hut hfam hxstar hγ
    Rs Cs P' Rc Cc hcomp Qc hQcard hQfib hCcard (by omega)

/-- Inner-phase (`R ≤ d < R+T`) unbalanced-row clash: a child receiving
`2^(R+T−d−1) + 1` blocks at threshold `⌈m·2^(−(d+1))⌉` bridges to a
classical `2^(k−1)+1`-copy member (`k = R+T−d ≤ T`, so `u ≤ t`), priced at
`D f + k` by `cor:plus-one-family` / `cor:two-copy-amplification` — above
the child's budget. -/
private theorem sep_inner_plus_clash {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {δ b ε : ℝ} (hb : 1 ≤ b) (hε : 0 ≤ ε)
    (T R : ℕ)
    {L : ℕ} {S : Fin L → Fin (2 ^ (R + T)) → Y}
    (hS : IsBalancedFamily (2 ^ T) S ε)
    {h : ℝ}
    (hrob : IsRobust f δ b) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hD : 2 ≤ D f) (hT1 : 1 ≤ T)
    (hband : 2 * (1 / 2 + δ) ^ 2 ≤ h / (1 + ε))
    (hbig : ((R + T : ℕ) : ℝ) + 1 ≤ b)
    (Rs : Finset (Fin (2 ^ (R + T)) × X)) (Cs : Finset (Fin L))
    (P' : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool)
    (Rc : Finset {p // p ∈ Rs}) (Cc : Finset {j // j ∈ Cs})
    (hcomp : ∀ x ∈ Rc, ∀ y ∈ Cc,
      P'.eval x y = subgame (relaxedInterlace f S) Rs Cs x y)
    {d : ℕ} (hRd : R ≤ d) (hdRT : d < R + T)
    (Qc : Finset (Fin (2 ^ (R + T))))
    (hQcard : 2 ^ (R + T - d - 1) + 1 ≤ Qc.card)
    (hQfib : ∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ)
        * (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ))⌉₊
        ≤ (Rc.filter (fun p => p.val.1 = qq)).card)
    (hCcard : h * (L : ℝ) ≤ (((Cc.image Subtype.val).card : ℕ) : ℝ))
    (hPcost : P'.cost + (d + 1) ≤ D f + (R + T)) : False := by
  have hdle : d ≤ R + T := le_of_lt hdRT
  have hk1 : 1 ≤ R + T - d := by omega
  have hkb : ((R + T - d : ℕ) : ℝ) ≤ b := by
    have hle : ((R + T - d : ℕ) : ℝ) ≤ ((R + T : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le (R + T) d
    linarith
  have hfam := sep_plus_one_fam hrob hb hδ0 hδ2 hD (R + T - d) hk1 hkb
  have hxstar : (2 : ℝ) ^ (((R + T - d : ℕ) : ℝ) - b)
      ≤ (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ)) := by
    apply sep_rpow_density_le
    rw [Nat.cast_sub hdle]
    push_cast
    push_cast at hbig
    linarith
  have hut : 2 ^ (R + T - d - 1) + 1 ≤ 2 ^ T := by
    have hle1 : R + T - d - 1 ≤ T - 1 := by omega
    have hp : 2 ^ (R + T - d - 1) ≤ 2 ^ (T - 1) :=
      Nat.pow_le_pow_right (by norm_num) hle1
    have h1le : 1 ≤ 2 ^ (T - 1) := Nat.one_le_two_pow
    have h2T : 2 ^ T = 2 ^ (T - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    omega
  have hQcard' : 2 ^ (R + T - d - 1) + 1 ≤ Qc.card := hQcard
  exact sep_bridge_clash f hε hS (Nat.succ_pos _) hut hfam hxstar
    (sep_band_weak hband) Rs Cs P' Rc Cc hcomp Qc hQcard' hQfib hCcard
    (by omega)

set_option maxHeartbeats 1000000 in
/-- The main chain (conclusion (a)): after `d` spent bits, a rectangle still
holding `≥ 2^(R+T−d)` blocks of `≥ ⌈m·2^(−d)⌉` rows (with the FULL column
set) under the budget `P'.cost + d ≤ D f + (R+T)` is row-only for the next
`R + T − d` bits.  Leaves and Bob nodes on live rectangles die by the
outer (`localized_extension`) or inner (bridged classical) clashes; an
Alice node splits every block-fiber, each block staying heavy in at least
one child (`sep_ceil_halving`), and a child hoarding `2^(R+T−d−1) + 1`
blocks dies by the Phase-2 chase (`d ≤ R`) or the bridged plus-one clash
(`d > R`) — so both children inherit the invariant. -/
private theorem sep_main_chain {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {δ b ε : ℝ} (hb : 1 ≤ b) (hε : 0 ≤ ε)
    (T R : ℕ) (hTb : (T : ℝ) ≤ b)
    {L : ℕ} (S : Fin L → Fin (2 ^ (R + T)) → Y)
    (hS : IsBalancedFamily (2 ^ T) S ε)
    (pseed : ℕ) {xseed h hseed : ℝ}
    (hx1 : (2 : ℝ) ^ (-b) ≤ xseed) (hx2 : xseed ≤ (2 : ℝ) ^ (-(R : ℝ)))
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs0 : 0 < hseed) (hs1 : hseed ≤ 1)
    (hp1 : 2 ^ T ≤ 2 * pseed) (hp2 : pseed ≤ 2 ^ T)
    (hres : IsColumnLossResilient f b ε (R + T) T h)
    (hseedbd : D f + T ≤ Dfamily (interlaceFun f pseed)
        (bracketGE X Y pseed xseed hseed))
    (hbridge : hseed ≤ h * (2 : ℝ) ^ (-((T + D f : ℕ) : ℝ)) / (1 + ε))
    (hrob : IsRobust f δ b) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hD : 2 ≤ D f) (hT1 : 1 ≤ T)
    (hband : 2 * (1 / 2 + δ) ^ 2 ≤ h / (1 + ε))
    (hbig : ((R + T : ℕ) : ℝ) + 1 ≤ b)
    (Rs : Finset (Fin (2 ^ (R + T)) × X)) (Cs : Finset (Fin L))
    (hCs : h * (L : ℝ) ≤ (Cs.card : ℝ))
    (P' : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool) :
    ∀ (d : ℕ) (Rc : Finset {p // p ∈ Rs}) (Qc : Finset (Fin (2 ^ (R + T)))),
      (∀ x ∈ Rc, ∀ y ∈ (Finset.univ : Finset {j // j ∈ Cs}),
        P'.eval x y = subgame (relaxedInterlace f S) Rs Cs x y) →
      P'.cost + d ≤ D f + (R + T) →
      2 ^ (R + T - d) ≤ Qc.card →
      (∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-(d : ℝ))⌉₊
          ≤ (Rc.filter (fun p => p.val.1 = qq)).card) →
      Protocol.FirstKRowBitsOn Rc (Finset.univ : Finset {j // j ∈ Cs})
        (R + T - d) P' := by
  classical
  have hCuniv : h * (L : ℝ)
      ≤ (((((Finset.univ : Finset {j // j ∈ Cs})).image Subtype.val).card : ℕ) : ℝ) := by
    rw [Finset.univ_eq_attach, Finset.attach_image_val]
    exact hCs
  induction P' with
  | leaf z =>
    intro d Rc Qc hcomp hcost hQcard hQfib
    rcases Nat.lt_or_ge d (R + T) with hdRT | hdRT
    · obtain ⟨n, hn⟩ : ∃ n, R + T - d = n + 1 := ⟨R + T - d - 1, by omega⟩
      rw [hn]
      by_cases hRc : Rc = ∅
      · exact Or.inl hRc
      by_cases hCe : (Finset.univ : Finset {j // j ∈ Cs}) = ∅
      · exact Or.inr hCe
      exfalso
      by_cases hdR : d ≤ R
      · have hC0 : h * (2 : ℝ) ^ (-((0 : ℕ) : ℝ)) * (L : ℝ)
            ≤ ((((Finset.univ : Finset {j // j ∈ Cs}).image
              Subtype.val).card : ℕ) : ℝ) := by
          have hrw : h * (2 : ℝ) ^ (-((0 : ℕ) : ℝ)) * (L : ℝ)
              = h * (L : ℝ) := by simp
          rw [hrw]
          exact hCuniv
        exact sep_outer_clash f hb hε T R hTb S hS pseed hx1 hx2 hh0 hh1 hs0
          hs1 hp1 hp2 hres hseedbd hbridge Rs Cs (Protocol.leaf z) Rc
          Finset.univ hcomp hdR (Nat.zero_le 1) Qc hQcard hQfib hC0
          (by
            have h0 : (Protocol.leaf z :
                Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool).cost = 0 := rfl
            omega)
      · exact sep_inner_clash f hb hε T R hS hrob hδ0 hδ2 hD hbig Rs Cs
          (Protocol.leaf z) Rc Finset.univ hcomp (by omega : R ≤ d) hdRT
          (sep_band_weak hband) Qc hQcard hQfib hCuniv
          (by
            have h0 : (Protocol.leaf z :
                Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool).cost = 0 := rfl
            omega)
    · have h0 : R + T - d = 0 := by omega
      rw [h0]
      trivial
  | bNode bp l r ihl ihr =>
    intro d Rc Qc hcomp hcost hQcard hQfib
    rcases Nat.lt_or_ge d (R + T) with hdRT | hdRT
    · obtain ⟨n, hn⟩ : ∃ n, R + T - d = n + 1 := ⟨R + T - d - 1, by omega⟩
      rw [hn]
      by_cases hRc : Rc = ∅
      · exact Or.inl hRc
      by_cases hCe : (Finset.univ : Finset {j // j ∈ Cs}) = ∅
      · exact Or.inr hCe
      exfalso
      have hcostnode : (Protocol.bNode bp l r :
          Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool).cost
          = 1 + max l.cost r.cost := rfl
      obtain ⟨β, hβ⟩ :=
        sep_half_side (Finset.univ : Finset {j // j ∈ Cs}) bp
      set Cch : Finset {j // j ∈ Cs} :=
        (Finset.univ : Finset {j // j ∈ Cs}).filter (fun c => bp c = β)
        with hCchdef
      have hChalfcard : h / 2 * (L : ℝ)
          ≤ (((Cch.image Subtype.val).card : ℕ) : ℝ) := by
        have himg1 : (((Finset.univ : Finset {j // j ∈ Cs})).image
            Subtype.val).card = (Finset.univ : Finset {j // j ∈ Cs}).card :=
          Finset.card_image_of_injective _ Subtype.val_injective
        have himg2 : (Cch.image Subtype.val).card = Cch.card :=
          Finset.card_image_of_injective Cch Subtype.val_injective
        have hβR : (((Finset.univ : Finset {j // j ∈ Cs}).card : ℕ) : ℝ)
            ≤ 2 * ((Cch.card : ℕ) : ℝ) := by
          exact_mod_cast hβ
        rw [himg2]
        rw [himg1] at hCuniv
        nlinarith [hCuniv, hβR]
      have hclash : ∀ Pc : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool,
          Pc.cost ≤ max l.cost r.cost →
          (∀ x ∈ Rc, ∀ y ∈ Cch,
            Pc.eval x y = subgame (relaxedInterlace f S) Rs Cs x y) →
          False := by
        intro Pc hPcc hcompc
        by_cases hdR : d ≤ R
        · have hChalf : h * (2 : ℝ) ^ (-((1 : ℕ) : ℝ)) * (L : ℝ)
              ≤ (((Cch.image Subtype.val).card : ℕ) : ℝ) := by
            have hrw : (2 : ℝ) ^ (-((1 : ℕ) : ℝ)) = 2⁻¹ := by
              rw [Nat.cast_one,
                Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_one]
            rw [hrw]
            have : h * 2⁻¹ * (L : ℝ) = h / 2 * (L : ℝ) := by ring
            rw [this]
            exact hChalfcard
          exact sep_outer_clash f hb hε T R hTb S hS pseed hx1 hx2 hh0 hh1
            hs0 hs1 hp1 hp2 hres hseedbd hbridge Rs Cs Pc Rc Cch hcompc hdR
            (le_refl 1) Qc hQcard hQfib hChalf (by omega)
        · have hγ2 : (1 / 2 + δ) ^ 2 ≤ (h / 2) / (1 + ε) := by
            have hrw : (h / 2) / (1 + ε) = h / (1 + ε) / 2 := by ring
            rw [hrw]
            linarith
          exact sep_inner_clash f hb hε T R hS hrob hδ0 hδ2 hD hbig Rs Cs
            Pc Rc Cch hcompc (by omega : R ≤ d) hdRT hγ2 Qc hQcard hQfib
            hChalfcard (by omega)
      cases β with
      | false =>
        refine hclash l (le_max_left _ _) ?_
        intro x hx y hy
        have hyc : bp y = false := (Finset.mem_filter.mp hy).2
        have hev := hcomp x hx y (Finset.mem_univ y)
        simp only [Protocol.eval] at hev
        rw [if_neg (by rw [hyc]; exact Bool.false_ne_true)] at hev
        exact hev
      | true =>
        refine hclash r (le_max_right _ _) ?_
        intro x hx y hy
        have hyc : bp y = true := (Finset.mem_filter.mp hy).2
        have hev := hcomp x hx y (Finset.mem_univ y)
        simp only [Protocol.eval] at hev
        rw [if_pos hyc] at hev
        exact hev
    · have h0 : R + T - d = 0 := by omega
      rw [h0]
      trivial
  | aNode ap l r ihl ihr =>
    intro d Rc Qc hcomp hcost hQcard hQfib
    rcases Nat.lt_or_ge d (R + T) with hdRT | hdRT
    · obtain ⟨n, hn⟩ : ∃ n, R + T - d = n + 1 := ⟨R + T - d - 1, by omega⟩
      rw [hn] at hQcard ⊢
      have hcostnode : (Protocol.aNode ap l r :
          Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool).cost
          = 1 + max l.cost r.cost := rfl
      have hcostl : l.cost + (d + 1) ≤ D f + (R + T) := by
        have hle : l.cost ≤ max l.cost r.cost := le_max_left _ _
        omega
      have hcostr : r.cost + (d + 1) ≤ D f + (R + T) := by
        have hle : r.cost ≤ max l.cost r.cost := le_max_right _ _
        omega
      have hkey := sep_ceil_halving (Fintype.card X) d
      set Rt : Finset {p // p ∈ Rs} := Rc.filter (fun p => ap p = true)
        with hRtdef
      set Rf : Finset {p // p ∈ Rs} := Rc.filter (fun p => ap p = false)
        with hRfdef
      have hcompR : ∀ x ∈ Rt,
          ∀ y ∈ (Finset.univ : Finset {j // j ∈ Cs}),
          r.eval x y = subgame (relaxedInterlace f S) Rs Cs x y := by
        intro x hx y hy
        have hxc : ap x = true := (Finset.mem_filter.mp hx).2
        have hev := hcomp x ((Finset.mem_filter.mp hx).1) y hy
        simp only [Protocol.eval] at hev
        rw [if_pos hxc] at hev
        exact hev
      have hcompL : ∀ x ∈ Rf,
          ∀ y ∈ (Finset.univ : Finset {j // j ∈ Cs}),
          l.eval x y = subgame (relaxedInterlace f S) Rs Cs x y := by
        intro x hx y hy
        have hxc : ap x = false := (Finset.mem_filter.mp hx).2
        have hev := hcomp x ((Finset.mem_filter.mp hx).1) y hy
        simp only [Protocol.eval] at hev
        rw [if_neg (by rw [hxc]; exact Bool.false_ne_true)] at hev
        exact hev
      have hsum : ∀ qq : Fin (2 ^ (R + T)),
          (Rt.filter (fun p => p.val.1 = qq)).card
            + (Rf.filter (fun p => p.val.1 = qq)).card
          = (Rc.filter (fun p => p.val.1 = qq)).card := by
        intro qq
        have e1 : Rt.filter (fun p => p.val.1 = qq)
            = (Rc.filter (fun p => p.val.1 = qq)).filter
                (fun p => ap p = true) := by
          rw [hRtdef, Finset.filter_comm]
        have e2 : Rf.filter (fun p => p.val.1 = qq)
            = (Rc.filter (fun p => p.val.1 = qq)).filter
                (fun p => ¬ (ap p = true)) := by
          rw [hRfdef, sep_filter_false_eq, Finset.filter_comm]
        rw [e1, e2]
        exact Finset.card_filter_add_card_filter_not
          (s := Rc.filter (fun p => p.val.1 = qq)) (p := fun p => ap p = true)
      set QT : Finset (Fin (2 ^ (R + T))) := Qc.filter (fun qq =>
        ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ))⌉₊
          ≤ (Rt.filter (fun p => p.val.1 = qq)).card) with hQTdef
      set QF : Finset (Fin (2 ^ (R + T))) := Qc.filter (fun qq =>
        ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ))⌉₊
          ≤ (Rf.filter (fun p => p.val.1 = qq)).card) with hQFdef
      have hcover : ∀ qq ∈ Qc, qq ∈ QT ∨ qq ∈ QF := by
        intro qq hqq
        have hs := hsum qq
        have hf := hQfib qq hqq
        by_cases hT' : ⌈(Fintype.card X : ℝ)
            * (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ))⌉₊
            ≤ (Rt.filter (fun p => p.val.1 = qq)).card
        · exact Or.inl (Finset.mem_filter.mpr ⟨hqq, hT'⟩)
        · refine Or.inr (Finset.mem_filter.mpr ⟨hqq, ?_⟩)
          omega
      have hQTF : Qc.card ≤ QT.card + QF.card := by
        calc Qc.card ≤ (QT ∪ QF).card :=
              Finset.card_le_card
                (fun qq hqq => Finset.mem_union.mpr (hcover qq hqq))
          _ ≤ QT.card + QF.card := Finset.card_union_le _ _
      have hpow2 : 2 ^ (n + 1) = 2 * 2 ^ n := by
        rw [pow_succ]
        ring
      have hQTfib : ∀ qq ∈ QT,
          ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ))⌉₊
          ≤ (Rt.filter (fun p => p.val.1 = qq)).card := by
        intro qq hqq
        exact (Finset.mem_filter.mp hqq).2
      have hQFfib : ∀ qq ∈ QF,
          ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ))⌉₊
          ≤ (Rf.filter (fun p => p.val.1 = qq)).card := by
        intro qq hqq
        exact (Finset.mem_filter.mp hqq).2
      -- clash on a side hoarding `2^n + 1` blocks
      have hclashT : 2 ^ n + 1 ≤ QT.card → False := by
        intro hbigT
        by_cases hdR : d ≤ R
        · have hexp : (R - d) + T - 1 = n := by omega
          refine sep_chase f hb hε T R hTb S hS pseed hx1 hx2 hh0 hh1 hs0 hs1
            hp1 hp2 hres hseedbd hbridge hrob hδ0 hδ2 hD hT1 hband hbig Rs Cs
            r (R - d) (d + 1) Rt Finset.univ QT (by omega) hcompR hcostr
            ?_ hQTfib hCuniv
          rw [hexp]
          exact hbigT
        · have hexp : R + T - d - 1 = n := by omega
          refine sep_inner_plus_clash f hb hε T R hS hrob hδ0 hδ2 hD hT1
            hband hbig Rs Cs r Rt Finset.univ hcompR (by omega : R ≤ d) hdRT QT
            ?_ hQTfib hCuniv hcostr
          rw [hexp]
          exact hbigT
      have hclashF : 2 ^ n + 1 ≤ QF.card → False := by
        intro hbigF
        by_cases hdR : d ≤ R
        · have hexp : (R - d) + T - 1 = n := by omega
          refine sep_chase f hb hε T R hTb S hS pseed hx1 hx2 hh0 hh1 hs0 hs1
            hp1 hp2 hres hseedbd hbridge hrob hδ0 hδ2 hD hT1 hband hbig Rs Cs
            l (R - d) (d + 1) Rf Finset.univ QF (by omega) hcompL hcostl
            ?_ hQFfib hCuniv
          rw [hexp]
          exact hbigF
        · have hexp : R + T - d - 1 = n := by omega
          refine sep_inner_plus_clash f hb hε T R hS hrob hδ0 hδ2 hD hT1
            hband hbig Rs Cs l Rf Finset.univ hcompL (by omega : R ≤ d) hdRT QF
            ?_ hQFfib hCuniv hcostl
          rw [hexp]
          exact hbigF
      have hnn : R + T - (d + 1) = n := by omega
      refine ⟨?_, ?_⟩
      · -- left child `l` on the `ap = false` rows
        by_cases hQFcard : 2 ^ n ≤ QF.card
        · have hres' := ihl (d + 1) Rf QF hcompL hcostl
            (by rw [hnn]; exact hQFcard) hQFfib
          rw [hnn] at hres'
          rw [hRfdef] at hres'
          exact hres'
        · exfalso
          exact hclashT (by omega)
      · -- right child `r` on the `ap = true` rows
        by_cases hQTcard : 2 ^ n ≤ QT.card
        · have hres' := ihr (d + 1) Rt QT hcompR hcostr
            (by rw [hnn]; exact hQTcard) hQTfib
          rw [hnn] at hres'
          rw [hRtdef] at hres'
          exact hres'
        · exfalso
          exact hclashF (by omega)
    · have h0 : R + T - d = 0 := by omega
      rw [h0]
      trivial

-- CLAIM-BEGIN thm:SeparationTheorem
/-- Paper `thm:SeparationTheorem` (Relaxed Near-Exact Separation, §4).
Renderings follow `thm:Extension` verbatim: `t = 2^T`, `r = 2^R` powers of
two (`q = r·t = 2^(R+T)`, so `log q = R + T`, `log t = T`, `log = log₂`);
`t ≤ 2^b` is `(T:ℝ) ≤ b`; `t/2 ≤ p_seed ≤ t` is `2^T ≤ 2·p_seed` and
`p_seed ≤ 2^T`; the relaxed interlace `Ŝ = ⟨M⟩_{q,S_{q,t}(Cols M)}` is
`relaxedInterlace f S` for an ARBITRARY `(q,t)`-balanced family `S` with
accuracy `ε` (the paper's selected family is one instance, and
`|Cols Ŝ| = L`). The paper's
`x_seed ≤ 1/r` is `xseed ≤ 2^(−(R:ℝ))` (rpow); `t ≥ 2` is `1 ≤ T`; the
robustness hypothesis is named `hrob` (`h` is the Extension column density);
`q⌈2^{−b+1}m⌉ < m` is `hgap` with `m = Fintype.card X`.
`N = Ŝ[Rows(Ŝ), C']` keeps ALL rows: the row set is
`(univ : Finset (Fin (2^(R+T)) × X))`, so every block fiber holds all `m`
rows and the no-waste threshold is `T₀ = Fintype.card X` EXACTLY (not
`⌈m·x⌉₊`) — the paper's dominant-fiber bound
`|R_{i*}| ≥ m − (q−1)⌈2^{−b+1}m⌉` is `NoWasteConclusion` at
`T₀ = Fintype.card X`, `T = ⌈2^(1−b)·m⌉₊`, `|Q| = q = 2^(R+T)`.
Conclusion (a) is the rectangle-threaded surviving-branch predicate
`FirstKRowBitsOn`:
a syntactic "no `bNode`/early `leaf` above depth `R+T`" conclusion is
UNPROVABLE (unreachable junk subtrees carry Bob nodes / leaves without
changing `eval` or `cost`), so Bob nodes and early leaves are forbidden only
on NONEMPTY current rectangles, vacuous on dead ones. Conclusion (b) labels
rows by `prefixLabelFinQ` (its junk→`0` branch is dead here since
`Rin = univ`: every row gets its genuine transcript code). The δ endpoint
`δ ≤ 1/√2 − 1/2` is kept SYMBOLIC, as in `classical_separation`. -/
theorem relaxed_separation {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {δ b ε : ℝ} (hb : 1 ≤ b) (hε : 0 ≤ ε)
    (T R : ℕ) (hTb : (T : ℝ) ≤ b)
    {L : ℕ} (S : Fin L → Fin (2 ^ (R + T)) → Y)
    (hS : IsBalancedFamily (2 ^ T) S ε)
    (pseed : ℕ) {xseed h hseed : ℝ}
    (hx1 : (2 : ℝ) ^ (-b) ≤ xseed) (hx2 : xseed ≤ (2 : ℝ) ^ (-(R : ℝ)))
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs0 : 0 < hseed) (hs1 : hseed ≤ 1)
    (hp1 : 2 ^ T ≤ 2 * pseed) (hp2 : pseed ≤ 2 ^ T)
    (hres : IsColumnLossResilient f b ε (R + T) T h)
    (hseedbd : D f + T ≤ Dfamily (interlaceFun f pseed)
        (bracketGE X Y pseed xseed hseed))
    (hbridge : hseed ≤ h * (2 : ℝ) ^ (-((T + D f : ℕ) : ℝ)) / (1 + ε))
    (hrob : IsRobust f δ b) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / Real.sqrt 2 - 1 / 2)
    (hD : 2 ≤ D f) (hT1 : 1 ≤ T)
    (hband : 2 * (1 / 2 + δ) ^ 2 ≤ h / (1 + ε))
    (hgap : 2 ^ (R + T) * ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊
        < Fintype.card X)
    (C' : Finset (Fin L)) (hC' : h * (L : ℝ) ≤ (C'.card : ℝ)) :
    ∀ P : Protocol {a // a ∈ (Finset.univ : Finset (Fin (2 ^ (R + T)) × X))}
        {c // c ∈ C'} Bool,
      P.Computes (subgame (relaxedInterlace f S)
        (Finset.univ : Finset (Fin (2 ^ (R + T)) × X)) C') →
      P.cost ≤ D f + (R + T) →
      Protocol.FirstKRowBitsOn
          (Finset.univ :
            Finset {a // a ∈ (Finset.univ : Finset (Fin (2 ^ (R + T)) × X))})
          (Finset.univ : Finset {c // c ∈ C'})
          (R + T) P
      ∧ NoWasteConclusion
          (Finset.univ : Finset (Fin (2 ^ (R + T))))
          (Finset.univ : Finset (Fin (2 ^ (R + T)) × X))
          (Protocol.prefixLabelFinQ
            (Finset.univ : Finset (Fin (2 ^ (R + T)) × X)) P)
          (Fintype.card X)
          ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊ :=
-- CLAIM-END thm:SeparationTheorem
  by
  classical
  obtain ⟨hm1, hbig⟩ := sep_gap_consequences hgap
  have hδ2 : δ ≤ 1 / 2 := sep_delta_half hδ
  intro P hPc hPcost
  -- ===== conclusion (a): the first R+T bits are row bits =====
  have hrowA : Protocol.FirstKRowBitsOn
      (Finset.univ :
        Finset {a // a ∈ (Finset.univ : Finset (Fin (2 ^ (R + T)) × X))})
      (Finset.univ : Finset {c // c ∈ C'}) (R + T) P := by
    have hfibsub : ∀ qq : Fin (2 ^ (R + T)),
        ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-((0 : ℕ) : ℝ))⌉₊
        ≤ ((Finset.univ :
            Finset {a // a ∈ (Finset.univ : Finset (Fin (2 ^ (R + T)) × X))}).filter
            (fun p => p.val.1 = qq)).card := by
      intro qq
      have hθ0 : ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (-((0 : ℕ) : ℝ))⌉₊
          = Fintype.card X := by simp
      have hcard : ((Finset.univ :
          Finset {a // a ∈ (Finset.univ : Finset (Fin (2 ^ (R + T)) × X))}).filter
          (fun p => p.val.1 = qq)).card = Fintype.card X := by
        rw [Finset.univ_eq_attach]
        have h1 := card_filter_image_val
          (u := (Finset.univ : Finset (Fin (2 ^ (R + T)) × X)).attach)
          (fun p : Fin (2 ^ (R + T)) × X => p.1 = qq)
        rw [Finset.attach_image_val] at h1
        rw [← h1]
        exact sep_fiber_univ_card qq
      rw [hθ0, hcard]
    have hchain := sep_main_chain f hb hε T R hTb S hS pseed hx1 hx2 hh0 hh1
      hs0 hs1 hp1 hp2 hres hseedbd hbridge hrob hδ0 hδ2 hD hT1 hband hbig
      (Finset.univ : Finset (Fin (2 ^ (R + T)) × X)) C' hC' P 0
      Finset.univ Finset.univ
      (fun x _ y _ => hPc x y)
      (by omega)
      (by simp)
      (fun qq _ => hfibsub qq)
    simpa using hchain
  refine ⟨hrowA, ?_⟩
  -- ===== conclusion (b): the no-waste dominant-block partition =====
  refine no_waste_row_partition (Finset.univ : Finset (Fin (2 ^ (R + T))))
    (Finset.univ : Finset (Fin (2 ^ (R + T)) × X)) (Fintype.card X)
    ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊ (2 ^ (R + T)) (by simp)
    (Protocol.prefixLabelFinQ (Finset.univ : Finset (Fin (2 ^ (R + T)) × X)) P)
    (fun qq _ => le_of_eq (sep_fiber_univ_card qq).symm)
    (by simpa using hgap) ?_
  -- hNoTwo: two heavy blocks in one part contradict the residual budget
  intro j hex
  obtain ⟨i₁, -, i₂, -, hne, hh₁, hh₂⟩ := hex
  have hfib : ∀ i : Fin (2 ^ (R + T)),
      (Finset.univ : Finset (Fin (2 ^ (R + T)) × X)).filter
        (fun p => Protocol.prefixLabelFinQ
          (Finset.univ : Finset (Fin (2 ^ (R + T)) × X)) P p = j ∧ p.1 = i)
      = (Protocol.prefixFiber (Finset.univ : Finset (Fin (2 ^ (R + T)) × X))
          (Protocol.prefixLabelFinQ
            (Finset.univ : Finset (Fin (2 ^ (R + T)) × X)) P) j).filter
          (fun p => p.1 = i) := by
    intro i
    rw [Protocol.prefixFiber, Finset.filter_filter]
  have hup : D (subgame (relaxedInterlace f S)
      (Protocol.prefixFiber (Finset.univ : Finset (Fin (2 ^ (R + T)) × X))
        (Protocol.prefixLabelFinQ
          (Finset.univ : Finset (Fin (2 ^ (R + T)) × X)) P) j) C')
      ≤ P.cost - (R + T) :=
    D_prefixFiber_le_of_residual
      (Finset.univ : Finset (Fin (2 ^ (R + T)) × X)) C'
      (relaxedInterlace f S) P j hrowA hPc
  have hpair : ({i₁, i₂} : Finset (Fin (2 ^ (R + T)))).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne),
      Finset.card_singleton]
  have hut2 : 2 ≤ 2 ^ T := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ T := Nat.pow_le_pow_right (by norm_num) hT1
  have hfam2 : D f + 1 ≤ Dfamily (interlaceFun f 2)
      (bracketGE X Y 2 ((2 : ℝ) ^ (1 - b)) ((1 / 2 + δ) ^ 2)) := by
    exact_mod_cast two_copy_amplification hrob hb hδ0 hδ2 hD
  have hfibs : ∀ qq ∈ ({i₁, i₂} : Finset (Fin (2 ^ (R + T)))),
      ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ (1 - b))⌉₊
      ≤ ((Protocol.prefixFiber (Finset.univ : Finset (Fin (2 ^ (R + T)) × X))
          (Protocol.prefixLabelFinQ
            (Finset.univ : Finset (Fin (2 ^ (R + T)) × X)) P) j).filter
          (fun p => p.1 = qq)).card := by
    intro qq hqq
    rw [← hfib qq]
    have hTeq : ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ (1 - b))⌉₊
        = ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊ := by rw [mul_comm]
    rw [hTeq]
    rcases Finset.mem_insert.mp hqq with rfl | hqq2
    · exact hh₁
    · rw [Finset.mem_singleton] at hqq2
      subst hqq2
      exact hh₂
  have hlow := sep_bridge_lower f hε hS (by norm_num : 0 < 2) hut2 hfam2
    (le_refl _) (sep_band_weak hband)
    ({i₁, i₂} : Finset (Fin (2 ^ (R + T)))) hpair
    (Protocol.prefixFiber (Finset.univ : Finset (Fin (2 ^ (R + T)) × X))
      (Protocol.prefixLabelFinQ
        (Finset.univ : Finset (Fin (2 ^ (R + T)) × X)) P) j) C' hfibs hC'
  omega

end NPCC
