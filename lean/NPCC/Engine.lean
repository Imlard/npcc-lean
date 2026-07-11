import Mathlib
import NPCC.Complexity
import NPCC.Twin
import NPCC.Robust
import NPCC.RobustAux
import Workspace.Types.Interlace
import Workspace.Appendix
import Workspace.Induction

/-! # Classical lower-bound engine (paper §2), typed statements.
Proof vehicle: the value-level transfer (`DSet_le_Dfamily`, NPCC.Twin) puts the
verified artifact's ladder machinery behind these; native first-bit analysis is
the fallback. -/

namespace NPCC

open Workspace.Types.CommComplexity Workspace.Types.Interlace
open Workspace.Types.BoolMat Workspace.Types.Bracket
open Workspace.Types.MatComplexity Workspace.Types.Lambda
open Workspace.Appendix Workspace.BracketLemmas

/-- Real square-root of a square: `(t^2)^{1/2} = t` for `t ≥ 0`. -/
private theorem rpow_sq_half {t : ℝ} (ht : 0 ≤ t) :
    Real.rpow (t ^ 2) (1 / 2) = t := by
  show ((t ^ 2 : ℝ)) ^ (1 / 2 : ℝ) = t
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq ht]

/-- `(t^2 / 4)^{1/2} = t / 2` for `t ≥ 0`. -/
private theorem rpow_sq_div4_half {t : ℝ} (ht : 0 ≤ t) :
    Real.rpow (t ^ 2 / 4) (1 / 2) = t / 2 := by
  have h : t ^ 2 / 4 = (t / 2) ^ 2 := by ring
  rw [h, rpow_sq_half (by positivity)]

-- CLAIM-BEGIN lem:two-copy-ladder
/-- Paper `lem:two-copy-ladder`: one-copy lower bounds at the three coupled
densities `y, y/2, y/4` (levels `H, H−1, H−2`, `H` real) lift through the
two-copy interlace to bounds at row density `2x` and densities
`y², y²/2, y²/4` (levels `H+1, H, H−1`). The paper's `M` is any Boolean
matrix — here any typed game `f` over Fintypes; `comp⟨M,k,·,·⟩` is
`Dfamily (interlaceFun f k) (bracketGE X Y k · ·)`; comparisons are ℝ-cast
since `H ∈ ℝ` (the paper's convention). The guard `1 < H` is added because
the printed statement is false at `H = 1`; `PAPER-FINDINGS.md` gives an
explicit two-column counterexample. All downstream use sites satisfy the
guard. Hypothesis order otherwise matches the paper:
`0 < x ≤ 1/2`, `0 < y ≤ 1`. -/
theorem two_copy_ladder {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {x y H : ℝ}
    (hH : 1 < H) (hx0 : 0 < x) (hx : x ≤ 1 / 2) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (h4 : H - 2 ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (y / 4)) : ℝ))
    (h2 : H - 1 ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (y / 2)) : ℝ))
    (h1 : H ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x y) : ℝ)) :
    H - 1 ≤ (Dfamily (interlaceFun f 2) (bracketGE X Y 2 (2 * x) (y ^ 2 / 4)) : ℝ) ∧
    H ≤ (Dfamily (interlaceFun f 2) (bracketGE X Y 2 (2 * x) (y ^ 2 / 2)) : ℝ) ∧
    H + 1 ≤ (Dfamily (interlaceFun f 2) (bracketGE X Y 2 (2 * x) (y ^ 2)) : ℝ) :=
-- CLAIM-END lem:two-copy-ladder
  by
  classical
  -- basic density facts
  have hx1 : x ≤ 1 := by linarith
  have h2x0 : 0 < 2 * x := by linarith
  have h2x1 : 2 * x ≤ 1 := by linarith
  have hy2_0 : 0 < y ^ 2 := by positivity
  have hy2_1 : y ^ 2 ≤ 1 := by nlinarith
  -- Degenerate: if card X = 0 or card Y = 0, the p=1 family is 0, contradicting h1.
  rcases Nat.eq_zero_or_pos (Fintype.card X) with hcX0 | hcXpos
  · exfalso
    have hXempty : IsEmpty X := Fintype.card_eq_zero_iff.mp hcX0
    -- every member of the p=1 family has empty row party, so D = 0, hence Dfamily = 0
    have hzero : Dfamily (interlaceFun f 1) (bracketGE X Y 1 x y) = 0 := by
      apply Nat.le_zero.mp
      -- exhibit a member whose subgame has empty rows
      -- bracketGE.nonempty needs 1 ≤ card X, unavailable; instead sInf over the
      -- family: any member has row subtype empty (Fin 1 × X empty).
      have hrowsEmpty : IsEmpty (Fin 1 × X) := by
        constructor; rintro ⟨_, xx⟩; exact hXempty.false xx
      -- The family is a subset of ℕ; if nonempty every element is 0.
      unfold Dfamily
      by_cases hne : (bracketGE X Y 1 x y).Nonempty
      · obtain ⟨RC, hRC⟩ := hne
        apply Nat.sInf_le
        refine ⟨RC, hRC, ?_⟩
        symm
        -- D (subgame ...) = 0 since row subtype empty
        have hsub : IsEmpty {a // a ∈ RC.1} :=
          Subtype.isEmpty_of_false (fun a => (hrowsEmpty.false a).elim)
        exact NPCC.D_zero_of_empty _ (Or.inl hsub)
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [show {d : ℕ | ∃ RC ∈ bracketGE X Y 1 x y,
            d = D (subgame (interlaceFun f 1) RC.1 RC.2)} = ∅ from ?_]
        · exact le_of_eq Nat.sInf_empty
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro d ⟨RC, hRC, _⟩; rw [hne] at hRC; exact hRC
    rw [hzero] at h1; simp at h1; linarith
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with hcY0 | hcYpos
  · exfalso
    have hYempty : IsEmpty Y := Fintype.card_eq_zero_iff.mp hcY0
    have hzero : Dfamily (interlaceFun f 1) (bracketGE X Y 1 x y) = 0 := by
      apply Nat.le_zero.mp
      have hcolsEmpty : IsEmpty (Fin 1 → Y) := by
        constructor; intro g; exact hYempty.false (g 0)
      unfold Dfamily
      by_cases hne : (bracketGE X Y 1 x y).Nonempty
      · obtain ⟨RC, hRC⟩ := hne
        apply Nat.sInf_le
        refine ⟨RC, hRC, ?_⟩
        symm
        have hsub : IsEmpty {c // c ∈ RC.2} :=
          Subtype.isEmpty_of_false (fun c => (hcolsEmpty.false c).elim)
        exact NPCC.D_zero_of_empty _ (Or.inr hsub)
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [show {d : ℕ | ∃ RC ∈ bracketGE X Y 1 x y,
            d = D (subgame (interlaceFun f 1) RC.1 RC.2)} = ∅ from ?_]
        · exact le_of_eq Nat.sInf_empty
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro d ⟨RC, hRC, _⟩; rw [hne] at hRC; exact hRC
    rw [hzero] at h1; simp at h1; linarith
  -- MAIN CASE: card X ≥ 1, card Y ≥ 1.
  have hX : 1 ≤ Fintype.card X := hcXpos
  -- Canonical presentation of f.
  set eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm with heXdef
  set eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm with heYdef
  set M : BoolMat := ⟨Fintype.card X, Fintype.card Y, fun i j => f (eX i) (eY j)⟩ with hMdef
  have he : ∀ i j, M.e i j = f (eX i) (eY j) := fun i j => rfl
  -- density bounds
  have hy4_0 : 0 < y / 4 := by linarith
  have hy4_1 : y / 4 ≤ 1 := by linarith
  have hy2h_0 : 0 < y / 2 := by linarith
  have hy2h_1 : y / 2 ≤ 1 := by linarith
  have hy2d2_0 : 0 < y ^ 2 / 2 := by positivity
  have hy2d2_1 : y ^ 2 / 2 ≤ 1 := by nlinarith
  have hy2d4_0 : 0 < y ^ 2 / 4 := by positivity
  have hy2d4_1 : y ^ 2 / 4 ≤ 1 := by nlinarith
  -- Transfer equalities (Dfamily = DSet) at the needed grid points.
  have hTy : Dfamily (interlaceFun f 1) (bracketGE X Y 1 x y) = DSet (bracket M 1 x y) :=
    Dfamily_eq_DSet f M eX eY he hx0 hx1 hy0 hy1 hX
  have hTy2 : Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (y / 2))
      = DSet (bracket M 1 x (y / 2)) :=
    Dfamily_eq_DSet f M eX eY he hx0 hx1 hy2h_0 hy2h_1 hX
  have hTy4 : Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (y / 4))
      = DSet (bracket M 1 x (y / 4)) :=
    Dfamily_eq_DSet f M eX eY he hx0 hx1 hy4_0 hy4_1 hX
  have hTsq : Dfamily (interlaceFun f 2) (bracketGE X Y 2 (2 * x) (y ^ 2))
      = DSet (bracket M 2 (2 * x) (y ^ 2)) :=
    Dfamily_eq_DSet f M eX eY he h2x0 h2x1 hy2_0 hy2_1 hX
  have hTsq2 : Dfamily (interlaceFun f 2) (bracketGE X Y 2 (2 * x) (y ^ 2 / 2))
      = DSet (bracket M 2 (2 * x) (y ^ 2 / 2)) :=
    Dfamily_eq_DSet f M eX eY he h2x0 h2x1 hy2d2_0 hy2d2_1 hX
  have hTsq4 : Dfamily (interlaceFun f 2) (bracketGE X Y 2 (2 * x) (y ^ 2 / 4))
      = DSet (bracket M 2 (2 * x) (y ^ 2 / 4)) :=
    Dfamily_eq_DSet f M eX eY he h2x0 h2x1 hy2d4_0 hy2d4_1 hX
  -- Rewrite all six occurrences to DSet.
  rw [hTy] at h1; rw [hTy2] at h2; rw [hTy4] at h4
  rw [hTsq, hTsq2, hTsq4]
  -- Abbreviations for the one-copy DSet values (ℕ).
  set d0 : ℕ := DSet (bracket M 1 x y) with hd0def
  set d1 : ℕ := DSet (bracket M 1 x (y / 2)) with hd1def
  set d2 : ℕ := DSet (bracket M 1 x (y / 4)) with hd2def
  -- h1 : H ≤ d0 ; h2 : H-1 ≤ d1 ; h4 : H-2 ≤ d2 (all real casts)
  -- Establish the nonemptiness hypothesis for the column ladder step:
  -- DSet (bracket M 2 (2x) (y²/4)) ≥ 1, via projection to bracket M 1 (2x) (y/2)
  -- then row-monotonicity down to bracket M 1 x (y/2) = d1, and d1 ≥ H-1 > 0.
  have hd1_pos : 1 ≤ d1 := by
    have hHd1 : (0 : ℝ) < (d1 : ℝ) := by linarith
    have : (0 : ℕ) < d1 := by exact_mod_cast hHd1
    omega
  have hLadderPos : DSet (bracket M 2 (2 * x) (y ^ 2 / 4)) ≥ 1 := by
    have hproj := extended_maximum_projection M 2 1 (2 * x) (y ^ 2 / 4)
      (by omega) (by omega) hy2d4_0
    have hexp : ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = (1 : ℝ) / 2 := by norm_num
    rw [hexp, rpow_sq_div4_half (le_of_lt hy0)] at hproj
    have hmono := monotonicity M 1 1 x (2 * x) (y / 2) (y / 2)
      (by omega) (le_refl _) hx0 (by linarith) h2x1 hy2h_0 (le_refl _) hy2h_1
    have : d1 ≤ DSet (bracket M 2 (2 * x) (y ^ 2 / 4)) :=
      le_trans hmono hproj
    omega
  -- The column ladder step at p = 1, τ = 1, base density y².
  have hlad := lemma_A4_column_ladder_step M 1 (by omega) x (y ^ 2) 1
    ⟨hx0, hx, hy2_0, hy2_1, by norm_num, le_refl _⟩
    (by simpa using hLadderPos)
  have hq : (⌊((1 : ℕ) : ℝ) * (1 - 1)⌋₊ + 1) = 1 := by norm_num
  have hw : Real.rpow (y ^ 2) (1 / (1 + 1)) = y := by
    rw [show (1 : ℝ) / (1 + 1) = 1 / 2 by norm_num]
    exact rpow_sq_half (le_of_lt hy0)
  rw [show (2 * 1 : ℕ) = 2 from rfl] at hlad
  rw [hq, hw] at hlad
  rw [min_self] at hlad
  simp only [Lambda] at hlad
  set D2y := DSet (bracket M 2 (2 * x) (y ^ 2)) with hD2ydef
  set D2y2 := DSet (bracket M 2 (2 * x) (y ^ 2 / 2)) with hD2y2def
  set D2y4 := DSet (bracket M 2 (2 * x) (y ^ 2 / 4)) with hD2y4def
  set L : ℕ := min d0 (min (1 + d1) (2 + d2)) with hLdef
  have hbound_y : D2y ≥ 1 + L := le_trans hlad (min_le_left _ _)
  have hbound_y2 : 1 + D2y2 ≥ 1 + L :=
    le_trans hlad (le_trans (min_le_right _ _) (min_le_left _ _))
  have hbound_y4 : 2 + D2y4 ≥ 1 + L :=
    le_trans hlad (le_trans (min_le_right _ _) (min_le_right _ _))
  have hHL : (H : ℝ) ≤ (L : ℝ) := by
    rw [hLdef]
    push_cast [Nat.cast_min]
    refine le_min h1 (le_min ?_ ?_)
    · linarith
    · linarith
  refine ⟨?_, ?_, ?_⟩
  · have : (1 : ℝ) + (L : ℝ) ≤ (2 : ℝ) + (D2y4 : ℝ) := by exact_mod_cast hbound_y4
    linarith
  · have : (1 : ℝ) + (L : ℝ) ≤ (1 : ℝ) + (D2y2 : ℝ) := by exact_mod_cast hbound_y2
    linarith
  · have : (1 : ℝ) + (L : ℝ) ≤ (D2y : ℝ) := by exact_mod_cast hbound_y
    linarith

-- CLAIM-BEGIN cor:robust-two-copy-ladder
/-- Paper `cor:robust-two-copy-ladder`, WITH the F1 repair: the paper states
this for `(δ,b)`-robust `M` with `b ≥ 1` only, instantiating the two-copy
ladder at `H = comp M` — but R1 supplies only `comp M ≥ 1`, and the ladder is
false at `H = 1` (see the explicit counterexample in `PAPER-FINDINGS.md` F1).
The hypothesis `2 ≤ D f` (equivalently the ladder's guard `1 < H`) is
therefore added; every downstream use in the paper satisfies it. Densities:
row `2^(1-b)` (= `2·2^{-b}`), columns `y₀²/4, y₀²/2, y₀²` for
`y₀ = 1/2 + δ`; levels `comp M − 1, comp M, comp M + 1`. `δ ≤ 1/2` is the
paper's standing `δ ∈ (0,1/2)` side condition. -/
theorem robust_two_copy_ladder {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) (hb : 1 ≤ b) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hD : 2 ≤ D f) :
    (D f : ℝ) - 1 ≤ (Dfamily (interlaceFun f 2)
        (bracketGE X Y 2 ((2 : ℝ) ^ (1 - b)) ((1 / 2 + δ) ^ 2 / 4)) : ℝ) ∧
    (D f : ℝ) ≤ (Dfamily (interlaceFun f 2)
        (bracketGE X Y 2 ((2 : ℝ) ^ (1 - b)) ((1 / 2 + δ) ^ 2 / 2)) : ℝ) ∧
    (D f : ℝ) + 1 ≤ (Dfamily (interlaceFun f 2)
        (bracketGE X Y 2 ((2 : ℝ) ^ (1 - b)) ((1 / 2 + δ) ^ 2)) : ℝ) :=
-- CLAIM-END cor:robust-two-copy-ladder
  by
  set x : ℝ := (2 : ℝ) ^ (-b) with hxdef
  set y : ℝ := 1 / 2 + δ with hydef
  set H : ℝ := (D f : ℝ) with hHdef
  have hH : 1 < H := by
    rw [hHdef]
    have : (2 : ℝ) ≤ (D f : ℝ) := by exact_mod_cast hD
    linarith
  have hx0 : 0 < x := by rw [hxdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hx : x ≤ 1 / 2 := by
    rw [hxdef]
    have hle : (2 : ℝ) ^ (-b) ≤ (2 : ℝ) ^ (-(1:ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    have heval : (2 : ℝ) ^ (-(1:ℝ)) = 1 / 2 := by
      rw [Real.rpow_neg_one]; norm_num
    rw [heval] at hle; exact hle
  have hy0 : 0 < y := by rw [hydef]; linarith
  have hy1 : y ≤ 1 := by rw [hydef]; linarith
  have hr2 := h.r2
  have hr3 := h.r3
  have hr4 := h.r4
  have h1 : H ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x y) : ℝ) := by
    rw [hHdef, hxdef, hydef]
    exact_mod_cast hr2
  have hyd2 : y / 2 = 1 / 4 + δ / 2 := by rw [hydef]; ring
  have h2 : H - 1 ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (y / 2)) : ℝ) := by
    rw [hHdef, hxdef, hyd2]
    have hcast : ((D f : ℤ) : ℝ) - 1 ≤ ((Dfamily (interlaceFun f 1)
        (bracketGE X Y 1 ((2:ℝ)^(-b)) (1 / 4 + δ / 2)) : ℤ) : ℝ) := by
      exact_mod_cast hr4
    push_cast at hcast ⊢
    linarith
  have hyd4 : y / 4 = 1 / 8 + δ / 4 := by rw [hydef]; ring
  have h4 : H - 2 ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (y / 4)) : ℝ) := by
    rw [hHdef, hxdef, hyd4]
    have hcast : ((D f : ℤ) : ℝ) - 2 ≤ ((Dfamily (interlaceFun f 1)
        (bracketGE X Y 1 ((2:ℝ)^(-b)) (1 / 8 + δ / 4)) : ℤ) : ℝ) := by
      exact_mod_cast hr3
    push_cast at hcast ⊢
    linarith
  have hlad := two_copy_ladder f hH hx0 hx hy0 hy1 h4 h2 h1
  have hrow : 2 * x = (2 : ℝ) ^ (1 - b) := by
    rw [hxdef]
    rw [show (1 : ℝ) - b = 1 + (-b) by ring, Real.rpow_add (by norm_num : (0:ℝ) < 2),
        Real.rpow_one]
  rw [hrow] at hlad
  exact hlad

-- CLAIM-BEGIN cor:two-copy-amplification
/-- Paper `cor:two-copy-amplification`: the top rung of
`robust_two_copy_ladder` (same F1 guard). -/
theorem two_copy_amplification {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) (hb : 1 ≤ b) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hD : 2 ≤ D f) :
    (D f : ℝ) + 1 ≤ (Dfamily (interlaceFun f 2)
        (bracketGE X Y 2 ((2 : ℝ) ^ (1 - b)) ((1 / 2 + δ) ^ 2)) : ℝ) :=
-- CLAIM-END cor:two-copy-amplification
  (robust_two_copy_ladder h hb hδ0 hδ hD).2.2

/-! ## Typed Λ (paper §2 three-rung ladder minimum)
`LambdaGE` is the typed twin of the artifact's `Workspace.Types.Lambda.Lambda`
(minimum over the three coupled rungs `y, y/2, y/4` at offsets `0, 1, 2`); it
transfers pointwise to the artifact's `Lambda` via `Dfamily_eq_DSet`.
Unregistered supporting definition — judged together with
`lem:odd-copy-seed-rungs`, whose statement depends on it. -/

/-- Typed `Λ_f(p, x, y) := min(comp y, 1 + comp (y/2), 2 + comp (y/4))` over
the `≥`-bracket families (paper §2 `\Lambda_M`). -/
noncomputable def LambdaGE {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (p : ℕ) (x y : ℝ) : ℕ :=
  min (Dfamily (interlaceFun f p) (bracketGE X Y p x y))
      (min (1 + Dfamily (interlaceFun f p) (bracketGE X Y p x (y / 2)))
           (2 + Dfamily (interlaceFun f p) (bracketGE X Y p x (y / 4))))

/-- Pointwise transfer of the typed `LambdaGE` to the artifact `Lambda`, given a
presentation of `f` as a Boolean matrix `M`. -/
theorem LambdaGE_eq_Lambda {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (M : BoolMat) (eX : Fin M.m ≃ X) (eY : Fin M.n ≃ Y)
    (he : ∀ i j, M.e i j = f (eX i) (eY j)) {p : ℕ} {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) :
    LambdaGE f p x y = Lambda M p x y := by
  have hy2_0 : 0 < y / 2 := by linarith
  have hy2_1 : y / 2 ≤ 1 := by linarith
  have hy4_0 : 0 < y / 4 := by linarith
  have hy4_1 : y / 4 ≤ 1 := by linarith
  unfold LambdaGE Lambda
  rw [Dfamily_eq_DSet f M eX eY he hx0 hx1 hy0 hy1 hX,
      Dfamily_eq_DSet f M eX eY he hx0 hx1 hy2_0 hy2_1 hX,
      Dfamily_eq_DSet f M eX eY he hx0 hx1 hy4_0 hy4_1 hX]

private theorem rpow_two_le_one_of_nonpos {a : ℝ} (ha : a ≤ 0) :
    (2 : ℝ) ^ a ≤ 1 := by
  calc (2 : ℝ) ^ a ≤ (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
    _ = 1 := by norm_num

private theorem rpow_two_le_half_of_le_neg_one {a : ℝ} (ha : a ≤ -1) :
    (2 : ℝ) ^ a ≤ 1 / 2 := by
  calc (2 : ℝ) ^ a ≤ (2 : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
    _ = 1 / 2 := by
      rw [Real.rpow_neg_one]
      norm_num

private theorem two_mul_rpow_two (a : ℝ) :
    2 * (2 : ℝ) ^ a = (2 : ℝ) ^ (a + 1) := by
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  ring

private theorem two_mul_rpow_two_sub (n : ℕ) (b : ℝ) :
    2 * (2 : ℝ) ^ ((n : ℝ) - b) = (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) - b) := by
  rw [show (((n + 1 : ℕ) : ℝ) - b) = ((n : ℝ) - b) + 1 by norm_num; ring,
    ← two_mul_rpow_two]

private theorem two_mul_two_pow_pred (n : ℕ) (hn : 1 ≤ n) :
    2 * 2 ^ (n - 1) = 2 ^ n := by
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
  calc
    2 * 2 ^ (n - 1) = 2 ^ (n - 1) * 2 := by ring
    _ = 2 ^ (n - 1 + 1) := by rw [pow_succ]
    _ = 2 ^ n := by rw [hpred]

-- CLAIM-BEGIN lem:odd-copy-seed-rungs
/-- Paper `lem:odd-copy-seed-rungs`: for `(δ,b)`-robust `f` with `D f ≥ 2`
(the paper's `comp M ≥ 2`) and every integer `2 ≤ ℓ ≤ b`,
`Λ_f(2^(ℓ−1)+1, 2^(ℓ−b), y₀) ≥ D f + ℓ`, where `y₀ = (1/2+δ)^2` per the
paper's `y := 1/2+δ`, `y₀ := y²`. The copy count `2^(ℓ−1)+1` is odd; the row
density `2^(ℓ−b)` is a real power (`b : ℝ`). `0 < δ ≤ 1/2` and `1 ≤ b` are
the paper's standing robustness side conditions. -/
theorem odd_copy_seed_rungs {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) (hb : 1 ≤ b) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hD : 2 ≤ D f) (ℓ : ℕ) (hℓ2 : 2 ≤ ℓ) (hℓb : (ℓ : ℝ) ≤ b) :
    D f + ℓ ≤ LambdaGE f (2 ^ (ℓ - 1) + 1) ((2 : ℝ) ^ ((ℓ : ℝ) - b))
      ((1 / 2 + δ) ^ 2) :=
-- CLAIM-END lem:odd-copy-seed-rungs
  by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card X) with hcX0 | hcXpos
  · exfalso
    have hXempty : IsEmpty X := Fintype.card_eq_zero_iff.mp hcX0
    have hzero : D f = 0 := NPCC.D_zero_of_empty f (Or.inl hXempty)
    rw [hzero] at hD
    omega
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with hcY0 | hcYpos
  · exfalso
    have hYempty : IsEmpty Y := Fintype.card_eq_zero_iff.mp hcY0
    have hzero : D f = 0 := NPCC.D_zero_of_empty f (Or.inr hYempty)
    rw [hzero] at hD
    omega
  have hX : 1 ≤ Fintype.card X := Nat.succ_le_of_lt hcXpos
  set eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm with heXdef
  set eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm with heYdef
  set M : BoolMat := ⟨Fintype.card X, Fintype.card Y, fun i j => f (eX i) (eY j)⟩ with hMdef
  have he : ∀ i j, M.e i j = f (eX i) (eY j) := fun i j => rfl
  set y0 : ℝ := (1 / 2 + δ) ^ 2 with hy0def
  set x1 : ℝ := (2 : ℝ) ^ (1 - b) with hx1def
  have hybase0 : 0 < 1 / 2 + δ := by linarith
  have hybase1 : 1 / 2 + δ ≤ 1 := by linarith
  have hy0pos : 0 < y0 := by
    rw [hy0def]
    positivity
  have hy0le1 : y0 ≤ 1 := by
    rw [hy0def]
    nlinarith [hybase0, hybase1]
  have hy02pos : 0 < y0 / 2 := by positivity
  have hy02le1 : y0 / 2 ≤ 1 := by linarith
  have hy04pos : 0 < y0 / 4 := by positivity
  have hy04le1 : y0 / 4 ≤ 1 := by linarith
  have hx1pos : 0 < x1 := by
    rw [hx1def]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hx1le1 : x1 ≤ 1 := by
    rw [hx1def]
    apply rpow_two_le_one_of_nonpos
    linarith
  have hT0 : Dfamily (interlaceFun f 2) (bracketGE X Y 2 x1 y0)
      = DSet (bracket M 2 x1 y0) :=
    Dfamily_eq_DSet f M eX eY he hx1pos hx1le1 hy0pos hy0le1 hX
  have hT2 : Dfamily (interlaceFun f 2) (bracketGE X Y 2 x1 (y0 / 2))
      = DSet (bracket M 2 x1 (y0 / 2)) :=
    Dfamily_eq_DSet f M eX eY he hx1pos hx1le1 hy02pos hy02le1 hX
  have hT4 : Dfamily (interlaceFun f 2) (bracketGE X Y 2 x1 (y0 / 4))
      = DSet (bracket M 2 x1 (y0 / 4)) :=
    Dfamily_eq_DSet f M eX eY he hx1pos hx1le1 hy04pos hy04le1 hX
  have hr := robust_two_copy_ladder h hb hδ0 hδ hD
  have hTopR : (D f : ℝ) + 1 ≤ (DSet (bracket M 2 x1 y0) : ℝ) := by
    rw [← hT0, hx1def, hy0def]
    exact hr.2.2
  have hMidR : (D f : ℝ) ≤ (DSet (bracket M 2 x1 (y0 / 2)) : ℝ) := by
    rw [← hT2, hx1def, hy0def]
    exact hr.2.1
  have hLowR : (D f : ℝ) - 1 ≤ (DSet (bracket M 2 x1 (y0 / 4)) : ℝ) := by
    rw [← hT4, hx1def, hy0def]
    exact hr.1
  have hTopN : D f + 1 ≤ DSet (bracket M 2 x1 y0) := by
    exact_mod_cast hTopR
  have hMidN : D f ≤ DSet (bracket M 2 x1 (y0 / 2)) := by
    exact_mod_cast hMidR
  have hLowN : D f - 1 ≤ DSet (bracket M 2 x1 (y0 / 4)) := by
    have hcastsub : ((D f - 1 : ℕ) : ℝ) = (D f : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ D f)]
      norm_num
    have hreal : ((D f - 1 : ℕ) : ℝ) ≤ (DSet (bracket M 2 x1 (y0 / 4)) : ℝ) := by
      rwa [hcastsub]
    exact_mod_cast hreal
  have hLowOne : 1 ≤ DSet (bracket M 2 x1 (y0 / 4)) := by
    omega
  have hLam2 : D f + 1 ≤ Lambda M 2 x1 y0 := by
    unfold Lambda
    exact le_min hTopN (le_min (by omega) (by omega))
  have hSeedPow :
      ∀ n : ℕ, 1 ≤ n → (((n + 1 : ℕ) : ℝ) ≤ b) →
        1 ≤ DSet (bracket M (2 ^ n) ((2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) - b)) (y0 / 4)) := by
    intro n hn hnb
    set xn : ℝ := (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) - b) with hxndef
    set d : ℝ := y0 / 4 with hddef
    set e : ℝ := (2 : ℝ) / ((2 ^ n : ℕ) : ℝ) with hedef
    have h2lepow : 2 ≤ 2 ^ n := by
      have hpow_ge1 : 1 ≤ 2 ^ (n - 1) :=
        Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < (2 : ℕ)) _)
      calc
        2 = 2 * 1 := by norm_num
        _ ≤ 2 * 2 ^ (n - 1) := Nat.mul_le_mul_left 2 hpow_ge1
        _ = 2 ^ n := two_mul_two_pow_pred n hn
    have hdenpos : 0 < ((2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) n)
    have he_nonneg : 0 ≤ e := by
      rw [hedef]
      positivity
    have he_le1 : e ≤ 1 := by
      rw [hedef]
      rw [div_le_one hdenpos]
      exact_mod_cast h2lepow
    have hdpos : 0 < d := by
      rw [hddef]
      positivity
    have hdle1 : d ≤ 1 := by
      rw [hddef]
      linarith
    have hdpowle1 : Real.rpow d e ≤ 1 := by
      calc Real.rpow d e ≤ Real.rpow d (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 he_nonneg
        _ = 1 := Real.rpow_zero d
    have hdlepow : d ≤ Real.rpow d e := by
      calc d = Real.rpow d (1 : ℝ) := (Real.rpow_one d).symm
        _ ≤ Real.rpow d e :=
            Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 he_le1
    have hxnpos : 0 < xn := by
      rw [hxndef]
      exact Real.rpow_pos_of_pos (by norm_num) _
    have hxnle1 : xn ≤ 1 := by
      rw [hxndef]
      apply rpow_two_le_one_of_nonpos
      linarith
    have hx1lexn : x1 ≤ xn := by
      rw [hx1def, hxndef]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hncast : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 1 ≤ n + 1)
      linarith
    have hproj := extended_maximum_projection M (2 ^ n) 2 xn d (by omega) h2lepow hdpos
    have heqexp : ((2 : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ) = e := by
      rw [hedef]
      norm_num
    rw [heqexp] at hproj
    have hmono := monotonicity M 2 2 x1 xn d (Real.rpow d e)
      (by omega) (le_refl 2) hx1pos hx1lexn hxnle1 hdpos hdlepow hdpowle1
    have hcalc : 1 ≤ DSet (bracket M (2 ^ n) xn d) := by
      calc
        1 ≤ DSet (bracket M 2 x1 d) := by
          simpa [hddef] using hLowOne
        _ ≤ DSet (bracket M 2 xn (Real.rpow d e)) := hmono
        _ ≤ DSet (bracket M (2 ^ n) xn d) := hproj
    simpa [hxndef, hddef] using hcalc
  have hArtAll :
      ∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ b →
        D f + n ≤ Lambda M (2 ^ (n - 1) + 1) ((2 : ℝ) ^ ((n : ℝ) - b)) y0 := by
    intro n hn2
    induction n, hn2 using Nat.le_induction with
    | base =>
        intro h2b
        have hseed := hSeedPow 1 (by norm_num) (by simpa using h2b)
        have hrow : 2 * x1 = (2 : ℝ) ^ (((1 + 1 : ℕ) : ℝ) - b) := by
          simpa [hx1def] using two_mul_rpow_two_sub 1 b
        have hseedA3 : DSet (bracket M (2 * 1) (2 * x1) (y0 / 4)) ≥ 1 := by
          simpa [hrow] using hseed
        have hx1half : x1 ≤ 1 / 2 := by
          rw [hx1def]
          apply rpow_two_le_half_of_le_neg_one
          have h2b' : (2 : ℝ) ≤ b := by simpa using h2b
          linarith
        have hstep := lemma_A3_row_ladder_step M 1 (by omega) 1 (by omega)
          x1 y0 ⟨hx1pos, hx1half, hy0pos, hy0le1⟩ hseedA3
        have hbase : D f + 2 ≤ Lambda M (2 * 1 + 1) (2 * x1) y0 := by
          calc
            D f + 2 = 1 + (D f + 1) := by omega
            _ ≤ 1 + Lambda M 2 x1 y0 := Nat.add_le_add_left hLam2 1
            _ ≤ Lambda M (2 * 1 + 1) (2 * x1) y0 := hstep
        simpa [hrow] using hbase
    | succ n hn2 ih =>
        intro hnb
        have hn1 : 1 ≤ n := by omega
        have hnb_prev : (n : ℝ) ≤ b := by
          have hnle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_succ n
          exact le_trans hnle hnb
        have hIH := ih hnb_prev
        set xn : ℝ := (2 : ℝ) ^ ((n : ℝ) - b) with hxndef
        have hxnpos : 0 < xn := by
          rw [hxndef]
          exact Real.rpow_pos_of_pos (by norm_num) _
        have hxnlehalf : xn ≤ 1 / 2 := by
          rw [hxndef]
          apply rpow_two_le_half_of_le_neg_one
          have hnb' : (n : ℝ) + 1 ≤ b := by simpa using hnb
          linarith
        have hseed := hSeedPow n hn1 hnb
        have hp_eq : 2 * 2 ^ (n - 1) = 2 ^ n := two_mul_two_pow_pred n hn1
        have hx_eq : 2 * xn = (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) - b) := by
          simpa [hxndef] using two_mul_rpow_two_sub n b
        have hseedA3 :
            DSet (bracket M (2 * 2 ^ (n - 1)) (2 * xn) (y0 / 4)) ≥ 1 := by
          simpa [hp_eq, hx_eq] using hseed
        have hp_pos : 1 ≤ 2 ^ (n - 1) :=
          Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < (2 : ℕ)) _)
        have hstep := lemma_A3_row_ladder_step M (2 ^ (n - 1)) hp_pos 1 (by omega)
          xn y0 ⟨hxnpos, hxnlehalf, hy0pos, hy0le1⟩ hseedA3
        have hcalc :
            D f + (n + 1) ≤ Lambda M (2 * 2 ^ (n - 1) + 1) (2 * xn) y0 := by
          calc
            D f + (n + 1) = 1 + (D f + n) := by omega
            _ ≤ 1 + Lambda M (2 ^ (n - 1) + 1) xn y0 :=
                Nat.add_le_add_left (by simpa [hxndef] using hIH) 1
            _ ≤ Lambda M (2 * 2 ^ (n - 1) + 1) (2 * xn) y0 := hstep
        have hp_succ : 2 * 2 ^ (n - 1) + 1 = 2 ^ ((n + 1) - 1) + 1 := by
          rw [hp_eq]
          have : (n + 1) - 1 = n := by omega
          rw [this]
        simpa [hp_succ, hx_eq] using hcalc
  have hArt := hArtAll ℓ hℓ2 hℓb
  have hxℓ0 : 0 < (2 : ℝ) ^ ((ℓ : ℝ) - b) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hxℓ1 : (2 : ℝ) ^ ((ℓ : ℝ) - b) ≤ 1 := by
    apply rpow_two_le_one_of_nonpos
    linarith
  rw [LambdaGE_eq_Lambda f M eX eY he hxℓ0 hxℓ1 hy0pos hy0le1 hX]
  exact hArt

-- CLAIM-BEGIN cor:plus-one-family
/-- Paper `cor:plus-one-family`: top-rung scalar consequence of the odd-copy
seed — `comp⟨f, 2^(k−1)+1, 2^(k−b), (1/2+δ)²⟩ ≥ D f + k` for every integer
`2 ≤ k ≤ b` (same standing hypotheses, same F1-adjacent `2 ≤ D f`). -/
theorem plus_one_family {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) (hb : 1 ≤ b) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hD : 2 ≤ D f) (k : ℕ) (hk2 : 2 ≤ k) (hkb : (k : ℝ) ≤ b) :
    D f + k ≤ Dfamily (interlaceFun f (2 ^ (k - 1) + 1))
      (bracketGE X Y (2 ^ (k - 1) + 1) ((2 : ℝ) ^ ((k : ℝ) - b))
        ((1 / 2 + δ) ^ 2)) :=
-- CLAIM-END cor:plus-one-family
  by
  have hΛ := odd_copy_seed_rungs h hb hδ0 hδ hD k hk2 hkb
  exact le_trans hΛ (by
    unfold LambdaGE
    exact min_le_left _ _)

-- CLAIM-BEGIN lem:partition
/-- Paper `lem:partition` (One-step partition): the paper's raw first-bit
trichotomy over the typed bracket families. Vehicle: verbatim transfer of the
artifact's `old_partition` (Workspace/BracketLemmas.lean) via `Dfamily_eq_DSet`
— the artifact statement IS the paper statement (its `δ` is the paper's `σ`;
its middle term is the same `sInf` over `(ℓ, a ∈ [0,1])` of the max of the two
children, with `p + δ + ℓ` for the paper's `p + ℓ + σ`). The inner minimum is
rendered as `sInf` on ℕ, nonempty at `ℓ = 0, a = 0` since `1 ≤ p`. -/
theorem one_step_partition {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (p σ : ℕ) (hp : 1 ≤ p) (hσ : σ ≤ 1) {x y : ℝ}
    (hx0 : 0 < x) (hx : x ≤ 1 / 2) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (h1 : 1 ≤ Dfamily (interlaceFun f (2 * p + σ))
        (bracketGE X Y (2 * p + σ) (2 * x) y)) :
    1 + min (Dfamily (interlaceFun f (2 * p + σ))
          (bracketGE X Y (2 * p + σ) x y))
        (min (sInf { d : ℕ | ∃ (ℓ : ℕ) (a : ℝ), ℓ < p ∧ 0 ≤ a ∧ a ≤ 1 ∧
              d = max (Dfamily (interlaceFun f (p + ℓ + σ))
                    (bracketGE X Y (p + ℓ + σ) x (y ^ a)))
                  (Dfamily (interlaceFun f (p - ℓ))
                    (bracketGE X Y (p - ℓ) x (y ^ (1 - a)))) })
          (Dfamily (interlaceFun f (2 * p + σ))
            (bracketGE X Y (2 * p + σ) (2 * x) (y / 2))))
      ≤ Dfamily (interlaceFun f (2 * p + σ))
          (bracketGE X Y (2 * p + σ) (2 * x) y) :=
-- CLAIM-END lem:partition
  by
  classical
  have hx1 : x ≤ 1 := by linarith
  have h2x0 : 0 < 2 * x := by linarith
  have h2x1 : 2 * x ≤ 1 := by linarith
  have hy2_0 : 0 < y / 2 := by linarith
  have hy2_1 : y / 2 ≤ 1 := by linarith
  rcases Nat.eq_zero_or_pos (Fintype.card X) with hcX0 | hcXpos
  · exfalso
    have hXempty : IsEmpty X := Fintype.card_eq_zero_iff.mp hcX0
    have hzero : Dfamily (interlaceFun f (2 * p + σ))
        (bracketGE X Y (2 * p + σ) (2 * x) y) = 0 := by
      apply Nat.le_zero.mp
      have hrowsEmpty : IsEmpty (Fin (2 * p + σ) × X) := by
        constructor
        rintro ⟨_, xx⟩
        exact hXempty.false xx
      unfold Dfamily
      by_cases hne : (bracketGE X Y (2 * p + σ) (2 * x) y).Nonempty
      · obtain ⟨RC, hRC⟩ := hne
        apply Nat.sInf_le
        refine ⟨RC, hRC, ?_⟩
        symm
        have hsub : IsEmpty {a // a ∈ RC.1} :=
          Subtype.isEmpty_of_false (fun a => (hrowsEmpty.false a).elim)
        exact NPCC.D_zero_of_empty _ (Or.inl hsub)
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [show {d : ℕ | ∃ RC ∈ bracketGE X Y (2 * p + σ) (2 * x) y,
            d = D (subgame (interlaceFun f (2 * p + σ)) RC.1 RC.2)} = ∅ from ?_]
        · exact le_of_eq Nat.sInf_empty
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro d ⟨RC, hRC, _⟩
          rw [hne] at hRC
          exact hRC
    rw [hzero] at h1
    omega
  have hX : 1 ≤ Fintype.card X := hcXpos
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with hcY0 | _hcYpos
  · exfalso
    have hPpos : 0 < 2 * p + σ := by omega
    have hzero : Dfamily (interlaceFun f (2 * p + σ))
        (bracketGE X Y (2 * p + σ) (2 * x) y) = 0 :=
      Dfamily_zero_degenerate f h2x1 hy1 hX (Or.inr ⟨hPpos, hcY0⟩)
    rw [hzero] at h1
    omega
  set eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm with heXdef
  set eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm with heYdef
  set M : BoolMat := ⟨Fintype.card X, Fintype.card Y, fun i j => f (eX i) (eY j)⟩ with hMdef
  have he : ∀ i j, M.e i j = f (eX i) (eY j) := fun i j => rfl
  have hTtop : Dfamily (interlaceFun f (2 * p + σ))
      (bracketGE X Y (2 * p + σ) (2 * x) y)
      = DSet (bracket M (2 * p + σ) (2 * x) y) :=
    Dfamily_eq_DSet f M eX eY he h2x0 h2x1 hy0 hy1 hX
  have hTleft : Dfamily (interlaceFun f (2 * p + σ))
      (bracketGE X Y (2 * p + σ) x y)
      = DSet (bracket M (2 * p + σ) x y) :=
    Dfamily_eq_DSet f M eX eY he hx0 hx1 hy0 hy1 hX
  have hTlow : Dfamily (interlaceFun f (2 * p + σ))
      (bracketGE X Y (2 * p + σ) (2 * x) (y / 2))
      = DSet (bracket M (2 * p + σ) (2 * x) (y / 2)) :=
    Dfamily_eq_DSet f M eX eY he h2x0 h2x1 hy2_0 hy2_1 hX
  have hInner :
      { d : ℕ | ∃ (ℓ : ℕ) (a : ℝ), ℓ < p ∧ 0 ≤ a ∧ a ≤ 1 ∧
            d = max (Dfamily (interlaceFun f (p + ℓ + σ))
                  (bracketGE X Y (p + ℓ + σ) x (y ^ a)))
                (Dfamily (interlaceFun f (p - ℓ))
                  (bracketGE X Y (p - ℓ) x (y ^ (1 - a)))) }
        =
      { v : ℕ | ∃ (ℓ : ℕ) (a : ℝ), ℓ < p ∧ 0 ≤ a ∧ a ≤ 1 ∧
            v = max (DSet (bracket M (p + σ + ℓ) x (Real.rpow y a)))
                    (DSet (bracket M (p - ℓ) x (Real.rpow y (1 - a)))) } := by
    ext d
    constructor
    · rintro ⟨ℓ, a, hℓ, ha0, ha1, rfl⟩
      have hya0 : 0 < y ^ a := Real.rpow_pos_of_pos hy0 a
      have hya1 : y ^ a ≤ 1 := Real.rpow_le_one (le_of_lt hy0) hy1 ha0
      have h1a0 : 0 ≤ 1 - a := by linarith
      have hy1a0 : 0 < y ^ (1 - a) := Real.rpow_pos_of_pos hy0 (1 - a)
      have hy1a1 : y ^ (1 - a) ≤ 1 :=
        Real.rpow_le_one (le_of_lt hy0) hy1 h1a0
      have hL : Dfamily (interlaceFun f (p + ℓ + σ))
          (bracketGE X Y (p + ℓ + σ) x (y ^ a))
          = DSet (bracket M (p + ℓ + σ) x (y ^ a)) :=
        Dfamily_eq_DSet f M eX eY he hx0 hx1 hya0 hya1 hX
      have hR : Dfamily (interlaceFun f (p - ℓ))
          (bracketGE X Y (p - ℓ) x (y ^ (1 - a)))
          = DSet (bracket M (p - ℓ) x (y ^ (1 - a))) :=
        Dfamily_eq_DSet f M eX eY he hx0 hx1 hy1a0 hy1a1 hX
      refine ⟨ℓ, a, hℓ, ha0, ha1, ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg₂ max hL hR
    · rintro ⟨ℓ, a, hℓ, ha0, ha1, rfl⟩
      have hya0 : 0 < y ^ a := Real.rpow_pos_of_pos hy0 a
      have hya1 : y ^ a ≤ 1 := Real.rpow_le_one (le_of_lt hy0) hy1 ha0
      have h1a0 : 0 ≤ 1 - a := by linarith
      have hy1a0 : 0 < y ^ (1 - a) := Real.rpow_pos_of_pos hy0 (1 - a)
      have hy1a1 : y ^ (1 - a) ≤ 1 :=
        Real.rpow_le_one (le_of_lt hy0) hy1 h1a0
      have hL : Dfamily (interlaceFun f (p + ℓ + σ))
          (bracketGE X Y (p + ℓ + σ) x (y ^ a))
          = DSet (bracket M (p + ℓ + σ) x (y ^ a)) :=
        Dfamily_eq_DSet f M eX eY he hx0 hx1 hya0 hya1 hX
      have hR : Dfamily (interlaceFun f (p - ℓ))
          (bracketGE X Y (p - ℓ) x (y ^ (1 - a)))
          = DSet (bracket M (p - ℓ) x (y ^ (1 - a))) :=
        Dfamily_eq_DSet f M eX eY he hx0 hx1 hy1a0 hy1a1 hX
      refine ⟨ℓ, a, hℓ, ha0, ha1, ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (congrArg₂ max hL hR).symm
  have hpos : DSet (bracket M (2 * p + σ) (2 * x) y) ≥ 1 := by
    rw [← hTtop]
    exact h1
  have hpart := old_partition M p σ x y hx0 hx hy0 hy1 hσ hpos
  rw [hTtop, hTleft, hTlow, hInner]
  exact hpart

/-! ## The grid induction (paper App. A) and its corollaries.
`gridFloor` names the paper's target copy count `⌊2^k β^s p⌋` with
`β = (ρ−1)/(ρ−2)` (unregistered supporting def per Ultra npcc-4 S2 fix —
judged with `lem:new-partition`, whose statement uses it twice). -/

/-- `⌊2^k · ((ρ−1)/(ρ−2))^s · p⌋₊` — the paper's iterated-amplification
target copy count. -/
noncomputable def gridFloor (ρ : ℝ) (k s p : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ (k : ℕ) * ((ρ - 1) / (ρ - 2)) ^ (s : ℕ) * (p : ℝ)⌋₊

private theorem dfamily_zero_of_empty_left {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (p : ℕ) (x y : ℝ) (hXempty : IsEmpty X) :
    Dfamily (interlaceFun f p) (bracketGE X Y p x y) = 0 := by
  classical
  apply Nat.le_zero.mp
  have hrowsEmpty : IsEmpty (Fin p × X) := by
    constructor
    rintro ⟨_, xx⟩
    exact hXempty.false xx
  unfold Dfamily
  by_cases hne : (bracketGE X Y p x y).Nonempty
  · obtain ⟨RC, hRC⟩ := hne
    apply Nat.sInf_le
    refine ⟨RC, hRC, ?_⟩
    symm
    have hsub : IsEmpty {a // a ∈ RC.1} :=
      Subtype.isEmpty_of_false (fun a => (hrowsEmpty.false a).elim)
    exact D_zero_of_empty _ (Or.inl hsub)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [show {d : ℕ | ∃ RC ∈ bracketGE X Y p x y,
        d = D (subgame (interlaceFun f p) RC.1 RC.2)} = ∅ from ?_]
    · exact le_of_eq Nat.sInf_empty
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro d ⟨RC, hRC, _⟩
      rw [hne] at hRC
      exact hRC

-- CLAIM-BEGIN lem:new-partition
/-- Paper `lem:new-partition` (Iterated density amplification, App. A): for
`2 < ρ`, `β = (ρ−1)/(ρ−2)`, `0 ≤ s ≤ k`, `p ≥ 1`, `0 < x ≤ 2^{−k}`,
`0 < y ≤ 1`, if `comp⟨f,p,x,y/4⟩ ≥ 1` and `(ρ−1)^k ≤ ρ^{k−s}` then both the
bundled (Λ) and scalar forms of
`Λ_f(⌊2^k β^s p⌋, 2^k x, y^{ρ^s}) ≥ k + Λ_f(p,x,y)` hold. Exponents `ρ^s`,
`(ρ−1)^k`, `ρ^{k−s}` are real powers with ℕ exponents (`k−s` is
ℕ-subtraction under `s ≤ k`); `y ^ (ρ^s)` is rpow. -/
theorem iterated_density_amplification {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {ρ : ℝ} (hρ : 2 < ρ) (k s p : ℕ) (hs : s ≤ k)
    (hp : 1 ≤ p) {x y : ℝ} (hx0 : 0 < x) (hxk : x ≤ (2 : ℝ) ^ (-(k : ℝ)))
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (h1 : 1 ≤ Dfamily (interlaceFun f p) (bracketGE X Y p x (y / 4)))
    (hside : (ρ - 1) ^ k ≤ ρ ^ (k - s)) :
    k + LambdaGE f p x y ≤
        LambdaGE f (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x) (y ^ (ρ ^ s)) ∧
    k + LambdaGE f p x y ≤
        Dfamily (interlaceFun f (gridFloor ρ k s p))
          (bracketGE X Y (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x)
            (y ^ (ρ ^ s))) :=
-- CLAIM-END lem:new-partition
  by
  classical
  have hρpos : 0 < ρ := by linarith
  have hx1 : x ≤ 1 := by
    calc
      x ≤ (2 : ℝ) ^ (-(k : ℝ)) := hxk
      _ ≤ (2 : ℝ) ^ (0 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
        linarith
      _ = 1 := by norm_num
  have hy4_0 : 0 < y / 4 := by positivity
  have hy4_1 : y / 4 ≤ 1 := by linarith
  rcases Nat.eq_zero_or_pos (Fintype.card X) with hcX0 | hcXpos
  · exfalso
    have hXempty : IsEmpty X := Fintype.card_eq_zero_iff.mp hcX0
    have hzero : Dfamily (interlaceFun f p) (bracketGE X Y p x (y / 4)) = 0 :=
      dfamily_zero_of_empty_left f p x (y / 4) hXempty
    rw [hzero] at h1
    omega
  have hX : 1 ≤ Fintype.card X := hcXpos
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with hcY0 | _hcYpos
  · exfalso
    have hp_pos : 0 < p := by omega
    have hzero : Dfamily (interlaceFun f p) (bracketGE X Y p x (y / 4)) = 0 :=
      Dfamily_zero_degenerate f hx1 hy4_1 hX (Or.inr ⟨hp_pos, hcY0⟩)
    rw [hzero] at h1
    omega
  set eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm with heXdef
  set eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm with heYdef
  set M : BoolMat := ⟨Fintype.card X, Fintype.card Y, fun i j => f (eX i) (eY j)⟩ with hMdef
  have he : ∀ i j, M.e i j = f (eX i) (eY j) := fun i j => rfl
  have hxT0 : 0 < (2 : ℝ) ^ (k : ℕ) * x := by positivity
  have hxT1 : (2 : ℝ) ^ (k : ℕ) * x ≤ 1 := by
    calc
      (2 : ℝ) ^ (k : ℕ) * x
          ≤ (2 : ℝ) ^ (k : ℕ) * (2 : ℝ) ^ (-(k : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hxk (by positivity)
      _ = 1 := by
        rw [show (2 : ℝ) ^ (k : ℕ) = (2 : ℝ) ^ (k : ℝ) by
          rw [Real.rpow_natCast]]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hyT0 : 0 < y ^ (ρ ^ s) := Real.rpow_pos_of_pos hy0 _
  have hyT1 : y ^ (ρ ^ s) ≤ 1 := by
    exact Real.rpow_le_one (le_of_lt hy0) hy1 (pow_nonneg (le_of_lt hρpos) s)
  have hTseed : Dfamily (interlaceFun f p) (bracketGE X Y p x (y / 4))
      = DSet (bracket M p x (y / 4)) :=
    Dfamily_eq_DSet f M eX eY he hx0 hx1 hy4_0 hy4_1 hX
  have hseedM : DSet (bracket M p x (y / 4)) ≥ 1 := by
    rw [ge_iff_le, ← hTseed]
    exact h1
  have hxkR : x ≤ Real.rpow 2 (-(k : ℝ)) := by
    simpa using hxk
  have hrung :
      Real.rpow (ρ - 1) (k : ℝ) ≤ Real.rpow ρ ((k : ℝ) - (s : ℝ)) := by
    have hks : ((k - s : ℕ) : ℝ) = (k : ℝ) - (s : ℝ) := by
      rw [Nat.cast_sub hs]
    have hleft : Real.rpow (ρ - 1) (k : ℝ) = (ρ - 1) ^ k := by
      change (ρ - 1) ^ (k : ℝ) = (ρ - 1) ^ k
      exact Real.rpow_natCast (ρ - 1) k
    have hright : ρ ^ (k - s) = Real.rpow ρ ((k : ℝ) - (s : ℝ)) := by
      rw [← hks]
      change ρ ^ (k - s) = ρ ^ ((k - s : ℕ) : ℝ)
      exact (Real.rpow_natCast ρ (k - s)).symm
    calc
      Real.rpow (ρ - 1) (k : ℝ) = (ρ - 1) ^ k := hleft
      _ ≤ ρ ^ (k - s) := hside
      _ = Real.rpow ρ ((k : ℝ) - (s : ℝ)) := hright
  have hArt := Workspace.Induction.lemma_4_8_iterated_partition
    ρ hρ ((ρ - 1) / (ρ - 2)) rfl M s k hs p hp x y hx0 hxkR hy0 hy1 hseedM hrung
  have hArt' :
      k + Lambda M p x y ≤
          Lambda M (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x) (y ^ (ρ ^ s)) ∧
      k + Lambda M p x y ≤
          DSet (bracket M (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x)
            (y ^ (ρ ^ s))) := by
    simpa [gridFloor, Real.rpow_natCast, ge_iff_le] using hArt
  have hLamIn : LambdaGE f p x y = Lambda M p x y :=
    LambdaGE_eq_Lambda f M eX eY he hx0 hx1 hy0 hy1 hX
  have hLamOut : LambdaGE f (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x)
      (y ^ (ρ ^ s))
      = Lambda M (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x) (y ^ (ρ ^ s)) :=
    LambdaGE_eq_Lambda f M eX eY he hxT0 hxT1 hyT0 hyT1 hX
  have hDOut : Dfamily (interlaceFun f (gridFloor ρ k s p))
      (bracketGE X Y (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x) (y ^ (ρ ^ s)))
      = DSet (bracket M (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x)
          (y ^ (ρ ^ s))) :=
    Dfamily_eq_DSet f M eX eY he hxT0 hxT1 hyT0 hyT1 hX
  rw [hLamIn, hLamOut, hDOut]
  exact hArt'

-- CLAIM-BEGIN cor:iterated-partition-seed
/-- Paper `cor:iterated-partition-seed`: under the hypotheses of
`lem:new-partition`, three-rung seed bounds at a real level `H`
(`comp(y) ≥ H`, `comp(y/2) ≥ H−1`, `comp(y/4) ≥ H−2`) give the scalar
conclusion `comp⟨f, ⌊2^k β^s p⌋, 2^k x, y^{ρ^s}⟩ ≥ k + H`. -/
theorem iterated_partition_seed {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {ρ : ℝ} (hρ : 2 < ρ) (k s p : ℕ) (hs : s ≤ k)
    (hp : 1 ≤ p) {x y : ℝ} (hx0 : 0 < x) (hxk : x ≤ (2 : ℝ) ^ (-(k : ℝ)))
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (h1 : 1 ≤ Dfamily (interlaceFun f p) (bracketGE X Y p x (y / 4)))
    (hside : (ρ - 1) ^ k ≤ ρ ^ (k - s)) {H : ℝ}
    (hH1 : H ≤ (Dfamily (interlaceFun f p) (bracketGE X Y p x y) : ℝ))
    (hH2 : H - 1 ≤
      (Dfamily (interlaceFun f p) (bracketGE X Y p x (y / 2)) : ℝ))
    (hH4 : H - 2 ≤
      (Dfamily (interlaceFun f p) (bracketGE X Y p x (y / 4)) : ℝ)) :
    (k : ℝ) + H ≤
      (Dfamily (interlaceFun f (gridFloor ρ k s p))
        (bracketGE X Y (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x)
          (y ^ (ρ ^ s))) : ℝ) :=
-- CLAIM-END cor:iterated-partition-seed
  by
  classical
  have hgrid :=
    iterated_density_amplification f hρ k s p hs hp hx0 hxk hy0 hy1 h1 hside
  have hΛseed : H ≤ (LambdaGE f p x y : ℝ) := by
    unfold LambdaGE
    push_cast [Nat.cast_min]
    refine le_min hH1 (le_min ?_ ?_)
    · linarith
    · linarith
  have hgridR :
      ((k + LambdaGE f p x y : ℕ) : ℝ) ≤
        (Dfamily (interlaceFun f (gridFloor ρ k s p))
          (bracketGE X Y (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x)
            (y ^ (ρ ^ s))) : ℝ) := by
    exact_mod_cast hgrid.2
  have hkΛ :
      (k : ℝ) + (LambdaGE f p x y : ℝ) ≤
        (Dfamily (interlaceFun f (gridFloor ρ k s p))
          (bracketGE X Y (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x)
            (y ^ (ρ ^ s))) : ℝ) := by
    simpa [Nat.cast_add] using hgridR
  linarith

-- CLAIM-BEGIN cor:power-of-two
/-- Paper `cor:power-of-two` (Power-of-two lower bound): for `(δ,b)`-robust
`f` with `1 ≤ b`, `D f ≥ 2` (F1 guard) and `y₀ = (1/2+δ)²`: every power of
two `u = 2^w` with `2 ≤ u ≤ 2^b` (rendered by the exponent: `1 ≤ w`,
`w ≤ b`) satisfies `comp⟨f, 2^w, 2^w·2^{−b}, y₀⟩ ≥ D f + w` (the paper's
`comp M + log u`). -/
theorem power_of_two_lower {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) (hb : 1 ≤ b) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hD : 2 ≤ D f) (w : ℕ) (hw1 : 1 ≤ w) (hwb : (w : ℝ) ≤ b) :
    D f + w ≤ Dfamily (interlaceFun f (2 ^ w))
      (bracketGE X Y (2 ^ w)
        ((2 : ℝ) ^ (w : ℕ) * (2 : ℝ) ^ (-b)) ((1 / 2 + δ) ^ 2)) :=
-- CLAIM-END cor:power-of-two
  by
  classical
  set x0 : ℝ := (2 : ℝ) ^ (1 - b) with hx0def
  set y0 : ℝ := (1 / 2 + δ) ^ 2 with hy0def
  set H : ℝ := (D f : ℝ) + 1 with hHdef
  have hrob := robust_two_copy_ladder h hb hδ0 hδ hD
  have hx0pos : 0 < x0 := by
    rw [hx0def]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hxk : x0 ≤ (2 : ℝ) ^ (-((w - 1 : ℕ) : ℝ)) := by
    rw [hx0def]
    rw [Nat.cast_sub hw1]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hexp : 1 - b ≤ -((w : ℝ) - 1) := by linarith
    simpa using hexp
  have hybase0 : 0 < 1 / 2 + δ := by linarith
  have hybase1 : 1 / 2 + δ ≤ 1 := by linarith
  have hy0pos : 0 < y0 := by
    rw [hy0def]
    positivity
  have hy0le1 : y0 ≤ 1 := by
    rw [hy0def]
    nlinarith [sq_nonneg (1 / 2 + δ), hybase0, hybase1]
  have hH1 : H ≤
      (Dfamily (interlaceFun f 2) (bracketGE X Y 2 x0 y0) : ℝ) := by
    rw [hHdef, hx0def, hy0def]
    exact hrob.2.2
  have hH2 : H - 1 ≤
      (Dfamily (interlaceFun f 2) (bracketGE X Y 2 x0 (y0 / 2)) : ℝ) := by
    rw [hHdef, hx0def, hy0def]
    simpa using hrob.2.1
  have hH4 : H - 2 ≤
      (Dfamily (interlaceFun f 2) (bracketGE X Y 2 x0 (y0 / 4)) : ℝ) := by
    rw [hHdef, hx0def, hy0def]
    linarith [hrob.1]
  have h1real :
      (1 : ℝ) ≤ (Dfamily (interlaceFun f 2) (bracketGE X Y 2 x0 (y0 / 4)) : ℝ) := by
    rw [hx0def, hy0def]
    have hDreal : (1 : ℝ) ≤ (D f : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (D f : ℝ) := by exact_mod_cast hD
      linarith
    linarith [hrob.1, hDreal]
  have h1 : 1 ≤ Dfamily (interlaceFun f 2) (bracketGE X Y 2 x0 (y0 / 4)) := by
    exact_mod_cast h1real
  have hside : ((3 : ℝ) - 1) ^ (w - 1) ≤ (3 : ℝ) ^ ((w - 1) - 0) := by
    norm_num
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 3) (w - 1)
  have hseed := iterated_partition_seed (f := f) (ρ := (3 : ℝ)) (by norm_num)
    (w - 1) 0 2 (by omega) (by norm_num) hx0pos hxk hy0pos hy0le1 h1 hside
    (H := H) hH1 hH2 hH4
  have hgrid : gridFloor (3 : ℝ) (w - 1) 0 2 = 2 ^ w := by
    unfold gridFloor
    have hmul : (2 : ℝ) ^ (w - 1) * 2 = (2 : ℝ) ^ w := by
      calc
        (2 : ℝ) ^ (w - 1) * 2 = (2 : ℝ) ^ ((w - 1) + 1) := by
          rw [pow_succ]
        _ = (2 : ℝ) ^ w := by
          rw [Nat.sub_add_cancel hw1]
    rw [show (((3 : ℝ) - 1) / ((3 : ℝ) - 2)) ^ (0 : ℕ) = 1 by norm_num]
    rw [mul_one]
    change ⌊(2 : ℝ) ^ (w - 1) * 2⌋₊ = 2 ^ w
    rw [hmul]
    have hcast : (2 : ℝ) ^ w = ((2 ^ w : ℕ) : ℝ) := by
      norm_num
    rw [hcast, Nat.floor_natCast]
  have hrow : (2 : ℝ) ^ (w - 1 : ℕ) * x0 =
      (2 : ℝ) ^ (w : ℕ) * (2 : ℝ) ^ (-b) := by
    rw [hx0def]
    rw [show (2 : ℝ) ^ (w - 1 : ℕ) = (2 : ℝ) ^ ((w - 1 : ℕ) : ℝ) by
      rw [Real.rpow_natCast]]
    rw [show (2 : ℝ) ^ (w : ℕ) = (2 : ℝ) ^ (w : ℝ) by
      rw [Real.rpow_natCast]]
    rw [Nat.cast_sub hw1]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hcol : y0 ^ ((3 : ℝ) ^ (0 : ℕ)) = y0 := by
    rw [pow_zero, Real.rpow_one]
  rw [hgrid, hrow, hcol] at hseed
  have hreal :
      ((D f + w : ℕ) : ℝ) ≤
        (Dfamily (interlaceFun f (2 ^ w))
          (bracketGE X Y (2 ^ w)
            ((2 : ℝ) ^ (w : ℕ) * (2 : ℝ) ^ (-b)) ((1 / 2 + δ) ^ 2)) : ℝ) := by
    rw [hy0def] at hseed
    have hleft :
        ((w - 1 : ℕ) : ℝ) + H = (D f : ℝ) + (w : ℝ) := by
      rw [hHdef, Nat.cast_sub hw1]
      ring
    have hcast : ((D f + w : ℕ) : ℝ) = (D f : ℝ) + (w : ℝ) := by
      norm_num
    rw [hcast]
    linarith
  exact_mod_cast hreal

private theorem dfamily_monotonicity_GE {X Y : Type u} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {p' p : ℕ} {x' x y' y : ℝ}
    (hp' : 1 ≤ p') (hpp : p' ≤ p)
    (hx'0 : 0 < x') (hx'x : x' ≤ x) (hx1 : x ≤ 1)
    (hy'0 : 0 < y') (hy'y : y' ≤ y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) :
    Dfamily (interlaceFun f p') (bracketGE X Y p' x' y') ≤
      Dfamily (interlaceFun f p) (bracketGE X Y p x y) := by
  classical
  set eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm with heXdef
  set eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm with heYdef
  set M : BoolMat := ⟨Fintype.card X, Fintype.card Y, fun i j => f (eX i) (eY j)⟩
    with hMdef
  have he : ∀ i j, M.e i j = f (eX i) (eY j) := fun i j => rfl
  have hT' : Dfamily (interlaceFun f p') (bracketGE X Y p' x' y')
      = DSet (bracket M p' x' y') :=
    Dfamily_eq_DSet f M eX eY he hx'0 (le_trans hx'x hx1) hy'0 (le_trans hy'y hy1) hX
  have hT : Dfamily (interlaceFun f p) (bracketGE X Y p x y)
      = DSet (bracket M p x y) :=
    Dfamily_eq_DSet f M eX eY he (lt_of_lt_of_le hx'0 hx'x) hx1
      (lt_of_lt_of_le hy'0 hy'y) hy1 hX
  rw [hT', hT]
  exact monotonicity M p' p x' x y' y hp' hpp hx'0 hx'x hx1 hy'0 hy'y hy1

private noncomputable def hardSeedDepth (m : ℕ) : ℕ :=
  ⌊Real.log 2 * Real.sqrt (m : ℝ) / Real.log (m : ℝ)⌋₊

private theorem hard_seed_side_from_log {ρ : ℝ} {k s : ℕ}
    (hρ2 : 2 < ρ) (hs : s ≤ k)
    (hlog : (s : ℝ) * ρ * Real.log ρ ≤ (k : ℝ)) :
    (ρ - 1) ^ k ≤ ρ ^ (k - s) := by
  have hρpos : 0 < ρ := by linarith
  have hρone : 1 < ρ := by linarith
  have hρm1pos : 0 < ρ - 1 := by linarith
  have hρm2pos : 0 < ρ - 2 := by linarith
  have hunitpos : 0 < 1 - 1 / ρ := by
    rw [sub_pos]
    exact (div_lt_one hρpos).mpr hρone
  have hfactor : ρ - 1 = ρ * (1 - 1 / ρ) := by
    field_simp [ne_of_gt hρpos]
  have hlog_factor : Real.log (ρ - 1) = Real.log ρ + Real.log (1 - 1 / ρ) := by
    rw [hfactor]
    exact Real.log_mul (ne_of_gt hρpos) (ne_of_gt hunitpos)
  have hlog_unit_le : Real.log (1 - 1 / ρ) ≤ -1 / ρ := by
    have h := Real.log_le_sub_one_of_pos hunitpos
    have hsimp : 1 - 1 / ρ - 1 = -1 / ρ := by ring
    rwa [hsimp] at h
  have hlog_m1_le : Real.log (ρ - 1) ≤ Real.log ρ - 1 / ρ := by
    calc
      Real.log (ρ - 1) = Real.log ρ + Real.log (1 - 1 / ρ) := hlog_factor
      _ ≤ Real.log ρ + (-1 / ρ) := add_le_add_right hlog_unit_le _
      _ = Real.log ρ - 1 / ρ := by ring
  have hslog_le : (s : ℝ) * Real.log ρ ≤ (k : ℝ) / ρ := by
    rw [le_div_iff₀ hρpos]
    nlinarith [hlog]
  have hmain :
      (k : ℝ) * Real.log (ρ - 1) ≤ ((k : ℝ) - (s : ℝ)) * Real.log ρ := by
    have hmul := mul_le_mul_of_nonneg_left hlog_m1_le (by positivity : 0 ≤ (k : ℝ))
    nlinarith [hmul, hslog_le]
  change (ρ - 1) ^ (k : ℕ) ≤ ρ ^ (k - s)
  rw [← Real.rpow_natCast, ← Real.rpow_natCast]
  rw [Nat.cast_sub hs]
  rw [Real.rpow_le_iff_le_log hρm1pos (Real.rpow_pos_of_pos hρpos ((k : ℝ) - (s : ℝ)))]
  rw [Real.log_rpow hρpos]
  exact hmain

private theorem gridFloor_le_mul_of_beta {ρ : ℝ} {k s p q : ℕ}
    (hβ : ((ρ - 1) / (ρ - 2)) ^ s * (p : ℝ) ≤ (q : ℝ)) :
    gridFloor ρ k s p ≤ q * 2 ^ k := by
  unfold gridFloor
  apply Nat.floor_le_of_le
  calc
    (2 : ℝ) ^ (k : ℕ) * ((ρ - 1) / (ρ - 2)) ^ (s : ℕ) * (p : ℝ)
        ≤ (2 : ℝ) ^ (k : ℕ) * (q : ℝ) := by
          have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (k : ℕ) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hβ hpow_nonneg]
    _ = ((q * 2 ^ k : ℕ) : ℝ) := by
          norm_num [Nat.cast_pow]
          ring

private theorem hard_seed_beta_bound {ρ L : ℝ} {s p q : ℕ}
    (hρ4 : 4 ≤ ρ) (hLpos : 0 < L)
    (hsA : (s : ℝ) ≤ Real.log 2 * ρ / L)
    (hp0 : 0 < p) (hpq : p < q)
    (hLlarge : (2 * Real.log 2) / Real.log ((q : ℝ) / (p : ℝ)) ≤ L) :
    ((ρ - 1) / (ρ - 2)) ^ s * (p : ℝ) ≤ (q : ℝ) := by
  have hρpos : 0 < ρ := by linarith
  have hρm2pos : 0 < ρ - 2 := by linarith
  have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hp0
  have hqRpos : 0 < (q : ℝ) := by exact_mod_cast (Nat.lt_trans hp0 hpq)
  have hpqR : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hqdiv_gt1 : 1 < (q : ℝ) / (p : ℝ) := by
    rw [one_lt_div₀ hpRpos]
    simpa using hpqR
  have hlogqp_pos : 0 < Real.log ((q : ℝ) / (p : ℝ)) :=
    Real.log_pos hqdiv_gt1
  set β : ℝ := (ρ - 1) / (ρ - 2) with hβdef
  have hβpos : 0 < β := by
    rw [hβdef]
    exact div_pos (by linarith) hρm2pos
  have hβge1 : 1 ≤ β := by
    rw [hβdef]
    rw [le_div_iff₀ hρm2pos]
    linarith
  have hlogβ_nonneg : 0 ≤ Real.log β := Real.log_nonneg hβge1
  have hβeq : β = 1 + 1 / (ρ - 2) := by
    rw [hβdef]
    field_simp [ne_of_gt hρm2pos]
    ring
  have hlogβ_le : Real.log β ≤ 1 / (ρ - 2) := by
    rw [hβeq]
    have hpos : 0 < 1 + 1 / (ρ - 2) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    have hsimp : 1 + 1 / (ρ - 2) - 1 = 1 / (ρ - 2) := by ring
    rwa [hsimp] at h
  have hA_nonneg : 0 ≤ Real.log 2 * ρ / L := by positivity
  have hρ_ratio : ρ / (ρ - 2) ≤ 2 := by
    rw [div_le_iff₀ hρm2pos]
    linarith
  have hlogs_le : (s : ℝ) * Real.log β ≤ Real.log ((q : ℝ) / (p : ℝ)) := by
    have h1 : (s : ℝ) * Real.log β ≤ (Real.log 2 * ρ / L) * Real.log β :=
      mul_le_mul_of_nonneg_right hsA hlogβ_nonneg
    have h2 : (Real.log 2 * ρ / L) * Real.log β ≤
        (Real.log 2 * ρ / L) * (1 / (ρ - 2)) :=
      mul_le_mul_of_nonneg_left hlogβ_le hA_nonneg
    have h3 : (Real.log 2 * ρ / L) * (1 / (ρ - 2)) ≤
        (2 * Real.log 2) / L := by
      have hlog2_nonneg : 0 ≤ Real.log 2 := by positivity
      calc
        (Real.log 2 * ρ / L) * (1 / (ρ - 2))
            = (Real.log 2 / L) * (ρ / (ρ - 2)) := by ring
        _ ≤ (Real.log 2 / L) * 2 := by
          apply mul_le_mul_of_nonneg_left hρ_ratio
          positivity
        _ = (2 * Real.log 2) / L := by ring
    have h4 : (2 * Real.log 2) / L ≤ Real.log ((q : ℝ) / (p : ℝ)) := by
      have hlarge' : 2 * Real.log 2 ≤ L * Real.log ((q : ℝ) / (p : ℝ)) := by
        rwa [div_le_iff₀ hlogqp_pos] at hLlarge
      rw [div_le_iff₀ hLpos]
      nlinarith
    exact le_trans h1 (le_trans h2 (le_trans h3 h4))
  have hpow :
      β ^ (s : ℕ) ≤ (q : ℝ) / (p : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [Real.rpow_le_iff_le_log hβpos (div_pos hqRpos hpRpos)]
    simpa [Real.log_div (ne_of_gt hqRpos) (ne_of_gt hpRpos)] using hlogs_le
  have hmul := mul_le_mul_of_nonneg_right hpow (le_of_lt hpRpos)
  calc
    ((ρ - 1) / (ρ - 2)) ^ s * (p : ℝ)
        = β ^ s * (p : ℝ) := by rw [hβdef]
    _ ≤ ((q : ℝ) / (p : ℝ)) * (p : ℝ) := hmul
    _ = (q : ℝ) := by field_simp [ne_of_gt hpRpos]

private theorem hard_seed_column_bound {δ η ρ L : ℝ} {s : ℕ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2)
    (hηdef : η = -Real.logb 2 ((1 / 2 + δ) ^ 2))
    (hρ1 : 1 < ρ) (hLpos : 0 < L)
    (hs_floor : s = ⌊Real.log 2 * ρ / L⌋₊)
    (hlogρ : Real.log ρ = L / 2)
    (hsmall : ρ * (2 : ℝ) ^ (-(1 / 100 : ℝ) * ρ) ≤ η) :
    ((1 / 2 + δ) ^ 2) ^ (ρ ^ s) ≤
      (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * ρ))) := by
  have hybase0 : 0 < 1 / 2 + δ := by linarith
  have hybase1 : 1 / 2 + δ < 1 := by linarith
  set y0 : ℝ := (1 / 2 + δ) ^ 2 with hy0def
  have hy0pos : 0 < y0 := by
    rw [hy0def]
    positivity
  have hy0lt1 : y0 < 1 := by
    rw [hy0def]
    nlinarith [hybase0, hybase1]
  have hηpos : 0 < η := by
    rw [hηdef]
    have hloglt : Real.logb 2 y0 < Real.logb 2 1 :=
      Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hy0pos hy0lt1
    rw [Real.logb_one] at hloglt
    linarith
  have hA_nonneg : 0 ≤ Real.log 2 * ρ / L := by positivity
  have hs_lower : Real.log 2 * ρ / L - 1 ≤ (s : ℝ) := by
    rw [hs_floor]
    have hlt := Nat.lt_floor_add_one (Real.log 2 * ρ / L)
    linarith
  have hρpow_lower :
      (2 : ℝ) ^ ((1 / 2 : ℝ) * ρ) / ρ ≤ ρ ^ s := by
    have hρpos : 0 < ρ := by linarith
    have hρpowA : ρ ^ (Real.log 2 * ρ / L) = (2 : ℝ) ^ ((1 / 2 : ℝ) * ρ) := by
      rw [Real.rpow_def_of_pos hρpos, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [hlogρ]
      have hLne : L ≠ 0 := ne_of_gt hLpos
      field_simp [hLne]
    calc
      (2 : ℝ) ^ ((1 / 2 : ℝ) * ρ) / ρ
          = ρ ^ (Real.log 2 * ρ / L - 1) := by
            rw [Real.rpow_sub hρpos]
            rw [hρpowA, Real.rpow_one]
      _ ≤ ρ ^ (s : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (le_of_lt hρ1)
            exact hs_lower
      _ = ρ ^ s := by rw [Real.rpow_natCast]
  have htarget_exp : (2 : ℝ) ^ ((49 / 100 : ℝ) * ρ) ≤ η * ρ ^ s := by
    have hsmall' : ρ * (2 : ℝ) ^ ((49 / 100 : ℝ) * ρ) ≤
        η * (2 : ℝ) ^ ((1 / 2 : ℝ) * ρ) := by
      have hmul := mul_le_mul_of_nonneg_right hsmall
        (by positivity : 0 ≤ (2 : ℝ) ^ ((1 / 2 : ℝ) * ρ))
      calc
        ρ * (2 : ℝ) ^ ((49 / 100 : ℝ) * ρ)
            = (ρ * (2 : ℝ) ^ (-(1 / 100 : ℝ) * ρ)) *
                (2 : ℝ) ^ ((1 / 2 : ℝ) * ρ) := by
              rw [mul_assoc]
              congr 1
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
              congr 1
              ring
        _ ≤ η * (2 : ℝ) ^ ((1 / 2 : ℝ) * ρ) := hmul
    have hdiv : (2 : ℝ) ^ ((49 / 100 : ℝ) * ρ) ≤
        η * ((2 : ℝ) ^ ((1 / 2 : ℝ) * ρ) / ρ) := by
      rw [show η * ((2 : ℝ) ^ ((1 / 2 : ℝ) * ρ) / ρ) =
          (η * (2 : ℝ) ^ ((1 / 2 : ℝ) * ρ)) / ρ by ring]
      rw [le_div_iff₀ (by linarith : 0 < ρ)]
      convert hsmall' using 1
      ring
    exact le_trans hdiv (mul_le_mul_of_nonneg_left hρpow_lower (le_of_lt hηpos))
  have hy0_two : y0 = (2 : ℝ) ^ (-η) := by
    rw [hηdef]
    have hneg : -(-Real.logb 2 y0) = Real.logb 2 y0 := by ring
    rw [hneg]
    exact (Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1) hy0pos).symm
  rw [hy0_two]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  nlinarith [htarget_exp, hηpos, Real.rpow_pos_of_pos (by linarith : 0 < ρ) (s : ℝ)]

private theorem hard_seed_core.{u} (j : ℕ) (hj : 2 ≤ j) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) (m : ℕ)
    (hmj : j ≤ m)
    (hρ2 : 2 < Real.sqrt (m : ℝ))
    (hs_le : hardSeedDepth m ≤ m - j)
    (hside :
      (Real.sqrt (m : ℝ) - 1) ^ (m - j) ≤
        (Real.sqrt (m : ℝ)) ^ ((m - j) - hardSeedDepth m))
    (hgrid :
      gridFloor (Real.sqrt (m : ℝ)) (m - j) (hardSeedDepth m) (2 ^ (j - 1) + 1) ≤
        (2 ^ (j - 1) + 2) * 2 ^ (m - j))
    (hcol :
      ((1 / 2 + δ) ^ 2) ^ ((Real.sqrt (m : ℝ)) ^ hardSeedDepth m) ≤
        (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ))))) :
    ∀ (X Y : Type u) [Fintype X] [Fintype Y]
      (f : X → Y → Bool) (b : ℝ),
      IsRobust f δ b → 1 ≤ b → 3 ≤ D f → (m : ℝ) ≤ b →
      D f + m ≤ Dfamily (interlaceFun f ((2 ^ (j - 1) + 2) * 2 ^ (m - j)))
        (bracketGE X Y ((2 ^ (j - 1) + 2) * 2 ^ (m - j))
          ((2 : ℝ) ^ (m : ℕ) * (2 : ℝ) ^ (-b))
          ((2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℕ)))))) := by
  classical
  intro X Y _ _ f b hrob hb hD3 hmb
  have hδle : δ ≤ 1 / 2 := le_of_lt hδ
  have hD2 : 2 ≤ D f := by omega
  have hjb : (j : ℝ) ≤ b := by
    have : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmj
    linarith
  set p : ℕ := 2 ^ (j - 1) + 1 with hpdef
  set pT : ℕ := (2 ^ (j - 1) + 2) * 2 ^ (m - j) with hpTdef
  set k : ℕ := m - j with hkdef
  set s : ℕ := hardSeedDepth m with hsdef
  set ρ : ℝ := Real.sqrt (m : ℝ) with hρdef
  set x : ℝ := (2 : ℝ) ^ ((j : ℝ) - b) with hxdef
  set y0 : ℝ := (1 / 2 + δ) ^ 2 with hy0def
  set yT : ℝ := (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ)))) with hyTdef
  set H : ℝ := (D f : ℝ) + j with hHdef
  have hp1 : 1 ≤ p := by
    rw [hpdef]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hx0 : 0 < x := by
    rw [hxdef]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hxk : x ≤ (2 : ℝ) ^ (-(k : ℝ)) := by
    rw [hxdef, hkdef]
    rw [Nat.cast_sub hmj]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hybase0 : 0 < 1 / 2 + δ := by linarith
  have hybase1 : 1 / 2 + δ < 1 := by linarith
  have hy0pos : 0 < y0 := by
    rw [hy0def]
    positivity
  have hy0le1 : y0 ≤ 1 := by
    rw [hy0def]
    nlinarith [hybase0, hybase1.le]
  have hseed := odd_copy_seed_rungs hrob hb hδ0 hδle hD2 j hj hjb
  have hTopNat : D f + j ≤
      Dfamily (interlaceFun f p) (bracketGE X Y p x y0) := by
    rw [← hpdef, ← hxdef, ← hy0def] at hseed
    unfold LambdaGE at hseed
    exact le_trans hseed (min_le_left _ _)
  have hMidNat : D f + j ≤
      1 + Dfamily (interlaceFun f p) (bracketGE X Y p x (y0 / 2)) := by
    rw [← hpdef, ← hxdef, ← hy0def] at hseed
    unfold LambdaGE at hseed
    exact le_trans hseed (le_trans (min_le_right _ _) (min_le_left _ _))
  have hLowNat : D f + j ≤
      2 + Dfamily (interlaceFun f p) (bracketGE X Y p x (y0 / 4)) := by
    rw [← hpdef, ← hxdef, ← hy0def] at hseed
    unfold LambdaGE at hseed
    exact le_trans hseed (le_trans (min_le_right _ _) (min_le_right _ _))
  have hH1 : H ≤
      (Dfamily (interlaceFun f p) (bracketGE X Y p x y0) : ℝ) := by
    rw [hHdef]
    exact_mod_cast hTopNat
  have hH2 : H - 1 ≤
      (Dfamily (interlaceFun f p) (bracketGE X Y p x (y0 / 2)) : ℝ) := by
    rw [hHdef]
    have hreal : ((D f + j : ℕ) : ℝ) ≤
        (1 + Dfamily (interlaceFun f p) (bracketGE X Y p x (y0 / 2)) : ℕ) := by
      exact_mod_cast hMidNat
    push_cast at hreal
    linarith
  have hH4 : H - 2 ≤
      (Dfamily (interlaceFun f p) (bracketGE X Y p x (y0 / 4)) : ℝ) := by
    rw [hHdef]
    have hreal : ((D f + j : ℕ) : ℝ) ≤
        (2 + Dfamily (interlaceFun f p) (bracketGE X Y p x (y0 / 4)) : ℕ) := by
      exact_mod_cast hLowNat
    push_cast at hreal
    linarith
  have hOneReal : (1 : ℝ) ≤
      (Dfamily (interlaceFun f p) (bracketGE X Y p x (y0 / 4)) : ℝ) := by
    have hDreal : (3 : ℝ) ≤ (D f : ℝ) := by exact_mod_cast hD3
    have hjreal : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have hOne : 1 ≤ Dfamily (interlaceFun f p) (bracketGE X Y p x (y0 / 4)) := by
    exact_mod_cast hOneReal
  have hiter := iterated_partition_seed (f := f) (ρ := ρ) (by simpa [hρdef] using hρ2)
    k s p (by simpa [hkdef, hsdef] using hs_le) hp1 hx0 hxk hy0pos hy0le1 hOne
    (by simpa [hρdef, hkdef, hsdef] using hside) (H := H) hH1 hH2 hH4
  have hiterReal :
      ((D f + m : ℕ) : ℝ) ≤
        (Dfamily (interlaceFun f (gridFloor ρ k s p))
          (bracketGE X Y (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x)
            (y0 ^ (ρ ^ s))) : ℝ) := by
    have hleft : (k : ℝ) + H = (D f : ℝ) + (m : ℝ) := by
      rw [hkdef, hHdef, Nat.cast_sub hmj]
      ring
    have hcast : ((D f + m : ℕ) : ℝ) = (D f : ℝ) + (m : ℝ) := by norm_num
    rw [hcast]
    linarith
  have hrow_eq : (2 : ℝ) ^ (k : ℕ) * x =
      (2 : ℝ) ^ (m : ℕ) * (2 : ℝ) ^ (-b) := by
    rw [hxdef, hkdef]
    rw [show (2 : ℝ) ^ (m - j : ℕ) = (2 : ℝ) ^ ((m - j : ℕ) : ℝ) by
      rw [Real.rpow_natCast]]
    rw [show (2 : ℝ) ^ (m : ℕ) = (2 : ℝ) ^ (m : ℝ) by
      rw [Real.rpow_natCast]]
    rw [Nat.cast_sub hmj]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hrow_pos : 0 < (2 : ℝ) ^ (m : ℕ) * (2 : ℝ) ^ (-b) := by positivity
  have hrow_le1 : (2 : ℝ) ^ (m : ℕ) * (2 : ℝ) ^ (-b) ≤ 1 := by
    rw [show (2 : ℝ) ^ (m : ℕ) = (2 : ℝ) ^ (m : ℝ) by
      rw [Real.rpow_natCast]]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply rpow_two_le_one_of_nonpos
    linarith
  have hyTpos : 0 < yT := by
    rw [hyTdef]
    positivity
  have hyTle1 : yT ≤ 1 := by
    rw [hyTdef]
    apply rpow_two_le_one_of_nonpos
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ)) := by
      positivity
    linarith
  have hSourceColPos : 0 < y0 ^ (ρ ^ s) := by
    exact Real.rpow_pos_of_pos hy0pos _
  have hSourceColLe : y0 ^ (ρ ^ s) ≤ yT := by
    exact hcol
  have hX : 1 ≤ Fintype.card X := by
    rcases Nat.eq_zero_or_pos (Fintype.card X) with hX0 | hXpos
    · exfalso
      have hXempty : IsEmpty X := Fintype.card_eq_zero_iff.mp hX0
      have hzero : D f = 0 := NPCC.D_zero_of_empty f (Or.inl hXempty)
      rw [hzero] at hD3
      omega
    · exact hXpos
  have hgrid' : gridFloor ρ k s p ≤ pT := by
    rw [hρdef, hkdef, hsdef, hpdef, hpTdef]
    exact hgrid
  have hgridOne : 1 ≤ gridFloor ρ k s p := by
    have hposreal : (1 : ℝ) ≤
        (Dfamily (interlaceFun f (gridFloor ρ k s p))
          (bracketGE X Y (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x)
            (y0 ^ (ρ ^ s))) : ℝ) := by
      have hDm : (1 : ℝ) ≤ ((D f + m : ℕ) : ℝ) := by
        have hpos : 0 < D f + m := Nat.add_pos_left (by omega : 0 < D f) m
        exact_mod_cast Nat.succ_le_iff.mpr hpos
      exact le_trans hDm hiterReal
    by_contra hnot
    have hg0 : gridFloor ρ k s p = 0 := by omega
    have hzero : Dfamily (interlaceFun f (gridFloor ρ k s p))
          (bracketGE X Y (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x)
            (y0 ^ (ρ ^ s))) = 0 := by
      rw [hg0]
      apply Dfamily_zero_degenerate f
      · rw [hrow_eq]
        exact hrow_le1
      · exact le_trans hSourceColLe hyTle1
      · exact hX
      · exact Or.inl rfl
    rw [hzero] at hposreal
    norm_num at hposreal
  have hmono := dfamily_monotonicity_GE (f := f)
    (p' := gridFloor ρ k s p) (p := pT)
    (x' := (2 : ℝ) ^ (k : ℕ) * x)
    (x := (2 : ℝ) ^ (m : ℕ) * (2 : ℝ) ^ (-b))
    (y' := y0 ^ (ρ ^ s)) (y := yT)
    hgridOne hgrid'
    (by rw [hrow_eq]; exact hrow_pos)
    (by rw [hrow_eq])
    hrow_le1 hSourceColPos hSourceColLe hyTle1 hX
  have hmonoReal :
      (Dfamily (interlaceFun f (gridFloor ρ k s p))
          (bracketGE X Y (gridFloor ρ k s p) ((2 : ℝ) ^ (k : ℕ) * x)
            (y0 ^ (ρ ^ s))) : ℝ) ≤
        (Dfamily (interlaceFun f pT)
          (bracketGE X Y pT ((2 : ℝ) ^ (m : ℕ) * (2 : ℝ) ^ (-b)) yT) : ℝ) := by
    exact_mod_cast hmono
  have hfinalReal :
      ((D f + m : ℕ) : ℝ) ≤
        (Dfamily (interlaceFun f pT)
          (bracketGE X Y pT ((2 : ℝ) ^ (m : ℕ) * (2 : ℝ) ^ (-b)) yT) : ℝ) :=
    le_trans hiterReal hmonoReal
  rw [hpTdef, hyTdef] at hfinalReal
  exact_mod_cast hfinalReal

open Filter Topology in
private theorem hard_seed_side_conditions (j : ℕ) (_hj : 2 ≤ j) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    ∃ m₀ : ℕ, j ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      j ≤ m ∧
      2 < Real.sqrt (m : ℝ) ∧
      hardSeedDepth m ≤ m - j ∧
      (Real.sqrt (m : ℝ) - 1) ^ (m - j) ≤
        (Real.sqrt (m : ℝ)) ^ ((m - j) - hardSeedDepth m) ∧
      gridFloor (Real.sqrt (m : ℝ)) (m - j) (hardSeedDepth m) (2 ^ (j - 1) + 1) ≤
        (2 ^ (j - 1) + 2) * 2 ^ (m - j) ∧
      ((1 / 2 + δ) ^ 2) ^ ((Real.sqrt (m : ℝ)) ^ hardSeedDepth m) ≤
        (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ)))) := by
  classical
  set p : ℕ := 2 ^ (j - 1) + 1 with hpdef
  set q : ℕ := 2 ^ (j - 1) + 2 with hqdef
  set η : ℝ := -Real.logb 2 ((1 / 2 + δ) ^ 2) with hηdef
  have hp0 : 0 < p := by
    rw [hpdef]
    exact Nat.succ_pos _
  have hpq : p < q := by
    rw [hpdef, hqdef]
    omega
  have hybase0 : 0 < 1 / 2 + δ := by linarith
  have hybase1 : 1 / 2 + δ < 1 := by linarith
  have hy0pos : 0 < (1 / 2 + δ) ^ 2 := by positivity
  have hy0lt1 : (1 / 2 + δ) ^ 2 < 1 := by
    nlinarith [hybase0, hybase1]
  have hηpos : 0 < η := by
    rw [hηdef]
    have hloglt : Real.logb 2 ((1 / 2 + δ) ^ 2) < Real.logb 2 1 :=
      Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hy0pos hy0lt1
    rw [Real.logb_one] at hloglt
    linarith
  have hlogEvent :
      ∀ᶠ m : ℕ in atTop,
        (2 * Real.log 2) / Real.log ((q : ℝ) / (p : ℝ)) ≤ Real.log (m : ℝ) := by
    have hlogT : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact hlogT.eventually_ge_atTop _
  have hsmallEvent :
      ∀ᶠ m : ℕ in atTop,
        Real.sqrt (m : ℝ) * (2 : ℝ) ^ (-(1 / 100 : ℝ) * Real.sqrt (m : ℝ)) ≤ η := by
    have hbpos : 0 < Real.log 2 / 100 := by positivity
    have ht :
        Tendsto (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(Real.log 2 / 100) * x))
          atTop (𝓝 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (Real.log 2 / 100) hbpos
    have hsmallR :
        ∀ᶠ x : ℝ in atTop,
          x * (2 : ℝ) ^ (-(1 / 100 : ℝ) * x) ≤ η := by
      filter_upwards [ht.eventually (eventually_lt_nhds hηpos)] with x hx
      have hrewrite :
          x ^ (1 : ℝ) * Real.exp (-(Real.log 2 / 100) * x)
            = x * (2 : ℝ) ^ (-(1 / 100 : ℝ) * x) := by
        rw [Real.rpow_one]
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring_nf
      rw [← hrewrite]
      exact hx.le
    exact (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually hsmallR
  have hEvent :
      ∀ᶠ m : ℕ in atTop,
        j ≤ m ∧
        2 < Real.sqrt (m : ℝ) ∧
        hardSeedDepth m ≤ m - j ∧
        (Real.sqrt (m : ℝ) - 1) ^ (m - j) ≤
          (Real.sqrt (m : ℝ)) ^ ((m - j) - hardSeedDepth m) ∧
        gridFloor (Real.sqrt (m : ℝ)) (m - j) (hardSeedDepth m) (2 ^ (j - 1) + 1) ≤
          (2 ^ (j - 1) + 2) * 2 ^ (m - j) ∧
        ((1 / 2 + δ) ^ 2) ^ ((Real.sqrt (m : ℝ)) ^ hardSeedDepth m) ≤
          (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ)))) := by
    filter_upwards [eventually_ge_atTop (max 16 (2 * j)), hlogEvent, hsmallEvent]
      with m hmBase hlogLarge hsmall
    have hm16 : 16 ≤ m := le_trans (Nat.le_max_left _ _) hmBase
    have hm2j : 2 * j ≤ m := le_trans (Nat.le_max_right _ _) hmBase
    have hmj : j ≤ m := by omega
    set ρ : ℝ := Real.sqrt (m : ℝ) with hρdef
    set L : ℝ := Real.log (m : ℝ) with hLdef
    set s : ℕ := hardSeedDepth m with hsdef
    set k : ℕ := m - j with hkdef
    have hmR_nonneg : 0 ≤ (m : ℝ) := by positivity
    have hmR16 : (16 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm16
    have hmR4 : (4 : ℝ) ≤ (m : ℝ) := by linarith
    have hρ4 : 4 ≤ ρ := by
      rw [hρdef]
      have hsqrt16 : Real.sqrt (16 : ℝ) ≤ Real.sqrt (m : ℝ) :=
        Real.sqrt_le_sqrt hmR16
      rwa [show Real.sqrt (16 : ℝ) = 4 by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hsqrt16
    have hρ2 : 2 < ρ := by linarith
    have hρ1 : 1 < ρ := by linarith
    have hρpos : 0 < ρ := by linarith
    have hm_gt1 : (1 : ℝ) < (m : ℝ) := by
      exact_mod_cast (by omega : 1 < m)
    have hLpos : 0 < L := by
      rw [hLdef]
      exact Real.log_pos hm_gt1
    have hlogρ : Real.log ρ = L / 2 := by
      rw [hρdef, hLdef]
      exact Real.log_sqrt hmR_nonneg
    have hA_nonneg : 0 ≤ Real.log 2 * ρ / L := by positivity
    have hsA : (s : ℝ) ≤ Real.log 2 * ρ / L := by
      rw [hsdef, hardSeedDepth, hρdef, hLdef]
      exact Nat.floor_le hA_nonneg
    have hlog2_le_logm : Real.log 2 ≤ L := by
      rw [hLdef]
      have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 ≤ m)
      exact Real.log_le_log (by norm_num : (0 : ℝ) < 2) hm2
    have hA_le_ρ : Real.log 2 * ρ / L ≤ ρ := by
      have hdiv : Real.log 2 / L ≤ 1 := (div_le_one hLpos).mpr hlog2_le_logm
      have hρnonneg : 0 ≤ ρ := le_of_lt hρpos
      calc
        Real.log 2 * ρ / L = (Real.log 2 / L) * ρ := by ring
        _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hdiv hρnonneg
        _ = ρ := by ring
    have hρ_le_half : ρ ≤ (m : ℝ) / 2 := by
      rw [hρdef, Real.sqrt_le_iff]
      constructor
      · positivity
      · nlinarith [hmR4]
    have hhalf_le_k : (m : ℝ) / 2 ≤ (k : ℝ) := by
      rw [hkdef, Nat.cast_sub hmj]
      have hm2jR : (2 * j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2j
      nlinarith
    have hs_le : s ≤ k := by
      have hs_real : (s : ℝ) ≤ (k : ℝ) :=
        le_trans hsA (le_trans hA_le_ρ (le_trans hρ_le_half hhalf_le_k))
      exact_mod_cast hs_real
    have hlogSide : (s : ℝ) * ρ * Real.log ρ ≤ (k : ℝ) := by
      have hlogρ_nonneg : 0 ≤ Real.log ρ := (Real.log_pos hρ1).le
      have hcoeff_nonneg : 0 ≤ ρ * Real.log ρ := mul_nonneg (le_of_lt hρpos) hlogρ_nonneg
      have h1 : (s : ℝ) * (ρ * Real.log ρ) ≤
          (Real.log 2 * ρ / L) * (ρ * Real.log ρ) :=
        mul_le_mul_of_nonneg_right hsA hcoeff_nonneg
      have hcalc : (Real.log 2 * ρ / L) * (ρ * Real.log ρ) =
          (Real.log 2 / 2) * (m : ℝ) := by
        rw [hlogρ]
        have hLne : L ≠ 0 := ne_of_gt hLpos
        have hρsq : ρ ^ 2 = (m : ℝ) := by
          rw [hρdef]
          exact Real.sq_sqrt hmR_nonneg
        field_simp [hLne]
        nlinarith [hρsq]
      have hlog2_le_one : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h
        exact h
      have h2 : (Real.log 2 / 2) * (m : ℝ) ≤ (m : ℝ) / 2 := by
        nlinarith [hlog2_le_one, hmR_nonneg]
      calc
        (s : ℝ) * ρ * Real.log ρ = (s : ℝ) * (ρ * Real.log ρ) := by ring
        _ ≤ (Real.log 2 * ρ / L) * (ρ * Real.log ρ) := h1
        _ = (Real.log 2 / 2) * (m : ℝ) := hcalc
        _ ≤ (m : ℝ) / 2 := h2
        _ ≤ (k : ℝ) := hhalf_le_k
    have hside : (ρ - 1) ^ k ≤ ρ ^ (k - s) :=
      hard_seed_side_from_log hρ2 hs_le hlogSide
    have hβ : ((ρ - 1) / (ρ - 2)) ^ s * (p : ℝ) ≤ (q : ℝ) :=
      hard_seed_beta_bound hρ4 hLpos hsA hp0 hpq (by simpa [hLdef] using hlogLarge)
    have hgrid' : gridFloor ρ k s p ≤ q * 2 ^ k :=
      gridFloor_le_mul_of_beta hβ
    have hcol' : ((1 / 2 + δ) ^ 2) ^ (ρ ^ s) ≤
        (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * ρ))) :=
      hard_seed_column_bound hδ0 hδ hηdef hρ1 hLpos hsdef hlogρ
        (by simpa [hρdef] using hsmall)
    refine ⟨hmj, by simpa [hρdef] using hρ2, ?_, ?_, ?_, ?_⟩
    · simpa [hkdef, hsdef] using hs_le
    · simpa [hρdef, hkdef, hsdef] using hside
    · simpa [hρdef, hkdef, hsdef, hpdef, hqdef] using hgrid'
    · simpa [hρdef, hsdef] using hcol'
  rw [eventually_atTop] at hEvent
  obtain ⟨m₁, hm₁⟩ := hEvent
  refine ⟨max j m₁, Nat.le_max_left _ _, ?_⟩
  intro m hm
  exact hm₁ m (le_trans (Nat.le_max_right _ _) hm)

-- CLAIM-BEGIN lem:hard-seed
/-- Paper `lem:hard-seed`, REFORMULATED per finding F2 (PAPER-FINDINGS.md):
fix `j ≥ 2` AND the robustness margin `δ` (paper's OPEN bound `0 < δ < 1/2`);
the threshold `m₀ = m₀(j, δ)` is then uniform in the GAME and in `b` (both
quantified inside — `b` grows with the downstream instance, while `δ` is a
fixed constant of the reduction's construction). The original rendering
hoisted `δ` inside the threshold and is unprovable: as `δ → 1/2⁻` the
required density-amplification depth diverges (`log₂(1/η)` with
`η = −2·log₂(1/2+δ)`) while the copy-count budget caps the grid depth at
`O(√m)` — a two-sided squeeze, machine-confirmed by two independent
re-derivations. Content otherwise unchanged: `t = 2^m` (`log = log₂`), copy
count `(2^(j−1)+2)·2^(m−j)` = `((2^(j−1)+2)t)/2^j`, row density
`2^m·2^{−b} = t·2^{−b}`, column density `2^{−2^{(49/100)·√m}}`, conclusion
`D f + m = comp M + log t`, hypotheses `D f ≥ 3` (paper), `t ≤ 2^b`. -/
theorem hard_seed.{u} (j : ℕ) (hj : 2 ≤ j) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ < 1 / 2) :
    ∃ m₀ : ℕ, j ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ (X Y : Type u) [Fintype X] [Fintype Y]
        (f : X → Y → Bool) (b : ℝ),
        IsRobust f δ b → 1 ≤ b → 3 ≤ D f → (m : ℝ) ≤ b →
        D f + m ≤ Dfamily (interlaceFun f ((2 ^ (j - 1) + 2) * 2 ^ (m - j)))
          (bracketGE X Y ((2 ^ (j - 1) + 2) * 2 ^ (m - j))
            ((2 : ℝ) ^ (m : ℕ) * (2 : ℝ) ^ (-b))
            ((2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℕ)))))) :=
-- CLAIM-END lem:hard-seed
  by
    obtain ⟨m₀, hjm₀, hcond⟩ := hard_seed_side_conditions j hj δ hδ0 hδ
    refine ⟨m₀, hjm₀, ?_⟩
    intro m hm X Y _ _ f b hrob hb1 hDf hb
    obtain ⟨hmj, hρ2, hs_le, hside, hgrid, hcol⟩ := hcond m hm
    exact hard_seed_core j hj δ hδ0 hδ m hmj hρ2 hs_le hside hgrid hcol
      X Y f b hrob hb1 hDf hb

end NPCC
