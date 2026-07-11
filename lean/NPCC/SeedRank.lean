import Mathlib
import NPCC.Complexity
import NPCC.DefsAux
import Workspace.Types.Interlace
import Workspace.LogRankBound

/-! # Seed rank claim (paper lem:rankclaim = M&S Lemma 2.5), typed form. -/

namespace NPCC

/-- The seed matrix `M₀ = [1 0]` as a game: one row, two columns, value `true`
exactly at column `0`. -/
def seedGame : Fin 1 → Fin 2 → Bool := fun _ j => j == 0

open Workspace.Types.CommComplexity
open Workspace.Types.BoolMat
open Workspace.Types.MatComplexity
open Workspace.LogRankBound
open Workspace.Types.Protocol
open Workspace.Types.Interlace

/-! ## Helpers for `lem:rankclaim` (above the frozen claim block). -/

/-- The entrywise Boolean complement of a two-party function. -/
def notFun {A B : Type*} (f : A → B → Bool) : A → B → Bool := fun a b => !(f a b)

/-- **Two-sided (pair) protocol rank bound.** The real ranks of the matrices of
the function computed by `P` and of its complement sum to at most `2 ^ P.cost`.
This is the leaf-counting sharpening of `protocol_rank_bound`: it carries both
the function and its complement through the same tree induction. -/
lemma protocol_rank_pair_bound {m n : ℕ} (P : Protocol (Fin m) (Fin n) Bool) :
    (matRf (Protocol.eval P)).rank + (matRf (notFun (Protocol.eval P))).rank
      ≤ 2 ^ P.cost := by
  induction P with
  | leaf z =>
      have hcost : (2 : ℕ) ^ (Protocol.leaf z : Protocol (Fin m) (Fin n) Bool).cost = 1 := by
        simp [Protocol.cost]
      rw [hcost]
      -- `eval = const z`, complement `= const !z`; one is the zero matrix.
      have heval : Protocol.eval (Protocol.leaf z : Protocol (Fin m) (Fin n) Bool)
          = fun (_ : Fin m) (_ : Fin n) => z := rfl
      cases z with
      | false =>
          have hL : matRf (Protocol.eval (Protocol.leaf false : Protocol (Fin m) (Fin n) Bool))
              = 0 := by
            ext i j; simp [matRf, heval]
          have hR : matRf (notFun (Protocol.eval
              (Protocol.leaf false : Protocol (Fin m) (Fin n) Bool)))
              = matRf (fun (_ : Fin m) (_ : Fin n) => true) := by
            funext i j; simp [matRf, notFun, heval]
          rw [hL, hR, Matrix.rank_zero, Nat.zero_add]
          exact rank_const_le_one true
      | true =>
          have hR : matRf (notFun (Protocol.eval
              (Protocol.leaf true : Protocol (Fin m) (Fin n) Bool))) = 0 := by
            ext i j; simp [matRf, notFun, heval]
          have hL : matRf (Protocol.eval (Protocol.leaf true : Protocol (Fin m) (Fin n) Bool))
              = matRf (fun (_ : Fin m) (_ : Fin n) => true) := by
            funext i j; simp [matRf, heval]
          rw [hR, hL, Matrix.rank_zero, Nat.add_zero]
          exact rank_const_le_one true
  | aNode a l r ihl ihr =>
      set D0 : Matrix (Fin m) (Fin m) ℝ :=
        Matrix.diagonal (fun i => if a i then (0 : ℝ) else 1) with hD0
      set D1 : Matrix (Fin m) (Fin m) ℝ :=
        Matrix.diagonal (fun i => if a i then (1 : ℝ) else 0) with hD1
      -- Row decomposition of both the matrix and its complement.
      have hdecomp : matRf (Protocol.eval (Protocol.aNode a l r))
          = D0 * matRf (Protocol.eval l) + D1 * matRf (Protocol.eval r) := by
        rw [hD0, hD1]
        ext i j
        simp only [matRf, Matrix.of_apply, Matrix.add_apply, Matrix.diagonal_mul]
        by_cases hai : a i
        · simp [Protocol.eval, hai]
        · simp [Protocol.eval, hai]
      have hdecompC : matRf (notFun (Protocol.eval (Protocol.aNode a l r)))
          = D0 * matRf (notFun (Protocol.eval l)) + D1 * matRf (notFun (Protocol.eval r)) := by
        rw [hD0, hD1]
        ext i j
        simp only [matRf, notFun, Matrix.of_apply, Matrix.add_apply, Matrix.diagonal_mul]
        by_cases hai : a i
        · simp [Protocol.eval, hai]
        · simp [Protocol.eval, hai]
      have hstep : (matRf (Protocol.eval (Protocol.aNode a l r))).rank
          ≤ (matRf (Protocol.eval l)).rank + (matRf (Protocol.eval r)).rank := by
        rw [hdecomp]
        calc (D0 * matRf (Protocol.eval l) + D1 * matRf (Protocol.eval r)).rank
            ≤ (D0 * matRf (Protocol.eval l)).rank + (D1 * matRf (Protocol.eval r)).rank :=
              rank_add_le _ _
          _ ≤ (matRf (Protocol.eval l)).rank + (matRf (Protocol.eval r)).rank :=
              Nat.add_le_add (Matrix.rank_mul_le_right _ _) (Matrix.rank_mul_le_right _ _)
      have hstepC : (matRf (notFun (Protocol.eval (Protocol.aNode a l r)))).rank
          ≤ (matRf (notFun (Protocol.eval l))).rank + (matRf (notFun (Protocol.eval r))).rank := by
        rw [hdecompC]
        calc (D0 * matRf (notFun (Protocol.eval l)) + D1 * matRf (notFun (Protocol.eval r))).rank
            ≤ (D0 * matRf (notFun (Protocol.eval l))).rank
                + (D1 * matRf (notFun (Protocol.eval r))).rank := rank_add_le _ _
          _ ≤ (matRf (notFun (Protocol.eval l))).rank
                + (matRf (notFun (Protocol.eval r))).rank :=
              Nat.add_le_add (Matrix.rank_mul_le_right _ _) (Matrix.rank_mul_le_right _ _)
      have hcost : (Protocol.aNode a l r).cost = 1 + max l.cost r.cost := rfl
      have hbl : (2 : ℕ) ^ l.cost ≤ 2 ^ (max l.cost r.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hbr : (2 : ℕ) ^ r.cost ≤ 2 ^ (max l.cost r.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      calc (matRf (Protocol.eval (Protocol.aNode a l r))).rank
              + (matRf (notFun (Protocol.eval (Protocol.aNode a l r)))).rank
          ≤ ((matRf (Protocol.eval l)).rank + (matRf (Protocol.eval r)).rank)
              + ((matRf (notFun (Protocol.eval l))).rank
                  + (matRf (notFun (Protocol.eval r))).rank) :=
            Nat.add_le_add hstep hstepC
        _ = ((matRf (Protocol.eval l)).rank + (matRf (notFun (Protocol.eval l))).rank)
              + ((matRf (Protocol.eval r)).rank + (matRf (notFun (Protocol.eval r))).rank) := by
            ring
        _ ≤ 2 ^ l.cost + 2 ^ r.cost := Nat.add_le_add ihl ihr
        _ ≤ 2 ^ (max l.cost r.cost) + 2 ^ (max l.cost r.cost) := Nat.add_le_add hbl hbr
        _ = 2 ^ (1 + max l.cost r.cost) := by ring
        _ = 2 ^ (Protocol.aNode a l r).cost := by rw [hcost]
  | bNode b l r ihl ihr =>
      set E0 : Matrix (Fin n) (Fin n) ℝ :=
        Matrix.diagonal (fun j => if b j then (0 : ℝ) else 1) with hE0
      set E1 : Matrix (Fin n) (Fin n) ℝ :=
        Matrix.diagonal (fun j => if b j then (1 : ℝ) else 0) with hE1
      have hdecomp : matRf (Protocol.eval (Protocol.bNode b l r))
          = matRf (Protocol.eval l) * E0 + matRf (Protocol.eval r) * E1 := by
        rw [hE0, hE1]
        ext i j
        simp only [matRf, Matrix.of_apply, Matrix.add_apply, Matrix.mul_diagonal]
        by_cases hbj : b j
        · simp [Protocol.eval, hbj]
        · simp [Protocol.eval, hbj]
      have hdecompC : matRf (notFun (Protocol.eval (Protocol.bNode b l r)))
          = matRf (notFun (Protocol.eval l)) * E0 + matRf (notFun (Protocol.eval r)) * E1 := by
        rw [hE0, hE1]
        ext i j
        simp only [matRf, notFun, Matrix.of_apply, Matrix.add_apply, Matrix.mul_diagonal]
        by_cases hbj : b j
        · simp [Protocol.eval, hbj]
        · simp [Protocol.eval, hbj]
      have hstep : (matRf (Protocol.eval (Protocol.bNode b l r))).rank
          ≤ (matRf (Protocol.eval l)).rank + (matRf (Protocol.eval r)).rank := by
        rw [hdecomp]
        calc (matRf (Protocol.eval l) * E0 + matRf (Protocol.eval r) * E1).rank
            ≤ (matRf (Protocol.eval l) * E0).rank + (matRf (Protocol.eval r) * E1).rank :=
              rank_add_le _ _
          _ ≤ (matRf (Protocol.eval l)).rank + (matRf (Protocol.eval r)).rank :=
              Nat.add_le_add (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_left _ _)
      have hstepC : (matRf (notFun (Protocol.eval (Protocol.bNode b l r)))).rank
          ≤ (matRf (notFun (Protocol.eval l))).rank + (matRf (notFun (Protocol.eval r))).rank := by
        rw [hdecompC]
        calc (matRf (notFun (Protocol.eval l)) * E0 + matRf (notFun (Protocol.eval r)) * E1).rank
            ≤ (matRf (notFun (Protocol.eval l)) * E0).rank
                + (matRf (notFun (Protocol.eval r)) * E1).rank := rank_add_le _ _
          _ ≤ (matRf (notFun (Protocol.eval l))).rank
                + (matRf (notFun (Protocol.eval r))).rank :=
              Nat.add_le_add (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_left _ _)
      have hcost : (Protocol.bNode b l r).cost = 1 + max l.cost r.cost := rfl
      have hbl : (2 : ℕ) ^ l.cost ≤ 2 ^ (max l.cost r.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hbr : (2 : ℕ) ^ r.cost ≤ 2 ^ (max l.cost r.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      calc (matRf (Protocol.eval (Protocol.bNode b l r))).rank
              + (matRf (notFun (Protocol.eval (Protocol.bNode b l r)))).rank
          ≤ ((matRf (Protocol.eval l)).rank + (matRf (Protocol.eval r)).rank)
              + ((matRf (notFun (Protocol.eval l))).rank
                  + (matRf (notFun (Protocol.eval r))).rank) :=
            Nat.add_le_add hstep hstepC
        _ = ((matRf (Protocol.eval l)).rank + (matRf (notFun (Protocol.eval l))).rank)
              + ((matRf (Protocol.eval r)).rank + (matRf (notFun (Protocol.eval r))).rank) := by
            ring
        _ ≤ 2 ^ l.cost + 2 ^ r.cost := Nat.add_le_add ihl ihr
        _ ≤ 2 ^ (max l.cost r.cost) + 2 ^ (max l.cost r.cost) := Nat.add_le_add hbl hbr
        _ = 2 ^ (1 + max l.cost r.cost) := by ring
        _ = 2 ^ (Protocol.bNode b l r).cost := by rw [hcost]

/-- The complement `BoolMat` of `M`: same dimensions, entrywise negated. -/
def boolMatCompl (M : BoolMat) : BoolMat where
  m := M.m
  n := M.n
  e := fun i j => !(M.e i j)

@[simp] lemma boolMatCompl_m (M : BoolMat) : (boolMatCompl M).m = M.m := rfl
@[simp] lemma boolMatCompl_n (M : BoolMat) : (boolMatCompl M).n = M.n := rfl

/-- **Pair rank bound at the matrix level.** For any `BoolMat M`,
`boolRank M + boolRank (boolMatCompl M) ≤ 2 ^ (Dmat M)`. -/
lemma boolRank_pair_le (M : BoolMat) :
    boolRank M + boolRank (boolMatCompl M) ≤ 2 ^ (Dmat M) := by
  have hne : (AchievableCosts M.e).Nonempty := achievableCosts_nonempty M
  have hmem : Dmat M ∈ AchievableCosts M.e := by
    have : sInf (AchievableCosts M.e) ∈ AchievableCosts M.e := Nat.sInf_mem hne
    simpa [Dmat, D] using this
  obtain ⟨P, hcost, hcomp⟩ := hmem
  have hPeval : Protocol.eval P = M.e := by funext x y; exact hcomp x y
  have hpair := protocol_rank_pair_bound P
  rw [hcost] at hpair
  have h1 : (matRf (Protocol.eval P)).rank = boolRank M := by
    rw [hPeval]; rfl
  have h2 : (matRf (notFun (Protocol.eval P))).rank = boolRank (boolMatCompl M) := by
    have : notFun (Protocol.eval P) = (boolMatCompl M).e := by
      funext i j; simp [notFun, hPeval, boolMatCompl]
    rw [this]; rfl
  rw [h1, h2] at hpair
  exact hpair

/-- The seed subgame value at a row `(q, 0)` and column `c`: `seedGame` reads off
whether `c q = 0`. -/
lemma interlace_seed_row0 (p : ℕ) (q : Fin p) (c : Fin p → Fin 2) :
    interlaceFun seedGame p (q, (0 : Fin 1)) c = (c q == 0) := by
  simp [interlaceFun, seedGame]

end NPCC

namespace NPCC

open Workspace.Types.CommComplexity
open Workspace.Types.BoolMat
open Workspace.Types.MatComplexity
open Workspace.LogRankBound
open Workspace.Types.Interlace

-- CLAIM-BEGIN lem:rankclaim
/-- Paper `lem:rankclaim` (imported there as M&S Lemma 2.5): for the seed
`M₀ = [1 0]`, any positive `p` and reals `0 < x, y ≤ 1` with `p + log₂ y > 0`,
the bracket-family complexity satisfies
`comp⟨M₀,p,x,y⟩ ≥ ⌈log₂(p + log₂ y)⌉ + 1`.

Typed rendering over the complexity layer: the ambient game is the `p`-fold
`interlaceFun` of `seedGame`; the family is `bracketGE (Fin 1) (Fin 2) p x y`;
`comp{·}` is `Dfamily`. Logs are base 2 (`Real.logb 2`), the outer ceiling is
the integer ceiling `⌈·⌉ : ℝ → ℤ` (its argument may be negative, whence the
`ℤ`-valued comparison with the cast of `Dfamily`). RESCOPED from
`port:rankclaim`: the artifact holds the generic engine
(`logRank_lowerBound`, `distinctCols_card_le_two_pow_rank`,
`protocol_rank_bound`) but not this bracket-form seed bound. -/
theorem rankclaim {p : ℕ} (_hp : 0 < p) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlog : 0 < (p : ℝ) + Real.logb 2 y) :
    (⌈Real.logb 2 ((p : ℝ) + Real.logb 2 y)⌉ + 1 : ℤ) ≤
      (Dfamily (Workspace.Types.Interlace.interlaceFun seedGame p)
        (bracketGE (Fin 1) (Fin 2) p x y) : ℤ) :=
-- CLAIM-END lem:rankclaim
  by
  classical
  set f := Workspace.Types.Interlace.interlaceFun seedGame p with hf
  set t : ℝ := (p : ℝ) + Real.logb 2 y with ht
  -- ### Step 1: the cost set is nonempty, so `Dfamily` is attained at a member.
  have hXcard : 1 ≤ Fintype.card (Fin 1) := by simp
  have hbne : (bracketGE (Fin 1) (Fin 2) p x y).Nonempty :=
    bracketGE.nonempty p x y hx1 hy1 hXcard
  set S : Set ℕ := { d : ℕ | ∃ RC ∈ bracketGE (Fin 1) (Fin 2) p x y,
      d = D (subgame f RC.1 RC.2) } with hS
  have hSne : S.Nonempty := by
    obtain ⟨RC, hRC⟩ := hbne
    exact ⟨D (subgame f RC.1 RC.2), RC, hRC, rfl⟩
  have hmem : Dfamily f (bracketGE (Fin 1) (Fin 2) p x y) ∈ S := by
    have : sInf S ∈ S := Nat.sInf_mem hSne
    simpa [Dfamily, hS] using this
  obtain ⟨RC, hRCmem, hRCeq⟩ := hmem
  obtain ⟨R, C⟩ := RC
  obtain ⟨hRow, hCol⟩ := hRCmem
  -- `Dfamily = D (subgame f R C)`.
  -- ### Step 2: row structure — every `(q, 0)` is in `R`.
  have hceil1 : (⌈(Fintype.card (Fin 1) : ℝ) * x⌉₊ : ℕ) = 1 := by
    have hx : (Fintype.card (Fin 1) : ℝ) * x = x := by simp
    rw [hx]
    have : ⌈x⌉₊ = 1 := by
      have h1 : ⌈x⌉₊ ≤ 1 := by
        rw [Nat.ceil_le]; exact_mod_cast hx1
      have h2 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx0
      omega
    exact this
  have hrowIn : ∀ q : Fin p, ((q, (0 : Fin 1)) ∈ R) := by
    intro q
    have hfib : 1 ≤ (R.filter (fun pr => pr.1 = q)).card := by
      have := hRow q (Finset.mem_univ q)
      rw [hceil1] at this
      exact this
    -- a nonempty fiber over `q` contains a pair, whose second coord is `0`.
    obtain ⟨pr, hpr⟩ := Finset.card_pos.mp (by omega : 0 < (R.filter (fun pr => pr.1 = q)).card)
    rw [Finset.mem_filter] at hpr
    obtain ⟨hprR, hpr1⟩ := hpr
    have : pr = (q, (0 : Fin 1)) := by
      apply Prod.ext
      · exact hpr1
      · exact Subsingleton.elim _ _
    rw [← this]; exact hprR
  -- ### Step 3/4: build the BoolMat `M` from the subgame via `equivFin`.
  set eR : {a // a ∈ R} ≃ Fin (Fintype.card {a // a ∈ R}) := Fintype.equivFin _ with heR
  set eC : {c // c ∈ C} ≃ Fin (Fintype.card {c // c ∈ C}) := Fintype.equivFin _ with heC
  set M : BoolMat :=
    { m := Fintype.card {a // a ∈ R}
      n := Fintype.card {c // c ∈ C}
      e := fun i j => subgame f R C (eR.symm i) (eC.symm j) } with hM
  -- `Dmat M = D (subgame f R C)` via D-invariance.
  have hDmat : Dmat M = D (subgame f R C) := by
    have := NPCC.D_equiv_invariance (subgame f R C) eR.symm eC.symm
    simpa [Dmat, hM] using this
  -- ### Column injectivity of `M` (and hence of its complement).
  have hcolinj : Function.Injective
      (fun (j : Fin M.n) => (fun i : Fin M.m => M.e i j)) := by
    intro j1 j2 hj
    by_contra hne
    -- underlying columns `c1 ≠ c2` in `C`.
    set c1 := (eC.symm j1).val with hc1
    set c2 := (eC.symm j2).val with hc2
    have hc12 : c1 ≠ c2 := by
      intro h
      apply hne
      have : eC.symm j1 = eC.symm j2 := Subtype.ext h
      exact eC.symm.injective this
    -- they differ at some coordinate `q`.
    obtain ⟨q, hq⟩ : ∃ q : Fin p, c1 q ≠ c2 q := by
      by_contra h
      push Not at h
      exact hc12 (funext h)
    -- pick the row for `(q, 0)`.
    have hrowmem : ((q, (0 : Fin 1)) : Fin p × Fin 1) ∈ R := hrowIn q
    set arow : {a // a ∈ R} := ⟨(q, (0 : Fin 1)), hrowmem⟩ with harow
    set i0 : Fin M.m := eR arow with hi0
    have hival : eR.symm i0 = arow := by rw [hi0]; exact eR.symm_apply_apply arow
    -- evaluate both columns at that row.
    have hcol : M.e i0 j1 = M.e i0 j2 := by
      have := congrFun hj i0
      simpa using this
    have hval1 : M.e i0 j1 = (c1 q == 0) := by
      show subgame f R C (eR.symm i0) (eC.symm j1) = _
      rw [hival]
      show f (arow.val) (eC.symm j1).val = _
      rw [harow, hf, ← hc1, interlace_seed_row0]
    have hval2 : M.e i0 j2 = (c2 q == 0) := by
      show subgame f R C (eR.symm i0) (eC.symm j2) = _
      rw [hival]
      show f (arow.val) (eC.symm j2).val = _
      rw [harow, hf, ← hc2, interlace_seed_row0]
    rw [hval1, hval2] at hcol
    -- over `Fin 2`, `c1 q ≠ c2 q` flips `(· == 0)`.
    apply hq
    -- from `(c1 q == 0) = (c2 q == 0)` conclude `c1 q = c2 q`.
    revert hcol
    generalize c1 q = v1
    generalize c2 q = v2
    revert v1 v2
    decide
  -- complement has the same columns' injectivity.
  have hcolinjC : Function.Injective
      (fun (j : Fin (boolMatCompl M).n) => (fun i : Fin (boolMatCompl M).m => (boolMatCompl M).e i j)) := by
    intro j1 j2 hj
    apply hcolinj
    funext i
    have := congrFun hj i
    simp only [boolMatCompl] at this
    have hbool : M.e i j1 = M.e i j2 := by
      by_cases h : M.e i j1 <;> simp_all
    exact hbool
  -- ### Step 5: distinct-column counts bound the ranks.
  have hMn_le_M : M.n ≤ 2 ^ boolRank M :=
    distinctCols_card_le_two_pow_rank M hcolinj
  have hMn_le_Mc : (boolMatCompl M).n ≤ 2 ^ boolRank (boolMatCompl M) :=
    distinctCols_card_le_two_pow_rank (boolMatCompl M) hcolinjC
  -- `M.n = C.card ≥ ⌈2^p y⌉₊`.
  have hMn_card : M.n = C.card := by rw [hM]; exact Fintype.card_coe C
  have hcolthresh : ⌈((Fintype.card (Fin 2) : ℝ) ^ p) * y⌉₊ ≤ C.card := hCol
  have hcard2 : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
  -- real lower bound on `M.n`.
  have hMn_ge : (2 : ℝ) ^ p * y ≤ (M.n : ℝ) := by
    rw [hMn_card]
    calc (2 : ℝ) ^ p * y
        ≤ (⌈((Fintype.card (Fin 2) : ℝ) ^ p) * y⌉₊ : ℝ) := by
          rw [hcard2]; exact Nat.le_ceil _
      _ ≤ (C.card : ℝ) := by exact_mod_cast hcolthresh
  -- ### `t ≤ boolRank M` and `t ≤ boolRank (compl)`.
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ p * y := by positivity
  have hlogb_eq : Real.logb 2 ((2 : ℝ) ^ p * y) = t := by
    rw [Real.logb_mul (by positivity) (ne_of_gt hy0)]
    rw [Real.logb_pow]
    rw [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
    rw [ht]; ring
  have hboundRank : ∀ (r : ℕ), (2 : ℝ) ^ p * y ≤ (2 : ℝ) ^ r → t ≤ (r : ℝ) := by
    intro r hr
    have hmono : Real.logb 2 ((2 : ℝ) ^ p * y) ≤ Real.logb 2 ((2 : ℝ) ^ r) :=
      Real.logb_le_logb_of_le (by norm_num) hpowpos hr
    rw [hlogb_eq] at hmono
    have hrhs : Real.logb 2 ((2 : ℝ) ^ r) = (r : ℝ) := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]; ring
    rw [hrhs] at hmono
    exact hmono
  have htM : t ≤ (boolRank M : ℝ) := by
    apply hboundRank
    calc (2 : ℝ) ^ p * y ≤ (M.n : ℝ) := hMn_ge
      _ ≤ ((2 ^ boolRank M : ℕ) : ℝ) := by exact_mod_cast hMn_le_M
      _ = (2 : ℝ) ^ boolRank M := by push_cast; ring
  have htMc : t ≤ (boolRank (boolMatCompl M) : ℝ) := by
    apply hboundRank
    calc (2 : ℝ) ^ p * y ≤ (M.n : ℝ) := hMn_ge
      _ = ((boolMatCompl M).n : ℝ) := by rw [boolMatCompl_n]
      _ ≤ ((2 ^ boolRank (boolMatCompl M) : ℕ) : ℝ) := by exact_mod_cast hMn_le_Mc
      _ = (2 : ℝ) ^ boolRank (boolMatCompl M) := by push_cast; ring
  -- ### Step 6: pair bound `2t ≤ 2^(Dmat M)`.
  have hpair : boolRank M + boolRank (boolMatCompl M) ≤ 2 ^ (Dmat M) :=
    boolRank_pair_le M
  have h2t : 2 * t ≤ (2 : ℝ) ^ (Dmat M) := by
    calc 2 * t = t + t := by ring
      _ ≤ (boolRank M : ℝ) + (boolRank (boolMatCompl M) : ℝ) := add_le_add htM htMc
      _ = ((boolRank M + boolRank (boolMatCompl M) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ (Dmat M) : ℕ) : ℝ) := by exact_mod_cast hpair
      _ = (2 : ℝ) ^ (Dmat M) := by push_cast; ring
  -- ### Final: `log₂ t + 1 ≤ Dmat M`, then ceiling.
  have h2tpos : (0 : ℝ) < 2 * t := by linarith [hlog]
  have hlogfinal : Real.logb 2 t + 1 ≤ (Dmat M : ℝ) := by
    have hstep : Real.logb 2 (2 * t) ≤ Real.logb 2 ((2 : ℝ) ^ (Dmat M)) :=
      Real.logb_le_logb_of_le (by norm_num) h2tpos h2t
    have hlhs : Real.logb 2 (2 * t) = Real.logb 2 t + 1 := by
      rw [Real.logb_mul (by norm_num) (ne_of_gt hlog)]
      rw [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]; ring
    have hrhs : Real.logb 2 ((2 : ℝ) ^ (Dmat M)) = (Dmat M : ℝ) := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]; ring
    rw [hlhs, hrhs] at hstep
    exact hstep
  -- Convert to the integer ceiling goal.
  have hceilgoal : (⌈Real.logb 2 t⌉ + 1 : ℤ) ≤ (Dmat M : ℤ) := by
    have : (⌈Real.logb 2 t + 1⌉ : ℤ) ≤ (Dmat M : ℤ) := by
      rw [Int.ceil_le]; exact_mod_cast hlogfinal
    rwa [Int.ceil_add_one] at this
  -- Assemble: goal target uses `Dfamily`, equal to `D (subgame ...) = Dmat M`.
  have hDfam : (Dfamily f (bracketGE (Fin 1) (Fin 2) p x y) : ℤ) = (Dmat M : ℤ) := by
    rw [hDmat]
    exact_mod_cast hRCeq
  rw [hDfam]
  exact hceilgoal

-- CLAIM-BEGIN port:rankclaim
/-- Source-port check for paper `lem:rankclaim`: the NPCC-facing typed
statement is already supplied by `rankclaim`. This wrapper keeps the original
port obligation visible without changing the proved theorem's frozen claim
block. -/
theorem rankclaim_port {p : ℕ} (hp : 0 < p) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlog : 0 < (p : ℝ) + Real.logb 2 y) :
    (⌈Real.logb 2 ((p : ℝ) + Real.logb 2 y)⌉ + 1 : ℤ) ≤
      (Dfamily (Workspace.Types.Interlace.interlaceFun seedGame p)
        (bracketGE (Fin 1) (Fin 2) p x y) : ℤ) :=
-- CLAIM-END port:rankclaim
  by
  exact rankclaim hp hx0 hx1 hy0 hy1 hlog

end NPCC
