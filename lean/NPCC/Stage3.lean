import NPCC.Stage2
import NPCC.Gadget
import NPCC.NoWaste

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
Stage-3 separation layer.

This module keeps the Stage-3 support surface local and derives the separated
protocol-control conclusion from `classical_separation`. Arithmetic and exact-
complexity requirements are exposed as named gates so later stages cannot use
them implicitly.
-/

namespace NPCC

open Finset
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace

noncomputable def M3_rowLoss (d : Nat) : Nat :=
  Nat.ceil ((2 : Real) ^ (1 - (Params.b2 d : Real)) *
    (Fintype.card (C2 d) : Real))

noncomputable def M2_colLoss (d : Nat) : Nat :=
  Nat.ceil ((2 : Real) ^ (1 - (Params.b1 d : Real)) *
    (Fintype.card (C1 d) : Real))

def M3_diagCol (d : Nat) (alpha : Fin (Params.q2 d)) (gamma : C1 d) : C3 d :=
  fun _ => (alpha, gamma)

structure M3SeparationConclusion
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool) : Prop where
  first_row_bits :
    Protocol.FirstKRowBitsOn
      (Finset.univ : Finset (R3 d))
      (Finset.univ : Finset (C3 d)) 2 P
  dominant_bins :
    NoWasteConclusion
      (Finset.univ : Finset (Fin 4))
      (Finset.univ : Finset (Fin 4 × C2 d))
      (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
      (Fintype.card (C2 d))
      (M3_rowLoss d)
  complexity :
    D (M3 d) = D (M2 d) + 2

structure M3FuzzyLeavesData
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool) where
  separation : M3SeparationConclusion d P
  binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2
  dimBranch :
    Fin 4 -> Fin (Params.q2 d) ->
      Protocol.BranchAt P (M3 d) (2 + Nat.clog 2 (Params.q2 d))
  bin_sideTrace :
    forall p,
      (binBranch p).sideTrace =
        [Protocol.ActualBitSide.alice, Protocol.ActualBitSide.alice]
  dim_sideTrace :
    forall p alpha,
      (dimBranch p alpha).sideTrace =
        (binBranch p).sideTrace ++
          List.replicate (Nat.clog 2 (Params.q2 d))
            Protocol.ActualBitSide.bob
  dim_extends :
    forall p alpha, Protocol.BranchExtends (binBranch p) (dimBranch p alpha)
  S : Fin 4 -> Finset (C2 d)
  Y : Fin 4 -> Fin (Params.q2 d) -> Finset (C1 d)
  cRep : Fin 4 -> Fin (Params.q2 d) -> R1 d -> C2 d
  bin_rows :
    forall p c, c ∈ S p -> (p, c) ∈ (binBranch p).rows
  S_dense_raw :
    forall p,
      (Fintype.card (C2 d) : Real) - 3 * (M3_rowLoss d : Real)
        <= ((S p).card : Real)
  S_dense :
    forall p,
      (1 - 8 * Params.h2 d) * (Fintype.card (C2 d) : Real)
        <= ((S p).card : Real)
  Y_dense :
    forall p alpha,
      (1 - Params.eta2 d) * (Fintype.card (C1 d) : Real)
        <= ((Y p alpha).card : Real)
  diag_cols :
    forall p alpha gamma,
      gamma ∈ Y p alpha ->
        M3_diagCol d alpha gamma ∈ (dimBranch p alpha).cols
  fiber_cover :
    forall p alpha,
      (S p).image (fun c : C2 d => S2fam d c alpha)
        = (Finset.univ : Finset (R1 d))
  cRep_mem :
    forall p alpha r, cRep p alpha r ∈ S p
  cRep_eval :
    forall p alpha r, S2fam d (cRep p alpha r) alpha = r
  exact_M1_copy :
    forall p alpha r gamma,
      gamma ∈ Y p alpha ->
        M3 d (p, cRep p alpha r) (M3_diagCol d alpha gamma) = M1 d r gamma

def M3FuzzyLeavesConclusion
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool) : Prop :=
  Nonempty (M3FuzzyLeavesData d P)

namespace Protocol

variable {A B Z : Type*} [DecidableEq A] [DecidableEq B]

private lemma image_val_filter_eq
    {R : Finset A} (R0 : Finset {a // a ∈ R}) (p : A -> Bool) (v : Bool) :
    (R0.filter fun a => p a.val = v).image (fun a => a.val) =
      (R0.image fun a => a.val).filter fun a => p a = v := by
  classical
  ext a
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, hx'.1, rfl⟩, hx'.2⟩
  · intro ha
    rcases Finset.mem_filter.mp ha with ⟨him, hp⟩
    rcases Finset.mem_image.mp him with ⟨x, hx, hxa⟩
    subst hxa
    exact Finset.mem_image.mpr
      ⟨x, Finset.mem_filter.mpr ⟨hx, hp⟩, rfl⟩

theorem firstKRowBitsOn_of_restrictSub
    (R : Finset A) (C : Finset B)
    (R0 : Finset {a // a ∈ R}) (C0 : Finset {b // b ∈ C})
    (k : Nat) (P : Protocol A B Z)
    (hrow : Protocol.FirstKRowBitsOn R0 C0 k (Protocol.restrictSub R C P)) :
    Protocol.FirstKRowBitsOn
      (R0.image fun a => a.val) (C0.image fun b => b.val) k P := by
  classical
  induction k generalizing R C R0 C0 P with
  | zero =>
      trivial
  | succ k ih =>
      cases P with
      | leaf z =>
          simp only [Protocol.restrictSub, Protocol.FirstKRowBitsOn] at hrow ⊢
          rcases hrow with hR | hC
          · left
            rw [hR]
            simp
          · right
            rw [hC]
            simp
      | bNode q l r =>
          simp only [Protocol.restrictSub, Protocol.FirstKRowBitsOn] at hrow ⊢
          rcases hrow with hR | hC
          · left
            rw [hR]
            simp
          · right
            rw [hC]
            simp
      | aNode q l r =>
          simp only [Protocol.restrictSub, Protocol.FirstKRowBitsOn] at hrow ⊢
          refine ⟨?_, ?_⟩
          · have hl :=
              ih R C (R0.filter fun a => q a.val = false) C0 l hrow.1
            simpa [image_val_filter_eq (R := R) R0 q false] using hl
          · have hr :=
              ih R C (R0.filter fun a => q a.val = true) C0 r hrow.2
            simpa [image_val_filter_eq (R := R) R0 q true] using hr

@[simp] theorem prefixCodeRaw_restrictSub
    (R : Finset A) (C : Finset B) (k : Nat)
    (P : Protocol A B Z) (a : {a // a ∈ R}) :
    Protocol.prefixCodeRaw k (Protocol.restrictSub R C P) a =
      Protocol.prefixCodeRaw k P a.val := by
  induction k generalizing P with
  | zero =>
      rfl
  | succ k ih =>
      cases P with
      | leaf z => rfl
      | bNode q l r => rfl
      | aNode q l r =>
          simp only [Protocol.restrictSub, Protocol.prefixCodeRaw]
          by_cases hq : q a.val
          · rw [if_pos hq, if_pos hq, ih]
          · rw [if_neg hq, if_neg hq, ih]

end Protocol

private theorem image_univ_subtype_val_eq_univ
    {A : Type*} [Fintype A] [DecidableEq A] (R : Finset A) :
    ((Finset.univ : Finset {a // a ∈ R}).image fun a => a.val) = R := by
  classical
  ext a
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨x, _hx, hxa⟩
    subst hxa
    exact x.2
  · intro ha
    exact Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩

private theorem stage3_noWaste_transport
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hnow :
      NoWasteConclusion
        (Finset.univ : Finset (Fin (2 ^ 2)))
        (Finset.univ : Finset (Fin (2 ^ 2) × C2 d))
        (Protocol.prefixLabelFinQ
          (Finset.univ : Finset (Fin (2 ^ 2) × C2 d))
          (Protocol.restrictSub
            (Finset.univ : Finset (Fin (2 ^ 2) × C2 d))
            (Finset.univ : Finset (Fin (2 ^ 2) -> R2 d)) P))
        (Fintype.card (C2 d))
        (M3_rowLoss d)) :
      NoWasteConclusion
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        (Fintype.card (C2 d))
        (M3_rowLoss d) := by
  simpa [NoWasteConclusion, Protocol.prefixLabelFinQ, M3_rowLoss] using hnow

private theorem stage3_firstBits_transport
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ :
          Finset {a // a ∈
            (Finset.univ : Finset (Fin (2 ^ 2) × C2 d))})
        (Finset.univ :
          Finset {c // c ∈
            (Finset.univ : Finset (Fin (2 ^ 2) -> R2 d))})
        2
        (Protocol.restrictSub
          (Finset.univ : Finset (Fin (2 ^ 2) × C2 d))
          (Finset.univ : Finset (Fin (2 ^ 2) -> R2 d)) P)) :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset (R3 d))
        (Finset.univ : Finset (C3 d)) 2 P := by
  classical
  have h :=
    Protocol.firstKRowBitsOn_of_restrictSub
      (A := R3 d) (B := C3 d)
      (R := (Finset.univ : Finset (R3 d)))
      (C := (Finset.univ : Finset (C3 d)))
      (R0 := (Finset.univ :
        Finset {a // a ∈ (Finset.univ : Finset (R3 d))}))
      (C0 := (Finset.univ :
        Finset {c // c ∈ (Finset.univ : Finset (C3 d))}))
      2 P hrow
  simpa [image_univ_subtype_val_eq_univ] using h

private theorem two_zpow_neg_nat_add_one_eq_rpow_one_sub_nat (n : Nat) :
    (2 : Real) ^ (-(n : Int) + 1) = (2 : Real) ^ (1 - (n : Real)) := by
  have hcast : (((-(n : Int) + 1 : Int) : Real) = 1 - (n : Real)) := by
    norm_num
    ring
  rw [hcast.symm]
  exact (Real.rpow_intCast (2 : Real) (-(n : Int) + 1)).symm

private theorem Dfamily_le_whole {A B : Type*} [Fintype A] [Fintype B]
    (f : A -> B -> Bool) {Phi : Set (Finset A × Finset B)}
    (hne : Phi.Nonempty) :
    Dfamily f Phi <= D f := by
  rcases hne with ⟨RC, hRC⟩
  have hmem :
      D (subgame f RC.1 RC.2) ∈
        {d : Nat | ∃ RC' ∈ Phi, d = D (subgame f RC'.1 RC'.2)} := by
    exact ⟨RC, hRC, rfl⟩
  exact le_trans (by simpa [Dfamily] using Nat.sInf_le hmem)
    (D_subgame_le f RC.1 RC.2)

private theorem M3_upper_bound (d : Nat) :
    D (M3 d) <= D (M2 d) + 2 := by
  classical
  let MT : C2 d -> R2 d -> Bool := fun c r => M2 d r c
  let sigma : R3 d -> Fin (2 ^ 2) := fun r => r.1
  have hpart : D (M3 d) <= 2 + D (M2 d) := by
    refine comp_le_partition (M3 d) 2 (D (M2 d)) sigma ?_
    intro k
    have hmap :
        D (fun (x : {x : R3 d // sigma x = k}) (y : C3 d) =>
          MT x.val.2 (y k)) <= D MT :=
      D_mapNodes_le MT
        (fun x : {x : R3 d // sigma x = k} => x.val.2)
        (fun y : C3 d => y k)
    have hbranch :
        (fun (x : {x : R3 d // sigma x = k}) (y : C3 d) =>
          M3 d x.val y)
          =
        (fun (x : {x : R3 d // sigma x = k}) (y : C3 d) =>
          MT x.val.2 (y k)) := by
      funext x y
      have hxk : x.val.1 = k := x.property
      rw [M3_apply]
      simp [MT, hxk]
    have hswap : D MT = D (M2 d) := by
      dsimp [MT]
      simpa using comp_transpose (M2 d)
    simpa [hbranch, hswap] using hmap
  omega

private theorem M3_lower_bound (d : Nat) (hchk : Checklist d)
    (hrobM2 :
      IsRobust (fun (c : C2 d) (r : R2 d) => M2 d r c)
        Params.delta (Params.b2 d))
    (hD2 : 2 <= D (fun (c : C2 d) (r : R2 d) => M2 d r c)) :
    D (M2 d) + 2 <= D (M3 d) := by
  classical
  let MT : C2 d -> R2 d -> Bool := fun c r => M2 d r c
  have hb : (1 : Real) <= (Params.b2 d : Real) := by
    have hb_nat : 1 <= Params.b2 d := by
      unfold Params.b2
      have hll : 1 <= Nat.log 2 (Nat.log 2 d) := hchk.loglog_pos
      omega
    exact_mod_cast hb_nat
  have hb2 : (2 : Real) <= (Params.b2 d : Real) := by
    have hb_nat : 2 <= Params.b2 d := by
      unfold Params.b2
      have hll : 1 <= Nat.log 2 (Nat.log 2 d) := hchk.loglog_pos
      omega
    exact_mod_cast hb_nat
  have hdelta0 : (0 : Real) < Params.delta := by
    norm_num [Params.delta]
  have hdelta_half : Params.delta <= (1 : Real) / 2 := by
    norm_num [Params.delta]
  have hpow_lower :
      D MT + 2 <= Dfamily (interlaceFun MT (2 ^ 2))
        (bracketGE (C2 d) (R2 d) (2 ^ 2)
          ((2 : Real) ^ (2 : Nat) * (2 : Real) ^ (-(Params.b2 d : Real)))
          ((1 / 2 + Params.delta) ^ 2)) := by
    simpa [MT] using
      power_of_two_lower (f := MT) (δ := Params.delta)
        (b := (Params.b2 d : Real)) hrobM2 hb hdelta0 hdelta_half
        hD2 2 (by norm_num) hb2
  have hx1 :
      (2 : Real) ^ (2 : Nat) * (2 : Real) ^ (-(Params.b2 d : Real)) <= 1 := by
    have hexp : -(Params.b2 d : Real) <= (-2 : Real) := by linarith
    have hpow_le :
        (2 : Real) ^ (-(Params.b2 d : Real)) <= (2 : Real) ^ (-2 : Real) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 2) hexp
    calc
      (2 : Real) ^ (2 : Nat) * (2 : Real) ^ (-(Params.b2 d : Real))
          = 4 * (2 : Real) ^ (-(Params.b2 d : Real)) := by norm_num
      _ <= 4 * (2 : Real) ^ (-2 : Real) := by
          exact mul_le_mul_of_nonneg_left hpow_le (by norm_num)
      _ = 1 := by norm_num [Real.rpow_natCast]
  have hy1 : (1 / 2 + Params.delta) ^ 2 <= (1 : Real) := by
    norm_num [Params.delta]
  have hC2card : 1 <= Fintype.card (C2 d) := by
    simpa [C2, Fintype.card_fin] using
      L2_pos d hchk.t2_le_q2 hchk.one_le_q1
  have hne :
      (bracketGE (C2 d) (R2 d) (2 ^ 2)
        ((2 : Real) ^ (2 : Nat) * (2 : Real) ^ (-(Params.b2 d : Real)))
        ((1 / 2 + Params.delta) ^ 2)).Nonempty :=
    bracketGE.nonempty (X := C2 d) (Y := R2 d) (p := 2 ^ 2)
      _ _ hx1 hy1 hC2card
  have hfamily_le :
      Dfamily (interlaceFun MT (2 ^ 2))
        (bracketGE (C2 d) (R2 d) (2 ^ 2)
          ((2 : Real) ^ (2 : Nat) * (2 : Real) ^ (-(Params.b2 d : Real)))
          ((1 / 2 + Params.delta) ^ 2))
        <= D (interlaceFun MT (2 ^ 2)) :=
    Dfamily_le_whole (interlaceFun MT (2 ^ 2)) hne
  have hlowerMT : D MT + 2 <= D (M3 d) := by
    exact le_trans hpow_lower (by simpa [MT, M3] using hfamily_le)
  have htr : D MT = D (M2 d) := by
    dsimp [MT]
    simpa using comp_transpose (M2 d)
  simpa [htr] using hlowerMT

-- CLAIM-BEGIN aux:m3-complexity
/-- Stage-3 exact complexity.  Alice first identifies one of the four Stage-3
row blocks, reducing each branch to `M2ᵀ`; the lower bound is the `w = 2`
case of `power_of_two_lower` for the robust transpose of `M2`, followed by the
subgame-to-whole-game comparison. -/
theorem M3_complexity (d : Nat) (hchk : Checklist d)
    (hrobM2 :
      IsRobust (fun (c : C2 d) (r : R2 d) => M2 d r c)
        Params.delta (Params.b2 d))
    (hD2 : 2 <= D (fun (c : C2 d) (r : R2 d) => M2 d r c)) :
    D (M3 d) = D (M2 d) + 2 := by
-- CLAIM-END aux:m3-complexity
  exact le_antisymm (M3_upper_bound d)
    (M3_lower_bound d hchk hrobM2 hD2)

private theorem M3_delta_sep :
    Params.delta <= 1 / Real.sqrt 2 - 1 / 2 := by
  have hspos : 0 < Real.sqrt (2 : Real) := Real.sqrt_pos.2 (by norm_num)
  have hsle : Real.sqrt (2 : Real) <= (5 : Real) / 3 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : Real) <= (5 : Real) / 3)]
    norm_num
  have hinv : (3 : Real) / 5 <= 1 / Real.sqrt 2 := by
    rw [one_div, div_eq_mul_inv]
    have hmul : (3 : Real) * Real.sqrt 2 <= 5 := by
      nlinarith
    have hsnonneg : 0 <= Real.sqrt (2 : Real) := le_of_lt hspos
    have hdiv : (3 : Real) <= 5 * (Real.sqrt 2)⁻¹ := by
      calc
        (3 : Real) = 3 * (Real.sqrt 2 * (Real.sqrt 2)⁻¹) := by
          field_simp [hspos.ne']
        _ = (3 * Real.sqrt 2) * (Real.sqrt 2)⁻¹ := by ring
        _ <= 5 * (Real.sqrt 2)⁻¹ := by
          exact mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr hsnonneg)
    nlinarith
  norm_num [Params.delta] at hinv ⊢
  linarith

private theorem M3_stage3_gap (d : Nat) (hlog : 2 ^ 18 <= Nat.log 2 d)
    (hchk : Checklist d) :
    4 * M3_rowLoss d < Fintype.card (C2 d) := by
  classical
  have hq1ge2 : 2 <= Params.q1 d := by
    have hle := Params.le_q1_add_two (d := d) (by omega : 1 <= Nat.log 2 d)
    nlinarith
  have heps_pos : 0 < epsQT (Params.q2 d) (Params.t2 d) :=
    epsQT_pos (Params.q2_pos d) (Params.t2_pos d)
  have hratio_half :
      (1 - epsQT (Params.q2 d) (Params.t2 d)) / (Params.q1 d : Real)
        < (1 : Real) / 2 := by
    have hqge : (2 : Real) <= (Params.q1 d : Real) := by exact_mod_cast hq1ge2
    have hqpos : 0 < (Params.q1 d : Real) := by nlinarith
    have hratio :
        (1 - epsQT (Params.q2 d) (Params.t2 d)) / (Params.q1 d : Real)
          < 1 / (Params.q1 d : Real) := by
      exact div_lt_div_of_pos_right (by linarith) hqpos
    have hhalf : (1 : Real) / (Params.q1 d : Real) <= 1 / 2 := by
      exact one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2) hqge
    exact lt_of_lt_of_le hratio hhalf
  have hh2_half : 8 * Params.h2 d < (1 : Real) / 2 :=
    lt_trans hchk.dens_fiber_survival hratio_half
  have hL2pos_nat : 0 < L2 d := L2_pos d hchk.t2_le_q2 hchk.one_le_q1
  have hL2pos : 0 < (L2 d : Real) := by exact_mod_cast hL2pos_nat
  have hloss_eq :
      M3_rowLoss d =
        Nat.ceil ((2 : Real) ^ (-(Params.b2 d : Int) + 1) * (L2 d : Real)) := by
    unfold M3_rowLoss C2
    rw [Fintype.card_fin]
    rw [two_zpow_neg_nat_add_one_eq_rpow_one_sub_nat]
  have hthree :
      3 * (M3_rowLoss d : Real) <= 8 * Params.h2 d * (L2 d : Real) := by
    simpa [hloss_eq, Params.h2] using hchk.dens_stage3_rowloss
  have hthree_lt : 3 * (M3_rowLoss d : Real) < (1 / 2) * (L2 d : Real) :=
    lt_of_le_of_lt hthree (mul_lt_mul_of_pos_right hh2_half hL2pos)
  have hfour_real : (4 * M3_rowLoss d : Real) < (L2 d : Real) := by
    have hloss_nonneg : 0 <= (M3_rowLoss d : Real) := by positivity
    nlinarith
  have hfour_card :
      ((4 * M3_rowLoss d : Nat) : Real) < (Fintype.card (C2 d) : Real) := by
    simpa [C2, Fintype.card_fin] using hfour_real
  exact_mod_cast hfour_card

-- CLAIM-BEGIN aux:m3-separation-core
theorem M3_separation
    (d : Nat) (hd : 2 <= d) (hpow : IsPow2 d) (hchk : Checklist d)
    (hrobM2 :
      IsRobust (fun (c : C2 d) (r : R2 d) => M2 d r c)
        Params.delta (Params.b2 d))
    (hdelta_sep : Params.delta <= 1 / Real.sqrt 2 - 1 / 2)
    (hD2 : 2 <= D (fun (c : C2 d) (r : R2 d) => M2 d r c))
    (hstage3_gap :
      4 * M3_rowLoss d < Fintype.card (C2 d))
    (hM3_complexity : D (M3 d) = D (M2 d) + 2)
    (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hcost : P.cost <= D (M2 d) + 2) :
    M3SeparationConclusion d P := by
-- CLAIM-END aux:m3-separation-core
  classical
  let MT : C2 d -> R2 d -> Bool := fun c r => M2 d r c
  let Psub : Protocol
      {a // a ∈ (Finset.univ : Finset (Fin (2 ^ 2) × C2 d))}
      {c // c ∈ (Finset.univ : Finset (Fin (2 ^ 2) -> R2 d))} Bool :=
    Protocol.restrictSub
      (Finset.univ : Finset (Fin (2 ^ 2) × C2 d))
      (Finset.univ : Finset (Fin (2 ^ 2) -> R2 d)) P
  have hrob : IsRobust MT Params.delta (Params.b2 d) := by
    dsimp [MT]
    exact hrobM2
  have hb : (1 : Real) <= (Params.b2 d : Real) := by
    have hb_nat : 1 <= Params.b2 d := by
      unfold Params.b2
      have hll : 1 <= Nat.log 2 (Nat.log 2 d) := hchk.loglog_pos
      omega
    exact_mod_cast hb_nat
  have hdelta0 : (0 : Real) < Params.delta := by
    norm_num [Params.delta]
  have hdelta : Params.delta <= 1 / Real.sqrt 2 - 1 / 2 := hdelta_sep
  have hx0 : (0 : Real) < 1 := by norm_num
  have hx1 : (1 : Real) <= 1 := by norm_num
  have hy : 2 * (1 / 2 + Params.delta) ^ 2 <= (1 : Real) := by
    norm_num [Params.delta]
  have hy1 : (1 : Real) <= 1 := by norm_num
  have hqx :
      ((2 : Nat) ^ 2 : Real) * (2 : Real) ^ (-(Params.b2 d : Real)) <= 1 := by
    have hb4 : (2 : Real) <= (Params.b2 d : Real) := by
      have hb_nat : 2 <= Params.b2 d := by
        unfold Params.b2
        have hll : 1 <= Nat.log 2 (Nat.log 2 d) := hchk.loglog_pos
        omega
      exact_mod_cast hb_nat
    have hexp : -(Params.b2 d : Real) <= (-2 : Real) := by
      linarith
    have hpow_le :
        (2 : Real) ^ (-(Params.b2 d : Real)) <= (2 : Real) ^ (-2 : Real) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 2) hexp
    calc
      ((2 : Nat) ^ 2 : Real) * (2 : Real) ^ (-(Params.b2 d : Real))
          = 4 * (2 : Real) ^ (-(Params.b2 d : Real)) := by norm_num
      _ <= 4 * (2 : Real) ^ (-2 : Real) := by
          exact mul_le_mul_of_nonneg_left hpow_le (by norm_num)
      _ = 1 := by norm_num [Real.rpow_natCast]
  have hgap :
      2 ^ 2 * Nat.ceil ((2 : Real) ^ (1 - (Params.b2 d : Real)) *
          (Fintype.card (C2 d) : Real))
        < Nat.ceil ((Fintype.card (C2 d) : Real) * (1 : Real)) := by
    have hceil : Nat.ceil ((Fintype.card (C2 d) : Real) * (1 : Real)) =
        Fintype.card (C2 d) := by
      rw [mul_one, Nat.ceil_natCast]
    simpa [M3_rowLoss, hceil] using hstage3_gap
  have hRC :
      ((Finset.univ : Finset (Fin (2 ^ 2) × C2 d)),
        (Finset.univ : Finset (Fin (2 ^ 2) -> R2 d)))
        ∈ bracketGE (C2 d) (R2 d) (2 ^ 2) (1 : Real) (1 : Real) := by
    simpa using (bracketGE.self_mem (X := C2 d) (Y := R2 d) (p := 2 ^ 2))
  have hPsub :
      Psub.Computes
        (subgame (interlaceFun MT (2 ^ 2))
          (Finset.univ : Finset (Fin (2 ^ 2) × C2 d))
          (Finset.univ : Finset (Fin (2 ^ 2) -> R2 d))) := by
    intro a c
    rw [Protocol.eval_restrictSub]
    simpa [Psub, MT, M3, subgame] using hP a.val c.val
  have htr : D MT = D (M2 d) := by
    dsimp [MT]
    simpa using comp_transpose (M2 d)
  have hcost_sub : Psub.cost <= D MT + 2 := by
    dsimp [Psub]
    rw [Protocol.cost_restrictSub]
    rw [htr]
    exact hcost
  have hsep :=
    classical_separation (X := C2 d) (Y := R2 d)
      (f := MT) (δ := Params.delta) (b := (Params.b2 d : Real))
      hrob hb hdelta0 hdelta hD2 2 (by norm_num)
      hx0 hx1 hy hy1 hqx hgap
      ((Finset.univ : Finset (Fin (2 ^ 2) × C2 d)),
        (Finset.univ : Finset (Fin (2 ^ 2) -> R2 d)))
      hRC Psub hPsub hcost_sub
  refine ⟨?_, ?_, hM3_complexity⟩
  · exact stage3_firstBits_transport d P hsep.1
  · have hnow :
        NoWasteConclusion
          (Finset.univ : Finset (Fin (2 ^ 2)))
          (Finset.univ : Finset (Fin (2 ^ 2) × C2 d))
          (Protocol.prefixLabelFinQ
            (Finset.univ : Finset (Fin (2 ^ 2) × C2 d))
            (Protocol.restrictSub
              (Finset.univ : Finset (Fin (2 ^ 2) × C2 d))
              (Finset.univ : Finset (Fin (2 ^ 2) -> R2 d)) P))
          (Fintype.card (C2 d))
          (M3_rowLoss d) := by
        simpa [Psub, M3_rowLoss, Nat.ceil_natCast] using hsep.2
    exact stage3_noWaste_transport d P hnow

-- CLAIM-BEGIN lem:M3Separation
/-- Closed Stage-3 separation composition.  The theorem supplies the live
`M3_separation` core with the exact Stage-3 complexity, the transposed Stage-2
complexity floor, the numeric delta separation, and the Stage-3 row-loss gap.
The remaining robustness input is the public Stage-2 robustness conclusion. -/
theorem M3_separation_closed
    (d : Nat) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) (hchk : Checklist d)
    (hrobM2 :
      IsRobust (fun (c : C2 d) (r : R2 d) => M2 d r c)
        Params.delta (Params.b2 d))
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : Nat) <= Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hrow_threshold :
      Nat.ceil ((2 : Real) ^ (Nat.log 2 (Params.r2 d) : Nat) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : Real))
          <= Fintype.card (C1 d))
    (hraw : M2_hard_seed_to_h2prime_exp d)
    (hprime : M2_h2prime_bridge_exp d)
    (hy_three_fifths :
      forall c, c <= M2_T d + D (M1T d) ->
        (3 : Real) / 5 <=
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c)
    (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hcost : P.cost <= D (M2 d) + 2) :
    M3SeparationConclusion d P := by
-- CLAIM-END lem:M3Separation
  classical
  have hd : 2 <= d := by
    obtain ⟨k, rfl⟩ := hpow
    have hk : 2 ^ 18 <= k := by
      simpa [log_two_pow] using hlog
    exact Nat.succ_le_of_lt (Nat.one_lt_two_pow (by omega : k ≠ 0))
  have hlog64 : 64 <= Nat.log 2 d := by omega
  have hM2comp := M2_complexity_h2prime d hpow hlog hchk hm0_le hr2pow
    hrow_threshold hraw hprime hy_three_fifths
  have hM1comp := M1_complexity d hpow hlog64
  have hD_M2 : 2 <= D (M2 d) := by
    rw [hM2comp, hM1comp]
    have ha : 2 <= Params.a d := hchk.a_ge_two
    omega
  have hD2 : 2 <= D (fun (c : C2 d) (r : R2 d) => M2 d r c) := by
    have htr :
        D (fun (c : C2 d) (r : R2 d) => M2 d r c) = D (M2 d) := by
      simpa using comp_transpose (M2 d)
    rwa [htr]
  have hM3comp : D (M3 d) = D (M2 d) + 2 :=
    M3_complexity d hchk hrobM2 hD2
  exact M3_separation d hd hpow hchk hrobM2 M3_delta_sep hD2
    (M3_stage3_gap d hlog hchk) hM3comp P hP hcost

-- CLAIM-BEGIN aux:m3-sync
/-- Ambient Stage-3 synchronization data in the exact branch shape consumed by
`M3FuzzyLeavesData`.

The theorem below packages the output of the budget synchronization step once
that step has supplied Bob-onlyness on each ambient bin residual.  It is local
to Stage 3 because the depth, indexing, and target game are the `M3` ones. -/
structure M3AmbientSyncData
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2) where
  dimBranch :
    Fin 4 -> Fin (Params.q2 d) ->
      Protocol.BranchAt P (M3 d) (2 + Nat.clog 2 (Params.q2 d))
  dim_sideTrace :
    forall p alpha,
      (dimBranch p alpha).sideTrace =
        (binBranch p).sideTrace ++
          List.replicate (Nat.clog 2 (Params.q2 d))
            Protocol.ActualBitSide.bob
  dim_extends :
    forall p alpha, Protocol.BranchExtends (binBranch p) (dimBranch p alpha)

/-- Consumer-shaped ambient synchronization for Stage 3.

Given a depth-2 ambient bin branch and, below it, a synchronized Bob-only
segment of length `clog q2` with one live code for each `alpha`, compose the two
actual branches into ambient depth `2 + clog q2` branches.  The proof is the
live `BranchAt.compose_colPrefix` constructor plus the promoted side-trace and
extension lemmas. -/
theorem M3_ambient_sync_from_colPrefix
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (codeOfAlpha :
      Fin 4 -> Fin (Params.q2 d) -> Fin (2 ^ Nat.clog 2 (Params.q2 d)))
    (hcol : forall p,
      Protocol.FirstKColBitsOn
        (Finset.univ : Finset {a // a ∈ (binBranch p).rows})
        (Finset.univ : Finset {b // b ∈ (binBranch p).cols})
        (Nat.clog 2 (Params.q2 d)) (binBranch p).residual)
    (hcols : forall p alpha,
      (Protocol.colPrefixCols (Nat.clog 2 (Params.q2 d))
        (binBranch p).residual (codeOfAlpha p alpha)).Nonempty) :
    Nonempty (M3AmbientSyncData d P binBranch) := by
  refine ⟨
    { dimBranch := fun p alpha =>
        Protocol.BranchAt.compose_colPrefix (binBranch p) (codeOfAlpha p alpha)
          (hcol p) (hcols p alpha)
      dim_sideTrace := ?_
      dim_extends := ?_ }⟩
  · intro p alpha
    unfold Protocol.BranchAt.compose_colPrefix Protocol.BranchAt.compose
    simp [Protocol.mkBranchAt_of_colPrefix, Protocol.branchAt_of_swap,
      Protocol.mkBranchAt_of_rowPrefix, Protocol.ActualBitSide.swap]
  · intro p alpha
    exact Protocol.BranchAt.branchExtends_compose_left
      (binBranch p)
      (Protocol.mkBranchAt_of_colPrefix
        (binBranch p).residual
        (subgame (M3 d) (binBranch p).rows (binBranch p).cols)
        (Nat.clog 2 (Params.q2 d)) (codeOfAlpha p alpha)
        (hcol p) (binBranch p).residual_computes
        (by
          obtain ⟨a, ha⟩ := (binBranch p).rows_nonempty
          exact ⟨⟨a, ha⟩, Finset.mem_univ _⟩)
        (hcols p alpha))
-- CLAIM-END aux:m3-sync

-- CLAIM-BEGIN aux:m3-budget
/-- The exact ambient target that the Stage-3 budget-forces-structure argument
must supply to the `aux:m3-sync` adapter.

The first field is the desired survivor-guarded Bob-only shape of every bin
residual.  The second field is the per-alpha live column-prefix witness needed
by `Protocol.mkBranchAt_of_colPrefix`. -/
def M3BudgetColumnTarget
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (codeOfAlpha :
      Fin 4 -> Fin (Params.q2 d) -> Fin (2 ^ Nat.clog 2 (Params.q2 d))) :
    Prop :=
  (forall p,
    Protocol.FirstKColBitsOn
      (Finset.univ : Finset {a // a ∈ (binBranch p).rows})
      (Finset.univ : Finset {b // b ∈ (binBranch p).cols})
      (Nat.clog 2 (Params.q2 d)) (binBranch p).residual) ∧
  (forall p alpha,
    (Protocol.colPrefixCols (Nat.clog 2 (Params.q2 d))
      (binBranch p).residual (codeOfAlpha p alpha)).Nonempty)

/-- Certified budget ledger for an ambient Stage-3 bin residual.

After the two actual bin bits, every residual has cost at most `D (M2 d)`.
This is the exact cost side of the intended stopping-time contradiction; the
missing part is the structural induction that turns this tight residual budget
and the dense Stage-2 floors into `M3BudgetColumnTarget`. -/
theorem M3_binResidual_cost_le_M2
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (hcost : P.cost <= D (M2 d) + 2) :
    forall p, (binBranch p).residual.cost <= D (M2 d) := by
  intro p
  have hbranch : 2 + (binBranch p).residual.cost <= P.cost :=
    (binBranch p).cost_after_actualBits
  omega

/-- Each ambient bin residual is an explicit protocol for its induced Stage-3
subgame, so its subgame complexity is bounded by the residual cost. -/
theorem M3_binResidual_subgame_D_le_cost
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2) :
    forall p,
      D (subgame (M3 d) (binBranch p).rows (binBranch p).cols) <=
        (binBranch p).residual.cost := by
  intro p
  have hmem :
      (binBranch p).residual.cost ∈
        AchievableCosts
          (subgame (M3 d) (binBranch p).rows (binBranch p).cols) := by
    exact ⟨(binBranch p).residual, rfl, (binBranch p).residual_computes⟩
  simpa [D] using Nat.sInf_le hmem

/-- Combined certified budget consequence for the induced bin subgames. -/
theorem M3_binResidual_subgame_D_le_M2
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (hcost : P.cost <= D (M2 d) + 2) :
    forall p,
      D (subgame (M3 d) (binBranch p).rows (binBranch p).cols) <=
        D (M2 d) := by
  intro p
  exact le_trans
    (M3_binResidual_subgame_D_le_cost d P binBranch p)
    (M3_binResidual_cost_le_M2 d P binBranch hcost p)

/-- Once the missing budget column target has been proved, the live sync
adapter immediately returns the ambient branch family. -/
theorem M3_ambient_sync_from_budget_target
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (codeOfAlpha :
      Fin 4 -> Fin (Params.q2 d) -> Fin (2 ^ Nat.clog 2 (Params.q2 d)))
    (htarget : M3BudgetColumnTarget d P binBranch codeOfAlpha) :
    Nonempty (M3AmbientSyncData d P binBranch) := by
  exact
    M3_ambient_sync_from_colPrefix d P binBranch codeOfAlpha
      htarget.1 htarget.2
-- CLAIM-END aux:m3-budget

-- CLAIM-BEGIN aux:m3-stopdata
/-- Dense stopping data needed to promote restricted Bob-onlyness to ambient
Bob-onlyness by the generic no-waste theorem.

The record is intentionally generic in the residual game.  In the Stage-3 use,
`Q` is a bin residual, `R` is the dense survivor row set, `C` is the diagonal
column set, `m = clog q2`, and `Bcap = D (M1 d)`. -/
structure Stage3StopData
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool) (Q : Protocol A B Bool)
    (R : Finset A) (C : Finset B) (m Bcap : Nat) : Prop where
  restricted_col :
    Protocol.FirstKColBitsOn R C m (Protocol.restrict R C Q)
  cover :
    Protocol.FullStoppingFiberCoverage R C (Protocol.restrict R C Q)
      (List.replicate m Protocol.ActualBitSide.bob)
  hard :
    Protocol.TerminalHardWitnesses G R C (Protocol.restrict R C Q)
      (List.replicate m Protocol.ActualBitSide.bob) Bcap

/-- The generic no-waste application specialized to `Stage3StopData`. -/
theorem Stage3StopData.ambient_col
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool) (Q : Protocol A B Bool)
    (R : Finset A) (C : Finset B) (m Bcap : Nat)
    (hcomp : Q.Computes G) (hbudget : Q.cost <= m + Bcap)
    (hdata : Stage3StopData G Q R C m Bcap) :
    Protocol.FirstKColBitsOn
      (Finset.univ : Finset A) (Finset.univ : Finset B) m Q := by
  exact
    Protocol.noWaste_firstKColBitsOn_univ_of_restrict
      G Q R C m Bcap hcomp hbudget
      hdata.restricted_col hdata.cover hdata.hard

/-- Stage-3 residual budget in the exact `clog q2 + Bcap` form consumed by
the no-waste bridge.  The equality hypotheses are the established Stage-2
complexity identity, the public `clog = log` gate, and the definition of
`Bcap`. -/
theorem stage3_bin_residual_budget
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (Bcap : Nat)
    (hcost : P.cost <= D (M2 d) + 2)
    (hM2 : D (M2 d) = D (M1 d) + Nat.log 2 (Params.q2 d))
    (hclog : Nat.clog 2 (Params.q2 d) = Nat.log 2 (Params.q2 d))
    (hBcap : Bcap = D (M1 d)) :
    forall p,
      (binBranch p).residual.cost <=
        Nat.clog 2 (Params.q2 d) + Bcap := by
  intro p
  have hres := M3_binResidual_cost_le_M2 d P binBranch hcost p
  have htarget :
      D (M2 d) = Nat.clog 2 (Params.q2 d) + Bcap := by
    rw [hM2, hclog, hBcap]
    omega
  omega

/-- Per-bin no-waste bridge from certified stop data to ambient Bob-onlyness
of the bin residual. -/
theorem stage3_binResidual_firstKColBitsOn_ambient
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Bcap : Nat)
    (R : Finset {a // a ∈ (binBranch p).rows})
    (C : Finset {b // b ∈ (binBranch p).cols})
    (hbudget :
      (binBranch p).residual.cost <=
        Nat.clog 2 (Params.q2 d) + Bcap)
    (hdata :
      Stage3StopData
        (subgame (M3 d) (binBranch p).rows (binBranch p).cols)
        (binBranch p).residual R C
        (Nat.clog 2 (Params.q2 d)) Bcap) :
    Protocol.FirstKColBitsOn
      (Finset.univ : Finset {a // a ∈ (binBranch p).rows})
      (Finset.univ : Finset {b // b ∈ (binBranch p).cols})
      (Nat.clog 2 (Params.q2 d)) (binBranch p).residual := by
  exact
    Stage3StopData.ambient_col
      (subgame (M3 d) (binBranch p).rows (binBranch p).cols)
      (binBranch p).residual R C
      (Nat.clog 2 (Params.q2 d)) Bcap
      (binBranch p).residual_computes hbudget hdata

/-- Stop data plus live column-prefix witnesses assemble the exact
`M3BudgetColumnTarget` consumed by the ambient sync adapter. -/
theorem M3_budget_column_target_of_stopdata
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (codeOfAlpha :
      Fin 4 -> Fin (Params.q2 d) -> Fin (2 ^ Nat.clog 2 (Params.q2 d)))
    (Bcap : Nat)
    (R : forall p, Finset {a // a ∈ (binBranch p).rows})
    (C : forall p, Finset {b // b ∈ (binBranch p).cols})
    (hbudget : forall p,
      (binBranch p).residual.cost <=
        Nat.clog 2 (Params.q2 d) + Bcap)
    (hdata : forall p,
      Stage3StopData
        (subgame (M3 d) (binBranch p).rows (binBranch p).cols)
        (binBranch p).residual (R p) (C p)
        (Nat.clog 2 (Params.q2 d)) Bcap)
    (hcols : forall p alpha,
      (Protocol.colPrefixCols (Nat.clog 2 (Params.q2 d))
        (binBranch p).residual (codeOfAlpha p alpha)).Nonempty) :
    M3BudgetColumnTarget d P binBranch codeOfAlpha := by
  constructor
  · intro p
    exact
      stage3_binResidual_firstKColBitsOn_ambient
        d P binBranch p Bcap (R p) (C p) (hbudget p) (hdata p)
  · exact hcols
-- CLAIM-END aux:m3-stopdata

-- CLAIM-BEGIN aux:m3-floor
/-- If a rectangle contains a pointwise copy of a game `H`, then its
communication complexity is at least that of `H`.

The maps need not be injective: if two source rows or columns collide, the
pointwise copy hypothesis already says the corresponding rows or columns of
`H` agree. -/
theorem D_exact_copy_le_subgame
    {A B A0 B0 : Type*} [Fintype A] [Fintype B] [Fintype A0] [Fintype B0]
    (G : A -> B -> Bool) (H : A0 -> B0 -> Bool)
    (rowEmbed : A0 -> A) (colEmbed : B0 -> B)
    (R : Finset A) (C : Finset B)
    (hrow : forall a, rowEmbed a ∈ R) (hcol : forall b, colEmbed b ∈ C)
    (hcopy : forall a b, G (rowEmbed a) (colEmbed b) = H a b) :
    D H <= D (subgame G R C) := by
  let rho : A0 -> {a // a ∈ R} := fun a => ⟨rowEmbed a, hrow a⟩
  let sigma : B0 -> {b // b ∈ C} := fun b => ⟨colEmbed b, hcol b⟩
  have hD :
      D (fun a b => (subgame G R C) (rho a) (sigma b)) <=
        D (subgame G R C) := by
    exact D_mapNodes_le (subgame G R C) rho sigma
  have hfun : (fun a b => (subgame G R C) (rho a) (sigma b)) = H := by
    funext a b
    exact hcopy a b
  simpa [hfun] using hD

/-- Build terminal hard witnesses from exact copies contained in every
stopping prefix fiber.

For each terminal Boolean word `w`, the caller supplies template-row and
template-column embeddings whose images lie in the corresponding reached
`rowsAtPrefix` and `colsAtPrefix` sets. The previous copy lemma then gives the
required lower bound for the chosen subrectangle. -/
theorem terminalHardWitnesses_of_prefix_exact_copy
    {A B A0 B0 : Type*} [Fintype A] [Fintype B] [Fintype A0] [Fintype B0]
    [Nonempty A0] [Nonempty B0]
    (G : A -> B -> Bool) (H : A0 -> B0 -> Bool)
    (R : Finset A) (C : Finset B) (Q : Protocol A B Bool)
    (pat : List Protocol.ActualBitSide) (Bcap : Nat)
    (rowEmbed : List Bool -> A0 -> A)
    (colEmbed : List Bool -> B0 -> B)
    (hrowPrefix :
      forall w, w.length = pat.length ->
        forall a, rowEmbed w a ∈ Protocol.rowsAtPrefix R C Q w)
    (hcolPrefix :
      forall w, w.length = pat.length ->
        forall b, colEmbed w b ∈ Protocol.colsAtPrefix R C Q w)
    (hcopy :
      forall w, w.length = pat.length ->
        forall a b, G (rowEmbed w a) (colEmbed w b) = H a b)
    (hcap : Bcap <= D H) :
    Protocol.TerminalHardWitnesses G R C Q pat Bcap := by
  classical
  intro w hw
  let Rw : Finset A := (Finset.univ : Finset A0).image (rowEmbed w)
  let Cw : Finset B := (Finset.univ : Finset B0).image (colEmbed w)
  refine ⟨Rw, Cw, ?_, ?_⟩
  · refine
      { rows_subset := ?_
        cols_subset := ?_
        rows_nonempty := ?_
        cols_nonempty := ?_ }
    · intro a ha
      rcases Finset.mem_image.mp ha with ⟨a0, _ha0, rfl⟩
      exact hrowPrefix w hw a0
    · intro b hb
      rcases Finset.mem_image.mp hb with ⟨b0, _hb0, rfl⟩
      exact hcolPrefix w hw b0
    · obtain ⟨a0⟩ := (inferInstance : Nonempty A0)
      exact ⟨rowEmbed w a0,
        Finset.mem_image.mpr ⟨a0, Finset.mem_univ a0, rfl⟩⟩
    · obtain ⟨b0⟩ := (inferInstance : Nonempty B0)
      exact ⟨colEmbed w b0,
        Finset.mem_image.mpr ⟨b0, Finset.mem_univ b0, rfl⟩⟩
  · exact le_trans hcap
      (D_exact_copy_le_subgame G H (rowEmbed w) (colEmbed w) Rw Cw
        (by
          intro a
          exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
        (by
          intro b
          exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩)
        (hcopy w hw))

/-- Stage-3-facing specialization of the terminal floor: if each reached
prefix rectangle contains an exact `M1 d` copy, then it supplies the
`Stage3StopData.hard` lower bound with budget `D (M1 d)`. -/
theorem M3_terminalHardWitnesses_of_prefix_M1_copies
    (d : Nat)
    {A B : Type*} [Fintype A] [Fintype B]
    (hR1 : Nonempty (R1 d)) (hC1 : Nonempty (C1 d))
    (G : A -> B -> Bool)
    (R : Finset A) (C : Finset B) (Q : Protocol A B Bool)
    (pat : List Protocol.ActualBitSide)
    (rowEmbed : List Bool -> R1 d -> A)
    (colEmbed : List Bool -> C1 d -> B)
    (hrowPrefix :
      forall w, w.length = pat.length ->
        forall r, rowEmbed w r ∈ Protocol.rowsAtPrefix R C Q w)
    (hcolPrefix :
      forall w, w.length = pat.length ->
        forall gamma, colEmbed w gamma ∈ Protocol.colsAtPrefix R C Q w)
    (hcopy :
      forall w, w.length = pat.length ->
        forall r gamma,
          G (rowEmbed w r) (colEmbed w gamma) = M1 d r gamma) :
    Protocol.TerminalHardWitnesses G R C Q pat (D (M1 d)) := by
  letI : Nonempty (R1 d) := hR1
  letI : Nonempty (C1 d) := hC1
  exact
    terminalHardWitnesses_of_prefix_exact_copy
      G (M1 d) R C Q pat (D (M1 d)) rowEmbed colEmbed
      hrowPrefix hcolPrefix hcopy (le_refl _)

-- CLAIM-END aux:m3-floor

-- CLAIM-BEGIN aux:m3-prefixcopy

namespace Protocol

/-- On a rectangle whose next `m` live bits are Bob bits, the length-`m`
actual bit list is independent of the row coordinate. -/
theorem actualBitListRaw_eq_of_firstKColBitsOn
    {A B Z : Type*} [DecidableEq A] [DecidableEq B]
    {R : Finset A} {C : Finset B} {P : Protocol A B Z}
    {m : Nat}
    (hcol : Protocol.FirstKColBitsOn R C m P)
    {a a' : A} (ha : a ∈ R) (ha' : a' ∈ R)
    {b : B} (hb : b ∈ C) :
    Protocol.actualBitListRaw m P a b =
      Protocol.actualBitListRaw m P a' b := by
  induction m generalizing R C P with
  | zero =>
      rfl
  | succ m ih =>
      cases P with
      | leaf z =>
          rfl
      | aNode q l r =>
          simp only [Protocol.FirstKColBitsOn, Protocol.FirstKRowBitsOn,
            Protocol.swap] at hcol
          rcases hcol with hC | hR
          · rw [hC] at hb
            exact absurd hb (Finset.notMem_empty b)
          · rw [hR] at ha
            exact absurd ha (Finset.notMem_empty a)
      | bNode q l r =>
          simp only [Protocol.FirstKColBitsOn, Protocol.FirstKRowBitsOn,
            Protocol.swap] at hcol
          by_cases hq : q b
          · have hb' : b ∈ C.filter fun y => q y = true := by
              rw [Finset.mem_filter]
              exact ⟨hb, hq⟩
            have htail :=
              ih (R := R) (C := C.filter fun y => q y = true) (P := r)
                hcol.2 ha ha' hb'
            simp [Protocol.actualBitListRaw, hq, htail]
          · have hqf : q b = false := by simp [hq]
            have hb' : b ∈ C.filter fun y => q y = false := by
              rw [Finset.mem_filter]
              exact ⟨hb, hqf⟩
            have htail :=
              ih (R := R) (C := C.filter fun y => q y = false) (P := l)
                hcol.1 ha ha' hb'
            simp [Protocol.actualBitListRaw, hq, htail]

/-- If every full Bob-prefix fiber is nonempty, then under Bob-onlyness every
retained row lies in every reached row-prefix set. -/
theorem rowsAtPrefix_eq_of_firstKColBitsOn
    {A B Z : Type*} [DecidableEq A] [DecidableEq B]
    {R : Finset A} {C : Finset B} {P : Protocol A B Z}
    {m : Nat}
    (hcol : Protocol.FirstKColBitsOn R C m P)
    (hcover : Protocol.FullStoppingFiberCoverage R C P
      (List.replicate m Protocol.ActualBitSide.bob))
    (w : List Bool) (hw : w.length = m) :
    Protocol.rowsAtPrefix R C P w = R := by
  classical
  ext a
  constructor
  · intro ha
    exact (Finset.mem_filter.mp ha).1
  · intro ha
    obtain ⟨a0, ha0, b0, hb0, hbits0⟩ := hcover w (by simp [hw])
    rw [Protocol.rowsAtPrefix, Finset.mem_filter]
    refine ⟨ha, b0, hb0, ?_⟩
    have hsame :=
      Protocol.actualBitListRaw_eq_of_firstKColBitsOn
        (R := R) (C := C) (P := P) (m := m) hcol ha ha0 hb0
    calc
      Protocol.actualBitListRaw w.length P a b0 =
          Protocol.actualBitListRaw m P a b0 := by rw [hw]
      _ = Protocol.actualBitListRaw m P a0 b0 := hsame
      _ = w := by simpa [hw] using hbits0

/-- The hard-witness part of Stage-3 stop data follows from Bob-onlyness,
full fiber coverage, column-prefix embeddings, and exact `M1` copies. -/
theorem M3_terminalHardWitnesses_of_colPrefix_M1_copies
    (d : Nat)
    {A B : Type*} [Fintype A] [Fintype B]
    (hR1 : Nonempty (R1 d)) (hC1 : Nonempty (C1 d))
    (G : A -> B -> Bool)
    (R : Finset A) (C : Finset B) (Q : Protocol A B Bool)
    (m : Nat)
    (hcol : Protocol.FirstKColBitsOn R C m Q)
    (hcover : Protocol.FullStoppingFiberCoverage R C Q
      (List.replicate m Protocol.ActualBitSide.bob))
    (rowEmbed : List Bool -> R1 d -> A)
    (colEmbed : List Bool -> C1 d -> B)
    (hrowMem : forall w, w.length = m -> forall r, rowEmbed w r ∈ R)
    (hcolPrefix :
      forall w, w.length = m ->
        forall gamma, colEmbed w gamma ∈ Protocol.colsAtPrefix R C Q w)
    (hcopy :
      forall w, w.length = m ->
        forall r gamma,
          G (rowEmbed w r) (colEmbed w gamma) = M1 d r gamma) :
    Protocol.TerminalHardWitnesses G R C Q
      (List.replicate m Protocol.ActualBitSide.bob) (D (M1 d)) := by
  classical
  refine
    M3_terminalHardWitnesses_of_prefix_M1_copies d hR1 hC1 G R C Q
      (List.replicate m Protocol.ActualBitSide.bob)
      rowEmbed colEmbed ?_ ?_ ?_
  · intro w hw r
    have hwlen : w.length = m := by simpa using hw
    rw [Protocol.rowsAtPrefix_eq_of_firstKColBitsOn
      (R := R) (C := C) (P := Q) (m := m) hcol hcover w hwlen]
    exact hrowMem w hwlen r
  · intro w hw gamma
    exact hcolPrefix w (by simpa using hw) gamma
  · intro w hw r gamma
    exact hcopy w (by simpa using hw) r gamma

end Protocol

/-- Assemble the full stop-data record once the restricted residual has a
Bob-only prefix, full stopping-fiber coverage, and per-prefix exact `M1` copies.

This is the last checked bridge before the Stage-3-specific orientation
transport: in the intended use, `Q` is a bin residual, `R` is the dense survivor
row set, and `C` is the diagonal column set. -/
theorem Stage3StopData.of_colPrefix_M1_copies
    (d : Nat)
    {A B : Type*} [Fintype A] [Fintype B]
    (hR1 : Nonempty (R1 d)) (hC1 : Nonempty (C1 d))
    (G : A -> B -> Bool) (Q : Protocol A B Bool)
    (R : Finset A) (C : Finset B) (m : Nat)
    (hrestricted_col :
      Protocol.FirstKColBitsOn R C m (Protocol.restrict R C Q))
    (hcover :
      Protocol.FullStoppingFiberCoverage R C (Protocol.restrict R C Q)
        (List.replicate m Protocol.ActualBitSide.bob))
    (rowEmbed : List Bool -> R1 d -> A)
    (colEmbed : List Bool -> C1 d -> B)
    (hrowMem : forall w, w.length = m -> forall r, rowEmbed w r ∈ R)
    (hcolPrefix :
      forall w, w.length = m ->
        forall gamma,
          colEmbed w gamma ∈
            Protocol.colsAtPrefix R C (Protocol.restrict R C Q) w)
    (hcopy :
      forall w, w.length = m ->
        forall r gamma,
          G (rowEmbed w r) (colEmbed w gamma) = M1 d r gamma) :
    Stage3StopData G Q R C m (D (M1 d)) where
  restricted_col := hrestricted_col
  cover := hcover
  hard :=
    Protocol.M3_terminalHardWitnesses_of_colPrefix_M1_copies d hR1 hC1
      G R C (Protocol.restrict R C Q) m hrestricted_col hcover
      rowEmbed colEmbed hrowMem hcolPrefix hcopy

/-- Exact per-bin data still needed from the Stage-2-to-Stage-3 orientation
transport.

The fields are deliberately concrete: they are precisely the data needed to
turn the restricted bin residual into `Stage3StopData` via the prefix-copy
bridge above. -/
structure M3PrefixCopyStopInputs
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (R : forall p, Finset {a // a ∈ (binBranch p).rows})
    (C : forall p, Finset {b // b ∈ (binBranch p).cols})
    (m : Nat) where
  restricted_col :
    forall p,
      Protocol.FirstKColBitsOn (R p) (C p) m
        (Protocol.restrict (R p) (C p) (binBranch p).residual)
  cover :
    forall p,
      Protocol.FullStoppingFiberCoverage (R p) (C p)
        (Protocol.restrict (R p) (C p) (binBranch p).residual)
        (List.replicate m Protocol.ActualBitSide.bob)
  rowEmbed :
    forall p, List Bool -> R1 d -> {a // a ∈ (binBranch p).rows}
  colEmbed :
    forall p, List Bool -> C1 d -> {b // b ∈ (binBranch p).cols}
  row_mem :
    forall p w, w.length = m -> forall r, rowEmbed p w r ∈ R p
  col_prefix :
    forall p w, w.length = m -> forall gamma,
      colEmbed p w gamma ∈
        Protocol.colsAtPrefix (R p) (C p)
          (Protocol.restrict (R p) (C p) (binBranch p).residual) w
  copy :
    forall p w, w.length = m -> forall r gamma,
      subgame (M3 d) (binBranch p).rows (binBranch p).cols
        (rowEmbed p w r) (colEmbed p w gamma) = M1 d r gamma

/-- The per-bin prefix-copy inputs assemble the `Stage3StopData` family consumed
by `M3_budget_column_target_of_stopdata`. -/
theorem M3PrefixCopyStopInputs.stage3StopData
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (R : forall p, Finset {a // a ∈ (binBranch p).rows})
    (C : forall p, Finset {b // b ∈ (binBranch p).cols})
    (m : Nat)
    (hR1 : Nonempty (R1 d)) (hC1 : Nonempty (C1 d))
    (hinputs : M3PrefixCopyStopInputs d P binBranch R C m) :
    forall p,
      Stage3StopData
        (subgame (M3 d) (binBranch p).rows (binBranch p).cols)
        (binBranch p).residual (R p) (C p) m (D (M1 d)) := by
  intro p
  exact
    Stage3StopData.of_colPrefix_M1_copies d hR1 hC1
      (subgame (M3 d) (binBranch p).rows (binBranch p).cols)
      (binBranch p).residual (R p) (C p) m
      (hinputs.restricted_col p) (hinputs.cover p)
      (hinputs.rowEmbed p) (hinputs.colEmbed p)
      (hinputs.row_mem p) (hinputs.col_prefix p) (hinputs.copy p)

-- CLAIM-END aux:m3-prefixcopy

-- CLAIM-BEGIN aux:m3-dense-floor
/-- Dense terminal floor from the chosen-coordinate Stage-1 threshold.

For every terminal word, the caller supplies a prefix-contained copy of the
chosen-coordinate dense local game on a dense `S'`. The Stage-1 dense threshold
then gives the `a + 2` lower bound on each reached subrectangle. -/
theorem terminalHardWitnesses_of_prefix_dense_HlocalAtSub
    (d : Nat) (hd : 2 <= d)
    (hbal : Params.t1 d <= Params.q1 d + 5)
    (hta : Params.a d + 2 <= Params.t1 d)
    {rho : Real} (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (hrho : rho < (1 - epsQT (Params.q1 d + 5) (Params.t1 d)) / 2)
    (S' : Finset (C1 d))
    (hS' : (1 - rho) * (L1 d : Real) <= (S'.card : Real))
    {u : Nat} (e : Fin u -> Fin (Params.q1 d + 5))
    (he : Function.Injective e) (hu : Params.q1 d + 3 <= u)
    (hrowNonempty : Nonempty (Fin u × Fin 1))
    (hcolNonempty : Nonempty {j // j ∈ S'})
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool)
    (R : Finset A) (C : Finset B) (Q : Protocol A B Bool)
    (pat : List Protocol.ActualBitSide)
    (rowEmbed : List Bool -> (Fin u × Fin 1) -> A)
    (colEmbed : List Bool -> {j // j ∈ S'} -> B)
    (hrowPrefix :
      forall w, w.length = pat.length ->
        forall x, rowEmbed w x ∈ Protocol.rowsAtPrefix R C Q w)
    (hcolPrefix :
      forall w, w.length = pat.length ->
        forall gamma, colEmbed w gamma ∈ Protocol.colsAtPrefix R C Q w)
    (hcopy :
      forall w, w.length = pat.length ->
        forall x gamma,
          G (rowEmbed w x) (colEmbed w gamma) =
            HlocalAtSub d (S1fam d) S' e x gamma) :
    Protocol.TerminalHardWitnesses G R C Q pat (Params.a d + 2) := by
  letI : Nonempty (Fin u × Fin 1) := hrowNonempty
  letI : Nonempty {j // j ∈ S'} := hcolNonempty
  exact
    terminalHardWitnesses_of_prefix_exact_copy
      G (HlocalAtSub d (S1fam d) S' e) R C Q pat (Params.a d + 2)
      rowEmbed colEmbed hrowPrefix hcolPrefix hcopy
      (stage1_chosen_dense_threshold d hd hbal hta hrho0 hrho1 hrho
        S' hS' e he hu)

/-- Weaken the dense terminal floor to any budget not exceeding `a + 2`. -/
theorem terminalHardWitnesses_of_prefix_dense_HlocalAtSub_le
    (d : Nat) (hd : 2 <= d)
    (hbal : Params.t1 d <= Params.q1 d + 5)
    (hta : Params.a d + 2 <= Params.t1 d)
    {rho : Real} (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (hrho : rho < (1 - epsQT (Params.q1 d + 5) (Params.t1 d)) / 2)
    (S' : Finset (C1 d))
    (hS' : (1 - rho) * (L1 d : Real) <= (S'.card : Real))
    {u : Nat} (e : Fin u -> Fin (Params.q1 d + 5))
    (he : Function.Injective e) (hu : Params.q1 d + 3 <= u)
    (hrowNonempty : Nonempty (Fin u × Fin 1))
    (hcolNonempty : Nonempty {j // j ∈ S'})
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool)
    (R : Finset A) (C : Finset B) (Q : Protocol A B Bool)
    (pat : List Protocol.ActualBitSide) (Bcap : Nat)
    (hBcap : Bcap <= Params.a d + 2)
    (rowEmbed : List Bool -> (Fin u × Fin 1) -> A)
    (colEmbed : List Bool -> {j // j ∈ S'} -> B)
    (hrowPrefix :
      forall w, w.length = pat.length ->
        forall x, rowEmbed w x ∈ Protocol.rowsAtPrefix R C Q w)
    (hcolPrefix :
      forall w, w.length = pat.length ->
        forall gamma, colEmbed w gamma ∈ Protocol.colsAtPrefix R C Q w)
    (hcopy :
      forall w, w.length = pat.length ->
        forall x gamma,
          G (rowEmbed w x) (colEmbed w gamma) =
            HlocalAtSub d (S1fam d) S' e x gamma) :
    Protocol.TerminalHardWitnesses G R C Q pat Bcap := by
  intro w hw
  rcases terminalHardWitnesses_of_prefix_dense_HlocalAtSub
      d hd hbal hta hrho0 hrho1 hrho S' hS' e he hu
      hrowNonempty hcolNonempty G R C Q pat rowEmbed colEmbed
      hrowPrefix hcolPrefix hcopy w hw with
    ⟨Rw, Cw, hstop, hhard⟩
  exact ⟨Rw, Cw, hstop, le_trans hBcap hhard⟩

namespace Protocol

/-- Dense Stage-3 terminal floor in the Bob-prefix form used by stop data. -/
theorem M3_terminalHardWitnesses_of_colPrefix_dense_HlocalAtSub
    (d : Nat) (hd : 2 <= d)
    (hbal : Params.t1 d <= Params.q1 d + 5)
    (hta : Params.a d + 2 <= Params.t1 d)
    {rho : Real} (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (hrho : rho < (1 - epsQT (Params.q1 d + 5) (Params.t1 d)) / 2)
    (S' : Finset (C1 d))
    (hS' : (1 - rho) * (L1 d : Real) <= (S'.card : Real))
    {u : Nat} (e : Fin u -> Fin (Params.q1 d + 5))
    (he : Function.Injective e) (hu : Params.q1 d + 3 <= u)
    (hrowNonempty : Nonempty (Fin u × Fin 1))
    (hcolNonempty : Nonempty {j // j ∈ S'})
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool)
    (R : Finset A) (C : Finset B) (Q : Protocol A B Bool)
    (m Bcap : Nat) (hBcap : Bcap <= Params.a d + 2)
    (hcol : Protocol.FirstKColBitsOn R C m Q)
    (hcover : Protocol.FullStoppingFiberCoverage R C Q
      (List.replicate m Protocol.ActualBitSide.bob))
    (rowEmbed : List Bool -> (Fin u × Fin 1) -> A)
    (colEmbed : List Bool -> {j // j ∈ S'} -> B)
    (hrowMem : forall w, w.length = m -> forall x, rowEmbed w x ∈ R)
    (hcolPrefix :
      forall w, w.length = m ->
        forall gamma, colEmbed w gamma ∈ Protocol.colsAtPrefix R C Q w)
    (hcopy :
      forall w, w.length = m ->
        forall x gamma,
          G (rowEmbed w x) (colEmbed w gamma) =
            HlocalAtSub d (S1fam d) S' e x gamma) :
    Protocol.TerminalHardWitnesses G R C Q
      (List.replicate m Protocol.ActualBitSide.bob) Bcap := by
  classical
  refine
    terminalHardWitnesses_of_prefix_dense_HlocalAtSub_le
      d hd hbal hta hrho0 hrho1 hrho S' hS' e he hu
      hrowNonempty hcolNonempty G R C Q
      (List.replicate m Protocol.ActualBitSide.bob) Bcap hBcap
      rowEmbed colEmbed ?_ ?_ ?_
  · intro w hw x
    have hwlen : w.length = m := by simpa using hw
    rw [Protocol.rowsAtPrefix_eq_of_firstKColBitsOn
      (R := R) (C := C) (P := Q) (m := m) hcol hcover w hwlen]
    exact hrowMem w hwlen x
  · intro w hw gamma
    exact hcolPrefix w (by simpa using hw) gamma
  · intro w hw x gamma
    exact hcopy w (by simpa using hw) x gamma

end Protocol

/-- Dense `HlocalAtSub` prefix copies assemble the stop-data hard field. -/
theorem Stage3StopData.of_colPrefix_dense_HlocalAtSub_copies
    (d : Nat) (hd : 2 <= d)
    (hbal : Params.t1 d <= Params.q1 d + 5)
    (hta : Params.a d + 2 <= Params.t1 d)
    {rho : Real} (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (hrho : rho < (1 - epsQT (Params.q1 d + 5) (Params.t1 d)) / 2)
    (S' : Finset (C1 d))
    (hS' : (1 - rho) * (L1 d : Real) <= (S'.card : Real))
    {u : Nat} (e : Fin u -> Fin (Params.q1 d + 5))
    (he : Function.Injective e) (hu : Params.q1 d + 3 <= u)
    (hrowNonempty : Nonempty (Fin u × Fin 1))
    (hcolNonempty : Nonempty {j // j ∈ S'})
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool) (Q : Protocol A B Bool)
    (R : Finset A) (C : Finset B) (m Bcap : Nat)
    (hBcap : Bcap <= Params.a d + 2)
    (hrestricted_col :
      Protocol.FirstKColBitsOn R C m (Protocol.restrict R C Q))
    (hcover :
      Protocol.FullStoppingFiberCoverage R C (Protocol.restrict R C Q)
        (List.replicate m Protocol.ActualBitSide.bob))
    (rowEmbed : List Bool -> (Fin u × Fin 1) -> A)
    (colEmbed : List Bool -> {j // j ∈ S'} -> B)
    (hrowMem : forall w, w.length = m -> forall x, rowEmbed w x ∈ R)
    (hcolPrefix :
      forall w, w.length = m ->
        forall gamma,
          colEmbed w gamma ∈
            Protocol.colsAtPrefix R C (Protocol.restrict R C Q) w)
    (hcopy :
      forall w, w.length = m ->
        forall x gamma,
          G (rowEmbed w x) (colEmbed w gamma) =
            HlocalAtSub d (S1fam d) S' e x gamma) :
    Stage3StopData G Q R C m Bcap where
  restricted_col := hrestricted_col
  cover := hcover
  hard :=
    Protocol.M3_terminalHardWitnesses_of_colPrefix_dense_HlocalAtSub
      d hd hbal hta hrho0 hrho1 hrho S' hS' e he hu
      hrowNonempty hcolNonempty G R C (Protocol.restrict R C Q)
      m Bcap hBcap hrestricted_col hcover
      rowEmbed colEmbed hrowMem hcolPrefix hcopy

-- CLAIM-END aux:m3-dense-floor

-- CLAIM-BEGIN aux:m3-fuzzy-partial
/-- Certified partial for paper `lem:MThreeFuzzyLeaves`.

This block reaches the two live inputs needed by the fuzzy-leaves construction:
the Stage-3 separation package for the ambient protocol, and the per-alpha
dense-row Stage-2 corollary at the Stage-3 survivor density
`sigma = 1 - 8 * h2`.  The remaining, intentionally unstated target theorem
requires a branch-transport lemma turning the mapped swapped bin residual into a
`BranchAt` of the original bin residual, so that `BranchAt.compose` can produce
the `dimBranch` field of `M3FuzzyLeavesData`. -/
theorem M3_fuzzy_leaves_dense_alpha_partial
    (d : Nat) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) (hchk : Checklist d)
    (hrobM2 :
      IsRobust (fun (c : C2 d) (r : R2 d) => M2 d r c)
        Params.delta (Params.b2 d))
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : Nat) <= Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hp1 : 2 ^ M2_T d <= 2 * M2_hard_seed_copies d)
    (hp2 : M2_hard_seed_copies d <= 2 ^ M2_T d)
    (hxseed_le_one : M2_hard_seed_rowDensity d <= 1)
    (hrow_threshold :
      Nat.ceil ((2 : Real) ^ (Nat.log 2 (Params.r2 d) : Nat) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : Real))
          <= Fintype.card (C1 d))
    (hseed_bridge : M2_hard_seed_columnDensity d <=
      Params.h2 d *
        (2 : Real) ^ (-((M2_T d + D (M1T d) : Nat) : Real)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hy_le_one : M1_stage2_terminal_density d <= 1)
    (hrowTerm : 9 * Params.t1 d <=
      16 * Nat.ceil ((Fintype.card (R1 d) : Real) *
        M1_stage2_terminal_density d))
    (hcolTerm : (2 : Real) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : Int))
        * (Fintype.card (C1 d) : Real) <=
      (Nat.ceil ((Fintype.card (C1 d) : Real) *
        ((2 : Real) ^ (-(Params.b1 d : Int)))) : Real))
    (hresidual_density : forall c, c <= M2_T d + D (M1T d) ->
      1 / 2 + Params.delta <=
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c /\
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c <= 1)
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hsigma0 : 0 < 1 - 8 * Params.h2 d)
    (hsigma1 : 1 - 8 * Params.h2 d <= 1)
    (hres_dense : IsColumnLossResilient (M1T d) (Params.b1 d : Real)
      (epsQT (Params.q2 d) (Params.t2 d))
      (Nat.log 2 (Params.q2 d)) (M2_T d) (1 - 8 * Params.h2 d))
    (hxseed_le_inv_r : M2_hard_seed_rowDensity d <=
      (2 : Real) ^ (-(Nat.log 2 (Params.r2 d) : Real)))
    (hseed_bridge_dense : M2_hard_seed_columnDensity d <=
      (1 - 8 * Params.h2 d) *
        (2 : Real) ^ (-((M2_T d + D (M1T d) : Nat) : Real)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hT1 : 1 <= M2_T d)
    (hgap_dense :
      2 ^ M2DenseDepth d *
        Nat.ceil ((2 : Real) ^ (1 - (Params.b1 d : Real)) *
          (Fintype.card (C1 d) : Real)) < Fintype.card (C1 d))
    (hraw : M2_hard_seed_to_h2prime_exp d)
    (hprime : M2_h2prime_bridge_exp d)
    (hy_three_fifths :
      forall c, c <= M2_T d + D (M1T d) ->
        (3 : Real) / 5 <=
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c)
    (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hcost : P.cost <= D (M2 d) + 2) :
    M3SeparationConclusion d P /\
      forall (Sdense : Finset (C2 d))
        (Pdense : Protocol (M2DenseRows d) (M2DenseCols d Sdense) Bool),
          (1 - 8 * Params.h2 d) * (L2 d : Real) <=
              (Sdense.card : Real) ->
          Pdense.Computes (M2DenseGame d hqcast Sdense) ->
          Pdense.cost <= D (M2 d) ->
          Nonempty
            (M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense Pdense) := by
  classical
  refine ⟨?_, ?_⟩
  · exact
      M3_separation_closed d hpow hlog hchk hrobM2 hm0_le hr2pow
        hrow_threshold hraw hprime hy_three_fifths P hP hcost
  · intro Sdense Pdense hSdense hPdense hcostDense
    have hlog256 : 256 <= Nat.log 2 d := by omega
    exact
      M2_separation_transpose_dense_rows_alpha d hpow hlog256 hchk
        hm0_le hr2pow hp1 hp2 hxseed_le_one hrow_threshold hseed_bridge
        hy_le_one hrowTerm hcolTerm hresidual_density hqcast
        (1 - 8 * Params.h2 d) hsigma0 hsigma1 (le_refl _)
        hres_dense hxseed_le_inv_r hseed_bridge_dense M3_delta_sep hT1
        hgap_dense Sdense hSdense Pdense hPdense hcostDense

-- CLAIM-END aux:m3-fuzzy-partial

-- CLAIM-BEGIN aux:m3-transport

theorem M3_diagCol_exact_M1
    (d : Nat) (p : Fin 4) (c : C2 d)
    (alpha : Fin (Params.q2 d)) (gamma : C1 d) :
    M3 d (p, c) (M3_diagCol d alpha gamma) =
      M1 d (S2fam d c alpha) gamma := by
  rfl

theorem M3_diagCol_exact_M1_of_fiber
    (d : Nat) (p : Fin 4) (c : C2 d)
    (alpha : Fin (Params.q2 d)) (gamma : C1 d) (r : R1 d)
    (hc : S2fam d c alpha = r) :
    M3 d (p, c) (M3_diagCol d alpha gamma) = M1 d r gamma := by
  rw [M3_diagCol_exact_M1, hc]

theorem M3_C2_fiber_cover_of_dense
    (d : Nat) (hchk : Checklist d)
    (S : Finset (C2 d))
    (hS :
      (1 - 8 * Params.h2 d) * (Fintype.card (C2 d) : Real) <=
        (S.card : Real))
    (alpha : Fin (Params.q2 d)) :
    S.image (fun c : C2 d => S2fam d c alpha) =
      (Finset.univ : Finset (R1 d)) := by
  classical
  have hLpos_nat : 0 < L2 d :=
    L2_pos d hchk.t2_le_q2 hchk.one_le_q1
  have hLpos : 0 < (L2 d : Real) := by
    exact_mod_cast hLpos_nat
  have hcardR :
      (Fintype.card (Prod (Fin (Params.q1 d)) (Fin 1)) : Real) =
        (Params.q1 d : Real) := by
    simp
  have hthreshold :
      (1 -
          (1 - epsQT (Params.q2 d) (Params.t2 d)) /
            (Fintype.card (Prod (Fin (Params.q1 d)) (Fin 1)) : Real)) *
          (L2 d : Real) <
        (S.card : Real) := by
    have hstrict :
        (1 -
            (1 - epsQT (Params.q2 d) (Params.t2 d)) /
              (Fintype.card (Prod (Fin (Params.q1 d)) (Fin 1)) : Real)) *
            (L2 d : Real) <
          (1 - 8 * Params.h2 d) * (L2 d : Real) := by
      rw [hcardR]
      nlinarith [hchk.dens_fiber_survival, hLpos]
    have hSdense :
        (1 - 8 * Params.h2 d) * (L2 d : Real) <=
          (S.card : Real) := by
      simpa [C2] using hS
    exact lt_of_lt_of_le hstrict hSdense
  exact
    (C2_fiber_survival d hchk.t2_le_q2 hchk.one_le_q1 S hthreshold
      alpha).2

structure M3BinDenseReindex
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBranch p).rows})
    (C : Finset {b // b ∈ (binBranch p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d) where
  rowEquiv : M2DenseRows d ≃ {b // b ∈ C}
  colEquiv : M2DenseCols d Sdense ≃ {a // a ∈ R}
  game_eq :
    forall a b,
      subgame (M3 d) (binBranch p).rows (binBranch p).cols
          (colEquiv b).val (rowEquiv a).val =
        M2DenseGame d hqcast Sdense a b

noncomputable def M3_bin_dense_protocol
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBranch p).rows})
    (C : Finset {b // b ∈ (binBranch p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (htr : M3BinDenseReindex d P binBranch p Sdense R C hqcast) :
    Protocol (M2DenseRows d) (M2DenseCols d Sdense) Bool :=
  Protocol.reindex htr.rowEquiv htr.colEquiv
    (Protocol.restrictSub C R
      (Protocol.swap (Protocol.restrict R C (binBranch p).residual)))

theorem M3_bin_dense_protocol_computes
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBranch p).rows})
    (C : Finset {b // b ∈ (binBranch p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (htr : M3BinDenseReindex d P binBranch p Sdense R C hqcast) :
    (M3_bin_dense_protocol d P binBranch p Sdense R C hqcast htr).Computes
      (M2DenseGame d hqcast Sdense) := by
  intro a b
  unfold M3_bin_dense_protocol
  rw [Protocol.eval_reindex]
  rw [Protocol.eval_restrictSub]
  rw [Protocol.eval_swap]
  rw [Protocol.eval_restrict_of_mem R C (binBranch p).residual
    (htr.colEquiv b).property (htr.rowEquiv a).property]
  calc
    (binBranch p).residual.eval (htr.colEquiv b).val (htr.rowEquiv a).val =
        subgame (M3 d) (binBranch p).rows (binBranch p).cols
          (htr.colEquiv b).val (htr.rowEquiv a).val := by
      exact (binBranch p).residual_computes
        (htr.colEquiv b).val (htr.rowEquiv a).val
    _ = M2DenseGame d hqcast Sdense a b := htr.game_eq a b

theorem M3_bin_dense_protocol_cost_le
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBranch p).rows})
    (C : Finset {b // b ∈ (binBranch p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hcost : P.cost <= D (M2 d) + 2)
    (htr : M3BinDenseReindex d P binBranch p Sdense R C hqcast) :
    (M3_bin_dense_protocol d P binBranch p Sdense R C hqcast htr).cost <=
      D (M2 d) := by
  unfold M3_bin_dense_protocol
  rw [Protocol.cost_reindex]
  rw [Protocol.cost_restrictSub]
  rw [Protocol.cost_swap]
  exact le_trans
    (Protocol.cost_restrict_le R C (binBranch p).residual)
    (M3_binResidual_cost_le_M2 d P binBranch hcost p)

theorem M3_bin_dense_alpha_data_of_reindex
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBranch p).rows})
    (C : Finset {b // b ∈ (binBranch p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hStage2 :
      forall (Sdense' : Finset (C2 d))
        (Pdense :
          Protocol (M2DenseRows d) (M2DenseCols d Sdense') Bool),
          (1 - 8 * Params.h2 d) * (L2 d : Real) <=
              (Sdense'.card : Real) ->
          Pdense.Computes (M2DenseGame d hqcast Sdense') ->
          Pdense.cost <= D (M2 d) ->
          Nonempty
            (M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense'
              Pdense))
    (hSdense :
      (1 - 8 * Params.h2 d) * (L2 d : Real) <=
        (Sdense.card : Real))
    (hcost : P.cost <= D (M2 d) + 2)
    (htr : M3BinDenseReindex d P binBranch p Sdense R C hqcast) :
    Nonempty
      (M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
        (M3_bin_dense_protocol d P binBranch p Sdense R C hqcast htr)) := by
  exact
    hStage2 Sdense
      (M3_bin_dense_protocol d P binBranch p Sdense R C hqcast htr)
      hSdense
      (M3_bin_dense_protocol_computes d P binBranch p Sdense R C hqcast htr)
      (M3_bin_dense_protocol_cost_le d P binBranch p Sdense R C hqcast
        hcost htr)

-- CLAIM-END aux:m3-transport

-- CLAIM-BEGIN aux:m3-binreindex-witness

noncomputable def equivOfInjectiveImage
    {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A -> B) (hf : Function.Injective f) :
    A ≃ {b // b ∈ (Finset.univ : Finset A).image f} where
  toFun := fun a =>
    ⟨f a, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
  invFun := fun b =>
    Classical.choose (Finset.mem_image.mp b.property)
  left_inv := by
    intro a
    apply hf
    exact
      (Classical.choose_spec
        (Finset.mem_image.mp
          (show f a ∈ (Finset.univ : Finset A).image f from
            Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩))).2
  right_inv := by
    intro b
    apply Subtype.ext
    exact
      (Classical.choose_spec (Finset.mem_image.mp b.property)).2

noncomputable def M3_diagColBranch
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hdiag_mem : forall a : M2DenseRows d,
      M3_diagCol d (Fin.cast hqcast a.val.1) a.val.2 ∈
        (binBranch p).cols)
    (a : M2DenseRows d) : {b // b ∈ (binBranch p).cols} :=
  ⟨M3_diagCol d (Fin.cast hqcast a.val.1) a.val.2, hdiag_mem a⟩

theorem M3_diagColBranch_injective
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hdiag_mem : forall a : M2DenseRows d,
      M3_diagCol d (Fin.cast hqcast a.val.1) a.val.2 ∈
        (binBranch p).cols) :
    Function.Injective
      (M3_diagColBranch d P binBranch p hqcast hdiag_mem) := by
  intro a a' h
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  have hpoint := congrFun hval (0 : Fin 4)
  simp [M3_diagColBranch, M3_diagCol] at hpoint
  apply Prod.ext
  · apply Fin.ext
    exact congrArg Fin.val hpoint.1
  · exact hpoint.2

noncomputable def M3_survivorRowBranch
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (hrow_mem : forall c, c ∈ Sdense -> (p, c) ∈ (binBranch p).rows)
    (c : M2DenseCols d Sdense) : {a // a ∈ (binBranch p).rows} :=
  ⟨(p, c.val), hrow_mem c.val c.property⟩

theorem M3_survivorRowBranch_injective
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (hrow_mem : forall c, c ∈ Sdense -> (p, c) ∈ (binBranch p).rows) :
    Function.Injective
      (M3_survivorRowBranch d P binBranch p Sdense hrow_mem) := by
  intro c c' h
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  exact congrArg Prod.snd hval

noncomputable def M3_denseDiagCols
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hdiag_mem : forall a : M2DenseRows d,
      M3_diagCol d (Fin.cast hqcast a.val.1) a.val.2 ∈
        (binBranch p).cols) :
    Finset {b // b ∈ (binBranch p).cols} :=
  (Finset.univ : Finset (M2DenseRows d)).image
    (M3_diagColBranch d P binBranch p hqcast hdiag_mem)

noncomputable def M3_denseSurvivorRows
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (hrow_mem : forall c, c ∈ Sdense -> (p, c) ∈ (binBranch p).rows) :
    Finset {a // a ∈ (binBranch p).rows} :=
  (Finset.univ : Finset (M2DenseCols d Sdense)).image
    (M3_survivorRowBranch d P binBranch p Sdense hrow_mem)

noncomputable def M3_binDenseReindex_of_memberships
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hrow_mem : forall c, c ∈ Sdense -> (p, c) ∈ (binBranch p).rows)
    (hdiag_mem : forall a : M2DenseRows d,
      M3_diagCol d (Fin.cast hqcast a.val.1) a.val.2 ∈
        (binBranch p).cols) :
    M3BinDenseReindex d P binBranch p Sdense
      (M3_denseSurvivorRows d P binBranch p Sdense hrow_mem)
      (M3_denseDiagCols d P binBranch p hqcast hdiag_mem) hqcast where
  rowEquiv :=
    equivOfInjectiveImage
      (M3_diagColBranch d P binBranch p hqcast hdiag_mem)
      (M3_diagColBranch_injective d P binBranch p hqcast hdiag_mem)
  colEquiv :=
    equivOfInjectiveImage
      (M3_survivorRowBranch d P binBranch p Sdense hrow_mem)
      (M3_survivorRowBranch_injective d P binBranch p Sdense hrow_mem)
  game_eq := by
    intro a b
    change
      M3 d (p, b.val)
          (M3_diagCol d (Fin.cast hqcast a.val.1) a.val.2) =
        M1 d (S2fam d b.val (Fin.cast hqcast a.val.1)) a.val.2
    rw [M3_diagCol_exact_M1]

-- CLAIM-END aux:m3-binreindex-witness

-- CLAIM-BEGIN aux:m3-binbranch-char

theorem Protocol.mkBranchAt_of_rowPrefix_rows
    {A B : Type*} [Fintype A] [Fintype B]
    (P : Protocol A B Bool) (G : A -> B -> Bool)
    (t : Nat) (j : Fin (2 ^ t))
    (hrow : Protocol.FirstKRowBitsOn
      (Finset.univ : Finset A) (Finset.univ : Finset B) t P)
    (hP : P.Computes G)
    (hrows : (Protocol.rowPrefixRows t P j).Nonempty)
    (hcols : (Finset.univ : Finset B).Nonempty) :
    (Protocol.mkBranchAt_of_rowPrefix P G t j hrow hP hrows hcols).rows =
      Protocol.rowPrefixRows t P j := rfl

theorem Protocol.mkBranchAt_of_rowPrefix_cols
    {A B : Type*} [Fintype A] [Fintype B]
    (P : Protocol A B Bool) (G : A -> B -> Bool)
    (t : Nat) (j : Fin (2 ^ t))
    (hrow : Protocol.FirstKRowBitsOn
      (Finset.univ : Finset A) (Finset.univ : Finset B) t P)
    (hP : P.Computes G)
    (hrows : (Protocol.rowPrefixRows t P j).Nonempty)
    (hcols : (Finset.univ : Finset B).Nonempty) :
    (Protocol.mkBranchAt_of_rowPrefix P G t j hrow hP hrows hcols).cols =
      (Finset.univ : Finset B) := rfl

private theorem M3_bin_row_fiber_card_eq_sum_label
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool) (i : Fin 4) :
    ((Finset.univ : Finset (Fin 4 × C2 d)).filter
        (fun p => p.1 = i)).card =
      Finset.sum (Finset.univ : Finset (Fin (2 ^ 2)))
        (fun j =>
          ((Finset.univ : Finset (Fin 4 × C2 d)).filter
            (fun p => Protocol.prefixCodeRaw 2 P p = j /\ p.1 = i)).card) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin 4 × C2 d)).filter
      (fun p => p.1 = i))
    (t := (Finset.univ : Finset (Fin (2 ^ 2))))
    (f := fun p : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P p)
    (by intro a _; exact Finset.mem_univ (Protocol.prefixCodeRaw 2 P a))
  simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using h

private theorem M3_bin_row_fiber_card (d : Nat) (i : Fin 4) :
    ((Finset.univ : Finset (Fin 4 × C2 d)).filter
        (fun p => p.1 = i)).card =
      Fintype.card (C2 d) := by
  classical
  rw [<- Finset.card_univ]
  refine Finset.card_bij (fun p _hp => p.2) ?hmem ?hinj ?hsurj
  · intro p _hp
    exact Finset.mem_univ p.2
  · intro p hp q hq hpq
    rw [Finset.mem_filter] at hp hq
    rcases hp with ⟨_hpR, hpfirst⟩
    rcases hq with ⟨_hqR, hqfirst⟩
    cases p with
    | mk pi px =>
        cases q with
        | mk qi qx =>
            simp only at hpq hpfirst hqfirst
            subst px
            subst pi
            subst qi
            rfl
  · intro x _hx
    refine ⟨(i, x), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩

theorem M3Bin_alphaOfCode_surj_on_Q
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hNW :
      NoWasteConclusion
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        (Fintype.card (C2 d))
        (M3_rowLoss d))
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d)) :
    Protocol.alphaOfCode_surj_on_Q
      (Finset.univ : Finset (Fin 4))
      (Finset.univ : Finset (Fin 4 × C2 d))
      (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
      hNW (fun j : Fin (2 ^ 2) => j) := by
  classical
  intro i hi
  by_contra hnone
  have hnot :
      forall j : Fin (2 ^ 2),
        Protocol.alphaOfCode
          (Finset.univ : Finset (Fin 4))
          (Finset.univ : Finset (Fin 4 × C2 d))
          (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
          hNW (fun j : Fin (2 ^ 2) => j) j ≠ i := by
    intro j hji
    exact hnone ⟨j, hji⟩
  have hlt :
      forall j : Fin (2 ^ 2),
        ((Finset.univ : Finset (Fin 4 × C2 d)).filter
          (fun p => Protocol.prefixCodeRaw 2 P p = j /\ p.1 = i)).card <
            M3_rowLoss d := by
    intro j
    have hspec :=
      Protocol.alphaOfCode_spec
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        hNW (fun j : Fin (2 ^ 2) => j) j
    exact hspec.2.2 i hi (by
      intro hia
      exact hnot j hia.symm)
  have hnonempty :
      (Finset.univ : Finset (Fin (2 ^ 2))).Nonempty := by
    exact ⟨⟨0, by norm_num⟩, Finset.mem_univ _⟩
  have hsum_lt :
      Finset.sum (Finset.univ : Finset (Fin (2 ^ 2)))
        (fun j =>
          ((Finset.univ : Finset (Fin 4 × C2 d)).filter
            (fun p => Protocol.prefixCodeRaw 2 P p = j /\ p.1 = i)).card)
        <
      Finset.sum (Finset.univ : Finset (Fin (2 ^ 2))) (fun _j => M3_rowLoss d) := by
    exact Finset.sum_lt_sum_of_nonempty hnonempty
      (by intro j _hj; exact hlt j)
  have hsum_loss :
      Finset.sum (Finset.univ : Finset (Fin (2 ^ 2)))
        (fun _j => M3_rowLoss d) =
        4 * M3_rowLoss d := by
    simp [Finset.sum_const]
  have hrow_sum := M3_bin_row_fiber_card_eq_sum_label d P i
  have hrow_card := M3_bin_row_fiber_card d i
  have hN_eq_sum :
      Fintype.card (C2 d) =
        Finset.sum (Finset.univ : Finset (Fin (2 ^ 2)))
          (fun j =>
            ((Finset.univ : Finset (Fin 4 × C2 d)).filter
              (fun p => Protocol.prefixCodeRaw 2 P p = j /\ p.1 = i)).card) := by
    exact hrow_card.symm.trans hrow_sum
  have hN_lt : Fintype.card (C2 d) < 4 * M3_rowLoss d := by
    rw [hN_eq_sum, <- hsum_loss]
    exact hsum_lt
  exact (not_lt_of_ge (Nat.le_of_lt hgap)) hN_lt

noncomputable def M3_codeOfBin
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hNW :
      NoWasteConclusion
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        (Fintype.card (C2 d))
        (M3_rowLoss d))
    (hsurj :
      Protocol.alphaOfCode_surj_on_Q
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        hNW (fun j : Fin (2 ^ 2) => j))
    (p : Fin 4) : Fin (2 ^ 2) :=
  Protocol.codeOfAlpha
    (Finset.univ : Finset (Fin 4))
    (Finset.univ : Finset (Fin 4 × C2 d))
    (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
    hNW (fun j : Fin (2 ^ 2) => j) hsurj p (by simp)

theorem M3_alphaOf_codeOfBin
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hNW :
      NoWasteConclusion
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        (Fintype.card (C2 d))
        (M3_rowLoss d))
    (hsurj :
      Protocol.alphaOfCode_surj_on_Q
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        hNW (fun j : Fin (2 ^ 2) => j))
    (p : Fin 4) :
    Protocol.alphaOfCode
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        hNW (fun j : Fin (2 ^ 2) => j)
        (M3_codeOfBin d P hNW hsurj p) = p := by
  unfold M3_codeOfBin
  exact
    Protocol.alphaOf_codeOfAlpha
      (Finset.univ : Finset (Fin 4))
      (Finset.univ : Finset (Fin 4 × C2 d))
      (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
      hNW (fun j : Fin (2 ^ 2) => j) hsurj p (by simp)

noncomputable def M3_binSurvivors
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hNW :
      NoWasteConclusion
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        (Fintype.card (C2 d))
        (M3_rowLoss d))
    (hsurj :
      Protocol.alphaOfCode_surj_on_Q
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        hNW (fun j : Fin (2 ^ 2) => j))
    (p : Fin 4) : Finset (C2 d) :=
  Protocol.Yalpha
    (Finset.univ : Finset (Fin 4))
    (Finset.univ : Finset (Fin 4 × C2 d))
    (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
    hNW (fun j : Fin (2 ^ 2) => j) hsurj p (by simp)

theorem M3_rowPrefixRows_nonempty_of_noWaste
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hNW :
      NoWasteConclusion
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        (Fintype.card (C2 d))
        (M3_rowLoss d))
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d))
    (j : Fin (2 ^ 2)) :
    (Protocol.rowPrefixRows 2 P j).Nonempty := by
  classical
  let alpha :=
    Protocol.alphaOfCode
      (Finset.univ : Finset (Fin 4))
      (Finset.univ : Finset (Fin 4 × C2 d))
      (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
      hNW (fun j : Fin (2 ^ 2) => j) j
  have hspec :=
    Protocol.alphaOfCode_spec
      (Finset.univ : Finset (Fin 4))
      (Finset.univ : Finset (Fin 4 × C2 d))
      (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
      hNW (fun j : Fin (2 ^ 2) => j) j
  have hlower_pos :
      0 < Fintype.card (C2 d) -
        (((Finset.univ : Finset (Fin 4)).card - 1) * M3_rowLoss d) := by
    have hle :
        (((Finset.univ : Finset (Fin 4)).card - 1) * M3_rowLoss d) <=
          4 * M3_rowLoss d := by
      simp
      omega
    exact Nat.sub_pos_of_lt (lt_of_le_of_lt hle hgap)
  have hcard_pos :
      0 <
        ((Finset.univ : Finset (Fin 4 × C2 d)).filter
          (fun p => Protocol.prefixCodeRaw 2 P p = j /\ p.1 = alpha)).card :=
    lt_of_lt_of_le hlower_pos hspec.2.1
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard_pos
  rw [Finset.mem_filter] at hp
  rcases hp with ⟨_hpR, hlabel, _halpha⟩
  refine ⟨p, ?_⟩
  rw [Protocol.rowPrefixRows, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hlabel⟩

theorem M3_binSurvivors_mem_code
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hNW :
      NoWasteConclusion
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        (Fintype.card (C2 d))
        (M3_rowLoss d))
    (hsurj :
      Protocol.alphaOfCode_surj_on_Q
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        hNW (fun j : Fin (2 ^ 2) => j))
    (p : Fin 4) (c : C2 d)
    (hc : c ∈ M3_binSurvivors d P hNW hsurj p) :
    Protocol.prefixCodeRaw 2 P (p, c) =
      M3_codeOfBin d P hNW hsurj p := by
  classical
  change c ∈
    ((Finset.univ : Finset (C2 d)).filter
      (fun x =>
        (Protocol.alphaOfCode
          (Finset.univ : Finset (Fin 4))
          (Finset.univ : Finset (Fin 4 × C2 d))
          (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
          hNW (fun j : Fin (2 ^ 2) => j)
          (M3_codeOfBin d P hNW hsurj p), x) ∈
            (Finset.univ : Finset (Fin 4 × C2 d)) /\
        Protocol.prefixCodeRaw 2 P
          (Protocol.alphaOfCode
            (Finset.univ : Finset (Fin 4))
            (Finset.univ : Finset (Fin 4 × C2 d))
            (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
            hNW (fun j : Fin (2 ^ 2) => j)
            (M3_codeOfBin d P hNW hsurj p), x) =
              M3_codeOfBin d P hNW hsurj p)) at hc
  have hmem := Finset.mem_filter.mp hc
  have halpha := M3_alphaOf_codeOfBin d P hNW hsurj p
  have hlabel := hmem.2.2
  rw [halpha] at hlabel
  exact hlabel

noncomputable def M3_binBranch
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hsep : M3SeparationConclusion d P)
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d))
    (hC3 : (Finset.univ : Finset (C3 d)).Nonempty)
    (p : Fin 4) : Protocol.BranchAt P (M3 d) 2 :=
  let hsurj :=
    M3Bin_alphaOfCode_surj_on_Q d P hsep.dominant_bins hgap
  Protocol.mkBranchAt_of_rowPrefix P (M3 d) 2
    (M3_codeOfBin d P hsep.dominant_bins hsurj p)
    hsep.first_row_bits hP
    (M3_rowPrefixRows_nonempty_of_noWaste d P hsep.dominant_bins hgap
      (M3_codeOfBin d P hsep.dominant_bins hsurj p))
    hC3

theorem M3_binBranch_rows
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hsep : M3SeparationConclusion d P)
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d))
    (hC3 : (Finset.univ : Finset (C3 d)).Nonempty)
    (p : Fin 4) :
    (M3_binBranch d P hP hsep hgap hC3 p).rows =
      Protocol.rowPrefixRows 2 P
        (M3_codeOfBin d P hsep.dominant_bins
          (M3Bin_alphaOfCode_surj_on_Q d P hsep.dominant_bins hgap) p) := by
  rfl

theorem M3_binBranch_cols
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hsep : M3SeparationConclusion d P)
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d))
    (hC3 : (Finset.univ : Finset (C3 d)).Nonempty)
    (p : Fin 4) :
    (M3_binBranch d P hP hsep hgap hC3 p).cols =
      (Finset.univ : Finset (C3 d)) := by
  rfl

theorem M3_binBranch_row_mem
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hsep : M3SeparationConclusion d P)
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d))
    (hC3 : (Finset.univ : Finset (C3 d)).Nonempty)
    (p : Fin 4) :
    forall c, c ∈ M3_binSurvivors d P hsep.dominant_bins
        (M3Bin_alphaOfCode_surj_on_Q d P hsep.dominant_bins hgap) p ->
      (p, c) ∈ (M3_binBranch d P hP hsep hgap hC3 p).rows := by
  intro c hc
  rw [M3_binBranch_rows]
  rw [Protocol.rowPrefixRows, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, M3_binSurvivors_mem_code d P
    hsep.dominant_bins
    (M3Bin_alphaOfCode_surj_on_Q d P hsep.dominant_bins hgap)
    p c hc⟩

theorem M3_binBranch_diag_mem
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hsep : M3SeparationConclusion d P)
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d))
    (hC3 : (Finset.univ : Finset (C3 d)).Nonempty)
    (p : Fin 4) (hqcast : 2 ^ M2DenseDepth d = Params.q2 d) :
    forall a : M2DenseRows d,
      M3_diagCol d (Fin.cast hqcast a.val.1) a.val.2 ∈
        (M3_binBranch d P hP hsep hgap hC3 p).cols := by
  intro a
  rw [M3_binBranch_cols]
  exact Finset.mem_univ _

theorem M3_C3_univ_nonempty (d : Nat) (hchk : Checklist d) :
    (Finset.univ : Finset (C3 d)).Nonempty := by
  classical
  have hL1 : 0 < L1 d := L1_pos d hchk.t1_le_q1_add_five
  have hq2 : 0 < Params.q2 d := Params.q2_pos d
  let r : R2 d := (⟨0, hq2⟩, ⟨0, hL1⟩)
  exact ⟨fun _ => r, Finset.mem_univ _⟩

theorem M3_binSurvivors_card_ge_nat
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hNW :
      NoWasteConclusion
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        (Fintype.card (C2 d))
        (M3_rowLoss d))
    (hsurj :
      Protocol.alphaOfCode_surj_on_Q
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        hNW (fun j : Fin (2 ^ 2) => j))
    (p : Fin 4) :
    Fintype.card (C2 d) - 3 * M3_rowLoss d <=
      (M3_binSurvivors d P hNW hsurj p).card := by
  have h :=
    Protocol.Yalpha_card_ge
      (Finset.univ : Finset (Fin 4))
      (Finset.univ : Finset (Fin 4 × C2 d))
      (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
      hNW (fun j : Fin (2 ^ 2) => j) hsurj p (by simp)
  simpa [M3_binSurvivors] using h

theorem M3_binSurvivors_dense_raw
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hNW :
      NoWasteConclusion
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        (Fintype.card (C2 d))
        (M3_rowLoss d))
    (hsurj :
      Protocol.alphaOfCode_surj_on_Q
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        hNW (fun j : Fin (2 ^ 2) => j))
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d))
    (p : Fin 4) :
    (Fintype.card (C2 d) : Real) - 3 * (M3_rowLoss d : Real) <=
      ((M3_binSurvivors d P hNW hsurj p).card : Real) := by
  have hnat := M3_binSurvivors_card_ge_nat d P hNW hsurj p
  have hle3 : 3 * M3_rowLoss d <= Fintype.card (C2 d) := by
    omega
  have hcast :
      ((Fintype.card (C2 d) - 3 * M3_rowLoss d : Nat) : Real) <=
        ((M3_binSurvivors d P hNW hsurj p).card : Real) := by
    exact_mod_cast hnat
  rw [Nat.cast_sub hle3] at hcast
  simpa [Nat.cast_mul] using hcast

theorem M3_binSurvivors_dense
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hchk : Checklist d)
    (hNW :
      NoWasteConclusion
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        (Fintype.card (C2 d))
        (M3_rowLoss d))
    (hsurj :
      Protocol.alphaOfCode_surj_on_Q
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d => Protocol.prefixCodeRaw 2 P r)
        hNW (fun j : Fin (2 ^ 2) => j))
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d))
    (p : Fin 4) :
    (1 - 8 * Params.h2 d) * (Fintype.card (C2 d) : Real) <=
      ((M3_binSurvivors d P hNW hsurj p).card : Real) := by
  have hraw := M3_binSurvivors_dense_raw d P hNW hsurj hgap p
  have hcard : (Fintype.card (C2 d) : Real) = (L2 d : Real) := by
    simp [C2]
  have hloss_eq :
      M3_rowLoss d =
        Nat.ceil ((2 : Real) ^ (-(Params.b2 d : Int) + 1) * (L2 d : Real)) := by
    unfold M3_rowLoss C2
    rw [Fintype.card_fin]
    rw [two_zpow_neg_nat_add_one_eq_rpow_one_sub_nat]
  have hthree :
      3 * (M3_rowLoss d : Real) <= 8 * Params.h2 d * (L2 d : Real) := by
    simpa [hloss_eq, Params.h2] using hchk.dens_stage3_rowloss
  rw [hcard] at hraw ⊢
  nlinarith

noncomputable def M3_binDenseReindex_for_binBranch
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hsep : M3SeparationConclusion d P)
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d))
    (hC3 : (Finset.univ : Finset (C3 d)).Nonempty)
    (p : Fin 4) (hqcast : 2 ^ M2DenseDepth d = Params.q2 d) :
    let hsurj := M3Bin_alphaOfCode_surj_on_Q d P hsep.dominant_bins hgap
    M3BinDenseReindex d P (M3_binBranch d P hP hsep hgap hC3) p
      (M3_binSurvivors d P hsep.dominant_bins hsurj p)
      (M3_denseSurvivorRows d P (M3_binBranch d P hP hsep hgap hC3) p
        (M3_binSurvivors d P hsep.dominant_bins hsurj p)
        (M3_binBranch_row_mem d P hP hsep hgap hC3 p))
      (M3_denseDiagCols d P (M3_binBranch d P hP hsep hgap hC3) p hqcast
        (M3_binBranch_diag_mem d P hP hsep hgap hC3 p hqcast))
      hqcast := by
  classical
  dsimp
  exact
    M3_binDenseReindex_of_memberships d P
      (M3_binBranch d P hP hsep hgap hC3) p
      (M3_binSurvivors d P hsep.dominant_bins
        (M3Bin_alphaOfCode_surj_on_Q d P hsep.dominant_bins hgap) p)
      hqcast
      (M3_binBranch_row_mem d P hP hsep hgap hC3 p)
      (M3_binBranch_diag_mem d P hP hsep hgap hC3 p hqcast)

theorem M3_bin_dense_alpha_data_for_binBranch
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hsep : M3SeparationConclusion d P)
    (hchk : Checklist d)
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d))
    (hC3 : (Finset.univ : Finset (C3 d)).Nonempty)
    (p : Fin 4) (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hStage2 :
      forall (Sdense : Finset (C2 d))
        (Pdense : Protocol (M2DenseRows d) (M2DenseCols d Sdense) Bool),
          (1 - 8 * Params.h2 d) * (L2 d : Real) <=
              (Sdense.card : Real) ->
          Pdense.Computes (M2DenseGame d hqcast Sdense) ->
          Pdense.cost <= D (M2 d) ->
          Nonempty
            (M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
              Pdense))
    (hcost : P.cost <= D (M2 d) + 2) :
    let hsurj := M3Bin_alphaOfCode_surj_on_Q d P hsep.dominant_bins hgap
    let Sdense := M3_binSurvivors d P hsep.dominant_bins hsurj p
    let hrow_mem := M3_binBranch_row_mem d P hP hsep hgap hC3 p
    let hdiag_mem := M3_binBranch_diag_mem d P hP hsep hgap hC3 p hqcast
    let htr := M3_binDenseReindex_for_binBranch d P hP hsep hgap hC3 p hqcast
    Nonempty
      (M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
        (M3_bin_dense_protocol d P (M3_binBranch d P hP hsep hgap hC3) p
          Sdense
          (M3_denseSurvivorRows d P (M3_binBranch d P hP hsep hgap hC3) p
            Sdense hrow_mem)
          (M3_denseDiagCols d P (M3_binBranch d P hP hsep hgap hC3) p hqcast
            hdiag_mem)
          hqcast htr)) := by
  classical
  dsimp
  exact
    M3_bin_dense_alpha_data_of_reindex d P
      (M3_binBranch d P hP hsep hgap hC3) p
      (M3_binSurvivors d P hsep.dominant_bins
        (M3Bin_alphaOfCode_surj_on_Q d P hsep.dominant_bins hgap) p)
      (M3_denseSurvivorRows d P (M3_binBranch d P hP hsep hgap hC3) p
        (M3_binSurvivors d P hsep.dominant_bins
          (M3Bin_alphaOfCode_surj_on_Q d P hsep.dominant_bins hgap) p)
        (M3_binBranch_row_mem d P hP hsep hgap hC3 p))
      (M3_denseDiagCols d P (M3_binBranch d P hP hsep hgap hC3) p hqcast
        (M3_binBranch_diag_mem d P hP hsep hgap hC3 p hqcast))
      hqcast hStage2
      (by
        simpa [C2] using
          M3_binSurvivors_dense d P hchk hsep.dominant_bins
            (M3Bin_alphaOfCode_surj_on_Q d P hsep.dominant_bins hgap)
            hgap p)
      hcost
      (M3_binDenseReindex_for_binBranch d P hP hsep hgap hC3 p hqcast)

-- CLAIM-END aux:m3-binbranch-char

-- CLAIM-BEGIN aux:m3-package

noncomputable def M3_fiber_cRep
    (d : Nat) (S : Finset (C2 d)) (alpha : Fin (Params.q2 d))
    (hcover :
      S.image (fun c : C2 d => S2fam d c alpha) =
        (Finset.univ : Finset (R1 d)))
    (r : R1 d) : C2 d :=
  Classical.choose
    (Finset.mem_image.mp
      (by
        rw [hcover]
        exact Finset.mem_univ r))

theorem M3_fiber_cRep_spec
    (d : Nat) (S : Finset (C2 d)) (alpha : Fin (Params.q2 d))
    (hcover :
      S.image (fun c : C2 d => S2fam d c alpha) =
        (Finset.univ : Finset (R1 d)))
    (r : R1 d) :
    M3_fiber_cRep d S alpha hcover r ∈ S ∧
      S2fam d (M3_fiber_cRep d S alpha hcover r) alpha = r := by
  classical
  unfold M3_fiber_cRep
  let himage :
      r ∈ S.image (fun c : C2 d => S2fam d c alpha) := by
    rw [hcover]
    exact Finset.mem_univ r
  exact Classical.choose_spec (Finset.mem_image.mp himage)

theorem M3_fiber_cRep_mem
    (d : Nat) (S : Finset (C2 d)) (alpha : Fin (Params.q2 d))
    (hcover :
      S.image (fun c : C2 d => S2fam d c alpha) =
        (Finset.univ : Finset (R1 d)))
    (r : R1 d) :
    M3_fiber_cRep d S alpha hcover r ∈ S :=
  (M3_fiber_cRep_spec d S alpha hcover r).1

theorem M3_fiber_cRep_eval
    (d : Nat) (S : Finset (C2 d)) (alpha : Fin (Params.q2 d))
    (hcover :
      S.image (fun c : C2 d => S2fam d c alpha) =
        (Finset.univ : Finset (R1 d)))
    (r : R1 d) :
    S2fam d (M3_fiber_cRep d S alpha hcover r) alpha = r :=
  (M3_fiber_cRep_spec d S alpha hcover r).2

structure M3PackageSyncBridge
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (Y : Fin 4 -> Fin (Params.q2 d) -> Finset (C1 d)) where
  sync : M3AmbientSyncData d P binBranch
  diag_cols :
    forall p alpha gamma,
      gamma ∈ Y p alpha ->
        M3_diagCol d alpha gamma ∈ (sync.dimBranch p alpha).cols

theorem M3_fuzzy_leaves_package_from_sync_bridge
    (d : Nat) (hchk : Checklist d)
    (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hcost : P.cost <= D (M2 d) + 2)
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hsep : M3SeparationConclusion d P)
    (hStage2 :
      forall (Sdense : Finset (C2 d))
        (Pdense : Protocol (M2DenseRows d) (M2DenseCols d Sdense) Bool),
          (1 - 8 * Params.h2 d) * (L2 d : Real) <=
              (Sdense.card : Real) ->
          Pdense.Computes (M2DenseGame d hqcast Sdense) ->
          Pdense.cost <= D (M2 d) ->
          Nonempty
            (M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
              Pdense))
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d))
    (hC3 : (Finset.univ : Finset (C3 d)).Nonempty)
    (hbridge :
      M3PackageSyncBridge d P
        (M3_binBranch d P hP hsep hgap hC3)
        (fun p alpha =>
          (Classical.choice
            (M3_bin_dense_alpha_data_for_binBranch d P hP hsep hchk hgap hC3
              p hqcast hStage2 hcost)).Yalpha alpha)) :
    M3FuzzyLeavesConclusion d P := by
  classical
  let hsurj := M3Bin_alphaOfCode_surj_on_Q d P hsep.dominant_bins hgap
  let binBranch := M3_binBranch d P hP hsep hgap hC3
  let S : Fin 4 -> Finset (C2 d) :=
    fun p => M3_binSurvivors d P hsep.dominant_bins hsurj p
  let alphaData :=
    fun p =>
      Classical.choice
        (M3_bin_dense_alpha_data_for_binBranch d P hP hsep hchk hgap hC3
          p hqcast hStage2 hcost)
  let Y : Fin 4 -> Fin (Params.q2 d) -> Finset (C1 d) :=
    fun p alpha => (alphaData p).Yalpha alpha
  let fiberCover :
      forall p alpha,
        (S p).image (fun c : C2 d => S2fam d c alpha) =
          (Finset.univ : Finset (R1 d)) := by
    intro p alpha
    exact
      M3_C2_fiber_cover_of_dense d hchk (S p)
        (by
          change
            (1 - 8 * Params.h2 d) * (Fintype.card (C2 d) : Real) <=
              ((M3_binSurvivors d P hsep.dominant_bins hsurj p).card : Real)
          exact M3_binSurvivors_dense d P hchk hsep.dominant_bins hsurj hgap p)
        alpha
  let cRep : Fin 4 -> Fin (Params.q2 d) -> R1 d -> C2 d :=
    fun p alpha r => M3_fiber_cRep d (S p) alpha (fiberCover p alpha) r
  refine ⟨
    { separation := hsep
      binBranch := binBranch
      dimBranch := hbridge.sync.dimBranch
      bin_sideTrace := ?_
      dim_sideTrace := hbridge.sync.dim_sideTrace
      dim_extends := hbridge.sync.dim_extends
      S := S
      Y := Y
      cRep := cRep
      bin_rows := ?_
      S_dense_raw := ?_
      S_dense := ?_
      Y_dense := ?_
      diag_cols := ?_
      fiber_cover := ?_
      cRep_mem := ?_
      cRep_eval := ?_
      exact_M1_copy := ?_ }⟩
  · intro p
    simp [binBranch, M3_binBranch, Protocol.mkBranchAt_of_rowPrefix]
  · intro p c hc
    change c ∈ M3_binSurvivors d P hsep.dominant_bins hsurj p at hc
    change (p, c) ∈ (M3_binBranch d P hP hsep hgap hC3 p).rows
    exact M3_binBranch_row_mem d P hP hsep hgap hC3 p c hc
  · intro p
    change
      (Fintype.card (C2 d) : Real) - 3 * (M3_rowLoss d : Real) <=
        ((M3_binSurvivors d P hsep.dominant_bins hsurj p).card : Real)
    exact M3_binSurvivors_dense_raw d P hsep.dominant_bins hsurj hgap p
  · intro p
    change
      (1 - 8 * Params.h2 d) * (Fintype.card (C2 d) : Real) <=
        ((M3_binSurvivors d P hsep.dominant_bins hsurj p).card : Real)
    exact M3_binSurvivors_dense d P hchk hsep.dominant_bins hsurj hgap p
  · intro p alpha
    exact (alphaData p).Yalpha_dense alpha
  · intro p alpha gamma hgamma
    exact hbridge.diag_cols p alpha gamma hgamma
  · intro p alpha
    exact fiberCover p alpha
  · intro p alpha r
    exact M3_fiber_cRep_mem d (S p) alpha (fiberCover p alpha) r
  · intro p alpha r
    exact M3_fiber_cRep_eval d (S p) alpha (fiberCover p alpha) r
  · intro p alpha r gamma hgamma
    exact
      M3_diagCol_exact_M1_of_fiber d p (cRep p alpha r) alpha gamma r
        (M3_fiber_cRep_eval d (S p) alpha (fiberCover p alpha) r)

-- CLAIM-END aux:m3-package

-- CLAIM-BEGIN aux:m3-package-final

noncomputable def M3_fuzzy_leaves_sync_bridge
    (d : Nat) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) (hchk : Checklist d)
    (hrobM2 :
      IsRobust (fun (c : C2 d) (r : R2 d) => M2 d r c)
        Params.delta (Params.b2 d))
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : Nat) <= Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hp1 : 2 ^ M2_T d <= 2 * M2_hard_seed_copies d)
    (hp2 : M2_hard_seed_copies d <= 2 ^ M2_T d)
    (hxseed_le_one : M2_hard_seed_rowDensity d <= 1)
    (hrow_threshold :
      Nat.ceil ((2 : Real) ^ (Nat.log 2 (Params.r2 d) : Nat) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : Real))
          <= Fintype.card (C1 d))
    (hseed_bridge : M2_hard_seed_columnDensity d <=
      Params.h2 d *
        (2 : Real) ^ (-((M2_T d + D (M1T d) : Nat) : Real)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hy_le_one : M1_stage2_terminal_density d <= 1)
    (hrowTerm : 9 * Params.t1 d <=
      16 * Nat.ceil ((Fintype.card (R1 d) : Real) *
        M1_stage2_terminal_density d))
    (hcolTerm : (2 : Real) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : Int))
        * (Fintype.card (C1 d) : Real) <=
      (Nat.ceil ((Fintype.card (C1 d) : Real) *
        ((2 : Real) ^ (-(Params.b1 d : Int)))) : Real))
    (hresidual_density : forall c, c <= M2_T d + D (M1T d) ->
      1 / 2 + Params.delta <=
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c /\
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c <= 1)
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hsigma0 : 0 < 1 - 8 * Params.h2 d)
    (hsigma1 : 1 - 8 * Params.h2 d <= 1)
    (hres_dense : IsColumnLossResilient (M1T d) (Params.b1 d : Real)
      (epsQT (Params.q2 d) (Params.t2 d))
      (Nat.log 2 (Params.q2 d)) (M2_T d) (1 - 8 * Params.h2 d))
    (hxseed_le_inv_r : M2_hard_seed_rowDensity d <=
      (2 : Real) ^ (-(Nat.log 2 (Params.r2 d) : Real)))
    (hseed_bridge_dense : M2_hard_seed_columnDensity d <=
      (1 - 8 * Params.h2 d) *
        (2 : Real) ^ (-((M2_T d + D (M1T d) : Nat) : Real)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hT1 : 1 <= M2_T d)
    (hgap_dense :
      2 ^ M2DenseDepth d *
        Nat.ceil ((2 : Real) ^ (1 - (Params.b1 d : Real)) *
          (Fintype.card (C1 d) : Real)) < Fintype.card (C1 d))
    (hraw : M2_hard_seed_to_h2prime_exp d)
    (hprime : M2_h2prime_bridge_exp d)
    (hy_three_fifths :
      forall c, c <= M2_T d + D (M1T d) ->
        (3 : Real) / 5 <=
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c)
    (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hcost : P.cost <= D (M2 d) + 2) : Type :=
  let hpartial :=
    M3_fuzzy_leaves_dense_alpha_partial d hpow hlog hchk hrobM2
      hm0_le hr2pow hp1 hp2 hxseed_le_one hrow_threshold hseed_bridge
      hy_le_one hrowTerm hcolTerm hresidual_density hqcast hsigma0
      hsigma1 hres_dense hxseed_le_inv_r hseed_bridge_dense hT1
      hgap_dense hraw hprime hy_three_fifths P hP hcost
  let hsep := hpartial.1
  let hStage2 := hpartial.2
  let hgap := M3_stage3_gap d hlog hchk
  let hC3 := M3_C3_univ_nonempty d hchk
  M3PackageSyncBridge d P
    (M3_binBranch d P hP hsep hgap hC3)
    (fun p alpha =>
      (Classical.choice
        (M3_bin_dense_alpha_data_for_binBranch d P hP hsep hchk hgap hC3
          p hqcast hStage2 hcost)).Yalpha alpha)

theorem M3_fuzzy_leaves_of_sync_bridge
    (d : Nat) (hd : 2 <= d) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) (hchk : Checklist d)
    (hrobM2 :
      IsRobust (fun (c : C2 d) (r : R2 d) => M2 d r c)
        Params.delta (Params.b2 d))
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : Nat) <= Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hp1 : 2 ^ M2_T d <= 2 * M2_hard_seed_copies d)
    (hp2 : M2_hard_seed_copies d <= 2 ^ M2_T d)
    (hxseed_le_one : M2_hard_seed_rowDensity d <= 1)
    (hrow_threshold :
      Nat.ceil ((2 : Real) ^ (Nat.log 2 (Params.r2 d) : Nat) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : Real))
          <= Fintype.card (C1 d))
    (hseed_bridge : M2_hard_seed_columnDensity d <=
      Params.h2 d *
        (2 : Real) ^ (-((M2_T d + D (M1T d) : Nat) : Real)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hy_le_one : M1_stage2_terminal_density d <= 1)
    (hrowTerm : 9 * Params.t1 d <=
      16 * Nat.ceil ((Fintype.card (R1 d) : Real) *
        M1_stage2_terminal_density d))
    (hcolTerm : (2 : Real) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : Int))
        * (Fintype.card (C1 d) : Real) <=
      (Nat.ceil ((Fintype.card (C1 d) : Real) *
        ((2 : Real) ^ (-(Params.b1 d : Int)))) : Real))
    (hresidual_density : forall c, c <= M2_T d + D (M1T d) ->
      1 / 2 + Params.delta <=
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c /\
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c <= 1)
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hsigma0 : 0 < 1 - 8 * Params.h2 d)
    (hsigma1 : 1 - 8 * Params.h2 d <= 1)
    (hres_dense : IsColumnLossResilient (M1T d) (Params.b1 d : Real)
      (epsQT (Params.q2 d) (Params.t2 d))
      (Nat.log 2 (Params.q2 d)) (M2_T d) (1 - 8 * Params.h2 d))
    (hxseed_le_inv_r : M2_hard_seed_rowDensity d <=
      (2 : Real) ^ (-(Nat.log 2 (Params.r2 d) : Real)))
    (hseed_bridge_dense : M2_hard_seed_columnDensity d <=
      (1 - 8 * Params.h2 d) *
        (2 : Real) ^ (-((M2_T d + D (M1T d) : Nat) : Real)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hT1 : 1 <= M2_T d)
    (hgap_dense :
      2 ^ M2DenseDepth d *
        Nat.ceil ((2 : Real) ^ (1 - (Params.b1 d : Real)) *
          (Fintype.card (C1 d) : Real)) < Fintype.card (C1 d))
    (hraw : M2_hard_seed_to_h2prime_exp d)
    (hprime : M2_h2prime_bridge_exp d)
    (hy_three_fifths :
      forall c, c <= M2_T d + D (M1T d) ->
        (3 : Real) / 5 <=
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c)
    (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hcost : P.cost <= D (M2 d) + 2)
    (hbridge :
      M3_fuzzy_leaves_sync_bridge d hpow hlog hchk hrobM2
        hm0_le hr2pow hp1 hp2 hxseed_le_one hrow_threshold hseed_bridge
        hy_le_one hrowTerm hcolTerm hresidual_density hqcast hsigma0
        hsigma1 hres_dense hxseed_le_inv_r hseed_bridge_dense hT1
        hgap_dense hraw hprime hy_three_fifths P hP hcost) :
    M3FuzzyLeavesConclusion d P := by
  classical
  let hpartial :=
    M3_fuzzy_leaves_dense_alpha_partial d hpow hlog hchk hrobM2
      hm0_le hr2pow hp1 hp2 hxseed_le_one hrow_threshold hseed_bridge
      hy_le_one hrowTerm hcolTerm hresidual_density hqcast hsigma0
      hsigma1 hres_dense hxseed_le_inv_r hseed_bridge_dense hT1
      hgap_dense hraw hprime hy_three_fifths P hP hcost
  exact
    M3_fuzzy_leaves_package_from_sync_bridge d hchk P hP hcost hqcast
      hpartial.1 hpartial.2 (M3_stage3_gap d hlog hchk)
      (M3_C3_univ_nonempty d hchk) hbridge

-- CLAIM-END aux:m3-package-final


-- CLAIM-BEGIN aux:m3-fuzzy-opus

/- Opus assembly for lem:MThreeFuzzyLeaves: the four load-bearing building
blocks toward `NPCC.M3_fuzzy_leaves`.  (1) the `restricted_col` transport from the
reindexed dense protocol's first-row-bits back to the ambient bin residual;
(2) the M1 dense-COLUMN-slice terminal floor a+1 (avoids both the full-C1 copy
trap and the Stage-4 vector machinery); (3) the dense-Yalpha hard-witness builder;
(4) the explicit sync-bridge assembler (sync + diag_cols) from the three per-bin
structural inputs.  Each compiles cleanly against the live Stage-3 surface. -/

namespace Protocol

variable {A B A' B' Z : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq A'] [DecidableEq B']

-- reverse reindex FirstKRowBits (from opus_probe_C, re-declared here)
theorem firstKRowBitsOn_of_reindex
    (e1 : A' ≃ A) (e2 : B' ≃ B) (P : Protocol A B Z) (k : Nat)
    (R' : Finset A') (C' : Finset B')
    (h : Protocol.FirstKRowBitsOn R' C' k (Protocol.reindex e1 e2 P)) :
    Protocol.FirstKRowBitsOn (R'.map e1.toEmbedding) (C'.map e2.toEmbedding) k P := by
  induction k generalizing R' C' P with
  | zero => trivial
  | succ k ih =>
      cases P with
      | leaf z =>
          simp only [Protocol.reindex, Protocol.FirstKRowBitsOn] at h ⊢
          rcases h with hR | hC
          · left; rw [hR]; simp
          · right; rw [hC]; simp
      | bNode b l r =>
          simp only [Protocol.reindex, Protocol.FirstKRowBitsOn] at h ⊢
          rcases h with hR | hC
          · left; rw [hR]; simp
          · right; rw [hC]; simp
      | aNode a l r =>
          simp only [Protocol.reindex, Protocol.FirstKRowBitsOn] at h ⊢
          refine ⟨?_, ?_⟩
          · have hl := ih (R' := R'.filter fun x => a (e1 x) = false) (C' := C') (P := l) h.1
            have hfilter :
                ((R'.filter fun x => a (e1 x) = false).map e1.toEmbedding) =
                  ((R'.map e1.toEmbedding).filter fun x => a x = false) := by
              ext x
              simp only [Finset.mem_map, Finset.mem_filter, Equiv.coe_toEmbedding]
              constructor
              · rintro ⟨y, ⟨hy, hya⟩, rfl⟩; exact ⟨⟨y, hy, rfl⟩, hya⟩
              · rintro ⟨⟨y, hy, rfl⟩, hya⟩; exact ⟨y, ⟨hy, hya⟩, rfl⟩
            rw [hfilter] at hl; exact hl
          · have hr := ih (R' := R'.filter fun x => a (e1 x) = true) (C' := C') (P := r) h.2
            have hfilter :
                ((R'.filter fun x => a (e1 x) = true).map e1.toEmbedding) =
                  ((R'.map e1.toEmbedding).filter fun x => a x = true) := by
              ext x
              simp only [Finset.mem_map, Finset.mem_filter, Equiv.coe_toEmbedding]
              constructor
              · rintro ⟨y, ⟨hy, hya⟩, rfl⟩; exact ⟨⟨y, hy, rfl⟩, hya⟩
              · rintro ⟨⟨y, hy, rfl⟩, hya⟩; exact ⟨y, ⟨hy, hya⟩, rfl⟩
            rw [hfilter] at hr; exact hr

theorem map_univ_equiv [Fintype A'] [Fintype A] (e : A' ≃ A) :
    ((Finset.univ : Finset A').map e.toEmbedding) = (Finset.univ : Finset A) := by
  ext a
  simp only [Finset.mem_map, Finset.mem_univ, Equiv.coe_toEmbedding, true_and, iff_true]
  exact ⟨e.symm a, by simp⟩

end Protocol

-- THE restricted_col TRANSPORT: from FirstKRowBitsOn univ univ m (reindex eA eB (restrictSub C R (swap Q0)))
-- to FirstKColBitsOn R C m Q0, where Q0 = restrict R C residual.
theorem M3_restricted_col_of_dense_first_row_bits
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (residual : Protocol X Y Bool)
    (R : Finset X) (C : Finset Y) (m : Nat)
    {A' B' : Type*} [Fintype A'] [Fintype B'] [DecidableEq A'] [DecidableEq B']
    (eA : A' ≃ {b // b ∈ C}) (eB : B' ≃ {a // a ∈ R})
    (hfrb :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset A') (Finset.univ : Finset B') m
        (Protocol.reindex eA eB
          (Protocol.restrictSub C R
            (Protocol.swap (Protocol.restrict R C residual))))) :
    Protocol.FirstKColBitsOn R C m (Protocol.restrict R C residual) := by
  classical
  -- step 1: reverse reindex → FirstKRowBitsOn univ univ m (restrictSub C R (swap (restrict R C residual)))
  have h1 := Protocol.firstKRowBitsOn_of_reindex eA eB
    (Protocol.restrictSub C R (Protocol.swap (Protocol.restrict R C residual)))
    m (Finset.univ : Finset A') (Finset.univ : Finset B') hfrb
  rw [Protocol.map_univ_equiv eA, Protocol.map_univ_equiv eB] at h1
  -- step 2: restrictSub peel → FirstKRowBitsOn C R m (swap (restrict R C residual))
  have h2 := Protocol.firstKRowBitsOn_of_restrictSub C R
    (Finset.univ : Finset {b // b ∈ C}) (Finset.univ : Finset {a // a ∈ R})
    m (Protocol.swap (Protocol.restrict R C residual)) h1
  have himgC : ((Finset.univ : Finset {b // b ∈ C}).image fun b => b.val) = C := by
    ext x
    constructor
    · intro hx; rcases Finset.mem_image.mp hx with ⟨y, _, rfl⟩; exact y.2
    · intro hx; exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
  have himgR : ((Finset.univ : Finset {a // a ∈ R}).image fun a => a.val) = R := by
    ext x
    constructor
    · intro hx; rcases Finset.mem_image.mp hx with ⟨y, _, rfl⟩; exact y.2
    · intro hx; exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
  rw [himgC, himgR] at h2
  -- h2 : FirstKRowBitsOn C R m (swap (restrict R C residual)) = FirstKColBitsOn R C m (restrict R C residual)
  exact h2

theorem M1_dense_column_subgame_floor
    (d : Nat) (hpow : IsPow2 d) (hlog : 64 <= Nat.log 2 d)
    (hchk : Checklist d)
    (Yalpha : Finset (C1 d))
    (hYdense : (1 - Params.eta2 d) * (Fintype.card (C1 d) : Real) <=
        (Yalpha.card : Real)) :
    Params.a d + 1 <= D (subgame (M1 d) (Finset.univ : Finset (R1 d)) Yalpha) := by
  classical
  have hd : 2 <= d := by
    obtain ⟨k, rfl⟩ := hpow
    have hk : 64 <= k := by simpa [log_two_pow] using hlog
    exact Nat.succ_le_of_lt (Nat.one_lt_two_pow (by omega : k ≠ 0))
  have hchk' : Params.t1 d <= Params.q1 d + 5 := Params.t1_le_q1_add_five hlog
  obtain ⟨hdiv, hTb, hRb, hgap⟩ := M1_low_column_stage2_gates hpow hlog
  -- r' = r1 setup (copied from M1_capacity_lower_canonical)
  have hr1pow : ∃ k, Params.r1 d = 2 ^ k := by
    have hqpow : Params.q1 d + 2 = 2 ^ Params.a d := (Params.two_pow_a hd).symm
    have hr1dvd : Params.r1 d ∣ 2 ^ Params.a d := by
      rw [hqpow.symm]; exact ⟨Params.t1 d, hdiv⟩
    obtain ⟨j, _hjle, hr1j⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hr1dvd
    exact ⟨j, hr1j⟩
  have hr1pos : 1 <= Params.r1 d := by
    obtain ⟨k, hk⟩ := hr1pow; rw [hk]; exact Nat.one_le_two_pow
  -- Column density: 2^(-(b1+log r2)) * |C1| <= |Yalpha| from dens_survive + Yalpha_dense
  have hcol : (2 : Real) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : Int))
        * (Fintype.card (C1 d) : Real) <= (Yalpha.card : Real) := by
    have hsurv : (2 : Real) ^ (-((Params.b1 d : Int) + Nat.log 2 (Params.r2 d)))
        <= 1 - Params.eta2 d := hchk.dens_survive
    have hcard_nonneg : (0 : Real) <= (Fintype.card (C1 d) : Real) := by positivity
    calc (2 : Real) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : Int))
            * (Fintype.card (C1 d) : Real)
        <= (1 - Params.eta2 d) * (Fintype.card (C1 d) : Real) := by
          apply mul_le_mul_of_nonneg_right _ hcard_nonneg
          have hcast : (-(Params.b1 d + Nat.log 2 (Params.r2 d) : Int)) =
              (-((Params.b1 d : Int) + Nat.log 2 (Params.r2 d))) := by ring
          rw [hcast]; exact hsurv
      _ <= (Yalpha.card : Real) := hYdense
  -- The row equipartition for r'=r1 needs a Q with 16|Q| = 9*r1*t1; take R'=univ.
  -- Reuse the exact construction from M1_capacity_lower_canonical.
  obtain ⟨n, hn_eq⟩ : ∃ n : Nat, 16 * n = 9 * Params.r1 d * Params.t1 d := by
    refine ⟨9 * Params.r1 d * Params.t1 d / 16, ?_⟩
    have ht1_clog : Params.t1 d = 2 ^ Nat.clog 2 (64 * Nat.log 2 d) := rfl
    have ht1pow : Params.t1 d = 2 ^ Nat.log 2 (Params.t1 d) := by
      rw [ht1_clog, log_two_pow]
    have hlog1 : 1 <= Nat.log 2 d := by omega
    have ht1ge16 : 16 <= Params.t1 d := by
      have ht := (Params.t1_bracket (d := d) hlog1).1; nlinarith
    have hlogt_ge4 : 4 <= Nat.log 2 (Params.t1 d) := by
      calc 4 = Nat.log 2 16 := by norm_num [Nat.log]
        _ <= Nat.log 2 (Params.t1 d) := Nat.log_mono_right ht1ge16
    have hdiv16 : 16 ∣ Params.t1 d := by
      rw [show 16 = (2 : Nat) ^ 4 by norm_num, ht1pow]
      exact pow_dvd_pow 2 hlogt_ge4
    have hdiv16prod : 16 ∣ 9 * Params.r1 d * Params.t1 d :=
      dvd_mul_of_dvd_right hdiv16 (9 * Params.r1 d)
    rw [mul_comm, Nat.div_mul_cancel hdiv16prod]
  have hn_le : n <= (Finset.univ : Finset (Fin (Params.q1 d))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have hqt : Params.q1 d + 2 = Params.r1 d * Params.t1 d := hdiv
    have hprod_ge5 : 5 <= Params.r1 d * Params.t1 d := by
      rw [← hqt]
      have hqlo := Params.le_q1_add_two (d := d) (by omega : 1 <= Nat.log 2 d)
      have hsmall : 5 <= 2 * Nat.log 2 d ^ 2 := by nlinarith
      omega
    have hmain_plus : n + 2 <= Params.r1 d * Params.t1 d := by
      have hn16lin : 16 * n = 9 * (Params.r1 d * Params.t1 d) := by
        simpa [Nat.mul_assoc] using hn_eq
      omega
    omega
  obtain ⟨Q, _hQsub, hQcard'⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin (Params.q1 d)))) hn_le
  have hQcard : 16 * Q.card = 9 * Params.r1 d * Params.t1 d := by rw [hQcard', hn_eq]
  let R' : Finset (R1 d) := (Finset.univ : Finset (R1 d))
  have hrow : IsEquipartitionedGE
              (R'.image (fun a => ((a.1 : Fin (Params.q1 d)), a.2))) Q 1 := by
    intro q hq
    apply Nat.succ_le_of_lt
    apply Finset.card_pos.mpr
    exact ⟨(q, 0), by simp [R']⟩
  -- Apply the SUBGAME floor lemma (M1_low_column_stage2) at r'=r1.
  have hslice := M1_low_column_stage2 d hd hchk' hdiv hTb hRb hgap
    hr1pow hr1pos (le_refl (Params.r1 d)) R' Yalpha Q hQcard hrow hcol
  rw [Dfamily.singleton] at hslice
  -- 1 + log t1 + log r1 = a + 1
  have hcap := M1_capacity_log_identity d hd hdiv
  have hInt : ((Params.a d + 1 : Nat) : Int) <=
      (D (subgame (M1 d) R' Yalpha) : Int) := by
    calc ((Params.a d + 1 : Nat) : Int)
        = (1 : Int) + (Nat.log 2 (Params.t1 d) : Int)
            + (Nat.log 2 (Params.r1 d) : Int) := by rw [hcap]; omega
      _ <= (D (subgame (M1 d) R' Yalpha) : Int) := hslice
  exact_mod_cast hInt

theorem M3_terminalHardWitnesses_of_prefix_M1_dense
    (d : Nat)
    {A B : Type*} [Fintype A] [Fintype B]
    (hR1 : Nonempty (R1 d))
    (Yalpha : Finset (C1 d)) (hYnonempty : Yalpha.Nonempty)
    (G : A -> B -> Bool)
    (R : Finset A) (C : Finset B) (Q : Protocol A B Bool)
    (pat : List Protocol.ActualBitSide)
    (hfloor : Params.a d + 1 <=
      D (subgame (M1 d) (Finset.univ : Finset (R1 d)) Yalpha))
    (rowEmbed : List Bool -> R1 d -> A)
    (colEmbed : List Bool -> {gamma // gamma ∈ Yalpha} -> B)
    (hrowPrefix :
      forall w, w.length = pat.length ->
        forall r, rowEmbed w r ∈ Protocol.rowsAtPrefix R C Q w)
    (hcolPrefix :
      forall w, w.length = pat.length ->
        forall gamma, colEmbed w gamma ∈ Protocol.colsAtPrefix R C Q w)
    (hcopy :
      forall w, w.length = pat.length ->
        forall r (gamma : {gamma // gamma ∈ Yalpha}),
          G (rowEmbed w r) (colEmbed w gamma) = M1 d r gamma.val) :
    Protocol.TerminalHardWitnesses G R C Q pat (Params.a d + 1) := by
  classical
  haveI : Nonempty (R1 d) := hR1
  haveI : Nonempty {gamma // gamma ∈ Yalpha} := hYnonempty.to_subtype
  haveI : Nonempty {a // a ∈ (Finset.univ : Finset (R1 d))} := by
    obtain ⟨r⟩ := hR1
    exact ⟨⟨r, Finset.mem_univ _⟩⟩
  -- H = subgame (M1 d) univ Yalpha, A0 = {a // a ∈ univ(R1)}, B0 = {gamma // gamma ∈ Yalpha}
  let H : {a // a ∈ (Finset.univ : Finset (R1 d))} -> {gamma // gamma ∈ Yalpha} -> Bool :=
    subgame (M1 d) (Finset.univ : Finset (R1 d)) Yalpha
  -- rowEmbed' takes A0 = {a // a ∈ univ}; strip the subtype
  let rowEmbed' : List Bool -> {a // a ∈ (Finset.univ : Finset (R1 d))} -> A :=
    fun w a => rowEmbed w a.val
  refine
    terminalHardWitnesses_of_prefix_exact_copy
      G H R C Q pat (Params.a d + 1)
      rowEmbed' colEmbed ?_ ?_ ?_ ?_
  · intro w hw a
    exact hrowPrefix w hw a.val
  · intro w hw gamma
    exact hcolPrefix w hw gamma
  · intro w hw a gamma
    -- G (rowEmbed' w a) (colEmbed w gamma) = H a gamma = M1 d a.val gamma.val
    change G (rowEmbed w a.val) (colEmbed w gamma) = M1 d a.val gamma.val
    exact hcopy w hw a.val gamma
  · exact hfloor

noncomputable def M3_build_sync_bridge
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (Y : Fin 4 -> Fin (Params.q2 d) -> Finset (C1 d))
    (codeOfAlpha :
      Fin 4 -> Fin (Params.q2 d) -> Fin (2 ^ Nat.clog 2 (Params.q2 d)))
    (hcol : forall p,
      Protocol.FirstKColBitsOn
        (Finset.univ : Finset {a // a ∈ (binBranch p).rows})
        (Finset.univ : Finset {b // b ∈ (binBranch p).cols})
        (Nat.clog 2 (Params.q2 d)) (binBranch p).residual)
    (hcols : forall p alpha,
      (Protocol.colPrefixCols (Nat.clog 2 (Params.q2 d))
        (binBranch p).residual (codeOfAlpha p alpha)).Nonempty)
    -- diag reachability: the Yalpha diagonals land in the colPrefix cols and in binBranch.cols
    (hdiag : forall p alpha gamma, gamma ∈ Y p alpha ->
      exists (hb : M3_diagCol d alpha gamma ∈ (binBranch p).cols),
        (⟨M3_diagCol d alpha gamma, hb⟩ : {b // b ∈ (binBranch p).cols}) ∈
          Protocol.colPrefixCols (Nat.clog 2 (Params.q2 d))
            (binBranch p).residual (codeOfAlpha p alpha)) :
    M3PackageSyncBridge d P binBranch Y := by
  classical
  -- Build the sync explicitly (NOT via Classical.choice) so dimBranch is the concrete
  -- compose_colPrefix and diag_cols is provable.
  refine
    { sync :=
        { dimBranch := fun p alpha =>
            Protocol.BranchAt.compose_colPrefix (binBranch p) (codeOfAlpha p alpha)
              (hcol p) (hcols p alpha)
          dim_sideTrace := ?_
          dim_extends := ?_ }
      diag_cols := ?_ }
  · intro p alpha
    unfold Protocol.BranchAt.compose_colPrefix Protocol.BranchAt.compose
    simp [Protocol.mkBranchAt_of_colPrefix, Protocol.branchAt_of_swap,
      Protocol.mkBranchAt_of_rowPrefix, Protocol.ActualBitSide.swap]
  · intro p alpha
    exact Protocol.BranchAt.branchExtends_compose_left
      (binBranch p)
      (Protocol.mkBranchAt_of_colPrefix
        (binBranch p).residual
        (subgame (M3 d) (binBranch p).rows (binBranch p).cols)
        (Nat.clog 2 (Params.q2 d)) (codeOfAlpha p alpha)
        (hcol p) (binBranch p).residual_computes
        (by
          obtain ⟨a, ha⟩ := (binBranch p).rows_nonempty
          exact ⟨⟨a, ha⟩, Finset.mem_univ _⟩)
        (hcols p alpha))
  · intro p alpha gamma hgamma
    -- M3_diagCol alpha gamma ∈ (dimBranch p alpha).cols
    -- dimBranch = compose_colPrefix = compose b1 (mkBranchAt_of_colPrefix ...)
    -- cols = liftCols b1 (mkBranchAt_of_colPrefix ...)
    obtain ⟨hb, hprefix⟩ := hdiag p alpha gamma hgamma
    show M3_diagCol d alpha gamma ∈
      (Protocol.BranchAt.compose_colPrefix (binBranch p) (codeOfAlpha p alpha)
        (hcol p) (hcols p alpha)).cols
    unfold Protocol.BranchAt.compose_colPrefix
    rw [show (Protocol.BranchAt.compose (binBranch p)
        (Protocol.mkBranchAt_of_colPrefix (binBranch p).residual
          (subgame (M3 d) (binBranch p).rows (binBranch p).cols)
          (Nat.clog 2 (Params.q2 d)) (codeOfAlpha p alpha)
          (hcol p) (binBranch p).residual_computes _ (hcols p alpha))).cols =
        Protocol.BranchAt.liftCols (binBranch p)
          (Protocol.mkBranchAt_of_colPrefix (binBranch p).residual
            (subgame (M3 d) (binBranch p).rows (binBranch p).cols)
            (Nat.clog 2 (Params.q2 d)) (codeOfAlpha p alpha)
            (hcol p) (binBranch p).residual_computes _ (hcols p alpha)) from rfl]
    rw [Protocol.BranchAt.mem_liftCols]
    refine ⟨hb, ?_⟩
    -- (mkBranchAt_of_colPrefix ...).cols = colPrefixCols (via branchAt_of_swap rows→cols)
    show (⟨M3_diagCol d alpha gamma, hb⟩ : {b // b ∈ (binBranch p).cols}) ∈
      (Protocol.mkBranchAt_of_colPrefix
        (binBranch p).residual
        (subgame (M3 d) (binBranch p).rows (binBranch p).cols)
        (Nat.clog 2 (Params.q2 d)) (codeOfAlpha p alpha)
        (hcol p) (binBranch p).residual_computes _ (hcols p alpha)).cols
    unfold Protocol.mkBranchAt_of_colPrefix Protocol.branchAt_of_swap
    exact hprefix

-- CLAIM-END aux:m3-fuzzy-opus


-- CLAIM-BEGIN aux:m3-fuzzy-transport

theorem M1_dense_columns_nonempty
    (d : Nat) (hpow : IsPow2 d) (hlog : 64 <= Nat.log 2 d)
    (hchk : Checklist d) (Yalpha : Finset (C1 d))
    (hYdense :
      (1 - Params.eta2 d) * (Fintype.card (C1 d) : Real) <=
        (Yalpha.card : Real)) :
    Yalpha.Nonempty := by
  have heta_le_half :
      Params.eta2 d <= (1 : Real) / 2 :=
    Params.eta2_le_half hpow (by omega : 2 <= Nat.log 2 d)
  have heta_lt_one : Params.eta2 d < 1 := by linarith
  have hcoeff_pos : 0 < (1 : Real) - Params.eta2 d := by linarith
  have hCpos_nat : 0 < Fintype.card (C1 d) := by
    simpa [C1, Fintype.card_fin] using
      L1_pos d hchk.t1_le_q1_add_five
  have hCpos : 0 < (Fintype.card (C1 d) : Real) := by
    exact_mod_cast hCpos_nat
  have hYpos_real : 0 < (Yalpha.card : Real) :=
    lt_of_lt_of_le (mul_pos hcoeff_pos hCpos) hYdense
  have hYpos_nat : 0 < Yalpha.card := by
    exact_mod_cast hYpos_real
  exact Finset.card_pos.mp hYpos_nat

theorem M3_restricted_col_of_dense_alpha
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBranch p).rows})
    (C : Finset {b // b ∈ (binBranch p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (htr : M3BinDenseReindex d P binBranch p Sdense R C hqcast)
    (ad :
      M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
        (M3_bin_dense_protocol d P binBranch p Sdense R C hqcast htr)) :
    Protocol.FirstKColBitsOn R C (Nat.clog 2 (Params.q2 d))
      (Protocol.restrict R C (binBranch p).residual) := by
  classical
  exact
    M3_restricted_col_of_dense_first_row_bits
      (binBranch p).residual R C (Nat.clog 2 (Params.q2 d))
      htr.rowEquiv htr.colEquiv
      (by
        simpa [M3_bin_dense_protocol, ad.depth_eq_clog_q2] using
          ad.first_row_bits)

namespace Protocol

noncomputable def codeOfBitList : (w : List Bool) -> Fin (2 ^ w.length)
  | [] => Protocol.zeroPow2 0
  | bit :: tail => Protocol.bitCons bit (codeOfBitList tail)

theorem prefixCodeRaw_reindex
    {A B A' B' Z : Type*} (eA : A' ≃ A) (eB : B' ≃ B)
    (k : Nat) (P : Protocol A B Z) (a : A') :
    Protocol.prefixCodeRaw k (Protocol.reindex eA eB P) a =
      Protocol.prefixCodeRaw k P (eA a) := by
  induction k generalizing P with
  | zero =>
      rfl
  | succ k ih =>
      cases P with
      | leaf z =>
          rfl
      | bNode q l r =>
          rfl
      | aNode q l r =>
          simp only [Protocol.reindex, Protocol.prefixCodeRaw]
          by_cases hq : q (eA a)
          · rw [if_pos hq, if_pos hq, ih]
          · rw [if_neg hq, if_neg hq, ih]

theorem actualBitListRaw_reindex
    {A B A' B' Z : Type*} (eA : A' ≃ A) (eB : B' ≃ B)
    (k : Nat) (P : Protocol A B Z) (a : A') (b : B') :
    Protocol.actualBitListRaw k (Protocol.reindex eA eB P) a b =
      Protocol.actualBitListRaw k P (eA a) (eB b) := by
  induction k generalizing P with
  | zero =>
      rfl
  | succ k ih =>
      cases P with
      | leaf z =>
          rfl
      | aNode q l r =>
          simp only [Protocol.reindex, Protocol.actualBitListRaw]
          by_cases hq : q (eA a)
          · rw [if_pos hq, if_pos hq, ih]
          · rw [if_neg hq, if_neg hq, ih]
      | bNode q l r =>
          simp only [Protocol.reindex, Protocol.actualBitListRaw]
          by_cases hq : q (eB b)
          · rw [if_pos hq, if_pos hq, ih]
          · rw [if_neg hq, if_neg hq, ih]

theorem actualBitListRaw_swap
    {A B Z : Type*} (k : Nat) (P : Protocol A B Z) (a : A) (b : B) :
    Protocol.actualBitListRaw k (Protocol.swap P) b a =
      Protocol.actualBitListRaw k P a b := by
  induction k generalizing P with
  | zero =>
      rfl
  | succ k ih =>
      cases P with
      | leaf z =>
          rfl
      | aNode q l r =>
          simp only [Protocol.swap, Protocol.actualBitListRaw]
          by_cases hq : q a
          · rw [if_pos hq, if_pos hq, ih]
          · rw [if_neg hq, if_neg hq, ih]
      | bNode q l r =>
          simp only [Protocol.swap, Protocol.actualBitListRaw]
          by_cases hq : q b
          · rw [if_pos hq, if_pos hq, ih]
          · rw [if_neg hq, if_neg hq, ih]

theorem actualBitListRaw_eq_of_firstKRowBitsOn_prefixCodeRaw
    {A B Z : Type*} [DecidableEq A] [DecidableEq B]
    {R : Finset A} {C : Finset B} {P : Protocol A B Z}
    {w : List Bool} {a : A} {b : B}
    (hrow : Protocol.FirstKRowBitsOn R C w.length P)
    (ha : a ∈ R) (hb : b ∈ C)
    (hcode :
      Protocol.prefixCodeRaw w.length P a = Protocol.codeOfBitList w) :
    Protocol.actualBitListRaw w.length P a b = w := by
  induction w generalizing R C P a b with
  | nil =>
      rfl
  | cons bit tail ih =>
      cases P with
      | leaf z =>
          simp only [Protocol.FirstKRowBitsOn] at hrow
          rcases hrow with hR | hC
          · rw [hR] at ha
            exact absurd ha (Finset.notMem_empty a)
          · rw [hC] at hb
            exact absurd hb (Finset.notMem_empty b)
      | bNode q l r =>
          simp only [Protocol.FirstKRowBitsOn] at hrow
          rcases hrow with hR | hC
          · rw [hR] at ha
            exact absurd ha (Finset.notMem_empty a)
          · rw [hC] at hb
            exact absurd hb (Finset.notMem_empty b)
      | aNode q l r =>
          simp only [Protocol.FirstKRowBitsOn] at hrow
          have hcode' :
              Protocol.bitCons (q a)
                  (Protocol.prefixCodeRaw tail.length
                    (if q a then r else l) a) =
                Protocol.bitCons bit (Protocol.codeOfBitList tail) := by
            simpa [Protocol.prefixCodeRaw, Protocol.codeOfBitList] using hcode
          have hpair :
              (q a,
                  Protocol.prefixCodeRaw tail.length
                    (if q a then r else l) a) =
                (bit, Protocol.codeOfBitList tail) :=
            Protocol.bitCons_injective hcode'
          have hhead : q a = bit := congrArg Prod.fst hpair
          have htail :
              Protocol.prefixCodeRaw tail.length
                    (if q a then r else l) a =
                Protocol.codeOfBitList tail := congrArg Prod.snd hpair
          by_cases hq : q a
          · have ha' : a ∈ R.filter fun x => q x = true := by
              rw [Finset.mem_filter]
              exact ⟨ha, hq⟩
            have hbit : bit = true := by
              simpa [hq] using hhead.symm
            have htailBits :=
              ih (R := R.filter fun x => q x = true) (C := C)
                (P := r) (a := a) (b := b)
                hrow.2 ha' hb (by simpa [hq] using htail)
            simp [Protocol.actualBitListRaw, hq, hbit, htailBits]
          · have hqf : q a = false := by simp [hq]
            have ha' : a ∈ R.filter fun x => q x = false := by
              rw [Finset.mem_filter]
              exact ⟨ha, hqf⟩
            have hbit : bit = false := by
              simpa [hq] using hhead.symm
            have htailBits :=
              ih (R := R.filter fun x => q x = false) (C := C)
                (P := l) (a := a) (b := b)
                hrow.1 ha' hb (by simpa [hq] using htail)
            simp [Protocol.actualBitListRaw, hq, hbit, htailBits]

theorem actualBitListRaw_eq_of_firstKRowBitsOn_prefixCodeRaw_eq
    {A B Z : Type*} [DecidableEq A] [DecidableEq B]
    {R : Finset A} {C : Finset B} {P : Protocol A B Z}
    {k : Nat} {a a' : A} {b b' : B}
    (hrow : Protocol.FirstKRowBitsOn R C k P)
    (ha : a ∈ R) (ha' : a' ∈ R) (hb : b ∈ C) (hb' : b' ∈ C)
    (hcode : Protocol.prefixCodeRaw k P a =
      Protocol.prefixCodeRaw k P a') :
    Protocol.actualBitListRaw k P a b =
      Protocol.actualBitListRaw k P a' b' := by
  induction k generalizing R C P with
  | zero =>
      rfl
  | succ k ih =>
      cases P with
      | leaf z =>
          exfalso
          simp only [Protocol.FirstKRowBitsOn] at hrow
          rcases hrow with hR | hC
          · rw [hR] at ha
            exact absurd ha (Finset.notMem_empty a)
          · rw [hC] at hb
            exact absurd hb (Finset.notMem_empty b)
      | bNode q l r =>
          exfalso
          simp only [Protocol.FirstKRowBitsOn] at hrow
          rcases hrow with hR | hC
          · rw [hR] at ha
            exact absurd ha (Finset.notMem_empty a)
          · rw [hC] at hb
            exact absurd hb (Finset.notMem_empty b)
      | aNode q l r =>
          simp only [Protocol.FirstKRowBitsOn] at hrow
          simp only [Protocol.prefixCodeRaw] at hcode
          have hpair :
              (q a, Protocol.prefixCodeRaw k (if q a then r else l) a) =
                (q a',
                  Protocol.prefixCodeRaw k (if q a' then r else l) a') :=
            Protocol.bitCons_injective hcode
          have hhead : q a = q a' := congrArg Prod.fst hpair
          have htail :
              Protocol.prefixCodeRaw k (if q a then r else l) a =
                Protocol.prefixCodeRaw k (if q a' then r else l) a' :=
            congrArg Prod.snd hpair
          by_cases hq : q a
          · have hq' : q a' = true := by
              simpa [hq] using hhead.symm
            have haT : a ∈ R.filter fun x => q x = true := by
              rw [Finset.mem_filter]
              exact ⟨ha, hq⟩
            have haT' : a' ∈ R.filter fun x => q x = true := by
              rw [Finset.mem_filter]
              exact ⟨ha', hq'⟩
            have htailR :
                Protocol.prefixCodeRaw k r a =
                  Protocol.prefixCodeRaw k r a' := by
              simpa [hq, hq'] using htail
            have hbits :=
              ih (R := R.filter fun x => q x = true) (C := C)
                (P := r) hrow.2 haT haT' hb hb' htailR
            simp [Protocol.actualBitListRaw, hq, hq', hbits]
          · have hqf : q a = false := by simp [hq]
            have hq'f : q a' = false := by
              simpa [hqf] using hhead.symm
            have haF : a ∈ R.filter fun x => q x = false := by
              rw [Finset.mem_filter]
              exact ⟨ha, hqf⟩
            have haF' : a' ∈ R.filter fun x => q x = false := by
              rw [Finset.mem_filter]
              exact ⟨ha', hq'f⟩
            have htailL :
                Protocol.prefixCodeRaw k l a =
                  Protocol.prefixCodeRaw k l a' := by
              simpa [hq, hq'f] using htail
            have hbits :=
              ih (R := R.filter fun x => q x = false) (C := C)
                (P := l) hrow.1 haF haF' hb hb' htailL
            simp [Protocol.actualBitListRaw, hq, hq'f, hbits]

theorem actualBitListRaw_eq_of_restrict_eq_of_firstKColBitsOn
    {A B Z : Type*} [DecidableEq A] [DecidableEq B]
    {S R : Finset A} {T C : Finset B} {P : Protocol A B Z}
    {k : Nat} {a a' : A} {b b' : B}
    (hcol : Protocol.FirstKColBitsOn S T k P)
    (hRsub : ∀ a, a ∈ R -> a ∈ S)
    (hCsub : ∀ b, b ∈ C -> b ∈ T)
    (ha : a ∈ R) (ha' : a' ∈ R) (hb : b ∈ C) (hb' : b' ∈ C)
    (hres :
      Protocol.actualBitListRaw k (Protocol.restrict R C P) a b =
        Protocol.actualBitListRaw k (Protocol.restrict R C P) a' b') :
    Protocol.actualBitListRaw k P a b =
      Protocol.actualBitListRaw k P a' b' := by
  induction k generalizing S T R C P with
  | zero =>
      rfl
  | succ k ih =>
      cases P with
      | leaf z =>
          exfalso
          simp only [Protocol.FirstKColBitsOn, Protocol.FirstKRowBitsOn,
            Protocol.swap] at hcol
          rcases hcol with hT | hS
          · have hbT : b ∈ T := hCsub b hb
            rw [hT] at hbT
            exact absurd hbT (Finset.notMem_empty b)
          · have haS : a ∈ S := hRsub a ha
            rw [hS] at haS
            exact absurd haS (Finset.notMem_empty a)
      | aNode q l r =>
          exfalso
          simp only [Protocol.FirstKColBitsOn, Protocol.FirstKRowBitsOn,
            Protocol.swap] at hcol
          rcases hcol with hT | hS
          · have hbT : b ∈ T := hCsub b hb
            rw [hT] at hbT
            exact absurd hbT (Finset.notMem_empty b)
          · have haS : a ∈ S := hRsub a ha
            rw [hS] at haS
            exact absurd haS (Finset.notMem_empty a)
      | bNode q l r =>
          simp only [Protocol.FirstKColBitsOn, Protocol.FirstKRowBitsOn,
            Protocol.swap] at hcol
          by_cases hconst : ∃ beta, Protocol.IsColConstantOn C q beta
          · have hbq : q b = Classical.choose hconst :=
              Classical.choose_spec hconst b hb
            have hbq' : q b' = Classical.choose hconst :=
              Classical.choose_spec hconst b' hb'
            by_cases hchoose : Classical.choose hconst = true
            · have hbTsub :
                  ∀ y, y ∈ C -> y ∈ T.filter fun y => q y = true := by
                intro y hy
                rw [Finset.mem_filter]
                exact ⟨hCsub y hy, by
                  simpa [hchoose] using (Classical.choose_spec hconst y hy)⟩
              have hresR :
                  Protocol.actualBitListRaw k (Protocol.restrict R C r) a b =
                    Protocol.actualBitListRaw k (Protocol.restrict R C r) a' b' := by
                have hresSucc :
                    Protocol.actualBitListRaw (k + 1) (Protocol.restrict R C r) a b =
                      Protocol.actualBitListRaw (k + 1) (Protocol.restrict R C r) a' b' := by
                  simpa [Protocol.restrict, hconst, hchoose] using hres
                have ht :=
                  congrArg (fun xs : List Bool => xs.take k) hresSucc
                simpa [Protocol.actualBitListRaw_take (Nat.le_succ k)
                  (Protocol.restrict R C r) a b,
                  Protocol.actualBitListRaw_take (Nat.le_succ k)
                    (Protocol.restrict R C r) a' b'] using ht
              have htail :=
                ih (S := S) (T := T.filter fun y => q y = true)
                  (R := R) (C := C) (P := r)
                  hcol.2 hRsub hbTsub ha ha' hb hb' hresR
              simp [Protocol.actualBitListRaw, hbq, hbq', hchoose, htail]
            · have hchooseF : Classical.choose hconst = false := by
                cases h : Classical.choose hconst <;> simp [h] at *
              have hbFsub :
                  ∀ y, y ∈ C -> y ∈ T.filter fun y => q y = false := by
                intro y hy
                rw [Finset.mem_filter]
                exact ⟨hCsub y hy, by
                  simpa [hchooseF] using (Classical.choose_spec hconst y hy)⟩
              have hresL :
                  Protocol.actualBitListRaw k (Protocol.restrict R C l) a b =
                    Protocol.actualBitListRaw k (Protocol.restrict R C l) a' b' := by
                have hresSucc :
                    Protocol.actualBitListRaw (k + 1) (Protocol.restrict R C l) a b =
                      Protocol.actualBitListRaw (k + 1) (Protocol.restrict R C l) a' b' := by
                  simpa [Protocol.restrict, hconst, hchooseF] using hres
                have ht :=
                  congrArg (fun xs : List Bool => xs.take k) hresSucc
                simpa [Protocol.actualBitListRaw_take (Nat.le_succ k)
                  (Protocol.restrict R C l) a b,
                  Protocol.actualBitListRaw_take (Nat.le_succ k)
                    (Protocol.restrict R C l) a' b'] using ht
              have htail :=
                ih (S := S) (T := T.filter fun y => q y = false)
                  (R := R) (C := C) (P := l)
                  hcol.1 hRsub hbFsub ha ha' hb hb' hresL
              simp [Protocol.actualBitListRaw, hbq, hbq', hchooseF, htail]
          · have hcons :
                q b ::
                    Protocol.actualBitListRaw k
                      (if q b then Protocol.restrict R (C.filter fun y => q y = true) r
                       else Protocol.restrict R (C.filter fun y => q y = false) l)
                      a b =
                  q b' ::
                    Protocol.actualBitListRaw k
                      (if q b' then Protocol.restrict R (C.filter fun y => q y = true) r
                       else Protocol.restrict R (C.filter fun y => q y = false) l)
                      a' b' := by
              simpa [Protocol.restrict, hconst, Protocol.actualBitListRaw] using hres
            have hhead : q b = q b' := (List.cons.inj hcons).1
            have htailEq :
                Protocol.actualBitListRaw k
                    (if q b then Protocol.restrict R (C.filter fun y => q y = true) r
                     else Protocol.restrict R (C.filter fun y => q y = false) l)
                    a b =
                  Protocol.actualBitListRaw k
                    (if q b' then Protocol.restrict R (C.filter fun y => q y = true) r
                     else Protocol.restrict R (C.filter fun y => q y = false) l)
                    a' b' := (List.cons.inj hcons).2
            by_cases hqb : q b
            · have hqb' : q b' = true := by
                simpa [hqb] using hhead.symm
              have hbC : b ∈ C.filter fun y => q y = true := by
                rw [Finset.mem_filter]
                exact ⟨hb, hqb⟩
              have hbC' : b' ∈ C.filter fun y => q y = true := by
                rw [Finset.mem_filter]
                exact ⟨hb', hqb'⟩
              have hCsubT :
                  ∀ y, y ∈ (C.filter fun y => q y = true) ->
                    y ∈ (T.filter fun y => q y = true) := by
                intro y hy
                rw [Finset.mem_filter] at hy ⊢
                exact ⟨hCsub y hy.1, hy.2⟩
              have htailR :
                  Protocol.actualBitListRaw k
                      (Protocol.restrict R (C.filter fun y => q y = true) r) a b =
                    Protocol.actualBitListRaw k
                      (Protocol.restrict R (C.filter fun y => q y = true) r) a' b' := by
                simpa [hqb, hqb'] using htailEq
              have htail :=
                ih (S := S) (T := T.filter fun y => q y = true)
                  (R := R) (C := C.filter fun y => q y = true) (P := r)
                  hcol.2 hRsub hCsubT ha ha' hbC hbC' htailR
              simp [Protocol.actualBitListRaw, hqb, hqb', htail]
            · have hqbf : q b = false := by simp [hqb]
              have hqb'f : q b' = false := by
                simpa [hqbf] using hhead.symm
              have hbC : b ∈ C.filter fun y => q y = false := by
                rw [Finset.mem_filter]
                exact ⟨hb, hqbf⟩
              have hbC' : b' ∈ C.filter fun y => q y = false := by
                rw [Finset.mem_filter]
                exact ⟨hb', hqb'f⟩
              have hCsubT :
                  ∀ y, y ∈ (C.filter fun y => q y = false) ->
                    y ∈ (T.filter fun y => q y = false) := by
                intro y hy
                rw [Finset.mem_filter] at hy ⊢
                exact ⟨hCsub y hy.1, hy.2⟩
              have htailL :
                  Protocol.actualBitListRaw k
                      (Protocol.restrict R (C.filter fun y => q y = false) l) a b =
                    Protocol.actualBitListRaw k
                      (Protocol.restrict R (C.filter fun y => q y = false) l) a' b' := by
                simpa [hqb, hqbf, hqb'f] using htailEq
              have htail :=
                ih (S := S) (T := T.filter fun y => q y = false)
                  (R := R) (C := C.filter fun y => q y = false) (P := l)
                  hcol.1 hRsub hCsubT ha ha' hbC hbC' htailL
              simp [Protocol.actualBitListRaw, hqb, hqb'f, htail]

end Protocol

theorem M3_dense_codeOfAlpha_bijective
    (d : Nat) {hqcast : 2 ^ M2DenseDepth d = Params.q2 d}
    {Sdense : Finset (C2 d)}
    {P : Protocol (M2DenseRows d) (M2DenseCols d Sdense) Bool}
    (ad : M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense P) :
    Function.Bijective ad.codeOfAlpha := by
  classical
  have hinj : Function.Injective ad.codeOfAlpha := by
    intro alpha beta h
    have hα :=
      congrArg
        (fun j =>
          Protocol.alphaOfCode
            (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
            (M2DenseRin d) (M2DenseLabel d P) ad.noWaste
            (fun j : Fin (2 ^ M2DenseDepth d) => j) j) h
    change
      Protocol.alphaOfCode
          (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
          (M2DenseRin d) (M2DenseLabel d P) ad.noWaste
          (fun j : Fin (2 ^ M2DenseDepth d) => j) (ad.codeOfAlpha alpha) =
        Protocol.alphaOfCode
          (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
          (M2DenseRin d) (M2DenseLabel d P) ad.noWaste
          (fun j : Fin (2 ^ M2DenseDepth d) => j) (ad.codeOfAlpha beta) at hα
    rw [ad.alphaOf_codeOfAlpha alpha, ad.alphaOf_codeOfAlpha beta] at hα
    apply Fin.ext
    simpa using congrArg Fin.val hα
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨hinj, ?_⟩
  simp [Fintype.card_fin, hqcast]

theorem M3_dense_Yalpha_prefixCode
    (d : Nat) {hqcast : 2 ^ M2DenseDepth d = Params.q2 d}
    {Sdense : Finset (C2 d)}
    {P : Protocol (M2DenseRows d) (M2DenseCols d Sdense) Bool}
    (ad : M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense P)
    (alpha : Fin (Params.q2 d)) (gamma : C1 d)
    (hgamma : gamma ∈ ad.Yalpha alpha) :
    Protocol.prefixCodeRaw (M2DenseDepth d) P
        (⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩ :
          M2DenseRows d) =
      ad.codeOfAlpha alpha := by
  classical
  have hγ := hgamma
  rw [ad.Yalpha_eq alpha] at hγ
  let alpha0 : Fin (2 ^ M2DenseDepth d) :=
      Protocol.alphaOfCode
        (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
        (M2DenseRin d) (M2DenseLabel d P) ad.noWaste
        (fun j : Fin (2 ^ M2DenseDepth d) => j) (ad.codeOfAlpha alpha)
  let rho0 : M2DenseRows d := ⟨(alpha0, gamma), by simp [M2DenseRin]⟩
  have hγcode :
      Protocol.prefixCodeRaw (M2DenseDepth d) P rho0 =
        ad.codeOfAlpha alpha := by
    simpa [Protocol.YofCode, M2DenseLabel, Protocol.prefixLabelFinQ,
      M2DenseRin, alpha0, rho0] using hγ
  let rho : M2DenseRows d :=
    ⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩
  have halpha0 : alpha0 = Fin.cast hqcast.symm alpha := by
    simpa [alpha0] using ad.alphaOf_codeOfAlpha alpha
  have hrho : rho0 = rho := by
    apply Subtype.ext
    dsimp [rho0, rho]
    exact Prod.ext halpha0 rfl
  change Protocol.prefixCodeRaw (M2DenseDepth d) P rho = ad.codeOfAlpha alpha
  rw [← hrho]
  exact hγcode

theorem M3_restricted_actualBitList_of_dense_Yalpha
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBranch p).rows})
    (C : Finset {b // b ∈ (binBranch p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (htr : M3BinDenseReindex d P binBranch p Sdense R C hqcast)
    (ad :
      M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
        (M3_bin_dense_protocol d P binBranch p Sdense R C hqcast htr))
    {w : List Bool} (hw : w.length = Nat.clog 2 (Params.q2 d))
    {alpha : Fin (Params.q2 d)}
    (hcode :
      ad.codeOfAlpha alpha =
        Fin.cast (by rw [hw, ← ad.depth_eq_clog_q2])
          (Protocol.codeOfBitList w))
    {c : C2 d} (hc : c ∈ Sdense)
    {gamma : C1 d} (hgamma : gamma ∈ ad.Yalpha alpha) :
    Protocol.actualBitListRaw w.length
        (Protocol.restrict R C (binBranch p).residual)
        (htr.colEquiv (⟨c, hc⟩ : M2DenseCols d Sdense)).val
        (htr.rowEquiv
          (⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩ :
            M2DenseRows d)).val =
      w := by
  classical
  let Q0 := Protocol.restrict R C (binBranch p).residual
  let Qswap := Protocol.restrictSub C R (Protocol.swap Q0)
  let Pdense :=
    M3_bin_dense_protocol d P binBranch p Sdense R C hqcast htr
  let rho : M2DenseRows d :=
    ⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩
  let sigma : M2DenseCols d Sdense := ⟨c, hc⟩
  have hwK : w.length = M2DenseDepth d := by
    rw [hw, ← ad.depth_eq_clog_q2]
  have hprefix0 :
      Protocol.prefixCodeRaw (M2DenseDepth d) Pdense rho =
        Fin.cast (by rw [hwK]) (Protocol.codeOfBitList w) := by
    exact (M3_dense_Yalpha_prefixCode d ad alpha gamma hgamma).trans hcode
  have hprefix :
      Protocol.prefixCodeRaw w.length Pdense rho =
        Protocol.codeOfBitList w := by
    apply Fin.ext
    have hleft :
        (Protocol.prefixCodeRaw w.length Pdense rho).val =
          (Protocol.prefixCodeRaw (M2DenseDepth d) Pdense rho).val := by
      rw [hwK]
    have hright :
        (Protocol.prefixCodeRaw (M2DenseDepth d) Pdense rho).val =
          (Protocol.codeOfBitList w).val := by
      simpa using congrArg Fin.val hprefix0
    exact hleft.trans hright
  have hrowDense :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset (M2DenseRows d))
        (Finset.univ : Finset (M2DenseCols d Sdense))
        w.length Pdense := by
    rw [hwK]
    simpa [Pdense] using ad.first_row_bits
  have hdenseBits :
      Protocol.actualBitListRaw w.length Pdense rho sigma = w := by
    exact
      Protocol.actualBitListRaw_eq_of_firstKRowBitsOn_prefixCodeRaw
        (R := (Finset.univ : Finset (M2DenseRows d)))
        (C := (Finset.univ : Finset (M2DenseCols d Sdense)))
        (P := Pdense) (w := w) (a := rho) (b := sigma)
        hrowDense (Finset.mem_univ rho) (Finset.mem_univ sigma)
        hprefix
  calc
    Protocol.actualBitListRaw w.length Q0
        (htr.colEquiv sigma).val (htr.rowEquiv rho).val =
        Protocol.actualBitListRaw w.length (Protocol.swap Q0)
          (htr.rowEquiv rho).val (htr.colEquiv sigma).val := by
          exact
            (Protocol.actualBitListRaw_swap w.length Q0
              (htr.colEquiv sigma).val (htr.rowEquiv rho).val).symm
    _ =
        Protocol.actualBitListRaw w.length Qswap
          (htr.rowEquiv rho) (htr.colEquiv sigma) := by
          exact
            (Protocol.actualBitListRaw_restrictSub C R (Protocol.swap Q0)
              (htr.rowEquiv rho) (htr.colEquiv sigma) w.length).symm
    _ =
        Protocol.actualBitListRaw w.length Pdense rho sigma := by
          exact
            (Protocol.actualBitListRaw_reindex htr.rowEquiv htr.colEquiv
              w.length Qswap rho sigma).symm
    _ = w := hdenseBits

theorem M3_restricted_colPrefix_mem_of_dense_Yalpha
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBranch p).rows})
    (C : Finset {b // b ∈ (binBranch p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (htr : M3BinDenseReindex d P binBranch p Sdense R C hqcast)
    (ad :
      M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
        (M3_bin_dense_protocol d P binBranch p Sdense R C hqcast htr))
    {w : List Bool} (hw : w.length = Nat.clog 2 (Params.q2 d))
    {alpha : Fin (Params.q2 d)}
    (hcode :
      ad.codeOfAlpha alpha =
        Fin.cast (by rw [hw, ← ad.depth_eq_clog_q2])
          (Protocol.codeOfBitList w))
    {c : C2 d} (hc : c ∈ Sdense)
    {gamma : C1 d} (hgamma : gamma ∈ ad.Yalpha alpha) :
    (htr.rowEquiv
        (⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩ :
          M2DenseRows d)).val ∈
      Protocol.colsAtPrefix R C
        (Protocol.restrict R C (binBranch p).residual) w := by
  classical
  rw [Protocol.colsAtPrefix, Finset.mem_filter]
  refine ⟨(htr.rowEquiv
      (⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩ :
        M2DenseRows d)).property, ?_⟩
  refine ⟨(htr.colEquiv (⟨c, hc⟩ : M2DenseCols d Sdense)).val,
    (htr.colEquiv (⟨c, hc⟩ : M2DenseCols d Sdense)).property, ?_⟩
  exact
    M3_restricted_actualBitList_of_dense_Yalpha d P binBranch p Sdense R C
      hqcast htr ad hw hcode hc hgamma

theorem M3_restricted_fullCoverage_of_dense_alpha
    (d : Nat) (hpow : IsPow2 d) (hlog : 64 <= Nat.log 2 d)
    (hchk : Checklist d)
    (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (hSnonempty : Sdense.Nonempty)
    (R : Finset {a // a ∈ (binBranch p).rows})
    (C : Finset {b // b ∈ (binBranch p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (htr : M3BinDenseReindex d P binBranch p Sdense R C hqcast)
    (ad :
      M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
        (M3_bin_dense_protocol d P binBranch p Sdense R C hqcast htr)) :
    Protocol.FullStoppingFiberCoverage R C
      (Protocol.restrict R C (binBranch p).residual)
      (List.replicate (Nat.clog 2 (Params.q2 d))
        Protocol.ActualBitSide.bob) := by
  classical
  intro w hw
  have hwlen : w.length = Nat.clog 2 (Params.q2 d) := by
    simpa using hw
  have hwK : w.length = M2DenseDepth d := by
    rw [hwlen, ← ad.depth_eq_clog_q2]
  let j : Fin (2 ^ M2DenseDepth d) :=
    Fin.cast (by rw [hwK]) (Protocol.codeOfBitList w)
  rcases (M3_dense_codeOfAlpha_bijective d ad).2 j with ⟨alpha, hcode⟩
  have hYnonempty : (ad.Yalpha alpha).Nonempty :=
    M1_dense_columns_nonempty d hpow hlog hchk (ad.Yalpha alpha)
      (ad.Yalpha_dense alpha)
  rcases hYnonempty with ⟨gamma, hgamma⟩
  rcases hSnonempty with ⟨c, hc⟩
  refine ⟨(htr.colEquiv (⟨c, hc⟩ : M2DenseCols d Sdense)).val,
    (htr.colEquiv (⟨c, hc⟩ : M2DenseCols d Sdense)).property,
    (htr.rowEquiv
      (⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩ :
        M2DenseRows d)).val,
    (htr.rowEquiv
      (⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩ :
        M2DenseRows d)).property, ?_⟩
  exact
    M3_restricted_actualBitList_of_dense_Yalpha d P binBranch p Sdense R C
      hqcast htr ad hwlen (by simpa [j] using hcode) hc hgamma

theorem M3_terminalHardWitnesses_of_wordwise_dense_Yalpha_prefix_copy
    (d : Nat) (hpow : IsPow2 d) (hlog : 64 <= Nat.log 2 d)
    (hchk : Checklist d)
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool)
    (R : Finset A) (C : Finset B) (Q : Protocol A B Bool)
    (pat : List Protocol.ActualBitSide)
    (Yalpha : List Bool -> Finset (C1 d))
    (hYdense :
      forall w, w.length = pat.length ->
        (1 - Params.eta2 d) * (Fintype.card (C1 d) : Real) <=
          ((Yalpha w).card : Real))
    (rowEmbed : forall w,
      {r // r ∈ (Finset.univ : Finset (R1 d))} -> A)
    (colEmbed : forall w, {gamma // gamma ∈ Yalpha w} -> B)
    (hrowPrefix :
      forall w, w.length = pat.length ->
        forall r, rowEmbed w r ∈ Protocol.rowsAtPrefix R C Q w)
    (hcolPrefix :
      forall w, w.length = pat.length ->
        forall gamma, colEmbed w gamma ∈ Protocol.colsAtPrefix R C Q w)
    (hcopy :
      forall w, w.length = pat.length ->
        forall r gamma,
          G (rowEmbed w r) (colEmbed w gamma) =
            subgame (M1 d) (Finset.univ : Finset (R1 d)) (Yalpha w)
              r gamma) :
    Protocol.TerminalHardWitnesses G R C Q pat (D (M1 d)) := by
  classical
  have hR1_nonempty : Nonempty (R1 d) := by
    have hq1pos : 0 < Params.q1 d :=
      lt_of_lt_of_le Nat.zero_lt_one hchk.one_le_q1
    exact ⟨(⟨0, hq1pos⟩, 0)⟩
  intro w hw
  have hY_nonempty : (Yalpha w).Nonempty :=
    M1_dense_columns_nonempty d hpow hlog hchk (Yalpha w)
      (hYdense w hw)
  let A0 := {r // r ∈ (Finset.univ : Finset (R1 d))}
  let B0 := {gamma // gamma ∈ Yalpha w}
  let Rw : Finset A := (Finset.univ : Finset A0).image (rowEmbed w)
  let Cw : Finset B := (Finset.univ : Finset B0).image (colEmbed w)
  refine ⟨Rw, Cw, ?_, ?_⟩
  · refine
      { rows_subset := ?_
        cols_subset := ?_
        rows_nonempty := ?_
        cols_nonempty := ?_ }
    · intro a ha
      rcases Finset.mem_image.mp ha with ⟨r, _hr, rfl⟩
      exact hrowPrefix w hw r
    · intro b hb
      rcases Finset.mem_image.mp hb with ⟨gamma, _hgamma, rfl⟩
      exact hcolPrefix w hw gamma
    · obtain ⟨r0⟩ := hR1_nonempty
      exact ⟨rowEmbed w ⟨r0, Finset.mem_univ _⟩,
        Finset.mem_image.mpr
          ⟨⟨r0, Finset.mem_univ _⟩, Finset.mem_univ _, rfl⟩⟩
    · rcases hY_nonempty with ⟨gamma0, hgamma0⟩
      exact ⟨colEmbed w ⟨gamma0, hgamma0⟩,
        Finset.mem_image.mpr
          ⟨⟨gamma0, hgamma0⟩, Finset.mem_univ _, rfl⟩⟩
  · have hcap :
        D (M1 d) <=
          D (subgame (M1 d) (Finset.univ : Finset (R1 d)) (Yalpha w)) := by
      rw [M1_complexity d hpow hlog]
      exact
        M1_dense_column_subgame_floor d hpow hlog hchk (Yalpha w)
          (hYdense w hw)
    exact le_trans hcap
      (D_exact_copy_le_subgame
        G (subgame (M1 d) (Finset.univ : Finset (R1 d)) (Yalpha w))
        (rowEmbed w) (colEmbed w) Rw Cw
        (by
          intro r
          exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩)
        (by
          intro gamma
          exact Finset.mem_image.mpr ⟨gamma, Finset.mem_univ gamma, rfl⟩)
        (hcopy w hw))

theorem M3_stage3StopData_for_dense_bin
    (d : Nat) (hpow : IsPow2 d) (hlog : 64 <= Nat.log 2 d)
    (hchk : Checklist d)
    (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hrow_mem : forall c, c ∈ Sdense -> (p, c) ∈ (binBranch p).rows)
    (hdiag_mem : forall a : M2DenseRows d,
      M3_diagCol d (Fin.cast hqcast a.val.1) a.val.2 ∈
        (binBranch p).cols)
    (hSnonempty : Sdense.Nonempty)
    (hfiberCover : forall alpha,
      Sdense.image (fun c : C2 d => S2fam d c alpha) =
        (Finset.univ : Finset (R1 d)))
    (ad :
      let R :=
        M3_denseSurvivorRows d P binBranch p Sdense hrow_mem
      let C := M3_denseDiagCols d P binBranch p hqcast hdiag_mem
      let htr :=
        M3_binDenseReindex_of_memberships d P binBranch p Sdense hqcast
          hrow_mem hdiag_mem
      M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
        (M3_bin_dense_protocol d P binBranch p Sdense R C hqcast htr)) :
    Stage3StopData
      (subgame (M3 d) (binBranch p).rows (binBranch p).cols)
      (binBranch p).residual
      (M3_denseSurvivorRows d P binBranch p Sdense hrow_mem)
      (M3_denseDiagCols d P binBranch p hqcast hdiag_mem)
      (Nat.clog 2 (Params.q2 d)) (D (M1 d)) := by
  classical
  let R := M3_denseSurvivorRows d P binBranch p Sdense hrow_mem
  let C := M3_denseDiagCols d P binBranch p hqcast hdiag_mem
  let htr :=
    M3_binDenseReindex_of_memberships d P binBranch p Sdense hqcast
      hrow_mem hdiag_mem
  change
    Stage3StopData
      (subgame (M3 d) (binBranch p).rows (binBranch p).cols)
      (binBranch p).residual R C
      (Nat.clog 2 (Params.q2 d)) (D (M1 d))
  let m := Nat.clog 2 (Params.q2 d)
  have hm_depth : m = M2DenseDepth d := by
    dsimp [m]
    exact ad.depth_eq_clog_q2.symm
  have hrestricted :
      Protocol.FirstKColBitsOn R C m
        (Protocol.restrict R C (binBranch p).residual) := by
    exact
      M3_restricted_col_of_dense_alpha d P binBranch p Sdense R C
        hqcast htr ad
  have hcover :
      Protocol.FullStoppingFiberCoverage R C
        (Protocol.restrict R C (binBranch p).residual)
        (List.replicate m Protocol.ActualBitSide.bob) := by
    exact
      M3_restricted_fullCoverage_of_dense_alpha d hpow hlog hchk P
        binBranch p Sdense hSnonempty R C hqcast htr ad
  let defaultAlpha : Fin (Params.q2 d) := ⟨0, Params.q2_pos d⟩
  let wordAlpha : List Bool -> Fin (Params.q2 d) := fun w =>
    if hw : w.length = m then
      Classical.choose
        ((M3_dense_codeOfAlpha_bijective d ad).2
          (Fin.cast (by rw [hw, hm_depth])
            (Protocol.codeOfBitList w)))
    else defaultAlpha
  have hwordAlpha_code :
      forall w (hw : w.length = m),
        ad.codeOfAlpha (wordAlpha w) =
          Fin.cast (by rw [hw, hm_depth])
            (Protocol.codeOfBitList w) := by
    intro w hw
    dsimp [wordAlpha]
    rw [dif_pos hw]
    exact
      Classical.choose_spec
        ((M3_dense_codeOfAlpha_bijective d ad).2
          (Fin.cast (by rw [hw, hm_depth])
            (Protocol.codeOfBitList w)))
  have hR1_nonempty : Nonempty (R1 d) := by
    have hq1pos : 0 < Params.q1 d :=
      lt_of_lt_of_le Nat.zero_lt_one hchk.one_le_q1
    exact ⟨(⟨0, hq1pos⟩, 0)⟩
  let r0 : R1 d := Classical.choice hR1_nonempty
  let rowEmbed :
      forall w, {r // r ∈ (Finset.univ : Finset (R1 d))} ->
        {a // a ∈ (binBranch p).rows} := fun w r =>
    let alpha := wordAlpha w
    let c := M3_fiber_cRep d Sdense alpha (hfiberCover alpha) r.val
    let hc : c ∈ Sdense :=
      M3_fiber_cRep_mem d Sdense alpha (hfiberCover alpha) r.val
    ⟨(p, c), hrow_mem c hc⟩
  let colEmbed :
      forall w, {gamma // gamma ∈ ad.Yalpha (wordAlpha w)} ->
        {b // b ∈ (binBranch p).cols} := fun w gamma =>
    let alpha := wordAlpha w
    let rho : M2DenseRows d :=
      ⟨(Fin.cast hqcast.symm alpha, gamma.val), by simp [M2DenseRin]⟩
    ⟨M3_diagCol d alpha gamma.val, by
      have h := hdiag_mem rho
      simpa [rho] using h⟩
  have hrowEmbed_mem :
      forall w r, rowEmbed w r ∈ R := by
    intro w r
    dsimp [rowEmbed, R, M3_denseSurvivorRows]
    refine Finset.mem_image.mpr ?_
    refine ⟨(⟨M3_fiber_cRep d Sdense (wordAlpha w)
          (hfiberCover (wordAlpha w)) r.val,
        M3_fiber_cRep_mem d Sdense (wordAlpha w)
          (hfiberCover (wordAlpha w)) r.val⟩ :
        M2DenseCols d Sdense), Finset.mem_univ _, ?_⟩
    rfl
  have hcolEmbed_mem :
      forall w gamma, colEmbed w gamma ∈ C := by
    intro w gamma
    dsimp [colEmbed, C, M3_denseDiagCols]
    refine Finset.mem_image.mpr ?_
    let rho : M2DenseRows d :=
      ⟨(Fin.cast hqcast.symm (wordAlpha w), gamma.val), by simp [M2DenseRin]⟩
    refine ⟨rho, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    simp [rho, M3_diagColBranch]
  refine
    { restricted_col := hrestricted
      cover := hcover
      hard := ?_ }
  refine
    M3_terminalHardWitnesses_of_wordwise_dense_Yalpha_prefix_copy
      d hpow hlog hchk
      (subgame (M3 d) (binBranch p).rows (binBranch p).cols)
      R C (Protocol.restrict R C (binBranch p).residual)
      (List.replicate m Protocol.ActualBitSide.bob)
      (fun w => ad.Yalpha (wordAlpha w))
      ?_ rowEmbed colEmbed ?_ ?_ ?_
  · intro w hw
    exact ad.Yalpha_dense (wordAlpha w)
  · intro w hw r
    have hwlen : w.length = m := by simpa using hw
    rw [Protocol.rowsAtPrefix_eq_of_firstKColBitsOn
      (R := R) (C := C)
      (P := Protocol.restrict R C (binBranch p).residual)
      (m := m) hrestricted hcover w hwlen]
    exact hrowEmbed_mem w r
  · intro w hw gamma
    have hwlen : w.length = m := by simpa using hw
    rw [Protocol.colsAtPrefix, Finset.mem_filter]
    refine ⟨hcolEmbed_mem w gamma, ?_⟩
    let alpha := wordAlpha w
    let c := M3_fiber_cRep d Sdense alpha (hfiberCover alpha) r0
    have hc : c ∈ Sdense :=
      M3_fiber_cRep_mem d Sdense alpha (hfiberCover alpha) r0
    refine ⟨rowEmbed w ⟨r0, Finset.mem_univ _⟩,
      hrowEmbed_mem w ⟨r0, Finset.mem_univ _⟩, ?_⟩
    have hbits :=
      M3_restricted_actualBitList_of_dense_Yalpha d P binBranch p Sdense R C
        hqcast htr ad hwlen (hwordAlpha_code w hwlen) hc gamma.property
    simpa [rowEmbed, colEmbed, alpha, c, htr,
      M3_binDenseReindex_of_memberships, equivOfInjectiveImage,
      M3_survivorRowBranch, M3_diagColBranch, R, C] using hbits
  · intro w hw r gamma
    let alpha := wordAlpha w
    let c := M3_fiber_cRep d Sdense alpha (hfiberCover alpha) r.val
    have hceval : S2fam d c alpha = r.val :=
      M3_fiber_cRep_eval d Sdense alpha (hfiberCover alpha) r.val
    simpa [rowEmbed, colEmbed, alpha, c, subgame] using
      M3_diagCol_exact_M1_of_fiber d p c alpha gamma.val r.val hceval

theorem M3_raw_prefix_eq_of_dense_Yalpha
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBranch p).rows})
    (C : Finset {b // b ∈ (binBranch p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (htr : M3BinDenseReindex d P binBranch p Sdense R C hqcast)
    (ad :
      M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
        (M3_bin_dense_protocol d P binBranch p Sdense R C hqcast htr))
    (hraw :
      Protocol.FirstKColBitsOn
        (Finset.univ : Finset {a // a ∈ (binBranch p).rows})
        (Finset.univ : Finset {b // b ∈ (binBranch p).cols})
        (Nat.clog 2 (Params.q2 d)) (binBranch p).residual)
    (hSnonempty : Sdense.Nonempty)
    {alpha : Fin (Params.q2 d)} {gamma gamma0 : C1 d}
    (hgamma : gamma ∈ ad.Yalpha alpha)
    (hgamma0 : gamma0 ∈ ad.Yalpha alpha) :
    Protocol.prefixCodeRaw (Nat.clog 2 (Params.q2 d))
        (Protocol.swap (binBranch p).residual)
        (htr.rowEquiv
          (⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩ :
            M2DenseRows d)).val =
      Protocol.prefixCodeRaw (Nat.clog 2 (Params.q2 d))
        (Protocol.swap (binBranch p).residual)
        (htr.rowEquiv
          (⟨(Fin.cast hqcast.symm alpha, gamma0), by simp [M2DenseRin]⟩ :
            M2DenseRows d)).val := by
  classical
  let m := Nat.clog 2 (Params.q2 d)
  let Q0 := Protocol.restrict R C (binBranch p).residual
  let Qswap := Protocol.restrictSub C R (Protocol.swap Q0)
  let Pdense :=
    M3_bin_dense_protocol d P binBranch p Sdense R C hqcast htr
  let rho : M2DenseRows d :=
    ⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩
  let rho0 : M2DenseRows d :=
    ⟨(Fin.cast hqcast.symm alpha, gamma0), by simp [M2DenseRin]⟩
  rcases hSnonempty with ⟨c, hc⟩
  let sigma : M2DenseCols d Sdense := ⟨c, hc⟩
  have hm : m = M2DenseDepth d := by
    dsimp [m]
    exact ad.depth_eq_clog_q2.symm
  have hprefix :
      Protocol.prefixCodeRaw (M2DenseDepth d) Pdense rho =
        Protocol.prefixCodeRaw (M2DenseDepth d) Pdense rho0 := by
    exact
      (M3_dense_Yalpha_prefixCode d ad alpha gamma hgamma).trans
        (M3_dense_Yalpha_prefixCode d ad alpha gamma0 hgamma0).symm
  have hdenseBits :
      Protocol.actualBitListRaw m Pdense rho sigma =
        Protocol.actualBitListRaw m Pdense rho0 sigma := by
    rw [hm]
    exact
      Protocol.actualBitListRaw_eq_of_firstKRowBitsOn_prefixCodeRaw_eq
        (R := (Finset.univ : Finset (M2DenseRows d)))
        (C := (Finset.univ : Finset (M2DenseCols d Sdense)))
        (P := Pdense) (k := M2DenseDepth d)
        ad.first_row_bits
        (Finset.mem_univ rho) (Finset.mem_univ rho0)
        (Finset.mem_univ sigma) (Finset.mem_univ sigma)
        hprefix
  have hresBits :
      Protocol.actualBitListRaw m Q0
          (htr.colEquiv sigma).val (htr.rowEquiv rho).val =
        Protocol.actualBitListRaw m Q0
          (htr.colEquiv sigma).val (htr.rowEquiv rho0).val := by
    calc
      Protocol.actualBitListRaw m Q0
          (htr.colEquiv sigma).val (htr.rowEquiv rho).val =
          Protocol.actualBitListRaw m (Protocol.swap Q0)
            (htr.rowEquiv rho).val (htr.colEquiv sigma).val := by
            exact
              (Protocol.actualBitListRaw_swap m Q0
                (htr.colEquiv sigma).val (htr.rowEquiv rho).val).symm
      _ =
          Protocol.actualBitListRaw m Qswap
            (htr.rowEquiv rho) (htr.colEquiv sigma) := by
            exact
              (Protocol.actualBitListRaw_restrictSub C R (Protocol.swap Q0)
                (htr.rowEquiv rho) (htr.colEquiv sigma) m).symm
      _ =
          Protocol.actualBitListRaw m Pdense rho sigma := by
            exact
              (Protocol.actualBitListRaw_reindex htr.rowEquiv htr.colEquiv
                m Qswap rho sigma).symm
      _ =
          Protocol.actualBitListRaw m Pdense rho0 sigma := hdenseBits
      _ =
          Protocol.actualBitListRaw m Qswap
            (htr.rowEquiv rho0) (htr.colEquiv sigma) := by
            exact
              Protocol.actualBitListRaw_reindex htr.rowEquiv htr.colEquiv
                m Qswap rho0 sigma
      _ =
          Protocol.actualBitListRaw m (Protocol.swap Q0)
            (htr.rowEquiv rho0).val (htr.colEquiv sigma).val := by
            exact
              Protocol.actualBitListRaw_restrictSub C R (Protocol.swap Q0)
                (htr.rowEquiv rho0) (htr.colEquiv sigma) m
      _ =
          Protocol.actualBitListRaw m Q0
            (htr.colEquiv sigma).val (htr.rowEquiv rho0).val := by
            exact
              Protocol.actualBitListRaw_swap m Q0
                (htr.colEquiv sigma).val (htr.rowEquiv rho0).val
  have hrawBits :
      Protocol.actualBitListRaw m (binBranch p).residual
          (htr.colEquiv sigma).val (htr.rowEquiv rho).val =
        Protocol.actualBitListRaw m (binBranch p).residual
          (htr.colEquiv sigma).val (htr.rowEquiv rho0).val := by
    exact
      Protocol.actualBitListRaw_eq_of_restrict_eq_of_firstKColBitsOn
        (S := (Finset.univ : Finset {a // a ∈ (binBranch p).rows}))
        (T := (Finset.univ : Finset {b // b ∈ (binBranch p).cols}))
        (R := R) (C := C) (P := (binBranch p).residual)
        (k := m) hraw
        (by intro a ha; exact Finset.mem_univ a)
        (by intro b hb; exact Finset.mem_univ b)
        (htr.colEquiv sigma).property (htr.colEquiv sigma).property
        (htr.rowEquiv rho).property (htr.rowEquiv rho0).property
        hresBits
  have hrawCode :
      Protocol.actualPrefixCodeRaw m (binBranch p).residual
          (htr.colEquiv sigma).val (htr.rowEquiv rho).val =
        Protocol.actualPrefixCodeRaw m (binBranch p).residual
          (htr.colEquiv sigma).val (htr.rowEquiv rho0).val :=
    Protocol.actualPrefixCodeRaw_eq_of_actualBitListRaw_eq hrawBits
  have hrowSwap :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset {b // b ∈ (binBranch p).cols})
        (Finset.univ : Finset {a // a ∈ (binBranch p).rows})
        m (Protocol.swap (binBranch p).residual) := by
    simpa [m, Protocol.FirstKColBitsOn] using hraw
  have hpref :
      Protocol.prefixCodeRaw m (Protocol.swap (binBranch p).residual)
          (htr.rowEquiv rho).val =
        Protocol.prefixCodeRaw m (Protocol.swap (binBranch p).residual)
          (htr.rowEquiv rho0).val := by
    calc
      Protocol.prefixCodeRaw m (Protocol.swap (binBranch p).residual)
          (htr.rowEquiv rho).val =
          Protocol.actualPrefixCodeRaw m
            (Protocol.swap (binBranch p).residual)
            (htr.rowEquiv rho).val (htr.colEquiv sigma).val := by
            exact
              (Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
                (Finset.univ : Finset {b // b ∈ (binBranch p).cols})
                (Finset.univ : Finset {a // a ∈ (binBranch p).rows})
                m (Protocol.swap (binBranch p).residual) hrowSwap
                (Finset.mem_univ (htr.rowEquiv rho).val)
                (Finset.mem_univ (htr.colEquiv sigma).val)).symm
      _ =
          Protocol.actualPrefixCodeRaw m (binBranch p).residual
            (htr.colEquiv sigma).val (htr.rowEquiv rho).val := by
            exact Protocol.actualPrefixCodeRaw_swap m
              (binBranch p).residual
              (htr.colEquiv sigma).val (htr.rowEquiv rho).val
      _ =
          Protocol.actualPrefixCodeRaw m (binBranch p).residual
            (htr.colEquiv sigma).val (htr.rowEquiv rho0).val := hrawCode
      _ =
          Protocol.actualPrefixCodeRaw m
            (Protocol.swap (binBranch p).residual)
            (htr.rowEquiv rho0).val (htr.colEquiv sigma).val := by
            exact
              (Protocol.actualPrefixCodeRaw_swap m
                (binBranch p).residual
                (htr.colEquiv sigma).val (htr.rowEquiv rho0).val).symm
      _ =
          Protocol.prefixCodeRaw m (Protocol.swap (binBranch p).residual)
            (htr.rowEquiv rho0).val := by
            exact
              Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
                (Finset.univ : Finset {b // b ∈ (binBranch p).cols})
                (Finset.univ : Finset {a // a ∈ (binBranch p).rows})
                m (Protocol.swap (binBranch p).residual) hrowSwap
                (Finset.mem_univ (htr.rowEquiv rho0).val)
                (Finset.mem_univ (htr.colEquiv sigma).val)
  simpa [m, rho, rho0] using hpref

theorem M3_fuzzy_transport_unit_cover_and_diag
    (d : Nat) (hpow : IsPow2 d) (hlog : 64 <= Nat.log 2 d)
    (hchk : Checklist d)
    (P : Protocol (R3 d) (C3 d) Bool)
    (binBranch : Fin 4 -> Protocol.BranchAt P (M3 d) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hrow_mem : forall c, c ∈ Sdense -> (p, c) ∈ (binBranch p).rows)
    (hdiag_mem : forall a : M2DenseRows d,
      M3_diagCol d (Fin.cast hqcast a.val.1) a.val.2 ∈
        (binBranch p).cols)
    (hSnonempty : Sdense.Nonempty)
    (hfiberCover : forall alpha,
      Sdense.image (fun c : C2 d => S2fam d c alpha) =
        (Finset.univ : Finset (R1 d)))
    (ad :
      let R :=
        M3_denseSurvivorRows d P binBranch p Sdense hrow_mem
      let C := M3_denseDiagCols d P binBranch p hqcast hdiag_mem
      let htr :=
        M3_binDenseReindex_of_memberships d P binBranch p Sdense hqcast
          hrow_mem hdiag_mem
      M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
        (M3_bin_dense_protocol d P binBranch p Sdense R C hqcast htr))
    (hraw :
      Protocol.FirstKColBitsOn
        (Finset.univ : Finset {a // a ∈ (binBranch p).rows})
        (Finset.univ : Finset {b // b ∈ (binBranch p).cols})
        (Nat.clog 2 (Params.q2 d)) (binBranch p).residual)
    {w : List Bool} (hw : w.length = Nat.clog 2 (Params.q2 d))
    {alpha : Fin (Params.q2 d)} {gamma gamma0 : C1 d}
    (hgamma : gamma ∈ ad.Yalpha alpha)
    (hgamma0 : gamma0 ∈ ad.Yalpha alpha) :
    let R :=
      M3_denseSurvivorRows d P binBranch p Sdense hrow_mem
    let C := M3_denseDiagCols d P binBranch p hqcast hdiag_mem
    Protocol.BranchFiberNonempty R C
      (Protocol.restrict R C (binBranch p).residual) w ∧
    ∃ hb : M3_diagCol d alpha gamma ∈ (binBranch p).cols,
      (⟨M3_diagCol d alpha gamma, hb⟩ : {b // b ∈ (binBranch p).cols}) ∈
        Protocol.colPrefixCols (Nat.clog 2 (Params.q2 d))
          (binBranch p).residual
          (Protocol.prefixCodeRaw (Nat.clog 2 (Params.q2 d))
            (Protocol.swap (binBranch p).residual)
            (⟨M3_diagCol d alpha gamma0, by
              let rho : M2DenseRows d :=
                ⟨(Fin.cast hqcast.symm alpha, gamma0), by simp [M2DenseRin]⟩
              have h := hdiag_mem rho
              simpa [rho] using h⟩ : {b // b ∈ (binBranch p).cols})) := by
  classical
  let R := M3_denseSurvivorRows d P binBranch p Sdense hrow_mem
  let C := M3_denseDiagCols d P binBranch p hqcast hdiag_mem
  let htr :=
    M3_binDenseReindex_of_memberships d P binBranch p Sdense hqcast
      hrow_mem hdiag_mem
  let hdata :=
    M3_stage3StopData_for_dense_bin d hpow hlog hchk P binBranch p
      Sdense hqcast hrow_mem hdiag_mem hSnonempty hfiberCover ad
  change
    Protocol.BranchFiberNonempty R C
        (Protocol.restrict R C (binBranch p).residual) w ∧
      ∃ hb : M3_diagCol d alpha gamma ∈ (binBranch p).cols,
        (⟨M3_diagCol d alpha gamma, hb⟩ : {b // b ∈ (binBranch p).cols}) ∈
          Protocol.colPrefixCols (Nat.clog 2 (Params.q2 d))
            (binBranch p).residual
            (Protocol.prefixCodeRaw (Nat.clog 2 (Params.q2 d))
              (Protocol.swap (binBranch p).residual)
              (⟨M3_diagCol d alpha gamma0, by
                let rho : M2DenseRows d :=
                  ⟨(Fin.cast hqcast.symm alpha, gamma0), by simp [M2DenseRin]⟩
                have h := hdiag_mem rho
                simpa [rho] using h⟩ : {b // b ∈ (binBranch p).cols}))
  refine ⟨?_, ?_⟩
  · exact hdata.cover w (by simpa using hw)
  · let hb : M3_diagCol d alpha gamma ∈ (binBranch p).cols := by
      let rho : M2DenseRows d :=
        ⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩
      have h := hdiag_mem rho
      simpa [rho] using h
    refine ⟨hb, ?_⟩
    rw [Protocol.colPrefixCols, Protocol.rowPrefixRows, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hprefix :=
      M3_raw_prefix_eq_of_dense_Yalpha d P binBranch p Sdense
        R C hqcast htr ad hraw hSnonempty hgamma hgamma0
    simpa [htr, M3_binDenseReindex_of_memberships, equivOfInjectiveImage,
      M3_diagColBranch, M3_diagCol] using hprefix

-- CLAIM-END aux:m3-fuzzy-transport

-- CLAIM-BEGIN lem:MThreeFuzzyLeaves

theorem M3_fuzzy_leaves
    (d : Nat) (hd : 2 <= d) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) (hchk : Checklist d)
    (hrobM2 :
      IsRobust (fun (c : C2 d) (r : R2 d) => M2 d r c)
        Params.delta (Params.b2 d))
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : Nat) <= Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hp1 : 2 ^ M2_T d <= 2 * M2_hard_seed_copies d)
    (hp2 : M2_hard_seed_copies d <= 2 ^ M2_T d)
    (hxseed_le_one : M2_hard_seed_rowDensity d <= 1)
    (hrow_threshold :
      Nat.ceil ((2 : Real) ^ (Nat.log 2 (Params.r2 d) : Nat) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : Real))
          <= Fintype.card (C1 d))
    (hseed_bridge : M2_hard_seed_columnDensity d <=
      Params.h2 d *
        (2 : Real) ^ (-((M2_T d + D (M1T d) : Nat) : Real)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hy_le_one : M1_stage2_terminal_density d <= 1)
    (hrowTerm : 9 * Params.t1 d <=
      16 * Nat.ceil ((Fintype.card (R1 d) : Real) *
        M1_stage2_terminal_density d))
    (hcolTerm : (2 : Real) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : Int))
        * (Fintype.card (C1 d) : Real) <=
      (Nat.ceil ((Fintype.card (C1 d) : Real) *
        ((2 : Real) ^ (-(Params.b1 d : Int)))) : Real))
    (hresidual_density : forall c, c <= M2_T d + D (M1T d) ->
      1 / 2 + Params.delta <=
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c /\
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c <= 1)
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hsigma0 : 0 < 1 - 8 * Params.h2 d)
    (hsigma1 : 1 - 8 * Params.h2 d <= 1)
    (hres_dense : IsColumnLossResilient (M1T d) (Params.b1 d : Real)
      (epsQT (Params.q2 d) (Params.t2 d))
      (Nat.log 2 (Params.q2 d)) (M2_T d) (1 - 8 * Params.h2 d))
    (hxseed_le_inv_r : M2_hard_seed_rowDensity d <=
      (2 : Real) ^ (-(Nat.log 2 (Params.r2 d) : Real)))
    (hseed_bridge_dense : M2_hard_seed_columnDensity d <=
      (1 - 8 * Params.h2 d) *
        (2 : Real) ^ (-((M2_T d + D (M1T d) : Nat) : Real)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hT1 : 1 <= M2_T d)
    (hgap_dense :
      2 ^ M2DenseDepth d *
        Nat.ceil ((2 : Real) ^ (1 - (Params.b1 d : Real)) *
          (Fintype.card (C1 d) : Real)) < Fintype.card (C1 d))
    (hraw : M2_hard_seed_to_h2prime_exp d)
    (hprime : M2_h2prime_bridge_exp d)
    (hy_three_fifths :
      forall c, c <= M2_T d + D (M1T d) ->
        (3 : Real) / 5 <=
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c)
    (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hcost : P.cost <= D (M2 d) + 2) :
    M3FuzzyLeavesConclusion d P := by
  classical
  have hlog64 : 64 <= Nat.log 2 d := by omega
  let hpartial :=
    M3_fuzzy_leaves_dense_alpha_partial d hpow hlog hchk hrobM2
      hm0_le hr2pow hp1 hp2 hxseed_le_one hrow_threshold hseed_bridge
      hy_le_one hrowTerm hcolTerm hresidual_density hqcast hsigma0
      hsigma1 hres_dense hxseed_le_inv_r hseed_bridge_dense hT1
      hgap_dense hraw hprime hy_three_fifths P hP hcost
  let hsep := hpartial.1
  let hStage2 := hpartial.2
  let hgap := M3_stage3_gap d hlog hchk
  let hC3 := M3_C3_univ_nonempty d hchk
  let binBranch := M3_binBranch d P hP hsep hgap hC3
  let hsurj := M3Bin_alphaOfCode_surj_on_Q d P hsep.dominant_bins hgap
  let S : Fin 4 -> Finset (C2 d) :=
    fun p => M3_binSurvivors d P hsep.dominant_bins hsurj p
  have hrow_mem :
      forall p, forall c, c ∈ S p -> (p, c) ∈ (binBranch p).rows := by
    intro p c hc
    dsimp [S, binBranch] at hc ⊢
    exact M3_binBranch_row_mem d P hP hsep hgap hC3 p c hc
  have hdiag_mem :
      forall p, forall a : M2DenseRows d,
        M3_diagCol d (Fin.cast hqcast a.val.1) a.val.2 ∈
          (binBranch p).cols := by
    intro p a
    dsimp [binBranch]
    exact M3_binBranch_diag_mem d P hP hsep hgap hC3 p hqcast a
  let R : forall p, Finset {a // a ∈ (binBranch p).rows} :=
    fun p => M3_denseSurvivorRows d P binBranch p (S p) (hrow_mem p)
  let C : forall p, Finset {b // b ∈ (binBranch p).cols} :=
    fun p => M3_denseDiagCols d P binBranch p hqcast (hdiag_mem p)
  let htr : forall p, M3BinDenseReindex d P binBranch p (S p)
      (R p) (C p) hqcast :=
    fun p =>
      M3_binDenseReindex_of_memberships d P binBranch p (S p) hqcast
        (hrow_mem p) (hdiag_mem p)
  let ad := fun p =>
    Classical.choice
      (M3_bin_dense_alpha_data_for_binBranch d P hP hsep hchk hgap hC3
        p hqcast hStage2 hcost)
  have hfiberCover :
      forall p alpha,
        (S p).image (fun c : C2 d => S2fam d c alpha) =
          (Finset.univ : Finset (R1 d)) := by
    intro p alpha
    exact
      M3_C2_fiber_cover_of_dense d hchk (S p)
        (by
          change
            (1 - 8 * Params.h2 d) * (Fintype.card (C2 d) : Real) <=
              ((M3_binSurvivors d P hsep.dominant_bins hsurj p).card : Real)
          exact
            M3_binSurvivors_dense d P hchk hsep.dominant_bins hsurj hgap p)
        alpha
  have hR1_nonempty : Nonempty (R1 d) := by
    have hq1pos : 0 < Params.q1 d :=
      lt_of_lt_of_le Nat.zero_lt_one hchk.one_le_q1
    exact ⟨(⟨0, hq1pos⟩, 0)⟩
  let r0 : R1 d := Classical.choice hR1_nonempty
  have hSnonempty : forall p, (S p).Nonempty := by
    intro p
    let alpha0 : Fin (Params.q2 d) := ⟨0, Params.q2_pos d⟩
    have hr0 :
        r0 ∈ (S p).image (fun c : C2 d => S2fam d c alpha0) := by
      rw [hfiberCover p alpha0]
      exact Finset.mem_univ r0
    rcases Finset.mem_image.mp hr0 with ⟨c, hc, _⟩
    exact ⟨c, hc⟩
  have hdata :
      forall p,
        Stage3StopData
          (subgame (M3 d) (binBranch p).rows (binBranch p).cols)
          (binBranch p).residual (R p) (C p)
          (Nat.clog 2 (Params.q2 d)) (D (M1 d)) := by
    intro p
    dsimp [R, C, htr, ad]
    exact
      M3_stage3StopData_for_dense_bin d hpow hlog64 hchk P binBranch p
        (S p) hqcast (hrow_mem p) (hdiag_mem p) (hSnonempty p)
        (hfiberCover p) (ad p)
  have hM2 :
      D (M2 d) = D (M1 d) + Nat.log 2 (Params.q2 d) :=
    M2_complexity_h2prime d hpow hlog hchk hm0_le hr2pow
      hrow_threshold hraw hprime hy_three_fifths
  have hbudget :
      forall p,
        (binBranch p).residual.cost <=
          Nat.clog 2 (Params.q2 d) + D (M1 d) := by
    exact
      stage3_bin_residual_budget d P binBranch (D (M1 d))
        hcost hM2 hchk.clog_q2_eq rfl
  have hcol :
      forall p,
        Protocol.FirstKColBitsOn
          (Finset.univ : Finset {a // a ∈ (binBranch p).rows})
          (Finset.univ : Finset {b // b ∈ (binBranch p).cols})
          (Nat.clog 2 (Params.q2 d)) (binBranch p).residual := by
    intro p
    exact
      stage3_binResidual_firstKColBitsOn_ambient d P binBranch p
        (D (M1 d)) (R p) (C p) (hbudget p) (hdata p)
  have hYnonempty :
      forall p alpha, ((ad p).Yalpha alpha).Nonempty := by
    intro p alpha
    exact
      M1_dense_columns_nonempty d hpow hlog64 hchk
        ((ad p).Yalpha alpha) ((ad p).Yalpha_dense alpha)
  let gammaRep : forall p alpha, C1 d :=
    fun p alpha => Classical.choose (hYnonempty p alpha)
  have gammaRep_mem :
      forall p alpha, gammaRep p alpha ∈ (ad p).Yalpha alpha := by
    intro p alpha
    exact Classical.choose_spec (hYnonempty p alpha)
  let diagSub :
      forall p alpha gamma, {b // b ∈ (binBranch p).cols} :=
    fun p alpha gamma =>
      ⟨M3_diagCol d alpha gamma, by
        let rho : M2DenseRows d :=
          ⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩
        have h := hdiag_mem p rho
        simpa [rho] using h⟩
  let codeOfAlpha :
      Fin 4 -> Fin (Params.q2 d) -> Fin (2 ^ Nat.clog 2 (Params.q2 d)) :=
    fun p alpha =>
      Protocol.prefixCodeRaw (Nat.clog 2 (Params.q2 d))
        (Protocol.swap (binBranch p).residual)
        (diagSub p alpha (gammaRep p alpha))
  have hcols :
      forall p alpha,
        (Protocol.colPrefixCols (Nat.clog 2 (Params.q2 d))
          (binBranch p).residual (codeOfAlpha p alpha)).Nonempty := by
    intro p alpha
    refine ⟨diagSub p alpha (gammaRep p alpha), ?_⟩
    simp [Protocol.colPrefixCols, Protocol.rowPrefixRows, codeOfAlpha]
  have htarget :
      M3BudgetColumnTarget d P binBranch codeOfAlpha := by
    exact
      M3_budget_column_target_of_stopdata d P binBranch codeOfAlpha
        (D (M1 d)) R C hbudget hdata hcols
  have hdiag :
      forall p alpha gamma, gamma ∈ (ad p).Yalpha alpha ->
        exists (hb : M3_diagCol d alpha gamma ∈ (binBranch p).cols),
          (⟨M3_diagCol d alpha gamma, hb⟩ :
            {b // b ∈ (binBranch p).cols}) ∈
            Protocol.colPrefixCols (Nat.clog 2 (Params.q2 d))
              (binBranch p).residual (codeOfAlpha p alpha) := by
    intro p alpha gamma hgamma
    refine ⟨(diagSub p alpha gamma).property, ?_⟩
    change diagSub p alpha gamma ∈
      Protocol.colPrefixCols (Nat.clog 2 (Params.q2 d))
        (binBranch p).residual (codeOfAlpha p alpha)
    rw [Protocol.colPrefixCols, Protocol.rowPrefixRows, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hprefix :=
      M3_raw_prefix_eq_of_dense_Yalpha d P binBranch p (S p)
        (R p) (C p) hqcast (htr p) (ad p) (hcol p)
        (hSnonempty p) hgamma (gammaRep_mem p alpha)
    simpa [codeOfAlpha, diagSub, htr,
      M3_binDenseReindex_of_memberships, equivOfInjectiveImage,
      M3_diagColBranch, M3_diagCol] using hprefix
  let bridge :
      M3_fuzzy_leaves_sync_bridge d hpow hlog hchk hrobM2
        hm0_le hr2pow hp1 hp2 hxseed_le_one hrow_threshold hseed_bridge
        hy_le_one hrowTerm hcolTerm hresidual_density hqcast hsigma0
        hsigma1 hres_dense hxseed_le_inv_r hseed_bridge_dense hT1
        hgap_dense hraw hprime hy_three_fifths P hP hcost := by
    dsimp [M3_fuzzy_leaves_sync_bridge]
    exact
      M3_build_sync_bridge d P binBranch
        (fun p alpha => (ad p).Yalpha alpha)
        codeOfAlpha htarget.1 htarget.2 hdiag
  exact
    M3_fuzzy_leaves_of_sync_bridge d hd hpow hlog hchk hrobM2
      hm0_le hr2pow hp1 hp2 hxseed_le_one hrow_threshold hseed_bridge
      hy_le_one hrowTerm hcolTerm hresidual_density hqcast hsigma0
      hsigma1 hres_dense hxseed_le_inv_r hseed_bridge_dense hT1
      hgap_dense hraw hprime hy_three_fifths P hP hcost bridge


-- CLAIM-END lem:MThreeFuzzyLeaves

end NPCC
