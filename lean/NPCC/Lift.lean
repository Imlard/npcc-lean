import NPCC.Reduction

set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1600000

namespace NPCC

open Workspace.Types.Protocol
open Workspace.Types.CommComplexity

def IsPartition4 {n : Nat} (B : Fin 4 -> Finset (Fin n)) : Prop :=
  ∀ i : Fin n, ∃! p : Fin 4, i ∈ B p

noncomputable def Xhat (d : Nat) (alpha : Fin (Params.q2 d)) : Finset (C4 d) :=
  diagCopySet d alpha

noncomputable def SPrime (d : Nat) (alpha : Fin (Params.q2 d))
    (Y : Finset (C4 d)) : Finset (C1 d) :=
  diagPullback d alpha Y

noncomputable def localCoordSet (d : Nat) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (alpha : Fin (Params.q2 d)) (B : Finset (Fin n)) :
    Finset (Fin (Params.q1 d + 5)) :=
  (Finset.univ.image (fun i : Fin (Params.q1 d) => baseIdx d i)) ∪
    ((transversalAt v alpha B).image
      (fun i : Fin n => slotIdx d (gadgetSlot v alpha i)))

noncomputable def localRows (d : Nat) {n : Nat} (p : Fin 4)
    (T : Finset (C2 d)) (B : Finset (Fin n)) : Finset (R4 d n) :=
  (T.image (fun c : C2 d => (Sum.inl (p, c) : R4 d n))) ∪
    (B.image (fun i : Fin n => (Sum.inr i : R4 d n)))

def DuplicateExpansionContained {A B A0 B0 : Type*}
    (G : A -> B -> Bool) (R : Finset A) (C : Finset B)
    (g0 : A0 -> B0 -> Bool) : Prop :=
  exists R' : Finset A, R' ⊆ R ∧
  exists C' : Finset B, C' ⊆ C ∧
  exists rowMap : {a // a ∈ R'} -> A0,
  exists colMap : {b // b ∈ C'} -> B0,
    Function.Surjective rowMap ∧
    Function.Surjective colMap ∧
    ∀ a b, G a.val b.val = g0 (rowMap a) (colMap b)

def DuplicateExpansionComputedByResidual {A B A0 B0 : Type*}
    {R0 : Finset A} {C0 : Finset B}
    (Q : Protocol {a // a ∈ R0} {b // b ∈ C0} Bool)
    (R : Finset A) (C : Finset B) (g0 : A0 -> B0 -> Bool) : Prop :=
  exists hR : R ⊆ R0,
  exists hC : C ⊆ C0,
  exists R' : Finset A,
  exists hR' : R' ⊆ R,
  exists C' : Finset B,
  exists hC' : C' ⊆ C,
  exists rowMap : {a // a ∈ R'} -> A0,
  exists colMap : {b // b ∈ C'} -> B0,
    Function.Surjective rowMap ∧
    Function.Surjective colMap ∧
    ∀ a b,
      Q.eval
          ⟨a.val, hR (hR' a.property)⟩
          ⟨b.val, hC (hC' b.property)⟩ =
        g0 (rowMap a) (colMap b)

def M4LocalBranch (d : Nat) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (B : Fin 4 -> Finset (Fin n))
    (p : Fin 4) (alpha : Fin (Params.q2 d))
    (br : Protocol.BranchAt P (M4 d v)
      (2 + Nat.clog 2 (Params.q2 d))) : Prop :=
  (∀ i : Fin n, (Sum.inr i : R4 d n) ∈ br.rows ↔ i ∈ B p) ∧
  br.residual.cost <= Bcap d ∧
  exists Y : Finset (C4 d),
    Y ⊆ br.cols ∧
    Y ⊆ Xhat d alpha ∧
    (1 - Params.eta2 d) * ((Xhat d alpha).card : Real) <=
      (Y.card : Real) ∧
    let S' := SPrime d alpha Y
    exists T : Finset (C2 d),
      (∀ c ∈ T, (Sum.inl (p, c) : R4 d n) ∈ br.rows) ∧
      (∀ r : R1 d, ∃ c ∈ T, S2fam d c alpha = r) ∧
      exists (u : Nat) (e : Fin u -> Fin (Params.q1 d + 5)),
        Function.Injective e ∧
        Finset.univ.image e = localCoordSet d v alpha (B p) ∧
        DuplicateExpansionContained
          (M4 d v)
          (localRows d p T (B p))
          Y
          (HlocalAtSub d (S1fam d) S' e) ∧
        DuplicateExpansionComputedByResidual
          br.residual
          (localRows d p T (B p))
          Y
          (HlocalAtSub d (S1fam d) S' e)

noncomputable def templateRows (d n : Nat) : Finset (R4 d n) :=
  Finset.univ.image (fun r : R3 d => (Sum.inl r : R4 d n))

noncomputable def templateCols (d : Nat) (k0 : Fin (2 ^ 5)) : Finset (C4 d) :=
  Finset.univ.image (fun c : C3 d => (k0, c))

noncomputable def templateRowMap (d n : Nat) :
    R3 d -> {r : R4 d n // r ∈ templateRows d n} :=
  fun r => ⟨Sum.inl r, by
    unfold templateRows
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩⟩

theorem templateRowMap_bijective (d n : Nat) :
    Function.Bijective (templateRowMap d n) := by
  constructor
  · intro x y h
    have hv := congrArg Subtype.val h
    exact Sum.inl.inj hv
  · intro r
    have hr := r.property
    unfold templateRows at hr
    rcases Finset.mem_image.mp hr with ⟨x, -, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

noncomputable def templateRowEquiv (d n : Nat) :
    R3 d ≃ {r : R4 d n // r ∈ templateRows d n} :=
  Equiv.ofBijective (templateRowMap d n) (templateRowMap_bijective d n)

noncomputable def templateColMap (d : Nat) (k0 : Fin (2 ^ 5)) :
    C3 d -> {c : C4 d // c ∈ templateCols d k0} :=
  fun c => ⟨(k0, c), by
    unfold templateCols
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩⟩

theorem templateColMap_bijective (d : Nat) (k0 : Fin (2 ^ 5)) :
    Function.Bijective (templateColMap d k0) := by
  constructor
  · intro x y h
    have hv := congrArg Subtype.val h
    exact Prod.mk.inj hv |>.2
  · intro c
    have hc := c.property
    unfold templateCols at hc
    rcases Finset.mem_image.mp hc with ⟨x, -, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

noncomputable def templateColEquiv (d : Nat) (k0 : Fin (2 ^ 5)) :
    C3 d ≃ {c : C4 d // c ∈ templateCols d k0} :=
  Equiv.ofBijective (templateColMap d k0) (templateColMap_bijective d k0)

noncomputable def templateSliceProtocol (d : Nat) {n : Nat}
    (P : Protocol (R4 d n) (C4 d) Bool) (k0 : Fin (2 ^ 5)) :
    Protocol (R3 d) (C3 d) Bool :=
  Protocol.reindex (templateRowEquiv d n) (templateColEquiv d k0)
    (Protocol.restrictSub (templateRows d n) (templateCols d k0)
      (Protocol.restrict (templateRows d n) (templateCols d k0) P))

theorem templateSliceProtocol_computes (d : Nat) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool) (k0 : Fin (2 ^ 5))
    (hP : P.Computes (M4 d v)) :
    (templateSliceProtocol d P k0).Computes (M3 d) := by
  intro r c
  unfold templateSliceProtocol
  rw [Protocol.eval_reindex]
  rw [Protocol.eval_restrictSub]
  rw [Protocol.eval_restrict_of_mem (templateRows d n) (templateCols d k0) P
    (templateRowEquiv d n r).property (templateColEquiv d k0 c).property]
  · rw [hP]
    rfl

theorem templateSliceProtocol_cost_le (d : Nat) {n : Nat}
    (P : Protocol (R4 d n) (C4 d) Bool) (k0 : Fin (2 ^ 5)) :
    (templateSliceProtocol d P k0).cost <= P.cost := by
  unfold templateSliceProtocol
  rw [Protocol.cost_reindex]
  rw [Protocol.cost_restrictSub]
  exact Protocol.cost_restrict_le (templateRows d n) (templateCols d k0) P

theorem templateSliceProtocol_cost_le_M3_budget
    (d : Nat) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) (hchk : Checklist d)
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
    {n : Nat} (P : Protocol (R4 d n) (C4 d) Bool)
    (hcost : P.cost <= Byes d) (k0 : Fin (2 ^ 5)) :
    (templateSliceProtocol d P k0).cost <= D (M2 d) + 2 := by
  have hlog64 : 64 <= Nat.log 2 d := by omega
  have hM1 : D (M1 d) = Bcap d := by
    rw [M1_complexity d hpow hlog64, Bcap]
  have hM2 :
      D (M2 d) = D (M1 d) + Nat.log 2 (Params.q2 d) :=
    M2_complexity_h2prime d hpow hlog hchk hm0_le hr2pow
      hrow_threshold hraw hprime hy_three_fifths
  have hByes : Byes d = D (M2 d) + 2 := by
    rw [Byes, hchk.clog_q2_eq, hM2, hM1]
    omega
  exact le_trans (templateSliceProtocol_cost_le d P k0)
    (by simpa [hByes] using hcost)

theorem templateSlice_fuzzy_leaves
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
    {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (hP : P.Computes (M4 d v))
    (hcost : P.cost <= Byes d)
    (k0 : Fin (2 ^ 5)) :
    M3FuzzyLeavesConclusion d (templateSliceProtocol d P k0) := by
  exact
    M3_fuzzy_leaves d hd hpow hlog hchk hrobM2
      hm0_le hr2pow hp1 hp2 hxseed_le_one hrow_threshold hseed_bridge
      hy_le_one hrowTerm hcolTerm hresidual_density hqcast hsigma0
      hsigma1 hres_dense hxseed_le_inv_r hseed_bridge_dense hT1
      hgap_dense hraw hprime hy_three_fifths
      (templateSliceProtocol d P k0)
      (templateSliceProtocol_computes d v P k0 hP)
      (templateSliceProtocol_cost_le_M3_budget d hpow hlog hchk hm0_le
        hr2pow hrow_threshold hraw hprime hy_three_fifths P hcost k0)

theorem templateSlice_separation
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
    {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (hP : P.Computes (M4 d v))
    (hcost : P.cost <= Byes d)
    (k0 : Fin (2 ^ 5)) :
    M3SeparationConclusion d (templateSliceProtocol d P k0) := by
  exact
    M3_separation_closed d hpow hlog hchk hrobM2
      hm0_le hr2pow hrow_threshold hraw hprime hy_three_fifths
      (templateSliceProtocol d P k0)
      (templateSliceProtocol_computes d v P k0 hP)
      (templateSliceProtocol_cost_le_M3_budget d hpow hlog hchk hm0_le
        hr2pow hrow_threshold hraw hprime hy_three_fifths P hcost k0)

private theorem image_univ_subtype_val_eq_self
    {A : Type*} [Fintype A] [DecidableEq A] (R : Finset A) :
    ((Finset.univ : Finset {a // a ∈ R}).image fun a => a.val) = R := by
  classical
  ext a
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨x, _hx, hxa⟩
    subst hxa
    exact x.property
  · intro ha
    exact Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩

private theorem map_univ_equiv_eq_univ
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) :
    (Finset.univ : Finset A).map ⟨e, e.injective⟩ =
      (Finset.univ : Finset B) := by
  classical
  ext b
  constructor
  · intro _; exact Finset.mem_univ b
  · intro _
    exact Finset.mem_map.mpr ⟨e.symm b, Finset.mem_univ _, by simp⟩

theorem templateSlice_first_row_bits_to_restrict
    (d : Nat) {n : Nat}
    (P : Protocol (R4 d n) (C4 d) Bool) (k0 : Fin (2 ^ 5))
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset (R3 d))
        (Finset.univ : Finset (C3 d))
        2 (templateSliceProtocol d P k0)) :
    Protocol.FirstKRowBitsOn
      (templateRows d n) (templateCols d k0) 2
      (Protocol.restrict (templateRows d n) (templateCols d k0) P) := by
  classical
  unfold templateSliceProtocol at hrow
  have h1 :=
    Protocol.firstKRowBitsOn_of_reindex
      (templateRowEquiv d n) (templateColEquiv d k0)
      (Protocol.restrictSub (templateRows d n) (templateCols d k0)
        (Protocol.restrict (templateRows d n) (templateCols d k0) P))
      2 (Finset.univ : Finset (R3 d))
      (Finset.univ : Finset (C3 d)) hrow
  have h1u :
      Protocol.FirstKRowBitsOn
        (Finset.univ :
          Finset {a : R4 d n // a ∈ templateRows d n})
        (Finset.univ :
          Finset {b : C4 d // b ∈ templateCols d k0})
        2
        (Protocol.restrictSub (templateRows d n) (templateCols d k0)
          (Protocol.restrict (templateRows d n) (templateCols d k0) P)) := by
    simpa [map_univ_equiv_eq_univ] using h1
  have h2 :=
    Protocol.firstKRowBitsOn_of_restrictSub
      (templateRows d n) (templateCols d k0)
      (Finset.univ :
        Finset {a : R4 d n // a ∈ templateRows d n})
      (Finset.univ :
        Finset {b : C4 d // b ∈ templateCols d k0})
      2
      (Protocol.restrict (templateRows d n) (templateCols d k0) P)
      h1u
  simpa [image_univ_subtype_val_eq_self] using h2

theorem M3_codeOfBin_bijective
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
        hNW (fun j : Fin (2 ^ 2) => j)) :
    Function.Bijective (fun p : Fin 4 => M3_codeOfBin d P hNW hsurj p) := by
  classical
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro p q hpq
    dsimp at hpq
    have hpa := M3_alphaOf_codeOfBin d P hNW hsurj p
    have hqa := M3_alphaOf_codeOfBin d P hNW hsurj q
    rw [hpq] at hpa
    exact hpa.symm.trans hqa
  · simp

private theorem two_zpow_neg_nat_add_one_eq_rpow_one_sub_nat_public (n : Nat) :
    (2 : Real) ^ (-(n : Int) + 1) = (2 : Real) ^ (1 - (n : Real)) := by
  have hcast : (((-(n : Int) + 1 : Int) : Real) = 1 - (n : Real)) := by
    norm_num
    ring
  rw [hcast.symm]
  exact (Real.rpow_intCast (2 : Real) (-(n : Int) + 1)).symm

theorem M3_stage3_gap_public (d : Nat) (hlog : 2 ^ 18 <= Nat.log 2 d)
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
    rw [two_zpow_neg_nat_add_one_eq_rpow_one_sub_nat_public]
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

theorem M3_binBranch_transcripts_bijective
    (d : Nat) (P : Protocol (R3 d) (C3 d) Bool)
    (hP : P.Computes (M3 d))
    (hsep : M3SeparationConclusion d P)
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d))
    (hC3 : (Finset.univ : Finset (C3 d)).Nonempty) :
    Function.Bijective
      (fun p : Fin 4 =>
        (M3_binBranch d P hP hsep hgap hC3 p).transcript) := by
  classical
  let hsurj := M3Bin_alphaOfCode_surj_on_Q d P hsep.dominant_bins hgap
  change Function.Bijective
    (fun p : Fin 4 => M3_codeOfBin d P hsep.dominant_bins hsurj p)
  exact M3_codeOfBin_bijective d P hsep.dominant_bins hsurj

theorem two_bit_codeOfBitList_surjective (j : Fin (2 ^ 2)) :
    exists w : {w : List Bool // w.length = 2},
      Fin.cast (by rw [w.property]) (Protocol.codeOfBitList w.val) = j := by
  fin_cases j
  · refine ⟨⟨[false, false], by simp⟩, ?_⟩
    apply Fin.ext
    norm_num [Protocol.codeOfBitList, Protocol.bitCons, Protocol.zeroPow2]
  · refine ⟨⟨[false, true], by simp⟩, ?_⟩
    apply Fin.ext
    norm_num [Protocol.codeOfBitList, Protocol.bitCons, Protocol.zeroPow2]
  · refine ⟨⟨[true, false], by simp⟩, ?_⟩
    apply Fin.ext
    norm_num [Protocol.codeOfBitList, Protocol.bitCons, Protocol.zeroPow2]
  · refine ⟨⟨[true, true], by simp⟩, ?_⟩
    apply Fin.ext
    norm_num [Protocol.codeOfBitList, Protocol.bitCons, Protocol.zeroPow2]

theorem actualPrefixCodeRaw_eq_codeOfBitList_of_actualBitListRaw_eq
    {A B Z : Type*} {k : Nat} (P : Protocol A B Z) (a : A) (b : B)
    {w : List Bool}
    (hbits : Protocol.actualBitListRaw k P a b = w)
    (hw : w.length = k) :
    Protocol.actualPrefixCodeRaw k P a b =
      Fin.cast (by rw [hw]) (Protocol.codeOfBitList w) := by
  induction k generalizing P w with
  | zero =>
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero hw
      subst w
      rfl
  | succ k ih =>
      cases P with
      | leaf z =>
          simp [Protocol.actualBitListRaw] at hbits
          subst w
          simp at hw
      | aNode q l r =>
          cases w with
          | nil =>
              simp at hw
          | cons bit tail =>
              have hbits' :
                  q a ::
                    Protocol.actualBitListRaw k
                      (if q a then r else l) a b =
                    bit :: tail := by
                simpa [Protocol.actualBitListRaw] using hbits
              have hhead : q a = bit := (List.cons.inj hbits').1
              have htail :
                  Protocol.actualBitListRaw k
                      (if q a then r else l) a b =
                    tail := (List.cons.inj hbits').2
              have htailLen : tail.length = k := by
                simpa using hw
              have htailCode :=
                ih (P := if q a then r else l) (w := tail) htail htailLen
              have htailVal :
                  (Protocol.actualPrefixCodeRaw k
                      (if q a then r else l) a b).val =
                    (Protocol.codeOfBitList tail).val := by
                have hv := congrArg Fin.val htailCode
                simpa [htailLen] using hv
              apply Fin.ext
              cases bit
              · simp [Protocol.actualPrefixCodeRaw,
                  Protocol.codeOfBitList, Protocol.bitCons, hhead]
                simpa [hhead] using htailVal
              · simp [Protocol.actualPrefixCodeRaw,
                  Protocol.codeOfBitList, Protocol.bitCons, hhead, htailLen]
                simpa [hhead] using htailVal
      | bNode q l r =>
          cases w with
          | nil =>
              simp at hw
          | cons bit tail =>
              have hbits' :
                  q b ::
                    Protocol.actualBitListRaw k
                      (if q b then r else l) a b =
                    bit :: tail := by
                simpa [Protocol.actualBitListRaw] using hbits
              have hhead : q b = bit := (List.cons.inj hbits').1
              have htail :
                  Protocol.actualBitListRaw k
                      (if q b then r else l) a b =
                    tail := (List.cons.inj hbits').2
              have htailLen : tail.length = k := by
                simpa using hw
              have htailCode :=
                ih (P := if q b then r else l) (w := tail) htail htailLen
              have htailVal :
                  (Protocol.actualPrefixCodeRaw k
                      (if q b then r else l) a b).val =
                    (Protocol.codeOfBitList tail).val := by
                have hv := congrArg Fin.val htailCode
                simpa [htailLen] using hv
              apply Fin.ext
              cases bit
              · simp [Protocol.actualPrefixCodeRaw,
                  Protocol.codeOfBitList, Protocol.bitCons, hhead]
                simpa [hhead] using htailVal
              · simp [Protocol.actualPrefixCodeRaw,
                  Protocol.codeOfBitList, Protocol.bitCons, hhead, htailLen]
                simpa [hhead] using htailVal

theorem C4_univ_nonempty (d : Nat) (hchk : Checklist d) (k0 : Fin (2 ^ 5)) :
    (Finset.univ : Finset (C4 d)).Nonempty := by
  classical
  obtain ⟨c, _hc⟩ := M3_C3_univ_nonempty d hchk
  exact ⟨(k0, c), Finset.mem_univ _⟩

noncomputable def vectorPrefixBin (d : Nat) {n : Nat}
    (P : Protocol (R4 d n) (C4 d) Bool)
    (code : Fin 4 -> Fin (2 ^ 2)) (p : Fin 4) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    Protocol.prefixCodeRaw 2 P (Sum.inr i : R4 d n) = code p

theorem vectorPrefixBin_partition (d : Nat) {n : Nat}
    (P : Protocol (R4 d n) (C4 d) Bool)
    (code : Fin 4 -> Fin (2 ^ 2))
    (hcode : Function.Bijective code) :
    IsPartition4 (vectorPrefixBin d P code) := by
  classical
  intro i
  obtain ⟨p, hp⟩ := hcode.2
    (Protocol.prefixCodeRaw 2 P (Sum.inr i : R4 d n))
  refine ⟨p, ?_, ?_⟩
  · change i ∈ (Finset.univ.filter fun i =>
      Protocol.prefixCodeRaw 2 P (Sum.inr i : R4 d n) = code p)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hp.symm⟩
  · intro q hq
    change i ∈ (Finset.univ.filter fun i =>
      Protocol.prefixCodeRaw 2 P (Sum.inr i : R4 d n) = code q) at hq
    rw [Finset.mem_filter] at hq
    apply hcode.1
    rw [hp, hq.2]

noncomputable def ambientBinBranch (d : Nat) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (code : Fin 4 -> Fin (2 ^ 2))
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset (R4 d n))
        (Finset.univ : Finset (C4 d)) 2 P)
    (hP : P.Computes (M4 d v))
    (hrows : forall p, (Protocol.rowPrefixRows 2 P (code p)).Nonempty)
    (hcols : (Finset.univ : Finset (C4 d)).Nonempty)
    (p : Fin 4) : Protocol.BranchAt P (M4 d v) 2 :=
  Protocol.mkBranchAt_of_rowPrefix P (M4 d v) 2 (code p)
    hrow hP (hrows p) hcols

theorem ambientBinBranch_transcripts_bijective (d : Nat) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (code : Fin 4 -> Fin (2 ^ 2))
    (hcode : Function.Bijective code)
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset (R4 d n))
        (Finset.univ : Finset (C4 d)) 2 P)
    (hP : P.Computes (M4 d v))
    (hrows : forall p, (Protocol.rowPrefixRows 2 P (code p)).Nonempty)
    (hcols : (Finset.univ : Finset (C4 d)).Nonempty) :
    Function.Bijective
      (fun p : Fin 4 =>
        (ambientBinBranch d v P code hrow hP hrows hcols p).transcript) := by
  simpa [ambientBinBranch] using hcode

theorem ambientBinBranch_sideTrace (d : Nat) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (code : Fin 4 -> Fin (2 ^ 2))
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset (R4 d n))
        (Finset.univ : Finset (C4 d)) 2 P)
    (hP : P.Computes (M4 d v))
    (hrows : forall p, (Protocol.rowPrefixRows 2 P (code p)).Nonempty)
    (hcols : (Finset.univ : Finset (C4 d)).Nonempty)
    (p : Fin 4) :
    (ambientBinBranch d v P code hrow hP hrows hcols p).sideTrace =
      [Protocol.ActualBitSide.alice, Protocol.ActualBitSide.alice] := by
  simp [ambientBinBranch, Protocol.mkBranchAt_of_rowPrefix]

theorem ambientBinBranch_cols_univ (d : Nat) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (code : Fin 4 -> Fin (2 ^ 2))
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset (R4 d n))
        (Finset.univ : Finset (C4 d)) 2 P)
    (hP : P.Computes (M4 d v))
    (hrows : forall p, (Protocol.rowPrefixRows 2 P (code p)).Nonempty)
    (hcols : (Finset.univ : Finset (C4 d)).Nonempty)
    (p : Fin 4) (y : C4 d) :
    y ∈ (ambientBinBranch d v P code hrow hP hrows hcols p).cols := by
  simp [ambientBinBranch, Protocol.mkBranchAt_of_rowPrefix]

theorem ambientBinBranch_vector_rows (d : Nat) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (code : Fin 4 -> Fin (2 ^ 2))
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset (R4 d n))
        (Finset.univ : Finset (C4 d)) 2 P)
    (hP : P.Computes (M4 d v))
    (hrows : forall p, (Protocol.rowPrefixRows 2 P (code p)).Nonempty)
    (hcols : (Finset.univ : Finset (C4 d)).Nonempty)
    (p : Fin 4) (i : Fin n) :
    (Sum.inr i : R4 d n) ∈
        (ambientBinBranch d v P code hrow hP hrows hcols p).rows ↔
      i ∈ vectorPrefixBin d P code p := by
  simp [ambientBinBranch, Protocol.mkBranchAt_of_rowPrefix,
    Protocol.rowPrefixRows, vectorPrefixBin]

theorem ambientBinBranch_residual_budget (d : Nat) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (code : Fin 4 -> Fin (2 ^ 2))
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset (R4 d n))
        (Finset.univ : Finset (C4 d)) 2 P)
    (hP : P.Computes (M4 d v))
    (hcost : P.cost <= Byes d)
    (hrows : forall p, (Protocol.rowPrefixRows 2 P (code p)).Nonempty)
    (hcols : (Finset.univ : Finset (C4 d)).Nonempty)
    (p : Fin 4) :
    (ambientBinBranch d v P code hrow hP hrows hcols p).residual.cost <=
      Nat.clog 2 (Params.q2 d) + Bcap d := by
  have hbranch :=
    (ambientBinBranch d v P code hrow hP hrows hcols p).cost_after_actualBits
  have hByes : Byes d = 2 + (Nat.clog 2 (Params.q2 d) + Bcap d) := by
    unfold Byes
    omega
  omega

theorem M4_ambient_first_two_row_bits_of_phaseA_certificates
    (d : Nat) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (hP : P.Computes (M4 d v))
    (hcost : P.cost <= Byes d)
    (k0 : Fin (2 ^ 5))
    (hfirst :
      Protocol.FirstKRowBitsOn
        (templateRows d n) (templateCols d k0) 2
        (Protocol.restrict (templateRows d n) (templateCols d k0) P))
    (hcover :
      Protocol.FullStoppingFiberCoverage
        (templateRows d n) (templateCols d k0)
        (Protocol.restrict (templateRows d n) (templateCols d k0) P)
        (List.replicate 2 Protocol.ActualBitSide.alice))
    (hhard :
      Protocol.TerminalHardWitnesses (M4 d v)
        (templateRows d n) (templateCols d k0)
        (Protocol.restrict (templateRows d n) (templateCols d k0) P)
        (List.replicate 2 Protocol.ActualBitSide.alice)
        (Nat.clog 2 (Params.q2 d) + Bcap d)) :
    Protocol.FirstKRowBitsOn
      (Finset.univ : Finset (R4 d n))
      (Finset.univ : Finset (C4 d)) 2 P := by
  have hcost' :
      P.cost <= 2 + (Nat.clog 2 (Params.q2 d) + Bcap d) := by
    unfold Byes at hcost
    omega
  exact
    Protocol.noWaste_firstKRowBitsOn_univ_of_restrict
      (M4 d v) P (templateRows d n) (templateCols d k0)
      2 (Nat.clog 2 (Params.q2 d) + Bcap d)
      hP hcost' hfirst hcover hhard

theorem M4_phaseA_package
    (d : Nat) (hchk : Checklist d) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (hP : P.Computes (M4 d v))
    (hcost : P.cost <= Byes d)
    (k0 : Fin (2 ^ 5))
    (code : Fin 4 -> Fin (2 ^ 2))
    (hcode : Function.Bijective code)
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset (R4 d n))
        (Finset.univ : Finset (C4 d)) 2 P)
    (hrows : forall p, (Protocol.rowPrefixRows 2 P (code p)).Nonempty) :
    ∃ B : Fin 4 -> Finset (Fin n),
      IsPartition4 B ∧
      ∃ binBr : ∀ p : Fin 4, Protocol.BranchAt P (M4 d v) 2,
        Function.Bijective (fun p : Fin 4 => (binBr p).transcript) ∧
        (∀ p : Fin 4,
          (binBr p).sideTrace =
            [Protocol.ActualBitSide.alice, Protocol.ActualBitSide.alice]) ∧
        (∀ p : Fin 4, ∀ y : C4 d, y ∈ (binBr p).cols) ∧
        (∀ p i, (Sum.inr i : R4 d n) ∈ (binBr p).rows ↔ i ∈ B p) ∧
        (∀ p, (binBr p).residual.cost <=
          Nat.clog 2 (Params.q2 d) + Bcap d) := by
  classical
  let B : Fin 4 -> Finset (Fin n) := vectorPrefixBin d P code
  let hcols : (Finset.univ : Finset (C4 d)).Nonempty :=
    C4_univ_nonempty d hchk k0
  let binBr : ∀ p : Fin 4, Protocol.BranchAt P (M4 d v) 2 :=
    ambientBinBranch d v P code hrow hP hrows hcols
  refine ⟨B, ?_, binBr, ?_, ?_, ?_, ?_, ?_⟩
  · exact vectorPrefixBin_partition d P code hcode
  · exact ambientBinBranch_transcripts_bijective d v P code hcode hrow hP hrows hcols
  · intro p
    exact ambientBinBranch_sideTrace d v P code hrow hP hrows hcols p
  · intro p y
    exact ambientBinBranch_cols_univ d v P code hrow hP hrows hcols p y
  · intro p i
    exact ambientBinBranch_vector_rows d v P code hrow hP hrows hcols p i
  · intro p
    exact ambientBinBranch_residual_budget d v P code hrow hP hcost hrows hcols p

theorem compose_colPrefix_sideTrace_eq
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1) (j : Fin (2 ^ t2))
    (hcol :
      Protocol.FirstKColBitsOn
        (Finset.univ : Finset {a // a ∈ b1.rows})
        (Finset.univ : Finset {b // b ∈ b1.cols}) t2 b1.residual)
    (hcols : (Protocol.colPrefixCols t2 b1.residual j).Nonempty) :
    (Protocol.BranchAt.compose_colPrefix b1 j hcol hcols).sideTrace =
      b1.sideTrace ++ List.replicate t2 Protocol.ActualBitSide.bob := by
  unfold Protocol.BranchAt.compose_colPrefix Protocol.BranchAt.compose
  simp [Protocol.mkBranchAt_of_colPrefix, Protocol.branchAt_of_swap,
    Protocol.mkBranchAt_of_rowPrefix, Protocol.ActualBitSide.swap]

theorem compose_colPrefix_extends
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1) (j : Fin (2 ^ t2))
    (hcol :
      Protocol.FirstKColBitsOn
        (Finset.univ : Finset {a // a ∈ b1.rows})
        (Finset.univ : Finset {b // b ∈ b1.cols}) t2 b1.residual)
    (hcols : (Protocol.colPrefixCols t2 b1.residual j).Nonempty) :
    Protocol.BranchExtends b1
      (Protocol.BranchAt.compose_colPrefix b1 j hcol hcols) := by
  exact Protocol.BranchAt.branchExtends_compose_left _ _

theorem compose_colPrefix_rows_eq
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1) (j : Fin (2 ^ t2))
    (hcol :
      Protocol.FirstKColBitsOn
        (Finset.univ : Finset {a // a ∈ b1.rows})
        (Finset.univ : Finset {b // b ∈ b1.cols}) t2 b1.residual)
    (hcols : (Protocol.colPrefixCols t2 b1.residual j).Nonempty) :
    (Protocol.BranchAt.compose_colPrefix b1 j hcol hcols).rows = b1.rows := by
  classical
  unfold Protocol.BranchAt.compose_colPrefix Protocol.BranchAt.compose
  ext a
  rw [Protocol.BranchAt.mem_liftRows]
  constructor
  · rintro ⟨ha, _⟩
    exact ha
  · intro ha
    refine ⟨ha, ?_⟩
    simp [Protocol.mkBranchAt_of_colPrefix, Protocol.branchAt_of_swap,
      Protocol.mkBranchAt_of_rowPrefix]

theorem actualBitListRaw_eq_of_restrict_eq_of_firstKRowBitsOn
    {A B Z : Type*} [DecidableEq A] [DecidableEq B]
    {S R : Finset A} {T C : Finset B} {P : Protocol A B Z}
    {k : Nat} {a a' : A} {b b' : B}
    (hrow : Protocol.FirstKRowBitsOn S T k P)
    (hRsub : forall a, a ∈ R -> a ∈ S)
    (hCsub : forall b, b ∈ C -> b ∈ T)
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
          simp only [Protocol.FirstKRowBitsOn] at hrow
          rcases hrow with hS | hT
          · have haS : a ∈ S := hRsub a ha
            rw [hS] at haS
            exact absurd haS (Finset.notMem_empty a)
          · have hbT : b ∈ T := hCsub b hb
            rw [hT] at hbT
            exact absurd hbT (Finset.notMem_empty b)
      | bNode q l r =>
          exfalso
          simp only [Protocol.FirstKRowBitsOn] at hrow
          rcases hrow with hS | hT
          · have haS : a ∈ S := hRsub a ha
            rw [hS] at haS
            exact absurd haS (Finset.notMem_empty a)
          · have hbT : b ∈ T := hCsub b hb
            rw [hT] at hbT
            exact absurd hbT (Finset.notMem_empty b)
      | aNode q l r =>
          simp only [Protocol.FirstKRowBitsOn] at hrow
          by_cases hconst : exists beta, Protocol.IsRowConstantOn R q beta
          · have haq : q a = Classical.choose hconst :=
              Classical.choose_spec hconst a ha
            have haq' : q a' = Classical.choose hconst :=
              Classical.choose_spec hconst a' ha'
            by_cases hchoose : Classical.choose hconst = true
            · have haTsub :
                  forall x, x ∈ R -> x ∈ S.filter fun x => q x = true := by
                intro x hx
                rw [Finset.mem_filter]
                exact ⟨hRsub x hx, by
                  simpa [hchoose] using (Classical.choose_spec hconst x hx)⟩
              have hresR :
                  Protocol.actualBitListRaw k (Protocol.restrict R C r) a b =
                    Protocol.actualBitListRaw k (Protocol.restrict R C r) a' b' := by
                have hresSucc :
                    Protocol.actualBitListRaw (k + 1) (Protocol.restrict R C r) a b =
                      Protocol.actualBitListRaw (k + 1) (Protocol.restrict R C r) a' b' := by
                  simpa [Protocol.restrict, hconst, hchoose] using hres
                have ht := congrArg (fun xs : List Bool => xs.take k) hresSucc
                simpa [Protocol.actualBitListRaw_take (Nat.le_succ k)
                  (Protocol.restrict R C r) a b,
                  Protocol.actualBitListRaw_take (Nat.le_succ k)
                    (Protocol.restrict R C r) a' b'] using ht
              have htail :=
                ih (S := S.filter fun x => q x = true) (T := T)
                  (R := R) (C := C) (P := r)
                  hrow.2 haTsub hCsub ha ha' hb hb' hresR
              simp [Protocol.actualBitListRaw, haq, haq', hchoose, htail]
            · have hchooseF : Classical.choose hconst = false := by
                cases h : Classical.choose hconst <;> simp [h, hchoose] at *
              have haFsub :
                  forall x, x ∈ R -> x ∈ S.filter fun x => q x = false := by
                intro x hx
                rw [Finset.mem_filter]
                exact ⟨hRsub x hx, by
                  simpa [hchooseF] using (Classical.choose_spec hconst x hx)⟩
              have hresL :
                  Protocol.actualBitListRaw k (Protocol.restrict R C l) a b =
                    Protocol.actualBitListRaw k (Protocol.restrict R C l) a' b' := by
                have hresSucc :
                    Protocol.actualBitListRaw (k + 1) (Protocol.restrict R C l) a b =
                      Protocol.actualBitListRaw (k + 1) (Protocol.restrict R C l) a' b' := by
                  simpa [Protocol.restrict, hconst, hchooseF] using hres
                have ht := congrArg (fun xs : List Bool => xs.take k) hresSucc
                simpa [Protocol.actualBitListRaw_take (Nat.le_succ k)
                  (Protocol.restrict R C l) a b,
                  Protocol.actualBitListRaw_take (Nat.le_succ k)
                    (Protocol.restrict R C l) a' b'] using ht
              have htail :=
                ih (S := S.filter fun x => q x = false) (T := T)
                  (R := R) (C := C) (P := l)
                  hrow.1 haFsub hCsub ha ha' hb hb' hresL
              simp [Protocol.actualBitListRaw, haq, haq', hchooseF, htail]
          · have hcons :
                q a ::
                    Protocol.actualBitListRaw k
                      (if q a then Protocol.restrict (R.filter fun x => q x = true) C r
                       else Protocol.restrict (R.filter fun x => q x = false) C l)
                      a b =
                  q a' ::
                    Protocol.actualBitListRaw k
                      (if q a' then Protocol.restrict (R.filter fun x => q x = true) C r
                       else Protocol.restrict (R.filter fun x => q x = false) C l)
                      a' b' := by
              simpa [Protocol.restrict, hconst, Protocol.actualBitListRaw] using hres
            have hhead : q a = q a' := (List.cons.inj hcons).1
            have htailEq :
                Protocol.actualBitListRaw k
                    (if q a then Protocol.restrict (R.filter fun x => q x = true) C r
                     else Protocol.restrict (R.filter fun x => q x = false) C l)
                    a b =
                  Protocol.actualBitListRaw k
                    (if q a' then Protocol.restrict (R.filter fun x => q x = true) C r
                     else Protocol.restrict (R.filter fun x => q x = false) C l)
                    a' b' := (List.cons.inj hcons).2
            by_cases hqa : q a
            · have hqa' : q a' = true := by
                simpa [hqa] using hhead.symm
              have haR : a ∈ R.filter fun x => q x = true := by
                rw [Finset.mem_filter]
                exact ⟨ha, hqa⟩
              have haR' : a' ∈ R.filter fun x => q x = true := by
                rw [Finset.mem_filter]
                exact ⟨ha', hqa'⟩
              have hRsubS :
                  forall x, x ∈ (R.filter fun x => q x = true) ->
                    x ∈ (S.filter fun x => q x = true) := by
                intro x hx
                rw [Finset.mem_filter] at hx ⊢
                exact ⟨hRsub x hx.1, hx.2⟩
              have htailR :
                  Protocol.actualBitListRaw k
                      (Protocol.restrict (R.filter fun x => q x = true) C r) a b =
                    Protocol.actualBitListRaw k
                      (Protocol.restrict (R.filter fun x => q x = true) C r) a' b' := by
                simpa [hqa, hqa'] using htailEq
              have htail :=
                ih (S := S.filter fun x => q x = true) (T := T)
                  (R := R.filter fun x => q x = true) (C := C) (P := r)
                  hrow.2 hRsubS hCsub haR haR' hb hb' htailR
              simp [Protocol.actualBitListRaw, hqa, hqa', htail]
            · have hqaf : q a = false := by simp [hqa]
              have hqa'f : q a' = false := by
                simpa [hqaf] using hhead.symm
              have haR : a ∈ R.filter fun x => q x = false := by
                rw [Finset.mem_filter]
                exact ⟨ha, hqaf⟩
              have haR' : a' ∈ R.filter fun x => q x = false := by
                rw [Finset.mem_filter]
                exact ⟨ha', hqa'f⟩
              have hRsubS :
                  forall x, x ∈ (R.filter fun x => q x = false) ->
                    x ∈ (S.filter fun x => q x = false) := by
                intro x hx
                rw [Finset.mem_filter] at hx ⊢
                exact ⟨hRsub x hx.1, hx.2⟩
              have htailL :
                  Protocol.actualBitListRaw k
                      (Protocol.restrict (R.filter fun x => q x = false) C l) a b =
                    Protocol.actualBitListRaw k
                      (Protocol.restrict (R.filter fun x => q x = false) C l) a' b' := by
                simpa [hqa, hqaf, hqa'f] using htailEq
              have htail :=
                ih (S := S.filter fun x => q x = false) (T := T)
                  (R := R.filter fun x => q x = false) (C := C) (P := l)
                  hrow.1 hRsubS hCsub haR haR' hb hb' htailL
              simp [Protocol.actualBitListRaw, hqa, hqaf, hqa'f, htail]

theorem fullStoppingFiberCoverage_rect_of_restrict
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (G : A -> B -> Bool) (P : Protocol A B Bool)
    (S : Finset A) (T : Finset B) (R : Finset A) (C : Finset B)
    (pat : List Protocol.ActualBitSide) (B0 : Nat)
    (hRsub : forall a, a ∈ R -> a ∈ S)
    (hCsub : forall b, b ∈ C -> b ∈ T)
    (hcomp : forall a, a ∈ S -> forall b, b ∈ T -> P.eval a b = G a b)
    (hcost : P.cost <= pat.length + B0)
    (hpat : Protocol.FirstPatternOn R C pat (Protocol.restrict R C P))
    (hcov : Protocol.FullStoppingFiberCoverage R C (Protocol.restrict R C P) pat)
    (hterm : Protocol.TerminalHardWitnesses G R C
      (Protocol.restrict R C P) pat B0) :
    Protocol.FullStoppingFiberCoverage S T P pat := by
  classical
  induction pat generalizing S T R C P with
  | nil =>
      intro w hw
      have hwNil : w = [] := List.eq_nil_of_length_eq_zero hw
      subst w
      rcases hcov [] rfl with ⟨a, ha, b, hb, _hbits⟩
      exact ⟨a, hRsub a ha, b, hCsub b hb, rfl⟩
  | cons side tail ih =>
      intro w hw
      cases w with
      | nil =>
          simp at hw
      | cons bit wt =>
          have hwtlen : wt.length = tail.length := by
            simpa using hw
          have hcompRestrict :
              forall a, a ∈ R -> forall b, b ∈ C ->
                (Protocol.restrict R C P).eval a b = G a b := by
            intro a ha b hb
            rw [Protocol.eval_restrict_of_mem R C P ha hb]
            exact hcomp a (hRsub a ha) b (hCsub b hb)
          have hlow :
              (side :: tail).length + B0 <= (Protocol.restrict R C P).cost :=
            Protocol.firstPatternOn_terminal_cost_lower hcompRestrict hpat hterm
          cases P with
          | leaf z =>
              exfalso
              simp [Protocol.restrict, Protocol.cost] at hlow
          | aNode q l r =>
              by_cases hconst : exists beta, Protocol.IsRowConstantOn R q beta
              · have hstrict :
                    (Protocol.restrict R C (Protocol.aNode q l r)).cost <
                      (Protocol.aNode q l r).cost := by
                  unfold Protocol.restrict
                  rw [dif_pos hconst]
                  by_cases hchoose : Classical.choose hconst = true
                  · rw [if_pos hchoose]
                    have hle := Protocol.cost_restrict_le R C r
                    have hchild : r.cost < (Protocol.aNode q l r).cost := by
                      simp [Protocol.cost]
                      omega
                    exact lt_of_le_of_lt hle hchild
                  · rw [if_neg hchoose]
                    have hle := Protocol.cost_restrict_le R C l
                    have hchild : l.cost < (Protocol.aNode q l r).cost := by
                      simp [Protocol.cost]
                      omega
                    exact lt_of_le_of_lt hle hchild
                omega
              · have hrestrict :
                    Protocol.restrict R C (Protocol.aNode q l r) =
                      Protocol.aNode q
                        (Protocol.restrict (R.filter fun x => q x = false) C l)
                        (Protocol.restrict (R.filter fun x => q x = true) C r) := by
                  change
                    (if h : exists beta, Protocol.IsRowConstantOn R q beta then
                      if Classical.choose h then Protocol.restrict R C r
                      else Protocol.restrict R C l
                    else
                      Protocol.aNode q
                        (Protocol.restrict (R.filter fun x => q x = false) C l)
                        (Protocol.restrict (R.filter fun x => q x = true) C r)) =
                      Protocol.aNode q
                        (Protocol.restrict (R.filter fun x => q x = false) C l)
                        (Protocol.restrict (R.filter fun x => q x = true) C r)
                  rw [dif_neg hconst]
                have hpat' := hpat
                have hcov' := hcov
                have hterm' := hterm
                rw [hrestrict] at hpat' hcov' hterm'
                cases side with
                | alice =>
                    obtain ⟨hpatL, hpatR⟩ := hpat'
                    cases bit
                    · have hRsubL :
                          forall a, a ∈ R.filter (fun x => q x = false) ->
                            a ∈ S.filter (fun x => q x = false) := by
                        intro a ha
                        rw [Finset.mem_filter] at ha ⊢
                        exact ⟨hRsub a ha.1, ha.2⟩
                      have hcompL :
                          forall a, a ∈ S.filter (fun x => q x = false) ->
                            forall b, b ∈ T -> l.eval a b = G a b := by
                        intro a ha b hb
                        have haS : a ∈ S := (Finset.mem_filter.mp ha).1
                        have hq : q a = false := (Finset.mem_filter.mp ha).2
                        have h := hcomp a haS b hb
                        simpa [Protocol.eval, hq] using h
                      have hcostL : l.cost <= tail.length + B0 := by
                        have hlt : l.cost < (Protocol.aNode q l r).cost := by
                          simp [Protocol.cost]
                          omega
                        have hs := Nat.succ_le_of_lt hlt
                        have hbudgetCons :
                            (Protocol.aNode q l r).cost <= tail.length + 1 + B0 := by
                          simpa [Nat.add_assoc] using hcost
                        have htotal := le_trans hs hbudgetCons
                        omega
                      have hcovL :
                          Protocol.FullStoppingFiberCoverage
                            (R.filter fun x => q x = false) C
                            (Protocol.restrict (R.filter fun x => q x = false) C l)
                            tail :=
                        Protocol.fullStoppingFiberCoverage_tail_false_of_aNode hcov'
                      have htermL :
                          Protocol.TerminalHardWitnesses G
                            (R.filter fun x => q x = false) C
                            (Protocol.restrict (R.filter fun x => q x = false) C l)
                            tail B0 :=
                        Protocol.terminalHardWitnesses_tail_false_of_aNode hterm'
                      rcases ih l (S.filter fun x => q x = false) T
                          (R.filter fun x => q x = false) C
                          hRsubL hCsub hcompL hcostL hpatL hcovL htermL
                          wt hwtlen with
                        ⟨a, ha, b, hb, hbits⟩
                      refine ⟨a, (Finset.mem_filter.mp ha).1, b, hb, ?_⟩
                      have hq : q a = false := (Finset.mem_filter.mp ha).2
                      simpa [Protocol.actualBitListRaw, hq, hbits]
                    · have hRsubR :
                          forall a, a ∈ R.filter (fun x => q x = true) ->
                            a ∈ S.filter (fun x => q x = true) := by
                        intro a ha
                        rw [Finset.mem_filter] at ha ⊢
                        exact ⟨hRsub a ha.1, ha.2⟩
                      have hcompR :
                          forall a, a ∈ S.filter (fun x => q x = true) ->
                            forall b, b ∈ T -> r.eval a b = G a b := by
                        intro a ha b hb
                        have haS : a ∈ S := (Finset.mem_filter.mp ha).1
                        have hq : q a = true := (Finset.mem_filter.mp ha).2
                        have h := hcomp a haS b hb
                        simpa [Protocol.eval, hq] using h
                      have hcostR : r.cost <= tail.length + B0 := by
                        have hlt : r.cost < (Protocol.aNode q l r).cost := by
                          simp [Protocol.cost]
                          omega
                        have hs := Nat.succ_le_of_lt hlt
                        have hbudgetCons :
                            (Protocol.aNode q l r).cost <= tail.length + 1 + B0 := by
                          simpa [Nat.add_assoc] using hcost
                        have htotal := le_trans hs hbudgetCons
                        omega
                      have hcovR :
                          Protocol.FullStoppingFiberCoverage
                            (R.filter fun x => q x = true) C
                            (Protocol.restrict (R.filter fun x => q x = true) C r)
                            tail :=
                        Protocol.fullStoppingFiberCoverage_tail_true_of_aNode hcov'
                      have htermR :
                          Protocol.TerminalHardWitnesses G
                            (R.filter fun x => q x = true) C
                            (Protocol.restrict (R.filter fun x => q x = true) C r)
                            tail B0 :=
                        Protocol.terminalHardWitnesses_tail_true_of_aNode hterm'
                      rcases ih r (S.filter fun x => q x = true) T
                          (R.filter fun x => q x = true) C
                          hRsubR hCsub hcompR hcostR hpatR hcovR htermR
                          wt hwtlen with
                        ⟨a, ha, b, hb, hbits⟩
                      refine ⟨a, (Finset.mem_filter.mp ha).1, b, hb, ?_⟩
                      have hq : q a = true := (Finset.mem_filter.mp ha).2
                      simpa [Protocol.actualBitListRaw, hq, hbits]
                | bob =>
                    exfalso
                    let w0 : List Bool := List.replicate (tail.length + 1) false
                    have hw0 : w0.length = (Protocol.ActualBitSide.bob :: tail).length := by
                      simp [w0]
                    have hfiber := hcov' w0 hw0
                    rcases hpat' with hRempty | hCempty
                    · obtain ⟨a, ha⟩ := Protocol.BranchFiberNonempty.rows_nonempty hfiber
                      rw [hRempty] at ha
                      exact absurd ha (Finset.notMem_empty a)
                    · obtain ⟨b, hb⟩ := Protocol.BranchFiberNonempty.cols_nonempty hfiber
                      rw [hCempty] at hb
                      exact absurd hb (Finset.notMem_empty b)
          | bNode q l r =>
              by_cases hconst : exists beta, Protocol.IsColConstantOn C q beta
              · have hstrict :
                    (Protocol.restrict R C (Protocol.bNode q l r)).cost <
                      (Protocol.bNode q l r).cost := by
                  unfold Protocol.restrict
                  rw [dif_pos hconst]
                  by_cases hchoose : Classical.choose hconst = true
                  · rw [if_pos hchoose]
                    have hle := Protocol.cost_restrict_le R C r
                    have hchild : r.cost < (Protocol.bNode q l r).cost := by
                      simp [Protocol.cost]
                      omega
                    exact lt_of_le_of_lt hle hchild
                  · rw [if_neg hchoose]
                    have hle := Protocol.cost_restrict_le R C l
                    have hchild : l.cost < (Protocol.bNode q l r).cost := by
                      simp [Protocol.cost]
                      omega
                    exact lt_of_le_of_lt hle hchild
                omega
              · have hrestrict :
                    Protocol.restrict R C (Protocol.bNode q l r) =
                      Protocol.bNode q
                        (Protocol.restrict R (C.filter fun y => q y = false) l)
                        (Protocol.restrict R (C.filter fun y => q y = true) r) := by
                  change
                    (if h : exists beta, Protocol.IsColConstantOn C q beta then
                      if Classical.choose h then Protocol.restrict R C r
                      else Protocol.restrict R C l
                    else
                      Protocol.bNode q
                        (Protocol.restrict R (C.filter fun y => q y = false) l)
                        (Protocol.restrict R (C.filter fun y => q y = true) r)) =
                      Protocol.bNode q
                        (Protocol.restrict R (C.filter fun y => q y = false) l)
                        (Protocol.restrict R (C.filter fun y => q y = true) r)
                  rw [dif_neg hconst]
                have hpat' := hpat
                have hcov' := hcov
                have hterm' := hterm
                rw [hrestrict] at hpat' hcov' hterm'
                cases side with
                | alice =>
                    exfalso
                    let w0 : List Bool := List.replicate (tail.length + 1) false
                    have hw0 : w0.length = (Protocol.ActualBitSide.alice :: tail).length := by
                      simp [w0]
                    have hfiber := hcov' w0 hw0
                    rcases hpat' with hRempty | hCempty
                    · obtain ⟨a, ha⟩ := Protocol.BranchFiberNonempty.rows_nonempty hfiber
                      rw [hRempty] at ha
                      exact absurd ha (Finset.notMem_empty a)
                    · obtain ⟨b, hb⟩ := Protocol.BranchFiberNonempty.cols_nonempty hfiber
                      rw [hCempty] at hb
                      exact absurd hb (Finset.notMem_empty b)
                | bob =>
                    obtain ⟨hpatL, hpatR⟩ := hpat'
                    cases bit
                    · have hCsubL :
                          forall b, b ∈ C.filter (fun y => q y = false) ->
                            b ∈ T.filter (fun y => q y = false) := by
                        intro b hb
                        rw [Finset.mem_filter] at hb ⊢
                        exact ⟨hCsub b hb.1, hb.2⟩
                      have hcompL :
                          forall a, a ∈ S ->
                            forall b, b ∈ T.filter (fun y => q y = false) ->
                              l.eval a b = G a b := by
                        intro a ha b hb
                        have hbT : b ∈ T := (Finset.mem_filter.mp hb).1
                        have hq : q b = false := (Finset.mem_filter.mp hb).2
                        have h := hcomp a ha b hbT
                        simpa [Protocol.eval, hq] using h
                      have hcostL : l.cost <= tail.length + B0 := by
                        have hlt : l.cost < (Protocol.bNode q l r).cost := by
                          simp [Protocol.cost]
                          omega
                        have hs := Nat.succ_le_of_lt hlt
                        have hbudgetCons :
                            (Protocol.bNode q l r).cost <= tail.length + 1 + B0 := by
                          simpa [Nat.add_assoc] using hcost
                        have htotal := le_trans hs hbudgetCons
                        omega
                      have hcovL :
                          Protocol.FullStoppingFiberCoverage R
                            (C.filter fun y => q y = false)
                            (Protocol.restrict R (C.filter fun y => q y = false) l)
                            tail :=
                        Protocol.fullStoppingFiberCoverage_tail_false_of_bNode hcov'
                      have htermL :
                          Protocol.TerminalHardWitnesses G R
                            (C.filter fun y => q y = false)
                            (Protocol.restrict R (C.filter fun y => q y = false) l)
                            tail B0 :=
                        Protocol.terminalHardWitnesses_tail_false_of_bNode hterm'
                      rcases ih l S (T.filter fun y => q y = false)
                          R (C.filter fun y => q y = false)
                          hRsub hCsubL hcompL hcostL hpatL hcovL htermL
                          wt hwtlen with
                        ⟨a, ha, b, hb, hbits⟩
                      refine ⟨a, ha, b, (Finset.mem_filter.mp hb).1, ?_⟩
                      have hq : q b = false := (Finset.mem_filter.mp hb).2
                      simpa [Protocol.actualBitListRaw, hq, hbits]
                    · have hCsubR :
                          forall b, b ∈ C.filter (fun y => q y = true) ->
                            b ∈ T.filter (fun y => q y = true) := by
                        intro b hb
                        rw [Finset.mem_filter] at hb ⊢
                        exact ⟨hCsub b hb.1, hb.2⟩
                      have hcompR :
                          forall a, a ∈ S ->
                            forall b, b ∈ T.filter (fun y => q y = true) ->
                              r.eval a b = G a b := by
                        intro a ha b hb
                        have hbT : b ∈ T := (Finset.mem_filter.mp hb).1
                        have hq : q b = true := (Finset.mem_filter.mp hb).2
                        have h := hcomp a ha b hbT
                        simpa [Protocol.eval, hq] using h
                      have hcostR : r.cost <= tail.length + B0 := by
                        have hlt : r.cost < (Protocol.bNode q l r).cost := by
                          simp [Protocol.cost]
                          omega
                        have hs := Nat.succ_le_of_lt hlt
                        have hbudgetCons :
                            (Protocol.bNode q l r).cost <= tail.length + 1 + B0 := by
                          simpa [Nat.add_assoc] using hcost
                        have htotal := le_trans hs hbudgetCons
                        omega
                      have hcovR :
                          Protocol.FullStoppingFiberCoverage R
                            (C.filter fun y => q y = true)
                            (Protocol.restrict R (C.filter fun y => q y = true) r)
                            tail :=
                        Protocol.fullStoppingFiberCoverage_tail_true_of_bNode hcov'
                      have htermR :
                          Protocol.TerminalHardWitnesses G R
                            (C.filter fun y => q y = true)
                            (Protocol.restrict R (C.filter fun y => q y = true) r)
                            tail B0 :=
                        Protocol.terminalHardWitnesses_tail_true_of_bNode hterm'
                      rcases ih r S (T.filter fun y => q y = true)
                          R (C.filter fun y => q y = true)
                          hRsub hCsubR hcompR hcostR hpatR hcovR htermR
                          wt hwtlen with
                        ⟨a, ha, b, hb, hbits⟩
                      refine ⟨a, ha, b, (Finset.mem_filter.mp hb).1, ?_⟩
                      have hq : q b = true := (Finset.mem_filter.mp hb).2
                      simpa [Protocol.actualBitListRaw, hq, hbits]

theorem M4_ambient_two_row_bit_coverage_of_phaseA_certificates
    (d : Nat) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (hP : P.Computes (M4 d v))
    (hcost : P.cost <= Byes d)
    (k0 : Fin (2 ^ 5))
    (hfirst :
      Protocol.FirstKRowBitsOn
        (templateRows d n) (templateCols d k0) 2
        (Protocol.restrict (templateRows d n) (templateCols d k0) P))
    (hcover :
      Protocol.FullStoppingFiberCoverage
        (templateRows d n) (templateCols d k0)
        (Protocol.restrict (templateRows d n) (templateCols d k0) P)
        (List.replicate 2 Protocol.ActualBitSide.alice))
    (hhard :
      Protocol.TerminalHardWitnesses (M4 d v)
        (templateRows d n) (templateCols d k0)
        (Protocol.restrict (templateRows d n) (templateCols d k0) P)
        (List.replicate 2 Protocol.ActualBitSide.alice)
        (Nat.clog 2 (Params.q2 d) + Bcap d)) :
    Protocol.FullStoppingFiberCoverage
      (Finset.univ : Finset (R4 d n))
      (Finset.univ : Finset (C4 d)) P
      (List.replicate 2 Protocol.ActualBitSide.alice) := by
  have hcost' :
      P.cost <= (List.replicate 2 Protocol.ActualBitSide.alice).length +
          (Nat.clog 2 (Params.q2 d) + Bcap d) := by
    unfold Byes at hcost
    simp
    omega
  have hpat :
      Protocol.FirstPatternOn (templateRows d n) (templateCols d k0)
        (List.replicate 2 Protocol.ActualBitSide.alice)
        (Protocol.restrict (templateRows d n) (templateCols d k0) P) := by
    exact (Protocol.firstPattern_replicate_alice_iff
      (templateRows d n) (templateCols d k0) 2
      (Protocol.restrict (templateRows d n) (templateCols d k0) P)).2 hfirst
  exact
    fullStoppingFiberCoverage_rect_of_restrict
      (M4 d v) P
      (Finset.univ : Finset (R4 d n))
      (Finset.univ : Finset (C4 d))
      (templateRows d n) (templateCols d k0)
      (List.replicate 2 Protocol.ActualBitSide.alice)
      (Nat.clog 2 (Params.q2 d) + Bcap d)
      (by intro a _; exact Finset.mem_univ a)
      (by intro b _; exact Finset.mem_univ b)
      (by intro a _ b _; exact hP a b)
      hcost' hpat hcover hhard

theorem rowPrefixRows_nonempty_of_two_row_bit_coverage
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (P : Protocol A B Bool)
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset A) (Finset.univ : Finset B) 2 P)
    (hcover :
      Protocol.FullStoppingFiberCoverage
        (Finset.univ : Finset A) (Finset.univ : Finset B) P
        (List.replicate 2 Protocol.ActualBitSide.alice))
    (j : Fin (2 ^ 2)) :
    (Protocol.rowPrefixRows 2 P j).Nonempty := by
  classical
  fin_cases j
  · rcases hcover [false, false] (by simp) with ⟨a, ha, b, hb, hbits⟩
    have hactual :=
      actualPrefixCodeRaw_eq_codeOfBitList_of_actualBitListRaw_eq
        P a b hbits (by simp)
    have hpref :
        Protocol.actualPrefixCodeRaw 2 P a b =
          Protocol.prefixCodeRaw 2 P a :=
      Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
        (Finset.univ : Finset A) (Finset.univ : Finset B) 2 P
        hrow ha hb
    refine ⟨a, ?_⟩
    rw [Protocol.rowPrefixRows, Finset.mem_filter]
    refine ⟨Finset.mem_univ a, ?_⟩
    calc
      Protocol.prefixCodeRaw 2 P a =
          Protocol.actualPrefixCodeRaw 2 P a b := hpref.symm
      _ = Fin.cast (by simp) (Protocol.codeOfBitList [false, false]) := hactual
      _ = 0 := by
        apply Fin.ext
        norm_num [Protocol.codeOfBitList, Protocol.bitCons, Protocol.zeroPow2]
  · rcases hcover [false, true] (by simp) with ⟨a, ha, b, hb, hbits⟩
    have hactual :=
      actualPrefixCodeRaw_eq_codeOfBitList_of_actualBitListRaw_eq
        P a b hbits (by simp)
    have hpref :
        Protocol.actualPrefixCodeRaw 2 P a b =
          Protocol.prefixCodeRaw 2 P a :=
      Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
        (Finset.univ : Finset A) (Finset.univ : Finset B) 2 P
        hrow ha hb
    refine ⟨a, ?_⟩
    rw [Protocol.rowPrefixRows, Finset.mem_filter]
    refine ⟨Finset.mem_univ a, ?_⟩
    calc
      Protocol.prefixCodeRaw 2 P a =
          Protocol.actualPrefixCodeRaw 2 P a b := hpref.symm
      _ = Fin.cast (by simp) (Protocol.codeOfBitList [false, true]) := hactual
      _ = 1 := by
        apply Fin.ext
        norm_num [Protocol.codeOfBitList, Protocol.bitCons, Protocol.zeroPow2]
  · rcases hcover [true, false] (by simp) with ⟨a, ha, b, hb, hbits⟩
    have hactual :=
      actualPrefixCodeRaw_eq_codeOfBitList_of_actualBitListRaw_eq
        P a b hbits (by simp)
    have hpref :
        Protocol.actualPrefixCodeRaw 2 P a b =
          Protocol.prefixCodeRaw 2 P a :=
      Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
        (Finset.univ : Finset A) (Finset.univ : Finset B) 2 P
        hrow ha hb
    refine ⟨a, ?_⟩
    rw [Protocol.rowPrefixRows, Finset.mem_filter]
    refine ⟨Finset.mem_univ a, ?_⟩
    calc
      Protocol.prefixCodeRaw 2 P a =
          Protocol.actualPrefixCodeRaw 2 P a b := hpref.symm
      _ = Fin.cast (by simp) (Protocol.codeOfBitList [true, false]) := hactual
      _ = 2 := by
        apply Fin.ext
        norm_num [Protocol.codeOfBitList, Protocol.bitCons, Protocol.zeroPow2]
  · rcases hcover [true, true] (by simp) with ⟨a, ha, b, hb, hbits⟩
    have hactual :=
      actualPrefixCodeRaw_eq_codeOfBitList_of_actualBitListRaw_eq
        P a b hbits (by simp)
    have hpref :
        Protocol.actualPrefixCodeRaw 2 P a b =
          Protocol.prefixCodeRaw 2 P a :=
      Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
        (Finset.univ : Finset A) (Finset.univ : Finset B) 2 P
        hrow ha hb
    refine ⟨a, ?_⟩
    rw [Protocol.rowPrefixRows, Finset.mem_filter]
    refine ⟨Finset.mem_univ a, ?_⟩
    calc
      Protocol.prefixCodeRaw 2 P a =
          Protocol.actualPrefixCodeRaw 2 P a b := hpref.symm
      _ = Fin.cast (by simp) (Protocol.codeOfBitList [true, true]) := hactual
      _ = 3 := by
        apply Fin.ext
        norm_num [Protocol.codeOfBitList, Protocol.bitCons, Protocol.zeroPow2]

theorem M4_phaseA_package_from_certificates
    (d : Nat) (hchk : Checklist d) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (hP : P.Computes (M4 d v))
    (hcost : P.cost <= Byes d)
    (k0 : Fin (2 ^ 5))
    (code : Fin 4 -> Fin (2 ^ 2))
    (hcode : Function.Bijective code)
    (hfirst :
      Protocol.FirstKRowBitsOn
        (templateRows d n) (templateCols d k0) 2
        (Protocol.restrict (templateRows d n) (templateCols d k0) P))
    (hcover :
      Protocol.FullStoppingFiberCoverage
        (templateRows d n) (templateCols d k0)
        (Protocol.restrict (templateRows d n) (templateCols d k0) P)
        (List.replicate 2 Protocol.ActualBitSide.alice))
    (hhard :
      Protocol.TerminalHardWitnesses (M4 d v)
        (templateRows d n) (templateCols d k0)
        (Protocol.restrict (templateRows d n) (templateCols d k0) P)
        (List.replicate 2 Protocol.ActualBitSide.alice)
        (Nat.clog 2 (Params.q2 d) + Bcap d)) :
    ∃ B : Fin 4 -> Finset (Fin n),
      IsPartition4 B ∧
      ∃ binBr : ∀ p : Fin 4, Protocol.BranchAt P (M4 d v) 2,
        Function.Bijective (fun p : Fin 4 => (binBr p).transcript) ∧
        (∀ p : Fin 4,
          (binBr p).sideTrace =
            [Protocol.ActualBitSide.alice, Protocol.ActualBitSide.alice]) ∧
        (∀ p : Fin 4, ∀ y : C4 d, y ∈ (binBr p).cols) ∧
        (∀ p i, (Sum.inr i : R4 d n) ∈ (binBr p).rows ↔ i ∈ B p) ∧
        (∀ p, (binBr p).residual.cost <=
          Nat.clog 2 (Params.q2 d) + Bcap d) := by
  let hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset (R4 d n))
        (Finset.univ : Finset (C4 d)) 2 P :=
    M4_ambient_first_two_row_bits_of_phaseA_certificates
      d v P hP hcost k0 hfirst hcover hhard
  let hcov :
      Protocol.FullStoppingFiberCoverage
        (Finset.univ : Finset (R4 d n))
        (Finset.univ : Finset (C4 d)) P
        (List.replicate 2 Protocol.ActualBitSide.alice) :=
    M4_ambient_two_row_bit_coverage_of_phaseA_certificates
      d v P hP hcost k0 hfirst hcover hhard
  let hrows : forall p, (Protocol.rowPrefixRows 2 P (code p)).Nonempty :=
    fun p =>
      rowPrefixRows_nonempty_of_two_row_bit_coverage P hrow hcov (code p)
  exact
    M4_phaseA_package d hchk v P hP hcost k0 code hcode hrow hrows

theorem image_univ_of_bijective {α β γ : Type*} [Fintype α] [Fintype β]
    [DecidableEq γ] (f : β -> γ) (e : α -> β) (he : Function.Bijective e) :
    (Finset.univ : Finset α).image (fun a => f (e a)) =
      (Finset.univ : Finset β).image f := by
  classical
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨e a, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := he.2 b
    exact ⟨a, by rw [ha]⟩

theorem m1PlusCoordEnum_image_eq_localCoordSet (d : Nat) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool) (alpha : Fin (Params.q2 d))
    (B : Finset (Fin n)) :
    Finset.univ.image (m1PlusCoordEnum d v alpha B) =
      localCoordSet d v alpha B := by
  classical
  have hstep1 :
      Finset.univ.image (m1PlusCoordEnum d v alpha B) =
        Finset.univ.image (m1PlusCoord d v alpha B) :=
    image_univ_of_bijective (m1PlusCoord d v alpha B)
      (Fintype.equivFin (M1PlusOuter d v alpha B)).symm
      (Fintype.equivFin (M1PlusOuter d v alpha B)).symm.bijective
  rw [hstep1]
  unfold localCoordSet
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨x, rfl⟩
    cases x with
    | inl q => exact Or.inl ⟨q, rfl⟩
    | inr i => exact Or.inr ⟨i.val, i.property, rfl⟩
  · rintro (⟨q, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨Sum.inl q, rfl⟩
    · exact ⟨Sum.inr ⟨i, hi⟩, rfl⟩

noncomputable def rowRep (d : Nat) (h₂ : Params.t2 d ≤ Params.q2 d)
    (hq1 : 1 ≤ Params.q1 d) {n : Nat}
    (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4)
    (alpha : Fin (Params.q2 d)) (B : Finset (Fin n)) :
    (M1PlusOuter d v alpha B × Fin 1) → R4 d n :=
  fun x =>
    match x.1 with
    | Sum.inl q => (Sum.inl (p, S2coordPreimage d h₂ hq1 alpha (q, x.2)) : R4 d n)
    | Sum.inr i => (Sum.inr i.val : R4 d n)

theorem M4_rowRep_val (d : Nat) (h₂ : Params.t2 d ≤ Params.q2 d)
    (hq1 : 1 ≤ Params.q1 d) {n : Nat}
    (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4)
    (alpha : Fin (Params.q2 d)) (B : Finset (Fin n)) (S' : Finset (C1 d))
    (x : M1PlusOuter d v alpha B × Fin 1) (γ : {γ // γ ∈ S'}) :
    M4 d v (rowRep d h₂ hq1 v p alpha B x) (diagCopyCol d alpha γ.val) =
      HlocalAtSub d (S1fam d) S' (m1PlusCoordEnum d v alpha B)
        ((Fintype.equivFin (M1PlusOuter d v alpha B) x.1), x.2) γ := by
  have h := m1PlusBranchCoreSub_eq_stage d h₂ hq1 v p alpha B S' x γ
  rw [← h]
  unfold m1PlusBranchCoreSub rowRep
  cases x.1 with
  | inl q => rfl
  | inr i => rfl

theorem M4_duplicateExpansionContained_localRows
    (d : Nat) (h₂ : Params.t2 d ≤ Params.q2 d) (hq1 : 1 ≤ Params.q1 d)
    {n : Nat} (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4)
    (alpha : Fin (Params.q2 d)) (B : Finset (Fin n)) (T : Finset (C2 d))
    (Y : Finset (C4 d)) (hYsub : Y ⊆ diagCopySet d alpha)
    (hTcov : ∀ q : Fin (Params.q1 d), ∀ r0 : Fin 1,
      S2coordPreimage d h₂ hq1 alpha (q, r0) ∈ T)
    (hBcov : transversalAt v alpha B ⊆ B) :
    DuplicateExpansionContained
      (M4 d v)
      (localRows d p T B)
      Y
      (HlocalAtSub d (S1fam d) (SPrime d alpha Y)
        (m1PlusCoordEnum d v alpha B)) := by
  classical
  set e := Fintype.equivFin (M1PlusOuter d v alpha B)
  have hpre : ∀ b : {b // b ∈ Y}, ∃ γ : C1 d, diagCopyCol d alpha γ = b.val := by
    intro b
    have hb := hYsub b.property
    unfold diagCopySet at hb
    rw [Finset.mem_image] at hb
    rcases hb with ⟨γ, -, hγ⟩
    exact ⟨γ, hγ⟩
  have hrowmem : ∀ x : M1PlusOuter d v alpha B × Fin 1,
      rowRep d h₂ hq1 v p alpha B x ∈ localRows d p T B := by
    intro x
    unfold rowRep localRows
    cases hx : x.1 with
    | inl q =>
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨_, hTcov q x.2, rfl⟩)
    | inr i =>
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i.val, hBcov i.property, rfl⟩)
  refine ⟨(Finset.univ : Finset (M1PlusOuter d v alpha B × Fin 1)).image
            (rowRep d h₂ hq1 v p alpha B), ?_, Y, Finset.Subset.refl _,
          fun a => (e (Classical.choose (Finset.mem_image.mp a.property)).1,
                    (Classical.choose (Finset.mem_image.mp a.property)).2),
          fun b => ⟨Classical.choose (hpre b), ?_⟩,
          ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨x, -, rfl⟩
    exact hrowmem x
  · unfold SPrime diagPullback
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by
      rw [Classical.choose_spec (hpre b)]
      exact b.property⟩
  · rintro ⟨oIdx, r0⟩
    set outer := e.symm oIdx with houter
    refine ⟨⟨rowRep d h₂ hq1 v p alpha B (outer, r0), Finset.mem_image.mpr
              ⟨(outer, r0), Finset.mem_univ _, rfl⟩⟩, ?_⟩
    set a : {a // a ∈ (Finset.univ : Finset (M1PlusOuter d v alpha B × Fin 1)).image
              (rowRep d h₂ hq1 v p alpha B)} :=
      ⟨rowRep d h₂ hq1 v p alpha B (outer, r0),
        Finset.mem_image.mpr ⟨(outer, r0), Finset.mem_univ _, rfl⟩⟩ with ha
    have hchoose := Classical.choose_spec (Finset.mem_image.mp a.property)
    set x0 := Classical.choose (Finset.mem_image.mp a.property) with hx0
    have hval : rowRep d h₂ hq1 v p alpha B x0 =
        rowRep d h₂ hq1 v p alpha B (outer, r0) := hchoose.2
    have hxo : x0 = (outer, r0) := by
      have hr0 : x0.2 = r0 := Subsingleton.elim _ _
      rcases ho : outer with q | i
      · have hrhs : rowRep d h₂ hq1 v p alpha B (outer, r0) =
            (Sum.inl (p, S2coordPreimage d h₂ hq1 alpha (q, r0)) : R4 d n) := by
          simp [rowRep, ho]
        rw [hrhs] at hval
        cases hx0o : x0.1 with
        | inl q' =>
            have hlhs : rowRep d h₂ hq1 v p alpha B x0 =
                (Sum.inl (p, S2coordPreimage d h₂ hq1 alpha (q', x0.2)) : R4 d n) := by
              simp [rowRep, hx0o]
            rw [hlhs] at hval
            have hqq : S2coordPreimage d h₂ hq1 alpha (q', x0.2) =
                S2coordPreimage d h₂ hq1 alpha (q, r0) := by
              have := Sum.inl.inj hval
              exact (Prod.ext_iff.mp this).2
            have hs1 := S2coordPreimage_spec d h₂ hq1 alpha (q', x0.2)
            have hs2 := S2coordPreimage_spec d h₂ hq1 alpha (q, r0)
            rw [hqq] at hs1
            rw [hs2] at hs1
            have hqeq : (q', x0.2) = (q, r0) := hs1.symm
            apply Prod.ext
            · rw [hx0o]
              exact congrArg Sum.inl (Prod.ext_iff.mp hqeq).1
            · exact hr0
        | inr i =>
            have hlhs : rowRep d h₂ hq1 v p alpha B x0 =
                (Sum.inr i.val : R4 d n) := by simp [rowRep, hx0o]
            rw [hlhs] at hval
            exact absurd hval (by simp)
      · have hrhs : rowRep d h₂ hq1 v p alpha B (outer, r0) =
            (Sum.inr i.val : R4 d n) := by simp [rowRep, ho]
        rw [hrhs] at hval
        cases hx0o : x0.1 with
        | inl q' =>
            have hlhs : rowRep d h₂ hq1 v p alpha B x0 =
                (Sum.inl (p, S2coordPreimage d h₂ hq1 alpha (q', x0.2)) : R4 d n) := by
              simp [rowRep, hx0o]
            rw [hlhs] at hval
            exact absurd hval (by simp)
        | inr j =>
            have hlhs : rowRep d h₂ hq1 v p alpha B x0 =
                (Sum.inr j.val : R4 d n) := by simp [rowRep, hx0o]
            rw [hlhs] at hval
            have hij : j.val = i.val := Sum.inr.inj hval
            apply Prod.ext
            · rw [hx0o]
              exact congrArg Sum.inr (Subtype.ext hij)
            · exact hr0
    show (e x0.1, x0.2) = (oIdx, r0)
    rw [hxo]
    simp only [houter, Equiv.apply_symm_apply]
  · rintro ⟨γ, hγ⟩
    unfold SPrime diagPullback at hγ
    rw [Finset.mem_filter] at hγ
    refine ⟨⟨diagCopyCol d alpha γ, hγ.2⟩, ?_⟩
    apply Subtype.ext
    exact diagCopyCol_injective d alpha
      (Classical.choose_spec (hpre ⟨diagCopyCol d alpha γ, hγ.2⟩))
  · intro a b
    have hchoose := Classical.choose_spec (Finset.mem_image.mp a.property)
    set x0 := Classical.choose (Finset.mem_image.mp a.property) with hx0
    have haval : a.val = rowRep d h₂ hq1 v p alpha B x0 := hchoose.2.symm
    have hbval : b.val = diagCopyCol d alpha (Classical.choose (hpre b)) :=
      (Classical.choose_spec (hpre b)).symm
    rw [haval, hbval]
    exact M4_rowRep_val d h₂ hq1 v p alpha B (SPrime d alpha Y) x0
      ⟨Classical.choose (hpre b), by
        unfold SPrime diagPullback
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by
          rw [Classical.choose_spec (hpre b)]
          exact b.property⟩⟩

theorem M4_duplicateExpansionComputedByResidual_of_branch
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool) (hP : P.Computes (M4 d v))
    {t : Nat} (br : Protocol.BranchAt P (M4 d v) t)
    {A0 B0 : Type*} (R : Finset (R4 d n)) (Cc : Finset (C4 d))
    (g0 : A0 -> B0 -> Bool)
    (hR : R ⊆ br.rows) (hC : Cc ⊆ br.cols)
    (hcontained : DuplicateExpansionContained (M4 d v) R Cc g0) :
    DuplicateExpansionComputedByResidual br.residual R Cc g0 := by
  classical
  obtain ⟨R', hR', C', hC', rowMap, colMap, hrsurj, hcsurj, hval⟩ := hcontained
  refine ⟨hR, hC, R', hR', C', hC', rowMap, colMap, hrsurj, hcsurj, ?_⟩
  intro a b
  rw [br.residual_eval_eq ⟨a.val, hR (hR' a.property)⟩
    ⟨b.val, hC (hC' b.property)⟩]
  rw [hP]
  exact hval a b

theorem M4_dense_Y_of_C1 (d : Nat) (alpha : Fin (Params.q2 d))
    (Y1 : Finset (C1 d))
    (hdense : (1 - Params.eta2 d) * (L1 d : Real) <= (Y1.card : Real)) :
    ∃ Y : Finset (C4 d),
      Y ⊆ diagCopySet d alpha ∧
      (1 - Params.eta2 d) * ((diagCopySet d alpha).card : Real) <=
        (Y.card : Real) ∧
      diagPullback d alpha Y = Y1 := by
  classical
  refine ⟨Y1.image (diagCopyCol d alpha), ?_, ?_, ?_⟩
  · intro c hc
    rw [Finset.mem_image] at hc
    rcases hc with ⟨γ, -, rfl⟩
    unfold diagCopySet
    exact Finset.mem_image.mpr ⟨γ, Finset.mem_univ _, rfl⟩
  · rw [diagCopySet_card d alpha,
      Finset.card_image_of_injective _ (diagCopyCol_injective d alpha)]
    exact hdense
  · unfold diagPullback
    ext γ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨γ', hγ', hγeq⟩
      have := diagCopyCol_injective d alpha hγeq
      rwa [← this]
    · intro hγ
      exact ⟨γ, hγ, rfl⟩

/-- The Stage-4 vector/M1 terminal floor, packaged for the ambient no-waste
column bridge.  For every reached stopping word `w`, the caller supplies a
dense diagonal column set `Yalpha w`, template-row and canonical-diagonal-column
embeddings landing in the reached prefix rectangle, and the exact `M1 d` copy
that `M4` realizes on the template rows (`M4_diagonal_copy_apply` chain).  The
resulting `TerminalHardWitnesses` carries floor `Bcap d = D (M1 d) = a + 1`,
exactly the residual budget consumed by `noWaste_firstKColBitsOn_univ_of_restrict`
after the Alice bin bits and Bob dimension bits are stripped.  This is the
Stage-4 analog of `M3_terminalHardWitnesses_of_prefix_M1_dense`, discharging the
`hard` field demand of both Phase-A and Phase-B stop data. -/
theorem M4_bin_terminalHard_of_fuzzy
    (d : Nat) (hpow : IsPow2 d) (hlog : 64 <= Nat.log 2 d) (hchk : Checklist d)
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool)
    (R : Finset A) (C : Finset B) (Q : Protocol A B Bool)
    (pat : List Protocol.ActualBitSide)
    (Yalpha : List Bool -> Finset (C1 d))
    (hYdense : forall w, w.length = pat.length ->
      (1 - Params.eta2 d) * (Fintype.card (C1 d) : Real) <=
        ((Yalpha w).card : Real))
    (rowEmbed : forall w, {r // r ∈ (Finset.univ : Finset (R1 d))} -> A)
    (colEmbed : forall w, {gamma // gamma ∈ Yalpha w} -> B)
    (hrowPrefix : forall w, w.length = pat.length ->
      forall r, rowEmbed w r ∈ Protocol.rowsAtPrefix R C Q w)
    (hcolPrefix : forall w, w.length = pat.length ->
      forall gamma, colEmbed w gamma ∈ Protocol.colsAtPrefix R C Q w)
    (hcopy : forall w, w.length = pat.length ->
      forall r gamma,
        G (rowEmbed w r) (colEmbed w gamma) =
          subgame (M1 d) (Finset.univ : Finset (R1 d)) (Yalpha w) r gamma) :
    Protocol.TerminalHardWitnesses G R C Q pat (Bcap d) := by
  classical
  have hBcap : Bcap d = D (M1 d) := by
    rw [Bcap, M1_complexity d hpow hlog]
  rw [hBcap]
  exact
    M3_terminalHardWitnesses_of_wordwise_dense_Yalpha_prefix_copy
      d hpow hlog hchk G R C Q pat Yalpha hYdense
      rowEmbed colEmbed hrowPrefix hcolPrefix hcopy

/-- The exact `M1 d` copy that `M4` realizes on a template row and a canonical
diagonal column: `M4 (p, S2coordPreimage α r) (diagCopyCol α γ) = M1 r γ`.
This is the value identity that instantiates the `hcopy` field of
`M4_bin_terminalHard_of_fuzzy` on the canonical diagonal (the columns
`M4LocalBranch` demands), via `M4_diagonal_copy_apply` + `S2coordPreimage_spec`. -/
theorem M4_diag_M1_copy
    (d : Nat) (h₂ : Params.t2 d ≤ Params.q2 d) (hq1 : 1 ≤ Params.q1 d)
    {n : Nat} (v : Fin n → Fin (Params.q2 d) → Bool)
    (p : Fin 4) (alpha : Fin (Params.q2 d)) (r : R1 d) (gamma : C1 d) :
    M4 d v (Sum.inl (p, S2coordPreimage d h₂ hq1 alpha r))
        (diagCopyCol d alpha gamma) = M1 d r gamma := by
  rw [M4_diagonal_copy_apply, M2_apply, S2coordPreimage_spec d h₂ hq1 alpha r,
    M1_apply]

/-- The value identity that `M4` realizes on template rows `{p}×C2` and canonical
diagonal columns `diagCopyCol r.1 r.2` (indexed by `r ∈ R2 = [q2]×C1`): it is EXACTLY
the transpose `M2ᵀ` (`lem:MFourDiagonalCopy`, `M4_diagonal_copy_apply`). This is the
copy relation feeding the Phase-A `D (M2)` terminal floor. -/
theorem M4_diag_M2transpose_copy
    (d : Nat) {n : Nat} (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4)
    (c : C2 d) (r : R2 d) :
    M4 d v (Sum.inl (p, c)) (diagCopyCol d r.1 r.2)
      = (fun (cc : C2 d) (rr : R2 d) => M2 d rr cc) c r :=
  M4_diagonal_copy_apply d v p c r.1 r.2

/-- The Stage-4 Phase-A terminal HARD-field builder at floor
`D (M2 d) = clog q2 + Bcap d`.  Each Alice-2-word stopping leaf of the template
restriction contains an exact `M2ᵀ` copy on template rows `{p}×C2` and diagonal
columns; since `D (M2ᵀ) = D (M2)` (`comp_transpose`), the leaf clears the `D (M2)`
floor demanded by the row no-waste bridge.  This discharges the `hhard` field of the
Phase-A certificate (the D(M2) floor of Obstruction 1, on the k0 slice — no
canonical-column issue since it lives entirely on the template restriction). -/
theorem M4_phaseA_terminalHard_of_M2copy
    (d : Nat) (hchk : Checklist d)
    {A B0 : Type*} [Fintype A] [Fintype B0]
    (G : A -> B0 -> Bool)
    (R : Finset A) (C : Finset B0) (Q : Protocol A B0 Bool)
    (pat : List Protocol.ActualBitSide)
    (rowEmbed : List Bool -> C2 d -> A)
    (colEmbed : List Bool -> R2 d -> B0)
    (hrowPrefix : forall w, w.length = pat.length ->
      forall c, rowEmbed w c ∈ Protocol.rowsAtPrefix R C Q w)
    (hcolPrefix : forall w, w.length = pat.length ->
      forall r, colEmbed w r ∈ Protocol.colsAtPrefix R C Q w)
    (hcopy : forall w, w.length = pat.length ->
      forall c r, G (rowEmbed w c) (colEmbed w r)
        = (fun (cc : C2 d) (rr : R2 d) => M2 d rr cc) c r) :
    Protocol.TerminalHardWitnesses G R C Q pat (D (M2 d)) := by
  classical
  have hL2 : 0 < L2 d := L2_pos d hchk.t2_le_q2 hchk.one_le_q1
  have hq2 : 0 < Params.q2 d := Params.q2_pos d
  have hL1 : 0 < L1 d := L1_pos d hchk.t1_le_q1_add_five
  haveI : Nonempty (C2 d) := ⟨(⟨0, hL2⟩ : Fin (L2 d))⟩
  haveI : Nonempty (R2 d) := ⟨(⟨0, hq2⟩, (⟨0, hL1⟩ : Fin (L1 d)))⟩
  refine
    terminalHardWitnesses_of_prefix_exact_copy
      G (fun (cc : C2 d) (rr : R2 d) => M2 d rr cc) R C Q pat (D (M2 d))
      rowEmbed colEmbed hrowPrefix hcolPrefix hcopy ?_
  rw [comp_transpose (M2 d)]

theorem M4_phaseB_branch_skeleton
    (d : Nat) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (B : Fin 4 -> Finset (Fin n))
    (binBr : ∀ p : Fin 4, Protocol.BranchAt P (M4 d v) 2)
    (hbinRows :
      ∀ p i, (Sum.inr i : R4 d n) ∈ (binBr p).rows ↔ i ∈ B p)
    (codeOfAlpha :
      Fin 4 -> Fin (Params.q2 d) ->
        Fin (2 ^ Nat.clog 2 (Params.q2 d)))
    (hcol : ∀ p,
      Protocol.FirstKColBitsOn
        (Finset.univ : Finset {a // a ∈ (binBr p).rows})
        (Finset.univ : Finset {b // b ∈ (binBr p).cols})
        (Nat.clog 2 (Params.q2 d)) (binBr p).residual)
    (hcols : ∀ p alpha,
      (Protocol.colPrefixCols (Nat.clog 2 (Params.q2 d))
        (binBr p).residual (codeOfAlpha p alpha)).Nonempty) :
    ∀ p : Fin 4, ∀ alpha : Fin (Params.q2 d),
      ∃ br : Protocol.BranchAt P (M4 d v)
          (2 + Nat.clog 2 (Params.q2 d)),
        Protocol.BranchExtends (binBr p) br ∧
        br.sideTrace =
          (binBr p).sideTrace ++
            List.replicate (Nat.clog 2 (Params.q2 d))
              Protocol.ActualBitSide.bob ∧
        (∀ i : Fin n,
          (Sum.inr i : R4 d n) ∈ br.rows ↔ i ∈ B p) := by
  intro p alpha
  let br : Protocol.BranchAt P (M4 d v)
      (2 + Nat.clog 2 (Params.q2 d)) :=
    Protocol.BranchAt.compose_colPrefix (binBr p) (codeOfAlpha p alpha)
      (hcol p) (hcols p alpha)
  refine ⟨br, ?_, ?_, ?_⟩
  · exact compose_colPrefix_extends (binBr p) (codeOfAlpha p alpha)
      (hcol p) (hcols p alpha)
  · exact compose_colPrefix_sideTrace_eq (binBr p) (codeOfAlpha p alpha)
      (hcol p) (hcols p alpha)
  · intro i
    have hrowsEq :
        br.rows = (binBr p).rows :=
      compose_colPrefix_rows_eq (binBr p) (codeOfAlpha p alpha)
        (hcol p) (hcols p alpha)
    rw [hrowsEq]
    exact hbinRows p i

theorem M4_no_waste_lift_from_certificates
    (d : Nat) (hchk : Checklist d) {n : Nat}
    (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (hP : P.Computes (M4 d v))
    (hcost : P.cost <= Byes d)
    (k0 : Fin (2 ^ 5))
    (code : Fin 4 -> Fin (2 ^ 2))
    (hcode : Function.Bijective code)
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset (R4 d n))
        (Finset.univ : Finset (C4 d)) 2 P)
    (hrows : forall p, (Protocol.rowPrefixRows 2 P (code p)).Nonempty)
    (codeOfAlpha :
      Fin 4 -> Fin (Params.q2 d) ->
        Fin (2 ^ Nat.clog 2 (Params.q2 d)))
    (hcol : ∀ p,
      Protocol.FirstKColBitsOn
        (Finset.univ :
          Finset {a // a ∈
            (ambientBinBranch d v P code hrow hP hrows
              (C4_univ_nonempty d hchk k0) p).rows})
        (Finset.univ :
          Finset {b // b ∈
            (ambientBinBranch d v P code hrow hP hrows
              (C4_univ_nonempty d hchk k0) p).cols})
        (Nat.clog 2 (Params.q2 d))
        (ambientBinBranch d v P code hrow hP hrows
          (C4_univ_nonempty d hchk k0) p).residual)
    (hcols : ∀ p alpha,
      (Protocol.colPrefixCols (Nat.clog 2 (Params.q2 d))
        (ambientBinBranch d v P code hrow hP hrows
          (C4_univ_nonempty d hchk k0) p).residual
        (codeOfAlpha p alpha)).Nonempty)
    (hlocal : ∀ p alpha,
      M4LocalBranch d v P (vectorPrefixBin d P code) p alpha
        (Protocol.BranchAt.compose_colPrefix
          (ambientBinBranch d v P code hrow hP hrows
            (C4_univ_nonempty d hchk k0) p)
          (codeOfAlpha p alpha) (hcol p) (hcols p alpha))) :
    ∃ B : Fin 4 -> Finset (Fin n),
      IsPartition4 B ∧
      ∃ binBr : ∀ p : Fin 4, Protocol.BranchAt P (M4 d v) 2,
        Function.Bijective (fun p : Fin 4 => (binBr p).transcript) ∧
        (∀ p : Fin 4,
          (binBr p).sideTrace =
            [Protocol.ActualBitSide.alice, Protocol.ActualBitSide.alice]) ∧
        (∀ p : Fin 4, ∀ y : C4 d, y ∈ (binBr p).cols) ∧
        (∀ p i, (Sum.inr i : R4 d n) ∈ (binBr p).rows ↔ i ∈ B p) ∧
        (∀ p, (binBr p).residual.cost <=
          Nat.clog 2 (Params.q2 d) + Bcap d) ∧
        ∀ p : Fin 4, ∀ alpha : Fin (Params.q2 d),
          ∃ br : Protocol.BranchAt P (M4 d v)
              (2 + Nat.clog 2 (Params.q2 d)),
            Protocol.BranchExtends (binBr p) br ∧
            br.sideTrace =
              (binBr p).sideTrace ++
                List.replicate (Nat.clog 2 (Params.q2 d))
                  Protocol.ActualBitSide.bob ∧
            (∀ i : Fin n,
              (Sum.inr i : R4 d n) ∈ br.rows ↔ i ∈ B p) ∧
            M4LocalBranch d v P B p alpha br := by
  classical
  let hC4 : (Finset.univ : Finset (C4 d)).Nonempty :=
    C4_univ_nonempty d hchk k0
  let B : Fin 4 -> Finset (Fin n) := vectorPrefixBin d P code
  let binBr : ∀ p : Fin 4, Protocol.BranchAt P (M4 d v) 2 :=
    ambientBinBranch d v P code hrow hP hrows hC4
  refine ⟨B, ?_, binBr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact vectorPrefixBin_partition d P code hcode
  · exact ambientBinBranch_transcripts_bijective d v P code hcode hrow hP hrows hC4
  · intro p
    exact ambientBinBranch_sideTrace d v P code hrow hP hrows hC4 p
  · intro p y
    exact ambientBinBranch_cols_univ d v P code hrow hP hrows hC4 p y
  · intro p i
    exact ambientBinBranch_vector_rows d v P code hrow hP hrows hC4 p i
  · intro p
    exact ambientBinBranch_residual_budget d v P code hrow hP hcost hrows hC4 p
  · intro p alpha
    let br : Protocol.BranchAt P (M4 d v)
        (2 + Nat.clog 2 (Params.q2 d)) :=
      Protocol.BranchAt.compose_colPrefix (binBr p) (codeOfAlpha p alpha)
        (hcol p) (hcols p alpha)
    refine ⟨br, ?_, ?_, ?_, ?_⟩
    · exact compose_colPrefix_extends (binBr p) (codeOfAlpha p alpha)
        (hcol p) (hcols p alpha)
    · exact compose_colPrefix_sideTrace_eq (binBr p) (codeOfAlpha p alpha)
        (hcol p) (hcols p alpha)
    · intro i
      have hrowsEq : br.rows = (binBr p).rows :=
        compose_colPrefix_rows_eq (binBr p) (codeOfAlpha p alpha)
          (hcol p) (hcols p alpha)
      rw [hrowsEq]
      exact ambientBinBranch_vector_rows d v P code hrow hP hrows hC4 p i
    · exact hlocal p alpha

/-! # Prefix synchronization lemmas for the Stage-4 lift -/

/-- Under a row-bits-only prefix on a live rectangle, the actual bit list has
full length (no early leaf can be reached from a live point). -/
theorem actualBitListRaw_length_of_firstKRowBitsOn
    {A B Z : Type*} [DecidableEq A] [DecidableEq B]
    {R : Finset A} {C : Finset B} {P : Protocol A B Z} {k : Nat}
    (hrow : Protocol.FirstKRowBitsOn R C k P)
    {a : A} {b : B} (ha : a ∈ R) (hb : b ∈ C) :
    (Protocol.actualBitListRaw k P a b).length = k := by
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
          obtain ⟨hl, hr⟩ := hrow
          by_cases hq : q a
          · have ha' : a ∈ R.filter fun x => q x = true := by
              rw [Finset.mem_filter]
              exact ⟨ha, hq⟩
            have htail := ih (R := R.filter fun x => q x = true) (C := C)
              (P := r) hr ha' hb
            simp [Protocol.actualBitListRaw, hq, htail]
          · have hqf : q a = false := by simp [hq]
            have ha' : a ∈ R.filter fun x => q x = false := by
              rw [Finset.mem_filter]
              exact ⟨ha, hqf⟩
            have htail := ih (R := R.filter fun x => q x = false) (C := C)
              (P := l) hl ha' hb
            simp [Protocol.actualBitListRaw, hq, htail]

/-- THE BUDGET-FORCED BIT-EQUALITY.  If the restricted protocol still carries
terminal hard witnesses worth `B0` below a `pat`-shaped stopping frontier and
the ambient protocol's total budget is only `pat.length + B0`, then the
ambient protocol cannot afford to spend any bit that the restriction deletes:
on the live rectangle, the ambient first `pat.length` actual bits agree with
the restricted first `pat.length` actual bits pointwise. -/
theorem actualBitListRaw_eq_restrict_of_terminal_budget
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (G : A -> B -> Bool) (P : Protocol A B Bool)
    (R : Finset A) (C : Finset B)
    (pat : List Protocol.ActualBitSide) (B0 : Nat)
    (hcomp : forall x, x ∈ R -> forall y, y ∈ C -> P.eval x y = G x y)
    (hcost : P.cost <= pat.length + B0)
    (hpat : Protocol.FirstPatternOn R C pat (Protocol.restrict R C P))
    (hterm : Protocol.TerminalHardWitnesses G R C
      (Protocol.restrict R C P) pat B0)
    {a : A} {b : B} (ha : a ∈ R) (hb : b ∈ C) :
    Protocol.actualBitListRaw pat.length P a b =
      Protocol.actualBitListRaw pat.length (Protocol.restrict R C P) a b := by
  classical
  induction pat generalizing R C P with
  | nil =>
      rfl
  | cons side tail ih =>
      have hcompRestrict :
          forall x, x ∈ R -> forall y, y ∈ C ->
            (Protocol.restrict R C P).eval x y = G x y := by
        intro x hx y hy
        rw [Protocol.eval_restrict_of_mem R C P hx hy]
        exact hcomp x hx y hy
      have hlow :
          (side :: tail).length + B0 <= (Protocol.restrict R C P).cost :=
        Protocol.firstPatternOn_terminal_cost_lower hcompRestrict hpat hterm
      cases P with
      | leaf z =>
          exfalso
          simp [Protocol.restrict, Protocol.cost] at hlow
      | aNode q l r =>
          by_cases hconst : exists beta, Protocol.IsRowConstantOn R q beta
          · exfalso
            have hstrict :
                (Protocol.restrict R C (Protocol.aNode q l r)).cost <
                  (Protocol.aNode q l r).cost := by
              unfold Protocol.restrict
              rw [dif_pos hconst]
              by_cases hchoose : Classical.choose hconst = true
              · rw [if_pos hchoose]
                have hle := Protocol.cost_restrict_le R C r
                have hchild : r.cost < (Protocol.aNode q l r).cost := by
                  simp [Protocol.cost]
                  omega
                exact lt_of_le_of_lt hle hchild
              · rw [if_neg hchoose]
                have hle := Protocol.cost_restrict_le R C l
                have hchild : l.cost < (Protocol.aNode q l r).cost := by
                  simp [Protocol.cost]
                  omega
                exact lt_of_le_of_lt hle hchild
            omega
          · have hrestrict :
                Protocol.restrict R C (Protocol.aNode q l r) =
                  Protocol.aNode q
                    (Protocol.restrict (R.filter fun x => q x = false) C l)
                    (Protocol.restrict (R.filter fun x => q x = true) C r) := by
              change
                (if h : exists beta, Protocol.IsRowConstantOn R q beta then
                  if Classical.choose h then Protocol.restrict R C r
                  else Protocol.restrict R C l
                else
                  Protocol.aNode q
                    (Protocol.restrict (R.filter fun x => q x = false) C l)
                    (Protocol.restrict (R.filter fun x => q x = true) C r)) =
                  Protocol.aNode q
                    (Protocol.restrict (R.filter fun x => q x = false) C l)
                    (Protocol.restrict (R.filter fun x => q x = true) C r)
              rw [dif_neg hconst]
            have hpat' := hpat
            have hterm' := hterm
            rw [hrestrict] at hpat' hterm'
            cases side with
            | alice =>
                obtain ⟨hpatL, hpatR⟩ := hpat'
                by_cases hq : q a
                · have haR : a ∈ R.filter fun x => q x = true := by
                    rw [Finset.mem_filter]
                    exact ⟨ha, hq⟩
                  have hcompR :
                      forall x, x ∈ R.filter (fun x => q x = true) ->
                        forall y, y ∈ C -> r.eval x y = G x y := by
                    intro x hx y hy
                    have hxR : x ∈ R := (Finset.mem_filter.mp hx).1
                    have hxq : q x = true := (Finset.mem_filter.mp hx).2
                    have h := hcomp x hxR y hy
                    simpa [Protocol.eval, hxq] using h
                  have hcostR : r.cost <= tail.length + B0 := by
                    have hlt : r.cost < (Protocol.aNode q l r).cost := by
                      simp [Protocol.cost]
                      omega
                    have hbudgetCons :
                        (Protocol.aNode q l r).cost <=
                          tail.length + 1 + B0 := by
                      simpa [Nat.add_assoc] using hcost
                    omega
                  have htermR :
                      Protocol.TerminalHardWitnesses G
                        (R.filter fun x => q x = true) C
                        (Protocol.restrict (R.filter fun x => q x = true) C r)
                        tail B0 :=
                    Protocol.terminalHardWitnesses_tail_true_of_aNode hterm'
                  have htail :=
                    ih (R := R.filter fun x => q x = true) (C := C) (P := r)
                      hcompR hcostR hpatR htermR haR hb
                  calc
                    Protocol.actualBitListRaw (Protocol.ActualBitSide.alice :: tail).length
                        (Protocol.aNode q l r) a b =
                        q a :: Protocol.actualBitListRaw tail.length r a b := by
                          simp [Protocol.actualBitListRaw, hq]
                    _ = q a ::
                        Protocol.actualBitListRaw tail.length
                          (Protocol.restrict (R.filter fun x => q x = true) C r)
                          a b := by rw [htail]
                    _ = Protocol.actualBitListRaw (Protocol.ActualBitSide.alice :: tail).length
                          (Protocol.restrict R C (Protocol.aNode q l r)) a b := by
                          rw [hrestrict]
                          simp [Protocol.actualBitListRaw, hq]
                · have hqf : q a = false := by simp [hq]
                  have haL : a ∈ R.filter fun x => q x = false := by
                    rw [Finset.mem_filter]
                    exact ⟨ha, hqf⟩
                  have hcompL :
                      forall x, x ∈ R.filter (fun x => q x = false) ->
                        forall y, y ∈ C -> l.eval x y = G x y := by
                    intro x hx y hy
                    have hxR : x ∈ R := (Finset.mem_filter.mp hx).1
                    have hxq : q x = false := (Finset.mem_filter.mp hx).2
                    have h := hcomp x hxR y hy
                    simpa [Protocol.eval, hxq] using h
                  have hcostL : l.cost <= tail.length + B0 := by
                    have hlt : l.cost < (Protocol.aNode q l r).cost := by
                      simp [Protocol.cost]
                      omega
                    have hbudgetCons :
                        (Protocol.aNode q l r).cost <=
                          tail.length + 1 + B0 := by
                      simpa [Nat.add_assoc] using hcost
                    omega
                  have htermL :
                      Protocol.TerminalHardWitnesses G
                        (R.filter fun x => q x = false) C
                        (Protocol.restrict (R.filter fun x => q x = false) C l)
                        tail B0 :=
                    Protocol.terminalHardWitnesses_tail_false_of_aNode hterm'
                  have htail :=
                    ih (R := R.filter fun x => q x = false) (C := C) (P := l)
                      hcompL hcostL hpatL htermL haL hb
                  calc
                    Protocol.actualBitListRaw (Protocol.ActualBitSide.alice :: tail).length
                        (Protocol.aNode q l r) a b =
                        q a :: Protocol.actualBitListRaw tail.length l a b := by
                          simp [Protocol.actualBitListRaw, hq]
                    _ = q a ::
                        Protocol.actualBitListRaw tail.length
                          (Protocol.restrict (R.filter fun x => q x = false) C l)
                          a b := by rw [htail]
                    _ = Protocol.actualBitListRaw (Protocol.ActualBitSide.alice :: tail).length
                          (Protocol.restrict R C (Protocol.aNode q l r)) a b := by
                          rw [hrestrict]
                          simp [Protocol.actualBitListRaw, hq]
            | bob =>
                exfalso
                rcases hpat' with hR | hC
                · rw [hR] at ha
                  exact absurd ha (Finset.notMem_empty a)
                · rw [hC] at hb
                  exact absurd hb (Finset.notMem_empty b)
      | bNode q l r =>
          by_cases hconst : exists beta, Protocol.IsColConstantOn C q beta
          · exfalso
            have hstrict :
                (Protocol.restrict R C (Protocol.bNode q l r)).cost <
                  (Protocol.bNode q l r).cost := by
              unfold Protocol.restrict
              rw [dif_pos hconst]
              by_cases hchoose : Classical.choose hconst = true
              · rw [if_pos hchoose]
                have hle := Protocol.cost_restrict_le R C r
                have hchild : r.cost < (Protocol.bNode q l r).cost := by
                  simp [Protocol.cost]
                  omega
                exact lt_of_le_of_lt hle hchild
              · rw [if_neg hchoose]
                have hle := Protocol.cost_restrict_le R C l
                have hchild : l.cost < (Protocol.bNode q l r).cost := by
                  simp [Protocol.cost]
                  omega
                exact lt_of_le_of_lt hle hchild
            omega
          · have hrestrict :
                Protocol.restrict R C (Protocol.bNode q l r) =
                  Protocol.bNode q
                    (Protocol.restrict R (C.filter fun y => q y = false) l)
                    (Protocol.restrict R (C.filter fun y => q y = true) r) := by
              change
                (if h : exists beta, Protocol.IsColConstantOn C q beta then
                  if Classical.choose h then Protocol.restrict R C r
                  else Protocol.restrict R C l
                else
                  Protocol.bNode q
                    (Protocol.restrict R (C.filter fun y => q y = false) l)
                    (Protocol.restrict R (C.filter fun y => q y = true) r)) =
                  Protocol.bNode q
                    (Protocol.restrict R (C.filter fun y => q y = false) l)
                    (Protocol.restrict R (C.filter fun y => q y = true) r)
              rw [dif_neg hconst]
            have hpat' := hpat
            have hterm' := hterm
            rw [hrestrict] at hpat' hterm'
            cases side with
            | alice =>
                exfalso
                rcases hpat' with hR | hC
                · rw [hR] at ha
                  exact absurd ha (Finset.notMem_empty a)
                · rw [hC] at hb
                  exact absurd hb (Finset.notMem_empty b)
            | bob =>
                obtain ⟨hpatL, hpatR⟩ := hpat'
                by_cases hq : q b
                · have hbC : b ∈ C.filter fun y => q y = true := by
                    rw [Finset.mem_filter]
                    exact ⟨hb, hq⟩
                  have hcompR :
                      forall x, x ∈ R ->
                        forall y, y ∈ C.filter (fun y => q y = true) ->
                          r.eval x y = G x y := by
                    intro x hx y hy
                    have hyC : y ∈ C := (Finset.mem_filter.mp hy).1
                    have hyq : q y = true := (Finset.mem_filter.mp hy).2
                    have h := hcomp x hx y hyC
                    simpa [Protocol.eval, hyq] using h
                  have hcostR : r.cost <= tail.length + B0 := by
                    have hlt : r.cost < (Protocol.bNode q l r).cost := by
                      simp [Protocol.cost]
                      omega
                    have hbudgetCons :
                        (Protocol.bNode q l r).cost <=
                          tail.length + 1 + B0 := by
                      simpa [Nat.add_assoc] using hcost
                    omega
                  have htermR :
                      Protocol.TerminalHardWitnesses G R
                        (C.filter fun y => q y = true)
                        (Protocol.restrict R (C.filter fun y => q y = true) r)
                        tail B0 :=
                    Protocol.terminalHardWitnesses_tail_true_of_bNode hterm'
                  have htail :=
                    ih (R := R) (C := C.filter fun y => q y = true) (P := r)
                      hcompR hcostR hpatR htermR ha hbC
                  calc
                    Protocol.actualBitListRaw (Protocol.ActualBitSide.bob :: tail).length
                        (Protocol.bNode q l r) a b =
                        q b :: Protocol.actualBitListRaw tail.length r a b := by
                          simp [Protocol.actualBitListRaw, hq]
                    _ = q b ::
                        Protocol.actualBitListRaw tail.length
                          (Protocol.restrict R (C.filter fun y => q y = true) r)
                          a b := by rw [htail]
                    _ = Protocol.actualBitListRaw (Protocol.ActualBitSide.bob :: tail).length
                          (Protocol.restrict R C (Protocol.bNode q l r)) a b := by
                          rw [hrestrict]
                          simp [Protocol.actualBitListRaw, hq]
                · have hqf : q b = false := by simp [hq]
                  have hbC : b ∈ C.filter fun y => q y = false := by
                    rw [Finset.mem_filter]
                    exact ⟨hb, hqf⟩
                  have hcompL :
                      forall x, x ∈ R ->
                        forall y, y ∈ C.filter (fun y => q y = false) ->
                          l.eval x y = G x y := by
                    intro x hx y hy
                    have hyC : y ∈ C := (Finset.mem_filter.mp hy).1
                    have hyq : q y = false := (Finset.mem_filter.mp hy).2
                    have h := hcomp x hx y hyC
                    simpa [Protocol.eval, hyq] using h
                  have hcostL : l.cost <= tail.length + B0 := by
                    have hlt : l.cost < (Protocol.bNode q l r).cost := by
                      simp [Protocol.cost]
                      omega
                    have hbudgetCons :
                        (Protocol.bNode q l r).cost <=
                          tail.length + 1 + B0 := by
                      simpa [Nat.add_assoc] using hcost
                    omega
                  have htermL :
                      Protocol.TerminalHardWitnesses G R
                        (C.filter fun y => q y = false)
                        (Protocol.restrict R (C.filter fun y => q y = false) l)
                        tail B0 :=
                    Protocol.terminalHardWitnesses_tail_false_of_bNode hterm'
                  have htail :=
                    ih (R := R) (C := C.filter fun y => q y = false) (P := l)
                      hcompL hcostL hpatL htermL ha hbC
                  calc
                    Protocol.actualBitListRaw (Protocol.ActualBitSide.bob :: tail).length
                        (Protocol.bNode q l r) a b =
                        q b :: Protocol.actualBitListRaw tail.length l a b := by
                          simp [Protocol.actualBitListRaw, hq]
                    _ = q b ::
                        Protocol.actualBitListRaw tail.length
                          (Protocol.restrict R (C.filter fun y => q y = false) l)
                          a b := by rw [htail]
                    _ = Protocol.actualBitListRaw (Protocol.ActualBitSide.bob :: tail).length
                          (Protocol.restrict R C (Protocol.bNode q l r)) a b := by
                          rw [hrestrict]
                          simp [Protocol.actualBitListRaw, hq]

/-! # Stage-4 dense reindex package (the transpose-separation port to C4)

The Stage-3 template (`M3BinDenseReindex` etc., Stage3.lean) is mirrored over
the Stage-4 ambient bins: rows are the surviving template rows
`Sum.inl (p, c)`, columns are the CANONICAL diagonal-copy columns
`diagCopyCol d alpha gamma` (not the `k0`-slice columns), and the reindexed
swapped restricted bin residual computes the SAME `M2DenseGame` as in
Stage 3, so the generic Stage-2 transpose-separation alpha data applies
verbatim. -/

private theorem M4_delta_sep :
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

theorem M4_M2DenseDepth_eq_log_q2 (d : Nat)
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d) :
    M2DenseDepth d = Nat.log 2 (Params.q2 d) := by
  rw [← hqcast, log_two_pow]

theorem M4_M2DenseDepth_eq_clog_q2 (d : Nat) (hchk : Checklist d)
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d) :
    M2DenseDepth d = Nat.clog 2 (Params.q2 d) := by
  rw [hchk.clog_q2_eq]
  exact M4_M2DenseDepth_eq_log_q2 d hqcast

/-- Stage-4 analogue of `equivOfInjectiveImage`-based reindex data
(`M3BinDenseReindex` ported over `C4`): the dense `M2` game sits inside the
bin rectangle transposed — the game's ROWS are canonical diagonal COLUMNS of
the branch, the game's COLUMNS are surviving template ROWS of the branch. -/
structure M4BinDenseReindex
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBr p).rows})
    (C : Finset {b // b ∈ (binBr p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d) where
  rowEquiv : M2DenseRows d ≃ {b // b ∈ C}
  colEquiv : M2DenseCols d Sdense ≃ {a // a ∈ R}
  game_eq :
    forall a b,
      subgame (M4 d v) (binBr p).rows (binBr p).cols
          (colEquiv b).val (rowEquiv a).val =
        M2DenseGame d hqcast Sdense a b

noncomputable def M4_diagColBranch
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hdiag_mem : forall a : M2DenseRows d,
      diagCopyCol d (Fin.cast hqcast a.val.1) a.val.2 ∈ (binBr p).cols)
    (a : M2DenseRows d) : {b // b ∈ (binBr p).cols} :=
  ⟨diagCopyCol d (Fin.cast hqcast a.val.1) a.val.2, hdiag_mem a⟩

theorem M4_diagColBranch_injective
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hdiag_mem : forall a : M2DenseRows d,
      diagCopyCol d (Fin.cast hqcast a.val.1) a.val.2 ∈ (binBr p).cols) :
    Function.Injective
      (M4_diagColBranch d v P binBr p hqcast hdiag_mem) := by
  intro a a' h
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  have hpoint := congrFun (congrArg Prod.snd hval) (0 : Fin 4)
  simp [M4_diagColBranch, diagCopyCol_eq] at hpoint
  apply Prod.ext
  · apply Fin.ext
    exact congrArg Fin.val hpoint.1
  · exact hpoint.2

noncomputable def M4_survivorRowBranch
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (hrow_mem : forall c, c ∈ Sdense ->
      (Sum.inl (p, c) : R4 d n) ∈ (binBr p).rows)
    (c : M2DenseCols d Sdense) : {a // a ∈ (binBr p).rows} :=
  ⟨(Sum.inl (p, c.val) : R4 d n), hrow_mem c.val c.property⟩

theorem M4_survivorRowBranch_injective
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (hrow_mem : forall c, c ∈ Sdense ->
      (Sum.inl (p, c) : R4 d n) ∈ (binBr p).rows) :
    Function.Injective
      (M4_survivorRowBranch d v P binBr p Sdense hrow_mem) := by
  intro c c' h
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  have hinl := Sum.inl.inj hval
  exact congrArg Prod.snd hinl

noncomputable def M4_denseDiagCols
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hdiag_mem : forall a : M2DenseRows d,
      diagCopyCol d (Fin.cast hqcast a.val.1) a.val.2 ∈ (binBr p).cols) :
    Finset {b // b ∈ (binBr p).cols} :=
  (Finset.univ : Finset (M2DenseRows d)).image
    (M4_diagColBranch d v P binBr p hqcast hdiag_mem)

noncomputable def M4_denseSurvivorRows
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (hrow_mem : forall c, c ∈ Sdense ->
      (Sum.inl (p, c) : R4 d n) ∈ (binBr p).rows) :
    Finset {a // a ∈ (binBr p).rows} :=
  (Finset.univ : Finset (M2DenseCols d Sdense)).image
    (M4_survivorRowBranch d v P binBr p Sdense hrow_mem)

/-- UNIT TEST TARGET (type-unit-test discipline): the hardest field `game_eq`
is inhabited from live data — `M4` on a surviving template row and a canonical
diagonal-copy column IS the `M2DenseGame` value, exactly as `M3BinDenseReindex`
realized it on the `k0` slice.  The value chain is
`M4 (Sum.inl (p,c)) (diagCopyCol α γ) = M2 (α,γ) c = M1 (S2fam c α) γ` (all
`rfl`), matching `M2DenseGame`'s `relaxedInterlace` unfolding. -/
noncomputable def M4_binDenseReindex_of_memberships
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hrow_mem : forall c, c ∈ Sdense ->
      (Sum.inl (p, c) : R4 d n) ∈ (binBr p).rows)
    (hdiag_mem : forall a : M2DenseRows d,
      diagCopyCol d (Fin.cast hqcast a.val.1) a.val.2 ∈ (binBr p).cols) :
    M4BinDenseReindex d v P binBr p Sdense
      (M4_denseSurvivorRows d v P binBr p Sdense hrow_mem)
      (M4_denseDiagCols d v P binBr p hqcast hdiag_mem) hqcast where
  rowEquiv :=
    equivOfInjectiveImage
      (M4_diagColBranch d v P binBr p hqcast hdiag_mem)
      (M4_diagColBranch_injective d v P binBr p hqcast hdiag_mem)
  colEquiv :=
    equivOfInjectiveImage
      (M4_survivorRowBranch d v P binBr p Sdense hrow_mem)
      (M4_survivorRowBranch_injective d v P binBr p Sdense hrow_mem)
  game_eq := by
    intro a b
    change
      M4 d v (Sum.inl (p, b.val))
          (diagCopyCol d (Fin.cast hqcast a.val.1) a.val.2) =
        M1 d (S2fam d b.val (Fin.cast hqcast a.val.1)) a.val.2
    rw [M4_diagonal_copy_apply, M2_apply]

noncomputable def M4_bin_dense_protocol
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBr p).rows})
    (C : Finset {b // b ∈ (binBr p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (htr : M4BinDenseReindex d v P binBr p Sdense R C hqcast) :
    Protocol (M2DenseRows d) (M2DenseCols d Sdense) Bool :=
  Protocol.reindex htr.rowEquiv htr.colEquiv
    (Protocol.restrictSub C R
      (Protocol.swap (Protocol.restrict R C (binBr p).residual)))

theorem M4_bin_dense_protocol_computes
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBr p).rows})
    (C : Finset {b // b ∈ (binBr p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (htr : M4BinDenseReindex d v P binBr p Sdense R C hqcast) :
    (M4_bin_dense_protocol d v P binBr p Sdense R C hqcast htr).Computes
      (M2DenseGame d hqcast Sdense) := by
  intro a b
  unfold M4_bin_dense_protocol
  rw [Protocol.eval_reindex]
  rw [Protocol.eval_restrictSub]
  rw [Protocol.eval_swap]
  rw [Protocol.eval_restrict_of_mem R C (binBr p).residual
    (htr.colEquiv b).property (htr.rowEquiv a).property]
  calc
    (binBr p).residual.eval (htr.colEquiv b).val (htr.rowEquiv a).val =
        subgame (M4 d v) (binBr p).rows (binBr p).cols
          (htr.colEquiv b).val (htr.rowEquiv a).val := by
      exact (binBr p).residual_computes
        (htr.colEquiv b).val (htr.rowEquiv a).val
    _ = M2DenseGame d hqcast Sdense a b := htr.game_eq a b

theorem M4_bin_dense_protocol_cost_le
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBr p).rows})
    (C : Finset {b // b ∈ (binBr p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hbudget : (binBr p).residual.cost <=
      Nat.clog 2 (Params.q2 d) + Bcap d)
    (hM2sum : D (M2 d) = Nat.clog 2 (Params.q2 d) + Bcap d)
    (htr : M4BinDenseReindex d v P binBr p Sdense R C hqcast) :
    (M4_bin_dense_protocol d v P binBr p Sdense R C hqcast htr).cost <=
      D (M2 d) := by
  unfold M4_bin_dense_protocol
  rw [Protocol.cost_reindex]
  rw [Protocol.cost_restrictSub]
  rw [Protocol.cost_swap]
  rw [hM2sum]
  exact le_trans
    (Protocol.cost_restrict_le R C (binBr p).residual)
    hbudget

/-- THE STAGE-2 DENSE FLOOR: `D(M2) <= D(M2DenseGame)` for any
`(1-8h2)`-dense column set.  Any cheaper protocol for the dense game would,
via the transpose-separation alpha data, leave after `M2DenseDepth = log q2`
row bits a residual of cost `< D(M1)` that still computes an `M1` dense-column
subgame worth `D(M1)` — impossible. -/
theorem M2Dense_game_floor
    (d : Nat) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) (hchk : Checklist d)
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
    (Sdense : Finset (C2 d))
    (hSdense : (1 - 8 * Params.h2 d) * (L2 d : Real) <= (Sdense.card : Real)) :
    D (M2 d) <= D (M2DenseGame d hqcast Sdense) := by
  classical
  have hlog256 : 256 <= Nat.log 2 d := by omega
  have hlog64 : 64 <= Nat.log 2 d := by omega
  have hne :=
    Workspace.UpperBound.AchievableCosts_nonempty
      (M2DenseGame d hqcast Sdense)
  have hmem : D (M2DenseGame d hqcast Sdense) ∈
      AchievableCosts (M2DenseGame d hqcast Sdense) := Nat.sInf_mem hne
  obtain ⟨Pd, hPdcost, hPdcomp⟩ := hmem
  by_cases hcase : D (M2 d) <= Pd.cost
  · rw [← hPdcost]
    exact hcase
  exfalso
  have hPdlt : Pd.cost < D (M2 d) := Nat.lt_of_not_le hcase
  have hPdcost' : Pd.cost <= D (M2 d) := le_of_lt hPdlt
  obtain ⟨ad⟩ :=
    M2_separation_transpose_dense_rows_alpha d hpow hlog256 hchk
      hm0_le hr2pow hp1 hp2 hxseed_le_one hrow_threshold hseed_bridge
      hy_le_one hrowTerm hcolTerm hresidual_density hqcast
      (1 - 8 * Params.h2 d) hsigma0 hsigma1 (le_refl _)
      hres_dense hxseed_le_inv_r hseed_bridge_dense M4_delta_sep hT1
      hgap_dense Sdense hSdense Pd hPdcomp hPdcost'
  let alpha0 : Fin (Params.q2 d) := ⟨0, Params.q2_pos d⟩
  let br := ad.branch alpha0
  -- fiber cover of the dense column set
  have hcardC2 : (Fintype.card (C2 d) : Real) = (L2 d : Real) := by
    simp [C2]
  have hfibcov :
      Sdense.image (fun c : C2 d => S2fam d c alpha0) =
        (Finset.univ : Finset (R1 d)) := by
    exact M3_C2_fiber_cover_of_dense d hchk Sdense
      (by rw [hcardC2]; exact hSdense) alpha0
  -- the dense M1 column set on the chosen dimension
  let YA : Finset (C1 d) := ad.Yalpha alpha0
  have hYdense :
      (1 - Params.eta2 d) * (Fintype.card (C1 d) : Real) <=
        (YA.card : Real) := ad.Yalpha_dense alpha0
  -- the row/column embeddings into the swapped branch rectangle
  let G' : {x // x ∈ br.rows} -> {y // y ∈ br.cols} -> Bool :=
    subgame
      (fun (c : M2DenseCols d Sdense) (a : M2DenseRows d) =>
        M2DenseGame d hqcast Sdense a c)
      br.rows br.cols
  let rho : {r // r ∈ (Finset.univ : Finset (R1 d))} -> {x // x ∈ br.rows} :=
    fun r =>
      ⟨⟨M3_fiber_cRep d Sdense alpha0 hfibcov r.val,
          M3_fiber_cRep_mem d Sdense alpha0 hfibcov r.val⟩,
        ad.S_rows_survive alpha0 _
          (M3_fiber_cRep_mem d Sdense alpha0 hfibcov r.val)⟩
  let sigma : {gamma // gamma ∈ YA} -> {y // y ∈ br.cols} :=
    fun gamma =>
      ⟨⟨(Fin.cast hqcast.symm alpha0, gamma.val), by simp [M2DenseRin]⟩,
        ad.diagonal_cols alpha0 gamma.val gamma.property⟩
  have hcastc :
      Fin.cast hqcast (Fin.cast hqcast.symm alpha0) = alpha0 := by
    apply Fin.ext
    rfl
  have hfun :
      (fun (r : {r // r ∈ (Finset.univ : Finset (R1 d))})
          (gamma : {gamma // gamma ∈ YA}) => G' (rho r) (sigma gamma)) =
        subgame (M1 d) (Finset.univ : Finset (R1 d)) YA := by
    funext r gamma
    show
      M2DenseGame d hqcast Sdense
          ⟨(Fin.cast hqcast.symm alpha0, gamma.val), by simp [M2DenseRin]⟩
          ⟨M3_fiber_cRep d Sdense alpha0 hfibcov r.val,
            M3_fiber_cRep_mem d Sdense alpha0 hfibcov r.val⟩ =
        subgame (M1 d) (Finset.univ : Finset (R1 d)) YA r gamma
    change
      M1 d (S2fam d (M3_fiber_cRep d Sdense alpha0 hfibcov r.val)
          (Fin.cast hqcast (Fin.cast hqcast.symm alpha0))) gamma.val =
        M1 d r.val gamma.val
    rw [hcastc, M3_fiber_cRep_eval d Sdense alpha0 hfibcov r.val]
  have hDres : D G' <= br.residual.cost :=
    Protocol.D_le_cost_of_computes br.residual_computes
  have hmap :
      D (subgame (M1 d) (Finset.univ : Finset (R1 d)) YA) <= D G' := by
    rw [← hfun]
    exact D_mapNodes_le G' rho sigma
  have hM1floor :
      Params.a d + 1 <=
        D (subgame (M1 d) (Finset.univ : Finset (R1 d)) YA) :=
    M1_dense_column_subgame_floor d hpow hlog64 hchk YA hYdense
  have hM1 : D (M1 d) = Params.a d + 1 := M1_complexity d hpow hlog64
  -- budget after the row bits
  have hbr := br.cost_after_actualBits
  have hswapcost : (Protocol.swap Pd).cost = Pd.cost := Protocol.cost_swap Pd
  have hM2 :
      D (M2 d) = D (M1 d) + Nat.log 2 (Params.q2 d) :=
    M2_complexity_h2prime d hpow hlog hchk hm0_le hr2pow
      hrow_threshold hraw hprime hy_three_fifths
  have hdepth : M2DenseDepth d = Nat.log 2 (Params.q2 d) :=
    M4_M2DenseDepth_eq_log_q2 d hqcast
  -- assemble the contradiction
  have hchain : D (M1 d) <= br.residual.cost :=
    le_trans (le_trans (by rw [hM1]; exact hM1floor) hmap) hDres
  rw [hswapcost] at hbr
  omega


/-! ## Ports of the Stage-3 fuzzy-transport lemmas to the Stage-4 shape -/

/-- Fiber-representative value identity on the canonical diagonal. -/
theorem M4_diagCopyCol_exact_M1_of_fiber
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (p : Fin 4) (c : C2 d)
    (alpha : Fin (Params.q2 d)) (gamma : C1 d) (r : R1 d)
    (hc : S2fam d c alpha = r) :
    M4 d v (Sum.inl (p, c)) (diagCopyCol d alpha gamma) = M1 d r gamma := by
  rw [M4_diagonal_copy_apply, M2_apply, hc]

/-- THE STAGE-4 restricted_col: the ambient canonical-diagonal
transpose-separation, via the GENERIC transport
`M3_restricted_col_of_dense_first_row_bits` fed by the Stage-4 reindexed dense
protocol's first-row-bits. -/
theorem M4_restricted_col_of_dense_alpha
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBr p).rows})
    (C : Finset {b // b ∈ (binBr p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (htr : M4BinDenseReindex d v P binBr p Sdense R C hqcast)
    (ad :
      M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
        (M4_bin_dense_protocol d v P binBr p Sdense R C hqcast htr)) :
    Protocol.FirstKColBitsOn R C (Nat.clog 2 (Params.q2 d))
      (Protocol.restrict R C (binBr p).residual) := by
  classical
  exact
    M3_restricted_col_of_dense_first_row_bits
      (binBr p).residual R C (Nat.clog 2 (Params.q2 d))
      htr.rowEquiv htr.colEquiv
      (by
        simpa [M4_bin_dense_protocol, ad.depth_eq_clog_q2] using
          ad.first_row_bits)

theorem M4_restricted_actualBitList_of_dense_Yalpha
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBr p).rows})
    (C : Finset {b // b ∈ (binBr p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (htr : M4BinDenseReindex d v P binBr p Sdense R C hqcast)
    (ad :
      M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
        (M4_bin_dense_protocol d v P binBr p Sdense R C hqcast htr))
    {w : List Bool} (hw : w.length = Nat.clog 2 (Params.q2 d))
    {alpha : Fin (Params.q2 d)}
    (hcode :
      ad.codeOfAlpha alpha =
        Fin.cast (by rw [hw, ← ad.depth_eq_clog_q2])
          (Protocol.codeOfBitList w))
    {c : C2 d} (hc : c ∈ Sdense)
    {gamma : C1 d} (hgamma : gamma ∈ ad.Yalpha alpha) :
    Protocol.actualBitListRaw w.length
        (Protocol.restrict R C (binBr p).residual)
        (htr.colEquiv (⟨c, hc⟩ : M2DenseCols d Sdense)).val
        (htr.rowEquiv
          (⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩ :
            M2DenseRows d)).val =
      w := by
  classical
  let Q0 := Protocol.restrict R C (binBr p).residual
  let Qswap := Protocol.restrictSub C R (Protocol.swap Q0)
  let Pdense :=
    M4_bin_dense_protocol d v P binBr p Sdense R C hqcast htr
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

theorem M4_restricted_fullCoverage_of_dense_alpha
    (d : Nat) (hpow : IsPow2 d) (hlog : 64 <= Nat.log 2 d)
    (hchk : Checklist d)
    {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (hSnonempty : Sdense.Nonempty)
    (R : Finset {a // a ∈ (binBr p).rows})
    (C : Finset {b // b ∈ (binBr p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (htr : M4BinDenseReindex d v P binBr p Sdense R C hqcast)
    (ad :
      M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
        (M4_bin_dense_protocol d v P binBr p Sdense R C hqcast htr)) :
    Protocol.FullStoppingFiberCoverage R C
      (Protocol.restrict R C (binBr p).residual)
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
    M4_restricted_actualBitList_of_dense_Yalpha d v P binBr p Sdense R C
      hqcast htr ad hwlen (by simpa [j] using hcode) hc hgamma

theorem M4_raw_prefix_eq_of_dense_Yalpha
    (d : Nat) {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (R : Finset {a // a ∈ (binBr p).rows})
    (C : Finset {b // b ∈ (binBr p).cols})
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (htr : M4BinDenseReindex d v P binBr p Sdense R C hqcast)
    (ad :
      M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
        (M4_bin_dense_protocol d v P binBr p Sdense R C hqcast htr))
    (hraw :
      Protocol.FirstKColBitsOn
        (Finset.univ : Finset {a // a ∈ (binBr p).rows})
        (Finset.univ : Finset {b // b ∈ (binBr p).cols})
        (Nat.clog 2 (Params.q2 d)) (binBr p).residual)
    (hSnonempty : Sdense.Nonempty)
    {alpha : Fin (Params.q2 d)} {gamma gamma0 : C1 d}
    (hgamma : gamma ∈ ad.Yalpha alpha)
    (hgamma0 : gamma0 ∈ ad.Yalpha alpha) :
    Protocol.prefixCodeRaw (Nat.clog 2 (Params.q2 d))
        (Protocol.swap (binBr p).residual)
        (htr.rowEquiv
          (⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩ :
            M2DenseRows d)).val =
      Protocol.prefixCodeRaw (Nat.clog 2 (Params.q2 d))
        (Protocol.swap (binBr p).residual)
        (htr.rowEquiv
          (⟨(Fin.cast hqcast.symm alpha, gamma0), by simp [M2DenseRin]⟩ :
            M2DenseRows d)).val := by
  classical
  let m := Nat.clog 2 (Params.q2 d)
  let Q0 := Protocol.restrict R C (binBr p).residual
  let Qswap := Protocol.restrictSub C R (Protocol.swap Q0)
  let Pdense :=
    M4_bin_dense_protocol d v P binBr p Sdense R C hqcast htr
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
      Protocol.actualBitListRaw m (binBr p).residual
          (htr.colEquiv sigma).val (htr.rowEquiv rho).val =
        Protocol.actualBitListRaw m (binBr p).residual
          (htr.colEquiv sigma).val (htr.rowEquiv rho0).val := by
    exact
      Protocol.actualBitListRaw_eq_of_restrict_eq_of_firstKColBitsOn
        (S := (Finset.univ : Finset {a // a ∈ (binBr p).rows}))
        (T := (Finset.univ : Finset {b // b ∈ (binBr p).cols}))
        (R := R) (C := C) (P := (binBr p).residual)
        (k := m) hraw
        (by intro a ha; exact Finset.mem_univ a)
        (by intro b hb; exact Finset.mem_univ b)
        (htr.colEquiv sigma).property (htr.colEquiv sigma).property
        (htr.rowEquiv rho).property (htr.rowEquiv rho0).property
        hresBits
  have hrawCode :
      Protocol.actualPrefixCodeRaw m (binBr p).residual
          (htr.colEquiv sigma).val (htr.rowEquiv rho).val =
        Protocol.actualPrefixCodeRaw m (binBr p).residual
          (htr.colEquiv sigma).val (htr.rowEquiv rho0).val :=
    Protocol.actualPrefixCodeRaw_eq_of_actualBitListRaw_eq hrawBits
  have hrowSwap :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset {b // b ∈ (binBr p).cols})
        (Finset.univ : Finset {a // a ∈ (binBr p).rows})
        m (Protocol.swap (binBr p).residual) := by
    simpa [m, Protocol.FirstKColBitsOn] using hraw
  have hpref :
      Protocol.prefixCodeRaw m (Protocol.swap (binBr p).residual)
          (htr.rowEquiv rho).val =
        Protocol.prefixCodeRaw m (Protocol.swap (binBr p).residual)
          (htr.rowEquiv rho0).val := by
    calc
      Protocol.prefixCodeRaw m (Protocol.swap (binBr p).residual)
          (htr.rowEquiv rho).val =
          Protocol.actualPrefixCodeRaw m
            (Protocol.swap (binBr p).residual)
            (htr.rowEquiv rho).val (htr.colEquiv sigma).val := by
            exact
              (Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
                (Finset.univ : Finset {b // b ∈ (binBr p).cols})
                (Finset.univ : Finset {a // a ∈ (binBr p).rows})
                m (Protocol.swap (binBr p).residual) hrowSwap
                (Finset.mem_univ (htr.rowEquiv rho).val)
                (Finset.mem_univ (htr.colEquiv sigma).val)).symm
      _ =
          Protocol.actualPrefixCodeRaw m (binBr p).residual
            (htr.colEquiv sigma).val (htr.rowEquiv rho).val := by
            exact Protocol.actualPrefixCodeRaw_swap m
              (binBr p).residual
              (htr.colEquiv sigma).val (htr.rowEquiv rho).val
      _ =
          Protocol.actualPrefixCodeRaw m (binBr p).residual
            (htr.colEquiv sigma).val (htr.rowEquiv rho0).val := hrawCode
      _ =
          Protocol.actualPrefixCodeRaw m
            (Protocol.swap (binBr p).residual)
            (htr.rowEquiv rho0).val (htr.colEquiv sigma).val := by
            exact
              (Protocol.actualPrefixCodeRaw_swap m
                (binBr p).residual
                (htr.colEquiv sigma).val (htr.rowEquiv rho0).val).symm
      _ =
          Protocol.prefixCodeRaw m (Protocol.swap (binBr p).residual)
            (htr.rowEquiv rho0).val := by
            exact
              Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
                (Finset.univ : Finset {b // b ∈ (binBr p).cols})
                (Finset.univ : Finset {a // a ∈ (binBr p).rows})
                m (Protocol.swap (binBr p).residual) hrowSwap
                (Finset.mem_univ (htr.rowEquiv rho0).val)
                (Finset.mem_univ (htr.colEquiv sigma).val)
  simpa [m, rho, rho0] using hpref

/-- THE STAGE-4 STOP DATA: `restricted_col` + `cover` + `hard` over the dense
canonical-diagonal rectangle of an ambient Stage-4 bin, at terminal floor
`Bcap d`. -/
theorem M4_stage4StopData_for_dense_bin
    (d : Nat) (hpow : IsPow2 d) (hlog : 64 <= Nat.log 2 d)
    (hchk : Checklist d)
    {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (binBr : Fin 4 -> Protocol.BranchAt P (M4 d v) 2)
    (p : Fin 4) (Sdense : Finset (C2 d))
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hrow_mem : forall c, c ∈ Sdense ->
      (Sum.inl (p, c) : R4 d n) ∈ (binBr p).rows)
    (hdiag_mem : forall a : M2DenseRows d,
      diagCopyCol d (Fin.cast hqcast a.val.1) a.val.2 ∈ (binBr p).cols)
    (hSnonempty : Sdense.Nonempty)
    (hfiberCover : forall alpha,
      Sdense.image (fun c : C2 d => S2fam d c alpha) =
        (Finset.univ : Finset (R1 d)))
    (ad :
      let R := M4_denseSurvivorRows d v P binBr p Sdense hrow_mem
      let C := M4_denseDiagCols d v P binBr p hqcast hdiag_mem
      let htr :=
        M4_binDenseReindex_of_memberships d v P binBr p Sdense hqcast
          hrow_mem hdiag_mem
      M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense
        (M4_bin_dense_protocol d v P binBr p Sdense R C hqcast htr)) :
    Stage3StopData
      (subgame (M4 d v) (binBr p).rows (binBr p).cols)
      (binBr p).residual
      (M4_denseSurvivorRows d v P binBr p Sdense hrow_mem)
      (M4_denseDiagCols d v P binBr p hqcast hdiag_mem)
      (Nat.clog 2 (Params.q2 d)) (Bcap d) := by
  classical
  let R := M4_denseSurvivorRows d v P binBr p Sdense hrow_mem
  let C := M4_denseDiagCols d v P binBr p hqcast hdiag_mem
  let htr :=
    M4_binDenseReindex_of_memberships d v P binBr p Sdense hqcast
      hrow_mem hdiag_mem
  change
    Stage3StopData
      (subgame (M4 d v) (binBr p).rows (binBr p).cols)
      (binBr p).residual R C
      (Nat.clog 2 (Params.q2 d)) (Bcap d)
  let m := Nat.clog 2 (Params.q2 d)
  have hm_depth : m = M2DenseDepth d := by
    dsimp [m]
    exact ad.depth_eq_clog_q2.symm
  have hrestricted :
      Protocol.FirstKColBitsOn R C m
        (Protocol.restrict R C (binBr p).residual) := by
    exact
      M4_restricted_col_of_dense_alpha d v P binBr p Sdense R C
        hqcast htr ad
  have hcover :
      Protocol.FullStoppingFiberCoverage R C
        (Protocol.restrict R C (binBr p).residual)
        (List.replicate m Protocol.ActualBitSide.bob) := by
    exact
      M4_restricted_fullCoverage_of_dense_alpha d hpow hlog hchk v P
        binBr p Sdense hSnonempty R C hqcast htr ad
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
        {a // a ∈ (binBr p).rows} := fun w r =>
    let alpha := wordAlpha w
    let c := M3_fiber_cRep d Sdense alpha (hfiberCover alpha) r.val
    let hc : c ∈ Sdense :=
      M3_fiber_cRep_mem d Sdense alpha (hfiberCover alpha) r.val
    ⟨(Sum.inl (p, c) : R4 d n), hrow_mem c hc⟩
  let colEmbed :
      forall w, {gamma // gamma ∈ ad.Yalpha (wordAlpha w)} ->
        {b // b ∈ (binBr p).cols} := fun w gamma =>
    let alpha := wordAlpha w
    let rho : M2DenseRows d :=
      ⟨(Fin.cast hqcast.symm alpha, gamma.val), by simp [M2DenseRin]⟩
    ⟨diagCopyCol d alpha gamma.val, by
      have h := hdiag_mem rho
      simpa [rho] using h⟩
  have hrowEmbed_mem :
      forall w r, rowEmbed w r ∈ R := by
    intro w r
    dsimp [rowEmbed, R, M4_denseSurvivorRows]
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
    dsimp [colEmbed, C, M4_denseDiagCols]
    refine Finset.mem_image.mpr ?_
    let rho : M2DenseRows d :=
      ⟨(Fin.cast hqcast.symm (wordAlpha w), gamma.val), by simp [M2DenseRin]⟩
    refine ⟨rho, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    simp [rho, M4_diagColBranch, diagCopyCol]
  refine
    { restricted_col := hrestricted
      cover := hcover
      hard := ?_ }
  refine
    M4_bin_terminalHard_of_fuzzy
      d hpow hlog hchk
      (subgame (M4 d v) (binBr p).rows (binBr p).cols)
      R C (Protocol.restrict R C (binBr p).residual)
      (List.replicate m Protocol.ActualBitSide.bob)
      (fun w => ad.Yalpha (wordAlpha w))
      ?_ rowEmbed colEmbed ?_ ?_ ?_
  · intro w hw
    exact ad.Yalpha_dense (wordAlpha w)
  · intro w hw r
    have hwlen : w.length = m := by simpa using hw
    rw [Protocol.rowsAtPrefix_eq_of_firstKColBitsOn
      (R := R) (C := C)
      (P := Protocol.restrict R C (binBr p).residual)
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
      M4_restricted_actualBitList_of_dense_Yalpha d v P binBr p Sdense R C
        hqcast htr ad hwlen (hwordAlpha_code w hwlen) hc gamma.property
    simpa [rowEmbed, colEmbed, alpha, c, htr,
      M4_binDenseReindex_of_memberships, equivOfInjectiveImage,
      M4_survivorRowBranch, M4_diagColBranch, R, C] using hbits
  · intro w hw r gamma
    let alpha := wordAlpha w
    let c := M3_fiber_cRep d Sdense alpha (hfiberCover alpha) r.val
    have hceval : S2fam d c alpha = r.val :=
      M3_fiber_cRep_eval d Sdense alpha (hfiberCover alpha) r.val
    simpa [rowEmbed, colEmbed, alpha, c, subgame] using
      M4_diagCopyCol_exact_M1_of_fiber d v p c alpha gamma.val r.val hceval



/-! ## Phase-A certificates: slice coverage, dense hard floor, code alignment -/

theorem M4_dense_C2_nonempty (d : Nat) (hchk : Checklist d)
    (hsigma0 : 0 < 1 - 8 * Params.h2 d)
    (S : Finset (C2 d))
    (hS : (1 - 8 * Params.h2 d) * (Fintype.card (C2 d) : Real) <=
      (S.card : Real)) :
    S.Nonempty := by
  have hL2 : 0 < L2 d := L2_pos d hchk.t2_le_q2 hchk.one_le_q1
  have hCpos : (0 : Real) < (Fintype.card (C2 d) : Real) := by
    have : (0 : Real) < (L2 d : Real) := by exact_mod_cast hL2
    simpa [C2] using this
  have hpos : (0 : Real) < (S.card : Real) :=
    lt_of_lt_of_le (mul_pos hsigma0 hCpos) hS
  have hposn : 0 < S.card := by exact_mod_cast hpos
  exact Finset.card_pos.mp hposn

theorem M4_D_M2_eq_clog_add_Bcap (d : Nat) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) (hchk : Checklist d)
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
            (Params.h2 d) c) :
    D (M2 d) = Nat.clog 2 (Params.q2 d) + Bcap d := by
  have hlog64 : 64 <= Nat.log 2 d := by omega
  have hM1 : D (M1 d) = Bcap d := by
    rw [M1_complexity d hpow hlog64, Bcap]
  have hM2 :
      D (M2 d) = D (M1 d) + Nat.log 2 (Params.q2 d) :=
    M2_complexity_h2prime d hpow hlog hchk hm0_le hr2pow
      hrow_threshold hraw hprime hy_three_fifths
  rw [hM2, hchk.clog_q2_eq, hM1]
  omega

theorem M4_inl_mem_templateRows (d : Nat) {n : Nat} (pc : R3 d) :
    (Sum.inl pc : R4 d n) ∈ templateRows d n := by
  unfold templateRows
  exact Finset.mem_image.mpr ⟨pc, Finset.mem_univ pc, rfl⟩

theorem M4_pair_mem_templateCols (d : Nat) (k0 : Fin (2 ^ 5)) (c3 : C3 d) :
    ((k0, c3) : C4 d) ∈ templateCols d k0 := by
  unfold templateCols
  exact Finset.mem_image.mpr ⟨c3, Finset.mem_univ c3, rfl⟩

/-- Slice prefix code = restricted prefix code on the template row block. -/
theorem M4_slice_prefixCode_eq_restrict (d : Nat) {n : Nat}
    (P : Protocol (R4 d n) (C4 d) Bool) (k0 : Fin (2 ^ 5)) (pc : R3 d) :
    Protocol.prefixCodeRaw 2 (templateSliceProtocol d P k0) pc =
      Protocol.prefixCodeRaw 2
        (Protocol.restrict (templateRows d n) (templateCols d k0) P)
        (Sum.inl pc : R4 d n) := by
  unfold templateSliceProtocol
  rw [Protocol.prefixCodeRaw_reindex]
  rw [Protocol.prefixCodeRaw_restrictSub]
  rfl

/-- A template row whose SLICE two-bit code matches `w` follows `w` as its
actual restricted bit list against any template column. -/
theorem M4_slice_restrict_bits (d : Nat) {n : Nat}
    (P : Protocol (R4 d n) (C4 d) Bool) (k0 : Fin (2 ^ 5))
    (hfirst :
      Protocol.FirstKRowBitsOn (templateRows d n) (templateCols d k0) 2
        (Protocol.restrict (templateRows d n) (templateCols d k0) P))
    {w : List Bool} (hw : w.length = 2)
    (pc : R3 d) (c3 : C3 d)
    (hcode : Protocol.prefixCodeRaw 2 (templateSliceProtocol d P k0) pc =
      Fin.cast (by rw [hw]) (Protocol.codeOfBitList w)) :
    Protocol.actualBitListRaw w.length
      (Protocol.restrict (templateRows d n) (templateCols d k0) P)
      (Sum.inl pc : R4 d n) ((k0, c3) : C4 d) = w := by
  classical
  have hfirst' :
      Protocol.FirstKRowBitsOn (templateRows d n) (templateCols d k0)
        w.length
        (Protocol.restrict (templateRows d n) (templateCols d k0) P) := by
    rw [hw]
    exact hfirst
  have hcodeR :
      Protocol.prefixCodeRaw w.length
          (Protocol.restrict (templateRows d n) (templateCols d k0) P)
          (Sum.inl pc : R4 d n) =
        Protocol.codeOfBitList w := by
    apply Fin.ext
    have hl :
        (Protocol.prefixCodeRaw w.length
            (Protocol.restrict (templateRows d n) (templateCols d k0) P)
            (Sum.inl pc : R4 d n)).val =
          (Protocol.prefixCodeRaw 2
            (Protocol.restrict (templateRows d n) (templateCols d k0) P)
            (Sum.inl pc : R4 d n)).val := by
      rw [hw]
    have hr :
        (Protocol.prefixCodeRaw 2
            (Protocol.restrict (templateRows d n) (templateCols d k0) P)
            (Sum.inl pc : R4 d n)).val =
          (Protocol.codeOfBitList w).val := by
      rw [← M4_slice_prefixCode_eq_restrict d P k0 pc, hcode]
      simp
    exact hl.trans hr
  exact
    Protocol.actualBitListRaw_eq_of_firstKRowBitsOn_prefixCodeRaw
      (R := templateRows d n) (C := templateCols d k0)
      (P := Protocol.restrict (templateRows d n) (templateCols d k0) P)
      (w := w) (a := (Sum.inl pc : R4 d n)) (b := ((k0, c3) : C4 d))
      hfirst' (M4_inl_mem_templateRows d pc)
      (M4_pair_mem_templateCols d k0 c3) hcodeR

/-- PIECE 1 (Phase-A `hcover`): full two-bit stopping fiber coverage of the
template restriction, from the slice bin machinery — every two-bit word is
the slice code of some reached row (the four codes biject onto the four bins). -/
theorem M4_template_restrict_coverage (d : Nat) (hchk : Checklist d) {n : Nat}
    (P : Protocol (R4 d n) (C4 d) Bool) (k0 : Fin (2 ^ 5))
    (hfirst :
      Protocol.FirstKRowBitsOn (templateRows d n) (templateCols d k0) 2
        (Protocol.restrict (templateRows d n) (templateCols d k0) P))
    (hNW :
      NoWasteConclusion
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d =>
          Protocol.prefixCodeRaw 2 (templateSliceProtocol d P k0) r)
        (Fintype.card (C2 d))
        (M3_rowLoss d))
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d)) :
    Protocol.FullStoppingFiberCoverage
      (templateRows d n) (templateCols d k0)
      (Protocol.restrict (templateRows d n) (templateCols d k0) P)
      (List.replicate 2 Protocol.ActualBitSide.alice) := by
  classical
  intro w hw
  have hw2 : w.length = 2 := by simpa using hw
  let j : Fin (2 ^ 2) := Fin.cast (by rw [hw2]) (Protocol.codeOfBitList w)
  obtain ⟨pc, hpc⟩ :=
    M3_rowPrefixRows_nonempty_of_noWaste d
      (templateSliceProtocol d P k0) hNW hgap j
  have hpccode :
      Protocol.prefixCodeRaw 2 (templateSliceProtocol d P k0) pc = j := by
    rw [Protocol.rowPrefixRows, Finset.mem_filter] at hpc
    exact hpc.2
  obtain ⟨c3, -⟩ := M3_C3_univ_nonempty d hchk
  refine ⟨Sum.inl pc, M4_inl_mem_templateRows d pc,
    (k0, c3), M4_pair_mem_templateCols d k0 c3, ?_⟩
  exact
    M4_slice_restrict_bits d P k0 hfirst hw2 pc c3
      (by simpa [j] using hpccode)

/-- PIECE 1' (Phase-A `hhard`): every reached two-bit leaf of the template
restriction contains the survivors x canonical-`k0`-diagonal copy of the dense
`M2` game, whose complexity is at least `D(M2) = clog q2 + Bcap` by the
Stage-2 dense floor. -/
theorem M4_phaseA_terminalHard_dense (d : Nat) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) (hchk : Checklist d)
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
    {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool) (k0 : Fin (2 ^ 5))
    (hfirst :
      Protocol.FirstKRowBitsOn (templateRows d n) (templateCols d k0) 2
        (Protocol.restrict (templateRows d n) (templateCols d k0) P))
    (hNW :
      NoWasteConclusion
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d =>
          Protocol.prefixCodeRaw 2 (templateSliceProtocol d P k0) r)
        (Fintype.card (C2 d))
        (M3_rowLoss d))
    (hsurj :
      Protocol.alphaOfCode_surj_on_Q
        (Finset.univ : Finset (Fin 4))
        (Finset.univ : Finset (Fin 4 × C2 d))
        (fun r : Fin 4 × C2 d =>
          Protocol.prefixCodeRaw 2 (templateSliceProtocol d P k0) r)
        hNW (fun j : Fin (2 ^ 2) => j))
    (hgap : 4 * M3_rowLoss d < Fintype.card (C2 d)) :
    Protocol.TerminalHardWitnesses (M4 d v)
      (templateRows d n) (templateCols d k0)
      (Protocol.restrict (templateRows d n) (templateCols d k0) P)
      (List.replicate 2 Protocol.ActualBitSide.alice)
      (Nat.clog 2 (Params.q2 d) + Bcap d) := by
  classical
  have hlog64 : 64 <= Nat.log 2 d := by omega
  have hM2sum : D (M2 d) = Nat.clog 2 (Params.q2 d) + Bcap d :=
    M4_D_M2_eq_clog_add_Bcap d hpow hlog hchk hm0_le hr2pow
      hrow_threshold hraw hprime hy_three_fifths
  intro w hw
  have hw2 : w.length = 2 := by simpa using hw
  let j : Fin (2 ^ 2) := Fin.cast (by rw [hw2]) (Protocol.codeOfBitList w)
  obtain ⟨p, hpj⟩ :=
    (M3_codeOfBin_bijective d (templateSliceProtocol d P k0) hNW hsurj).2 j
  set Sw := M3_binSurvivors d (templateSliceProtocol d P k0) hNW hsurj p
    with hSwdef
  have hSwdense :
      (1 - 8 * Params.h2 d) * (Fintype.card (C2 d) : Real) <=
        ((Sw).card : Real) :=
    M3_binSurvivors_dense d (templateSliceProtocol d P k0) hchk hNW hsurj
      hgap p
  have hSwne : Sw.Nonempty :=
    M4_dense_C2_nonempty d hchk hsigma0 Sw hSwdense
  obtain ⟨cS, hcS⟩ := hSwne
  obtain ⟨c3, -⟩ := M3_C3_univ_nonempty d hchk
  have hbitsS :
      forall c, c ∈ Sw -> forall y : C3 d,
        Protocol.actualBitListRaw w.length
          (Protocol.restrict (templateRows d n) (templateCols d k0) P)
          (Sum.inl (p, c) : R4 d n) ((k0, y) : C4 d) = w := by
    intro c hc y
    refine M4_slice_restrict_bits d P k0 hfirst hw2 (p, c) y ?_
    have hmemcode :=
      M3_binSurvivors_mem_code d (templateSliceProtocol d P k0) hNW hsurj
        p c hc
    rw [hmemcode]
    exact hpj
  let Rw : Finset (R4 d n) :=
    (Finset.univ : Finset (M2DenseCols d Sw)).image
      (fun c => (Sum.inl (p, c.val) : R4 d n))
  let Cw : Finset (C4 d) :=
    (Finset.univ : Finset (M2DenseRows d)).image
      (fun rho =>
        ((k0, M3_diagCol d (Fin.cast hqcast rho.val.1) rho.val.2) : C4 d))
  have hC1pos : 0 < L1 d := L1_pos d hchk.t1_le_q1_add_five
  have hDRne : Nonempty (M2DenseRows d) :=
    ⟨⟨(⟨0, by positivity⟩, (⟨0, hC1pos⟩ : Fin (L1 d))),
      by simp [M2DenseRin]⟩⟩
  refine ⟨Rw, Cw, ?_, ?_⟩
  · refine
      { rows_subset := ?_
        cols_subset := ?_
        rows_nonempty := ?_
        cols_nonempty := ?_ }
    · intro a ha
      rcases Finset.mem_image.mp ha with ⟨c, -, rfl⟩
      rw [Protocol.rowsAtPrefix, Finset.mem_filter]
      refine ⟨M4_inl_mem_templateRows d (p, c.val), ?_⟩
      exact ⟨(k0, c3), M4_pair_mem_templateCols d k0 c3,
        hbitsS c.val c.property c3⟩
    · intro b hb
      rcases Finset.mem_image.mp hb with ⟨rho, -, rfl⟩
      rw [Protocol.colsAtPrefix, Finset.mem_filter]
      refine ⟨M4_pair_mem_templateCols d k0 _, ?_⟩
      exact ⟨Sum.inl (p, cS), M4_inl_mem_templateRows d (p, cS),
        hbitsS cS hcS _⟩
    · exact ⟨Sum.inl (p, cS),
        Finset.mem_image.mpr ⟨⟨cS, hcS⟩, Finset.mem_univ _, rfl⟩⟩
    · obtain ⟨rho0⟩ := hDRne
      exact ⟨(k0, M3_diagCol d (Fin.cast hqcast rho0.val.1) rho0.val.2),
        Finset.mem_image.mpr ⟨rho0, Finset.mem_univ _, rfl⟩⟩
  · have hSwL2 :
        (1 - 8 * Params.h2 d) * (L2 d : Real) <= ((Sw).card : Real) := by
      have hcardC2 : (Fintype.card (C2 d) : Real) = (L2 d : Real) := by
        simp [C2]
      rw [← hcardC2]
      exact hSwdense
    have hfloor1 : D (M2 d) <= D (M2DenseGame d hqcast Sw) :=
      M2Dense_game_floor d hpow hlog hchk hm0_le hr2pow hp1 hp2
        hxseed_le_one hrow_threshold hseed_bridge hy_le_one hrowTerm
        hcolTerm hresidual_density hqcast hsigma0 hsigma1 hres_dense
        hxseed_le_inv_r hseed_bridge_dense hT1 hgap_dense hraw hprime
        hy_three_fifths Sw hSwL2
    have htrans :
        D (fun (c : M2DenseCols d Sw) (rho : M2DenseRows d) =>
            M2DenseGame d hqcast Sw rho c) =
          D (M2DenseGame d hqcast Sw) :=
      comp_transpose (M2DenseGame d hqcast Sw)
    have hcopyD :
        D (fun (c : M2DenseCols d Sw) (rho : M2DenseRows d) =>
            M2DenseGame d hqcast Sw rho c) <=
          D (subgame (M4 d v) Rw Cw) := by
      refine
        D_exact_copy_le_subgame (M4 d v)
          (fun (c : M2DenseCols d Sw) (rho : M2DenseRows d) =>
            M2DenseGame d hqcast Sw rho c)
          (fun c => (Sum.inl (p, c.val) : R4 d n))
          (fun rho =>
            ((k0, M3_diagCol d (Fin.cast hqcast rho.val.1) rho.val.2) : C4 d))
          Rw Cw ?_ ?_ ?_
      · intro c
        exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩
      · intro rho
        exact Finset.mem_image.mpr ⟨rho, Finset.mem_univ _, rfl⟩
      · intro c rho
        change
          M3 d (p, c.val)
              (M3_diagCol d (Fin.cast hqcast rho.val.1) rho.val.2) =
            M2DenseGame d hqcast Sw rho c
        change
          M3 d (p, c.val)
              (M3_diagCol d (Fin.cast hqcast rho.val.1) rho.val.2) =
            M1 d (S2fam d c.val (Fin.cast hqcast rho.val.1)) rho.val.2
        rw [M3_diagCol_exact_M1]
    calc
      Nat.clog 2 (Params.q2 d) + Bcap d = D (M2 d) := hM2sum.symm
      _ <= D (M2DenseGame d hqcast Sw) := hfloor1
      _ = D (fun (c : M2DenseCols d Sw) (rho : M2DenseRows d) =>
            M2DenseGame d hqcast Sw rho c) := htrans.symm
      _ <= D (subgame (M4 d v) Rw Cw) := hcopyD

/-- CODE ALIGNMENT: under the Phase-A no-waste budget, the ambient two-bit
prefix code of a template row equals its slice prefix code (the ambient
protocol cannot afford any bit that the template restriction deletes). -/
theorem M4_ambient_prefixCode_eq_slice (d : Nat) (hchk : Checklist d)
    {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (hP : P.Computes (M4 d v)) (hcost : P.cost <= Byes d)
    (k0 : Fin (2 ^ 5))
    (hfirst :
      Protocol.FirstKRowBitsOn (templateRows d n) (templateCols d k0) 2
        (Protocol.restrict (templateRows d n) (templateCols d k0) P))
    (hhard :
      Protocol.TerminalHardWitnesses (M4 d v)
        (templateRows d n) (templateCols d k0)
        (Protocol.restrict (templateRows d n) (templateCols d k0) P)
        (List.replicate 2 Protocol.ActualBitSide.alice)
        (Nat.clog 2 (Params.q2 d) + Bcap d))
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset (R4 d n))
        (Finset.univ : Finset (C4 d)) 2 P)
    (pc : R3 d) :
    Protocol.prefixCodeRaw 2 P (Sum.inl pc : R4 d n) =
      Protocol.prefixCodeRaw 2 (templateSliceProtocol d P k0) pc := by
  classical
  obtain ⟨c3, -⟩ := M3_C3_univ_nonempty d hchk
  have hmemR : (Sum.inl pc : R4 d n) ∈ templateRows d n :=
    M4_inl_mem_templateRows d pc
  have hmemC : ((k0, c3) : C4 d) ∈ templateCols d k0 :=
    M4_pair_mem_templateCols d k0 c3
  have hpat :
      Protocol.FirstPatternOn (templateRows d n) (templateCols d k0)
        (List.replicate 2 Protocol.ActualBitSide.alice)
        (Protocol.restrict (templateRows d n) (templateCols d k0) P) :=
    (Protocol.firstPattern_replicate_alice_iff
      (templateRows d n) (templateCols d k0) 2
      (Protocol.restrict (templateRows d n) (templateCols d k0) P)).2 hfirst
  have hcost2 :
      P.cost <=
        (List.replicate 2 Protocol.ActualBitSide.alice).length +
          (Nat.clog 2 (Params.q2 d) + Bcap d) := by
    unfold Byes at hcost
    simp
    omega
  have hbits :=
    actualBitListRaw_eq_restrict_of_terminal_budget
      (M4 d v) P (templateRows d n) (templateCols d k0)
      (List.replicate 2 Protocol.ActualBitSide.alice)
      (Nat.clog 2 (Params.q2 d) + Bcap d)
      (fun a _ b _ => hP a b) hcost2 hpat hhard hmemR hmemC
  have hbits2 :
      Protocol.actualBitListRaw 2 P (Sum.inl pc : R4 d n) ((k0, c3) : C4 d) =
        Protocol.actualBitListRaw 2
          (Protocol.restrict (templateRows d n) (templateCols d k0) P)
          (Sum.inl pc : R4 d n) ((k0, c3) : C4 d) := by
    simpa using hbits
  have hwlen :
      (Protocol.actualBitListRaw 2
        (Protocol.restrict (templateRows d n) (templateCols d k0) P)
        (Sum.inl pc : R4 d n) ((k0, c3) : C4 d)).length = 2 :=
    actualBitListRaw_length_of_firstKRowBitsOn hfirst hmemR hmemC
  have hambient :
      Protocol.actualPrefixCodeRaw 2 P (Sum.inl pc : R4 d n)
          ((k0, c3) : C4 d) =
        Protocol.prefixCodeRaw 2 P (Sum.inl pc : R4 d n) :=
    Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
      (Finset.univ : Finset (R4 d n)) (Finset.univ : Finset (C4 d)) 2 P
      hrow (Finset.mem_univ _) (Finset.mem_univ _)
  have hambient2 :=
    actualPrefixCodeRaw_eq_codeOfBitList_of_actualBitListRaw_eq
      P (Sum.inl pc : R4 d n) ((k0, c3) : C4 d) hbits2 hwlen
  have hrestr :
      Protocol.actualPrefixCodeRaw 2
          (Protocol.restrict (templateRows d n) (templateCols d k0) P)
          (Sum.inl pc : R4 d n) ((k0, c3) : C4 d) =
        Protocol.prefixCodeRaw 2
          (Protocol.restrict (templateRows d n) (templateCols d k0) P)
          (Sum.inl pc : R4 d n) :=
    Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
      (templateRows d n) (templateCols d k0) 2
      (Protocol.restrict (templateRows d n) (templateCols d k0) P)
      hfirst hmemR hmemC
  have hrestr2 :=
    actualPrefixCodeRaw_eq_codeOfBitList_of_actualBitListRaw_eq
      (Protocol.restrict (templateRows d n) (templateCols d k0) P)
      (Sum.inl pc : R4 d n) ((k0, c3) : C4 d) rfl hwlen
  rw [← hambient, hambient2, M4_slice_prefixCode_eq_restrict d P k0 pc,
    ← hrestr, hrestr2]

/-! ## The fiber-representative local duplicate expansion -/

noncomputable def rowRepFiber (d : Nat) {n : Nat}
    (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4)
    (alpha : Fin (Params.q2 d)) (B : Finset (Fin n))
    (rep : R1 d -> C2 d) :
    (M1PlusOuter d v alpha B × Fin 1) → R4 d n :=
  fun x =>
    match x.1 with
    | Sum.inl q => (Sum.inl (p, rep (q, x.2)) : R4 d n)
    | Sum.inr i => (Sum.inr i.val : R4 d n)

theorem M4_rowRepFiber_val (d : Nat) (h₂ : Params.t2 d ≤ Params.q2 d)
    (hq1 : 1 ≤ Params.q1 d) {n : Nat}
    (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4)
    (alpha : Fin (Params.q2 d)) (B : Finset (Fin n)) (S' : Finset (C1 d))
    (rep : R1 d -> C2 d)
    (hrep_eval : ∀ r, S2fam d (rep r) alpha = r)
    (x : M1PlusOuter d v alpha B × Fin 1) (γ : {γ // γ ∈ S'}) :
    M4 d v (rowRepFiber d v p alpha B rep x) (diagCopyCol d alpha γ.val) =
      HlocalAtSub d (S1fam d) S' (m1PlusCoordEnum d v alpha B)
        ((Fintype.equivFin (M1PlusOuter d v alpha B) x.1), x.2) γ := by
  have h := m1PlusBranchCoreSub_eq_stage d h₂ hq1 v p alpha B S' x γ
  rw [← h]
  unfold m1PlusBranchCoreSub rowRepFiber
  cases hx : x.1 with
  | inl q =>
      simp only [M4_diagonal_copy_apply, M2_apply]
      rw [hrep_eval (q, x.2), S2coordPreimage_spec d h₂ hq1 alpha (q, x.2)]
  | inr i =>
      rfl

theorem M4_duplicateExpansionContained_localRows_fiber
    (d : Nat) (h₂ : Params.t2 d ≤ Params.q2 d) (hq1 : 1 ≤ Params.q1 d)
    {n : Nat} (v : Fin n → Fin (Params.q2 d) → Bool) (p : Fin 4)
    (alpha : Fin (Params.q2 d)) (B : Finset (Fin n)) (T : Finset (C2 d))
    (Y : Finset (C4 d)) (hYsub : Y ⊆ diagCopySet d alpha)
    (rep : R1 d -> C2 d)
    (hrep_mem : ∀ r, rep r ∈ T)
    (hrep_eval : ∀ r, S2fam d (rep r) alpha = r) :
    DuplicateExpansionContained
      (M4 d v)
      (localRows d p T B)
      Y
      (HlocalAtSub d (S1fam d) (SPrime d alpha Y)
        (m1PlusCoordEnum d v alpha B)) := by
  classical
  set e := Fintype.equivFin (M1PlusOuter d v alpha B)
  have hpre : ∀ b : {b // b ∈ Y}, ∃ γ : C1 d, diagCopyCol d alpha γ = b.val := by
    intro b
    have hb := hYsub b.property
    unfold diagCopySet at hb
    rw [Finset.mem_image] at hb
    rcases hb with ⟨γ, -, hγ⟩
    exact ⟨γ, hγ⟩
  have hrowmem : ∀ x : M1PlusOuter d v alpha B × Fin 1,
      rowRepFiber d v p alpha B rep x ∈ localRows d p T B := by
    intro x
    unfold rowRepFiber localRows
    cases hx : x.1 with
    | inl q =>
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨_, hrep_mem (q, x.2), rfl⟩)
    | inr i =>
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr
            ⟨i.val, transversalAt_subset v alpha B i.property, rfl⟩)
  refine ⟨(Finset.univ : Finset (M1PlusOuter d v alpha B × Fin 1)).image
            (rowRepFiber d v p alpha B rep), ?_, Y, Finset.Subset.refl _,
          fun a => (e (Classical.choose (Finset.mem_image.mp a.property)).1,
                    (Classical.choose (Finset.mem_image.mp a.property)).2),
          fun b => ⟨Classical.choose (hpre b), ?_⟩,
          ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨x, -, rfl⟩
    exact hrowmem x
  · unfold SPrime diagPullback
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by
      rw [Classical.choose_spec (hpre b)]
      exact b.property⟩
  · rintro ⟨oIdx, r0⟩
    set outer := e.symm oIdx with houter
    refine ⟨⟨rowRepFiber d v p alpha B rep (outer, r0), Finset.mem_image.mpr
              ⟨(outer, r0), Finset.mem_univ _, rfl⟩⟩, ?_⟩
    set a : {a // a ∈ (Finset.univ : Finset (M1PlusOuter d v alpha B × Fin 1)).image
              (rowRepFiber d v p alpha B rep)} :=
      ⟨rowRepFiber d v p alpha B rep (outer, r0),
        Finset.mem_image.mpr ⟨(outer, r0), Finset.mem_univ _, rfl⟩⟩ with ha
    have hchoose := Classical.choose_spec (Finset.mem_image.mp a.property)
    set x0 := Classical.choose (Finset.mem_image.mp a.property) with hx0
    have hval : rowRepFiber d v p alpha B rep x0 =
        rowRepFiber d v p alpha B rep (outer, r0) := hchoose.2
    have hxo : x0 = (outer, r0) := by
      have hr0 : x0.2 = r0 := Subsingleton.elim _ _
      rcases ho : outer with q | i
      · have hrhs : rowRepFiber d v p alpha B rep (outer, r0) =
            (Sum.inl (p, rep (q, r0)) : R4 d n) := by
          simp [rowRepFiber, ho]
        rw [hrhs] at hval
        cases hx0o : x0.1 with
        | inl q' =>
            have hlhs : rowRepFiber d v p alpha B rep x0 =
                (Sum.inl (p, rep (q', x0.2)) : R4 d n) := by
              simp [rowRepFiber, hx0o]
            rw [hlhs] at hval
            have hqq : rep (q', x0.2) = rep (q, r0) := by
              have := Sum.inl.inj hval
              exact (Prod.ext_iff.mp this).2
            have hs1 := hrep_eval (q', x0.2)
            have hs2 := hrep_eval (q, r0)
            rw [hqq] at hs1
            rw [hs2] at hs1
            have hqeq : (q', x0.2) = (q, r0) := hs1.symm
            apply Prod.ext
            · rw [hx0o]
              exact congrArg Sum.inl (Prod.ext_iff.mp hqeq).1
            · exact hr0
        | inr i =>
            have hlhs : rowRepFiber d v p alpha B rep x0 =
                (Sum.inr i.val : R4 d n) := by simp [rowRepFiber, hx0o]
            rw [hlhs] at hval
            exact absurd hval (by simp)
      · have hrhs : rowRepFiber d v p alpha B rep (outer, r0) =
            (Sum.inr i.val : R4 d n) := by simp [rowRepFiber, ho]
        rw [hrhs] at hval
        cases hx0o : x0.1 with
        | inl q' =>
            have hlhs : rowRepFiber d v p alpha B rep x0 =
                (Sum.inl (p, rep (q', x0.2)) : R4 d n) := by
              simp [rowRepFiber, hx0o]
            rw [hlhs] at hval
            exact absurd hval (by simp)
        | inr j =>
            have hlhs : rowRepFiber d v p alpha B rep x0 =
                (Sum.inr j.val : R4 d n) := by simp [rowRepFiber, hx0o]
            rw [hlhs] at hval
            have hij : j.val = i.val := Sum.inr.inj hval
            apply Prod.ext
            · rw [hx0o]
              exact congrArg Sum.inr (Subtype.ext hij)
            · exact hr0
    show (e x0.1, x0.2) = (oIdx, r0)
    rw [hxo]
    simp only [houter, Equiv.apply_symm_apply]
  · rintro ⟨γ, hγ⟩
    unfold SPrime diagPullback at hγ
    rw [Finset.mem_filter] at hγ
    refine ⟨⟨diagCopyCol d alpha γ, hγ.2⟩, ?_⟩
    apply Subtype.ext
    exact diagCopyCol_injective d alpha
      (Classical.choose_spec (hpre ⟨diagCopyCol d alpha γ, hγ.2⟩))
  · intro a b
    have hchoose := Classical.choose_spec (Finset.mem_image.mp a.property)
    set x0 := Classical.choose (Finset.mem_image.mp a.property) with hx0
    have haval : a.val = rowRepFiber d v p alpha B rep x0 := hchoose.2.symm
    have hbval : b.val = diagCopyCol d alpha (Classical.choose (hpre b)) :=
      (Classical.choose_spec (hpre b)).symm
    rw [haval, hbval]
    exact M4_rowRepFiber_val d h₂ hq1 v p alpha B (SPrime d alpha Y) rep
      hrep_eval x0
      ⟨Classical.choose (hpre b), by
        unfold SPrime diagPullback
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by
          rw [Classical.choose_spec (hpre b)]
          exact b.property⟩⟩


-- CLAIM-BEGIN lem:MFourNoWasteLift
/-! ## THE THEOREM: `M4_no_waste_lift` (paper `lem:MFourNoWasteLift`),
with both Phase-A and Phase-B certificates discharged.  Hypothesis list =
the standard analytic bundle of `M3_fuzzy_leaves` plus the claim's
`hd`/`hchk`/`hactive`; NO protocol-side certificate hypotheses remain. -/

theorem M4_no_waste_lift
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
    {n : Nat} (v : Fin n -> Fin (Params.q2 d) -> Bool)
    (hactive : ∀ alpha : Fin (Params.q2 d), (activeSet v alpha).card <= 4)
    (P : Protocol (R4 d n) (C4 d) Bool)
    (hP : P.Computes (M4 d v))
    (hcost : P.cost <= Byes d)
    (k0 : Fin (2 ^ 5)) :
    ∃ B : Fin 4 -> Finset (Fin n),
      IsPartition4 B ∧
      ∃ binBr : ∀ p : Fin 4, Protocol.BranchAt P (M4 d v) 2,
        Function.Bijective (fun p : Fin 4 => (binBr p).transcript) ∧
        (∀ p : Fin 4,
          (binBr p).sideTrace =
            [Protocol.ActualBitSide.alice, Protocol.ActualBitSide.alice]) ∧
        (∀ p : Fin 4, ∀ y : C4 d, y ∈ (binBr p).cols) ∧
        (∀ p i, (Sum.inr i : R4 d n) ∈ (binBr p).rows ↔ i ∈ B p) ∧
        (∀ p, (binBr p).residual.cost <=
          Nat.clog 2 (Params.q2 d) + Bcap d) ∧
        ∀ p : Fin 4, ∀ alpha : Fin (Params.q2 d),
          ∃ br : Protocol.BranchAt P (M4 d v)
              (2 + Nat.clog 2 (Params.q2 d)),
            Protocol.BranchExtends (binBr p) br ∧
            br.sideTrace =
              (binBr p).sideTrace ++
                List.replicate (Nat.clog 2 (Params.q2 d))
                  Protocol.ActualBitSide.bob ∧
            (∀ i : Fin n,
              (Sum.inr i : R4 d n) ∈ br.rows ↔ i ∈ B p) ∧
            M4LocalBranch d v P B p alpha br :=
-- CLAIM-END lem:MFourNoWasteLift
  by
  classical
  have hlog64 : 64 <= Nat.log 2 d := by omega
  have hlog256 : 256 <= Nat.log 2 d := by omega
  have h₂ : Params.t2 d ≤ Params.q2 d := hchk.t2_le_q2
  have hq1 : 1 ≤ Params.q1 d := hchk.one_le_q1
  -- ===== the k0 template-slice separation =====
  have hsep : M3SeparationConclusion d (templateSliceProtocol d P k0) :=
    templateSlice_separation d hpow hlog hchk hrobM2 hm0_le hr2pow
      hrow_threshold hraw hprime hy_three_fifths v P hP hcost k0
  have hgap : 4 * M3_rowLoss d < Fintype.card (C2 d) :=
    M3_stage3_gap_public d hlog hchk
  let hsurj :=
    M3Bin_alphaOfCode_surj_on_Q d (templateSliceProtocol d P k0)
      hsep.dominant_bins hgap
  let code : Fin 4 -> Fin (2 ^ 2) := fun p =>
    M3_codeOfBin d (templateSliceProtocol d P k0) hsep.dominant_bins hsurj p
  have hcode : Function.Bijective code :=
    M3_codeOfBin_bijective d (templateSliceProtocol d P k0)
      hsep.dominant_bins hsurj
  let S : Fin 4 -> Finset (C2 d) := fun p =>
    M3_binSurvivors d (templateSliceProtocol d P k0) hsep.dominant_bins
      hsurj p
  have hSdense : ∀ p,
      (1 - 8 * Params.h2 d) * (Fintype.card (C2 d) : Real) <=
        ((S p).card : Real) := fun p =>
    M3_binSurvivors_dense d (templateSliceProtocol d P k0) hchk
      hsep.dominant_bins hsurj hgap p
  have hSne : ∀ p, (S p).Nonempty := fun p =>
    M4_dense_C2_nonempty d hchk hsigma0 (S p) (hSdense p)
  -- ===== Phase-A certificates =====
  have hfirst :=
    templateSlice_first_row_bits_to_restrict d P k0 hsep.first_row_bits
  have hcover :=
    M4_template_restrict_coverage d hchk P k0 hfirst hsep.dominant_bins hgap
  have hhard :=
    M4_phaseA_terminalHard_dense d hpow hlog hchk hm0_le hr2pow hp1 hp2
      hxseed_le_one hrow_threshold hseed_bridge hy_le_one hrowTerm hcolTerm
      hresidual_density hqcast hsigma0 hsigma1 hres_dense hxseed_le_inv_r
      hseed_bridge_dense hT1 hgap_dense hraw hprime hy_three_fifths
      v P k0 hfirst hsep.dominant_bins hsurj hgap
  have hrow :=
    M4_ambient_first_two_row_bits_of_phaseA_certificates
      d v P hP hcost k0 hfirst hcover hhard
  -- ===== code alignment: slice survivors live in the ambient bins =====
  have hcodeAmb : ∀ pc : R3 d,
      Protocol.prefixCodeRaw 2 P (Sum.inl pc : R4 d n) =
        Protocol.prefixCodeRaw 2 (templateSliceProtocol d P k0) pc :=
    fun pc =>
      M4_ambient_prefixCode_eq_slice d hchk v P hP hcost k0 hfirst hhard
        hrow pc
  have hsurvAmb : ∀ p, ∀ c ∈ S p,
      (Sum.inl (p, c) : R4 d n) ∈ Protocol.rowPrefixRows 2 P (code p) := by
    intro p c hc
    rw [Protocol.rowPrefixRows, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hcodeAmb (p, c)]
    exact
      M3_binSurvivors_mem_code d (templateSliceProtocol d P k0)
        hsep.dominant_bins hsurj p c hc
  have hrows : ∀ p, (Protocol.rowPrefixRows 2 P (code p)).Nonempty := by
    intro p
    obtain ⟨c, hc⟩ := hSne p
    exact ⟨Sum.inl (p, c), hsurvAmb p c hc⟩
  -- ===== the ambient bin branches =====
  let hC4 : (Finset.univ : Finset (C4 d)).Nonempty :=
    C4_univ_nonempty d hchk k0
  let binBr : ∀ p : Fin 4, Protocol.BranchAt P (M4 d v) 2 :=
    ambientBinBranch d v P code hrow hP hrows hC4
  have hbinRows : ∀ p, ∀ c, c ∈ S p ->
      (Sum.inl (p, c) : R4 d n) ∈ (binBr p).rows := by
    intro p c hc
    have hre : (binBr p).rows = Protocol.rowPrefixRows 2 P (code p) := rfl
    rw [hre]
    exact hsurvAmb p c hc
  have hbinColsUniv : ∀ p, ∀ y : C4 d, y ∈ (binBr p).cols := fun p y =>
    ambientBinBranch_cols_univ d v P code hrow hP hrows hC4 p y
  have hbudget : ∀ p,
      (binBr p).residual.cost <= Nat.clog 2 (Params.q2 d) + Bcap d :=
    fun p =>
      ambientBinBranch_residual_budget d v P code hrow hP hcost hrows hC4 p
  have hM2sum : D (M2 d) = Nat.clog 2 (Params.q2 d) + Bcap d :=
    M4_D_M2_eq_clog_add_Bcap d hpow hlog hchk hm0_le hr2pow
      hrow_threshold hraw hprime hy_three_fifths
  -- ===== the Stage-4 dense reindex + Stage-2 alpha data per bin =====
  have hdiag_mem : ∀ p, ∀ a : M2DenseRows d,
      diagCopyCol d (Fin.cast hqcast a.val.1) a.val.2 ∈ (binBr p).cols :=
    fun p a => hbinColsUniv p _
  have hfibcov : ∀ p alpha,
      (S p).image (fun c : C2 d => S2fam d c alpha) =
        (Finset.univ : Finset (R1 d)) := fun p alpha =>
    M3_C2_fiber_cover_of_dense d hchk (S p) (hSdense p) alpha
  have hSdenseL2 : ∀ p,
      (1 - 8 * Params.h2 d) * (L2 d : Real) <= ((S p).card : Real) := by
    intro p
    have hcardC2 : (Fintype.card (C2 d) : Real) = (L2 d : Real) := by
      simp [C2]
    rw [← hcardC2]
    exact hSdense p
  let htr : ∀ p,
      M4BinDenseReindex d v P binBr p (S p)
        (M4_denseSurvivorRows d v P binBr p (S p) (hbinRows p))
        (M4_denseDiagCols d v P binBr p hqcast (hdiag_mem p)) hqcast :=
    fun p =>
      M4_binDenseReindex_of_memberships d v P binBr p (S p) hqcast
        (hbinRows p) (hdiag_mem p)
  let ad : ∀ p,
      M2SeparationTransposeDenseRowsAlphaData d hqcast (S p)
        (M4_bin_dense_protocol d v P binBr p (S p)
          (M4_denseSurvivorRows d v P binBr p (S p) (hbinRows p))
          (M4_denseDiagCols d v P binBr p hqcast (hdiag_mem p))
          hqcast (htr p)) :=
    fun p =>
      Classical.choice
        (M2_separation_transpose_dense_rows_alpha d hpow hlog256 hchk
          hm0_le hr2pow hp1 hp2 hxseed_le_one hrow_threshold hseed_bridge
          hy_le_one hrowTerm hcolTerm hresidual_density hqcast
          (1 - 8 * Params.h2 d) hsigma0 hsigma1 (le_refl _)
          hres_dense hxseed_le_inv_r hseed_bridge_dense M4_delta_sep hT1
          hgap_dense (S p) (hSdenseL2 p) _
          (M4_bin_dense_protocol_computes d v P binBr p (S p)
            (M4_denseSurvivorRows d v P binBr p (S p) (hbinRows p))
            (M4_denseDiagCols d v P binBr p hqcast (hdiag_mem p))
            hqcast (htr p))
          (M4_bin_dense_protocol_cost_le d v P binBr p (S p)
            (M4_denseSurvivorRows d v P binBr p (S p) (hbinRows p))
            (M4_denseDiagCols d v P binBr p hqcast (hdiag_mem p))
            hqcast (hbudget p) hM2sum (htr p)))
  have hdata : ∀ p,
      Stage3StopData
        (subgame (M4 d v) (binBr p).rows (binBr p).cols)
        (binBr p).residual
        (M4_denseSurvivorRows d v P binBr p (S p) (hbinRows p))
        (M4_denseDiagCols d v P binBr p hqcast (hdiag_mem p))
        (Nat.clog 2 (Params.q2 d)) (Bcap d) :=
    fun p =>
      M4_stage4StopData_for_dense_bin d hpow hlog64 hchk v P binBr p (S p)
        hqcast (hbinRows p) (hdiag_mem p) (hSne p) (hfibcov p) (ad p)
  have hcol : ∀ p,
      Protocol.FirstKColBitsOn
        (Finset.univ : Finset {a // a ∈ (binBr p).rows})
        (Finset.univ : Finset {b // b ∈ (binBr p).cols})
        (Nat.clog 2 (Params.q2 d)) (binBr p).residual :=
    fun p =>
      Stage3StopData.ambient_col
        (subgame (M4 d v) (binBr p).rows (binBr p).cols)
        (binBr p).residual
        (M4_denseSurvivorRows d v P binBr p (S p) (hbinRows p))
        (M4_denseDiagCols d v P binBr p hqcast (hdiag_mem p))
        (Nat.clog 2 (Params.q2 d)) (Bcap d)
        (binBr p).residual_computes (hbudget p) (hdata p)
  -- ===== the Bob dimension codes =====
  have hYne : ∀ p alpha, ((ad p).Yalpha alpha).Nonempty := fun p alpha =>
    M1_dense_columns_nonempty d hpow hlog64 hchk _
      ((ad p).Yalpha_dense alpha)
  let gammaRep : ∀ (_ : Fin 4) (_ : Fin (Params.q2 d)), C1 d :=
    fun p alpha => Classical.choose (hYne p alpha)
  have gammaRep_mem : ∀ p alpha,
      gammaRep p alpha ∈ (ad p).Yalpha alpha := fun p alpha =>
    Classical.choose_spec (hYne p alpha)
  let diagSub : ∀ (p : Fin 4) (alpha : Fin (Params.q2 d)) (gamma : C1 d),
      {b // b ∈ (binBr p).cols} :=
    fun p alpha gamma => ⟨diagCopyCol d alpha gamma, hbinColsUniv p _⟩
  let codeOfAlpha :
      Fin 4 -> Fin (Params.q2 d) -> Fin (2 ^ Nat.clog 2 (Params.q2 d)) :=
    fun p alpha =>
      Protocol.prefixCodeRaw (Nat.clog 2 (Params.q2 d))
        (Protocol.swap (binBr p).residual)
        (diagSub p alpha (gammaRep p alpha))
  have hcols : ∀ p alpha,
      (Protocol.colPrefixCols (Nat.clog 2 (Params.q2 d))
        (binBr p).residual (codeOfAlpha p alpha)).Nonempty := by
    intro p alpha
    refine ⟨diagSub p alpha (gammaRep p alpha), ?_⟩
    simp [Protocol.colPrefixCols, Protocol.rowPrefixRows, codeOfAlpha]
  have hdiagPrefix : ∀ p alpha gamma, gamma ∈ (ad p).Yalpha alpha ->
      diagSub p alpha gamma ∈
        Protocol.colPrefixCols (Nat.clog 2 (Params.q2 d))
          (binBr p).residual (codeOfAlpha p alpha) := by
    intro p alpha gamma hgamma
    rw [Protocol.colPrefixCols, Protocol.rowPrefixRows, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hprefix :=
      M4_raw_prefix_eq_of_dense_Yalpha d v P binBr p (S p)
        (M4_denseSurvivorRows d v P binBr p (S p) (hbinRows p))
        (M4_denseDiagCols d v P binBr p hqcast (hdiag_mem p))
        hqcast (htr p) (ad p) (hcol p) (hSne p) hgamma
        (gammaRep_mem p alpha)
    simpa [codeOfAlpha, diagSub, htr,
      M4_binDenseReindex_of_memberships, equivOfInjectiveImage,
      M4_diagColBranch] using hprefix
  -- ===== hlocal: the Stage-1 local branch content per (p, alpha) =====
  have hlocal : ∀ p alpha,
      M4LocalBranch d v P (vectorPrefixBin d P code) p alpha
        (Protocol.BranchAt.compose_colPrefix (binBr p) (codeOfAlpha p alpha)
          (hcol p) (hcols p alpha)) := by
    intro p alpha
    have hrowsEq :
        (Protocol.BranchAt.compose_colPrefix (binBr p) (codeOfAlpha p alpha)
          (hcol p) (hcols p alpha)).rows = (binBr p).rows :=
      compose_colPrefix_rows_eq (binBr p) (codeOfAlpha p alpha)
        (hcol p) (hcols p alpha)
    -- the dense diagonal column set
    obtain ⟨Y, hYsub, hYdenseY, hYpull⟩ :=
      M4_dense_Y_of_C1 d alpha ((ad p).Yalpha alpha)
        (by simpa [C1] using (ad p).Yalpha_dense alpha)
    have hYmem : ∀ gamma, gamma ∈ (ad p).Yalpha alpha ->
        diagCopyCol d alpha gamma ∈
          (Protocol.BranchAt.compose_colPrefix (binBr p)
            (codeOfAlpha p alpha) (hcol p) (hcols p alpha)).cols := by
      intro gamma hgamma
      unfold Protocol.BranchAt.compose_colPrefix
      rw [show (Protocol.BranchAt.compose (binBr p)
          (Protocol.mkBranchAt_of_colPrefix (binBr p).residual
            (subgame (M4 d v) (binBr p).rows (binBr p).cols)
            (Nat.clog 2 (Params.q2 d)) (codeOfAlpha p alpha)
            (hcol p) (binBr p).residual_computes _
            (hcols p alpha))).cols =
          Protocol.BranchAt.liftCols (binBr p)
            (Protocol.mkBranchAt_of_colPrefix (binBr p).residual
              (subgame (M4 d v) (binBr p).rows (binBr p).cols)
              (Nat.clog 2 (Params.q2 d)) (codeOfAlpha p alpha)
              (hcol p) (binBr p).residual_computes _
              (hcols p alpha)) from rfl]
      rw [Protocol.BranchAt.mem_liftCols]
      refine ⟨hbinColsUniv p _, ?_⟩
      show (⟨diagCopyCol d alpha gamma, hbinColsUniv p _⟩ :
          {b // b ∈ (binBr p).cols}) ∈
        (Protocol.mkBranchAt_of_colPrefix (binBr p).residual
          (subgame (M4 d v) (binBr p).rows (binBr p).cols)
          (Nat.clog 2 (Params.q2 d)) (codeOfAlpha p alpha)
          (hcol p) (binBr p).residual_computes _
          (hcols p alpha)).cols
      unfold Protocol.mkBranchAt_of_colPrefix Protocol.branchAt_of_swap
      exact hdiagPrefix p alpha gamma hgamma
    have hYbrCols : Y ⊆
        (Protocol.BranchAt.compose_colPrefix (binBr p)
          (codeOfAlpha p alpha) (hcol p) (hcols p alpha)).cols := by
      intro y hy
      have hy' := hYsub hy
      unfold diagCopySet at hy'
      rw [Finset.mem_image] at hy'
      rcases hy' with ⟨gamma, -, rfl⟩
      have hgammaY : gamma ∈ (ad p).Yalpha alpha := by
        rw [← hYpull]
        unfold diagPullback
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hy⟩
      exact hYmem gamma hgammaY
    -- the fiber-representative duplicate expansion
    have hcontained :=
      M4_duplicateExpansionContained_localRows_fiber d h₂ hq1 v p alpha
        (vectorPrefixBin d P code p) (S p) Y hYsub
        (fun r => M3_fiber_cRep d (S p) alpha (hfibcov p alpha) r)
        (fun r => M3_fiber_cRep_mem d (S p) alpha (hfibcov p alpha) r)
        (fun r => M3_fiber_cRep_eval d (S p) alpha (hfibcov p alpha) r)
    have hlocalRowsSub :
        localRows d p (S p) (vectorPrefixBin d P code p) ⊆
          (Protocol.BranchAt.compose_colPrefix (binBr p)
            (codeOfAlpha p alpha) (hcol p) (hcols p alpha)).rows := by
      intro a ha
      unfold localRows at ha
      rcases Finset.mem_union.mp ha with h | h
      · rcases Finset.mem_image.mp h with ⟨c, hc, rfl⟩
        rw [hrowsEq]
        exact hbinRows p c hc
      · rcases Finset.mem_image.mp h with ⟨i, hi, rfl⟩
        rw [hrowsEq]
        exact
          (ambientBinBranch_vector_rows d v P code hrow hP hrows hC4 p i).2 hi
    refine ⟨?_, ?_, ?_⟩
    · intro i
      rw [hrowsEq]
      exact ambientBinBranch_vector_rows d v P code hrow hP hrows hC4 p i
    · have hbits :=
        (Protocol.BranchAt.compose_colPrefix (binBr p) (codeOfAlpha p alpha)
          (hcol p) (hcols p alpha)).cost_after_actualBits
      unfold Byes at hcost
      omega
    · refine ⟨Y, hYbrCols, hYsub, hYdenseY, ?_⟩
      refine ⟨S p, ?_, ?_, ?_⟩
      · intro c hc
        rw [hrowsEq]
        exact hbinRows p c hc
      · intro r
        have hmem : r ∈ (S p).image (fun c : C2 d => S2fam d c alpha) := by
          rw [hfibcov p alpha]
          exact Finset.mem_univ r
        rcases Finset.mem_image.mp hmem with ⟨c, hc, hceq⟩
        exact ⟨c, hc, hceq⟩
      · refine
          ⟨Fintype.card (M1PlusOuter d v alpha (vectorPrefixBin d P code p)),
            m1PlusCoordEnum d v alpha (vectorPrefixBin d P code p),
            m1PlusCoordEnum_injective d v alpha _ (hactive alpha),
            m1PlusCoordEnum_image_eq_localCoordSet d v alpha _,
            hcontained, ?_⟩
        exact
          M4_duplicateExpansionComputedByResidual_of_branch d v P hP
            (Protocol.BranchAt.compose_colPrefix (binBr p)
              (codeOfAlpha p alpha) (hcol p) (hcols p alpha))
            (localRows d p (S p) (vectorPrefixBin d P code p)) Y
            (HlocalAtSub d (S1fam d) (SPrime d alpha Y)
              (m1PlusCoordEnum d v alpha (vectorPrefixBin d P code p)))
            hlocalRowsSub hYbrCols hcontained
  -- ===== final assembly =====
  exact
    M4_no_waste_lift_from_certificates d hchk v P hP hcost k0 code hcode
      hrow hrows codeOfAlpha hcol hcols hlocal

end NPCC
