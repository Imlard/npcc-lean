import NPCC.Control

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
Historical construction note for the current `NPCC/NoWaste.lean` module.

The file is intentionally standalone over `NPCC.Control`. It adds the mixed
side-pattern layer and the branch/terminal packaging needed by the frontier
no-waste argument. Intermediate `..._statement` definitions expose the proof
specification without adding assumptions; the ambient synchronization theorem
and its row-only and column-only corollaries are proved at the end of the file.
-/

namespace NPCC

open Workspace.Types.Protocol
open Workspace.Types.CommComplexity

namespace Protocol

-- CLAIM-BEGIN aux:nowaste-core

variable {A B Z : Type*}

/-- Mixed side-pattern predicate on surviving branches.

At an empty current rectangle the predicate is vacuous, matching
`FirstKRowBitsOn`.  At a live node, the next protocol node must query the side
specified by the head of the pattern; the current rectangle is then threaded
through the corresponding child rectangles.
-/
def FirstPatternOn :
    Finset A -> Finset B -> List ActualBitSide -> Protocol A B Z -> Prop
  | _, _, [], _ => True
  | R, C, _ :: _, Protocol.leaf _ => R = (∅ : Finset A) ∨ C = (∅ : Finset B)
  | R, C, ActualBitSide.alice :: pat, Protocol.aNode a l r =>
      FirstPatternOn (R.filter fun x => a x = false) C pat l ∧
      FirstPatternOn (R.filter fun x => a x = true) C pat r
  | R, C, ActualBitSide.bob :: pat, Protocol.bNode b l r =>
      FirstPatternOn R (C.filter fun y => b y = false) pat l ∧
      FirstPatternOn R (C.filter fun y => b y = true) pat r
  | R, C, ActualBitSide.alice :: _, Protocol.bNode _ _ _ =>
      R = (∅ : Finset A) ∨ C = (∅ : Finset B)
  | R, C, ActualBitSide.bob :: _, Protocol.aNode _ _ _ =>
      R = (∅ : Finset A) ∨ C = (∅ : Finset B)

theorem firstPatternOn_of_left_empty
    (C : Finset B) (pat : List ActualBitSide) (P : Protocol A B Z)
    {R : Finset A} (hR : R = (∅ : Finset A)) :
    FirstPatternOn R C pat P := by
  induction pat generalizing R C P with
  | nil =>
      trivial
  | cons side pat ih =>
      cases P with
      | leaf z =>
          exact Or.inl hR
      | aNode a l r =>
          cases side with
          | alice =>
              refine ⟨?_, ?_⟩
              · exact ih _ _ (by rw [hR]; simp)
              · exact ih _ _ (by rw [hR]; simp)
          | bob =>
              exact Or.inl hR
      | bNode b l r =>
          cases side with
          | alice =>
              exact Or.inl hR
          | bob =>
              refine ⟨?_, ?_⟩
              · exact ih _ _ hR
              · exact ih _ _ hR

theorem firstPatternOn_of_right_empty
    (R : Finset A) (pat : List ActualBitSide) (P : Protocol A B Z)
    {C : Finset B} (hC : C = (∅ : Finset B)) :
    FirstPatternOn R C pat P := by
  induction pat generalizing R C P with
  | nil =>
      trivial
  | cons side pat ih =>
      cases P with
      | leaf z =>
          exact Or.inr hC
      | aNode a l r =>
          cases side with
          | alice =>
              refine ⟨?_, ?_⟩
              · exact ih _ _ hC
              · exact ih _ _ hC
          | bob =>
              exact Or.inr hC
      | bNode b l r =>
          cases side with
          | alice =>
              exact Or.inr hC
          | bob =>
              refine ⟨?_, ?_⟩
              · exact ih _ _ (by rw [hC]; simp)
              · exact ih _ _ (by rw [hC]; simp)

theorem firstPattern_replicate_alice_iff
    (R : Finset A) (C : Finset B) (k : Nat) (P : Protocol A B Z) :
    FirstPatternOn R C (List.replicate k ActualBitSide.alice) P ↔
      FirstKRowBitsOn R C k P := by
  induction k generalizing R C P with
  | zero =>
      cases P <;> simp [List.replicate, Protocol.FirstPatternOn,
        Protocol.FirstKRowBitsOn]
  | succ k ih =>
      cases P with
      | leaf z =>
          simp [List.replicate, Protocol.FirstPatternOn,
            Protocol.FirstKRowBitsOn]
      | aNode a l r =>
          simp [List.replicate, Protocol.FirstPatternOn,
            Protocol.FirstKRowBitsOn, ih]
      | bNode b l r =>
          simp [List.replicate, Protocol.FirstPatternOn,
            Protocol.FirstKRowBitsOn]

theorem firstPattern_replicate_bob_iff
    (R : Finset A) (C : Finset B) (k : Nat) (P : Protocol A B Z) :
    FirstPatternOn R C (List.replicate k ActualBitSide.bob) P ↔
      FirstKColBitsOn R C k P := by
  induction k generalizing R C P with
  | zero =>
      cases P <;> simp [List.replicate, Protocol.FirstPatternOn,
        Protocol.FirstKColBitsOn, Protocol.FirstKRowBitsOn, Protocol.swap]
  | succ k ih =>
      cases P with
      | leaf z =>
          simp [List.replicate, Protocol.FirstPatternOn,
            Protocol.FirstKColBitsOn, Protocol.FirstKRowBitsOn, Protocol.swap,
            or_comm]
      | aNode a l r =>
          simp [List.replicate, Protocol.FirstPatternOn,
            Protocol.FirstKColBitsOn, Protocol.FirstKRowBitsOn, Protocol.swap,
            or_comm]
      | bNode b l r =>
          simp [List.replicate, Protocol.FirstPatternOn,
            Protocol.FirstKColBitsOn, Protocol.FirstKRowBitsOn, Protocol.swap,
            ih]

namespace FirstPatternOn

theorem take
    {R : Finset A} {C : Finset B} {pre suffix : List ActualBitSide}
    {P : Protocol A B Z} :
    FirstPatternOn R C (pre ++ suffix) P ->
      FirstPatternOn R C pre P := by
  induction pre generalizing R C P with
  | nil =>
      intro _
      trivial
  | cons side tail ih =>
      intro h
      cases P with
      | leaf z =>
          cases side <;> simpa [Protocol.FirstPatternOn] using h
      | aNode a l r =>
          cases side with
          | alice =>
              obtain ⟨hl, hr⟩ := h
              exact ⟨ih hl, ih hr⟩
          | bob =>
              simpa [Protocol.FirstPatternOn] using h
      | bNode b l r =>
          cases side with
          | alice =>
              simpa [Protocol.FirstPatternOn] using h
          | bob =>
              obtain ⟨hl, hr⟩ := h
              exact ⟨ih hl, ih hr⟩

theorem drop_false_of_cons_alice_aNode
    {R : Finset A} {C : Finset B} {pat : List ActualBitSide}
    {q : A -> Bool} {l r : Protocol A B Z}
    (h : FirstPatternOn R C (ActualBitSide.alice :: pat)
      (Protocol.aNode q l r)) :
    FirstPatternOn (R.filter fun x => q x = false) C pat l :=
  h.1

theorem drop_true_of_cons_alice_aNode
    {R : Finset A} {C : Finset B} {pat : List ActualBitSide}
    {q : A -> Bool} {l r : Protocol A B Z}
    (h : FirstPatternOn R C (ActualBitSide.alice :: pat)
      (Protocol.aNode q l r)) :
    FirstPatternOn (R.filter fun x => q x = true) C pat r :=
  h.2

theorem drop_false_of_cons_bob_bNode
    {R : Finset A} {C : Finset B} {pat : List ActualBitSide}
    {q : B -> Bool} {l r : Protocol A B Z}
    (h : FirstPatternOn R C (ActualBitSide.bob :: pat)
      (Protocol.bNode q l r)) :
    FirstPatternOn R (C.filter fun y => q y = false) pat l :=
  h.1

theorem drop_true_of_cons_bob_bNode
    {R : Finset A} {C : Finset B} {pat : List ActualBitSide}
    {q : B -> Bool} {l r : Protocol A B Z}
    (h : FirstPatternOn R C (ActualBitSide.bob :: pat)
      (Protocol.bNode q l r)) :
    FirstPatternOn R (C.filter fun y => q y = true) pat r :=
  h.2

end FirstPatternOn

/-- Boolean transcript as a list, parallel to `actualPrefixCodeRaw`. -/
def actualBitListRaw :
    (k : Nat) -> Protocol A B Z -> A -> B -> List Bool
  | 0, _, _, _ => []
  | _ + 1, Protocol.leaf _, _, _ => []
  | k + 1, Protocol.aNode q l r, a, b =>
      q a :: actualBitListRaw k (if q a then r else l) a b
  | k + 1, Protocol.bNode q l r, a, b =>
      q b :: actualBitListRaw k (if q b then r else l) a b

theorem actualBitListRaw_take
    {k n : Nat} (hkn : k <= n) (P : Protocol A B Z) (a : A) (b : B) :
    (actualBitListRaw n P a b).take k = actualBitListRaw k P a b := by
  induction k generalizing n P with
  | zero =>
      simp [actualBitListRaw]
  | succ k ih =>
      cases n with
      | zero =>
          omega
      | succ n =>
          cases P with
          | leaf z =>
              simp [actualBitListRaw]
          | aNode q l r =>
              by_cases hq : q a
              · simp [actualBitListRaw, hq, ih (Nat.succ_le_succ_iff.mp hkn)]
              · simp [actualBitListRaw, hq, ih (Nat.succ_le_succ_iff.mp hkn)]
          | bNode q l r =>
              by_cases hq : q b
              · simp [actualBitListRaw, hq, ih (Nat.succ_le_succ_iff.mp hkn)]
              · simp [actualBitListRaw, hq, ih (Nat.succ_le_succ_iff.mp hkn)]

theorem actualBitListRaw_restrictSub
    (R : Finset A) (C : Finset B) (P : Protocol A B Z)
    (a : {a // a ∈ R}) (b : {b // b ∈ C}) (k : Nat) :
    actualBitListRaw k (Protocol.restrictSub R C P) a b =
      actualBitListRaw k P a.val b.val := by
  induction k generalizing P with
  | zero =>
      rfl
  | succ k ih =>
      cases P with
      | leaf z =>
          rfl
      | aNode q l r =>
          by_cases hq : q a.val
          · simp [actualBitListRaw, Protocol.restrictSub, hq, ih]
          · simp [actualBitListRaw, Protocol.restrictSub, hq, ih]
      | bNode q l r =>
          by_cases hq : q b.val
          · simp [actualBitListRaw, Protocol.restrictSub, hq, ih]
          · simp [actualBitListRaw, Protocol.restrictSub, hq, ih]

def BranchFiberNonempty
    (R : Finset A) (C : Finset B) (P : Protocol A B Z)
    (w : List Bool) : Prop :=
  ∃ a, a ∈ R ∧ ∃ b, b ∈ C ∧ actualBitListRaw w.length P a b = w

def extendBitsTo (w : List Bool) (m : Nat) : List Bool :=
  w ++ List.replicate (m - w.length) false

theorem extendBitsTo_length {w : List Bool} {m : Nat} (hwm : w.length <= m) :
    (extendBitsTo w m).length = m := by
  simp [extendBitsTo]
  omega

theorem extendBitsTo_take_length (w : List Bool) (m : Nat) :
    (extendBitsTo w m).take w.length = w := by
  simp [extendBitsTo]

namespace BranchFiberNonempty

theorem rows_nonempty
    {R : Finset A} {C : Finset B} {P : Protocol A B Z} {w : List Bool}
    (h : BranchFiberNonempty R C P w) :
    R.Nonempty := by
  rcases h with ⟨a, ha, b, hb, hbits⟩
  exact ⟨a, ha⟩

theorem cols_nonempty
    {R : Finset A} {C : Finset B} {P : Protocol A B Z} {w : List Bool}
    (h : BranchFiberNonempty R C P w) :
    C.Nonempty := by
  rcases h with ⟨a, ha, b, hb, hbits⟩
  exact ⟨b, hb⟩

theorem of_full_length
    {R : Finset A} {C : Finset B} {P : Protocol A B Z}
    {m : Nat}
    (hfull : ∀ w : List Bool, w.length = m -> BranchFiberNonempty R C P w)
    (τ : List Bool) (hτ : τ.length <= m) :
    BranchFiberNonempty R C P τ := by
  let w := extendBitsTo τ m
  have hwlen : w.length = m := extendBitsTo_length hτ
  rcases hfull w hwlen with ⟨a, ha, b, hb, hbits⟩
  refine ⟨a, ha, b, hb, ?_⟩
  have hbitsm : actualBitListRaw m P a b = w := by
    simpa [hwlen] using hbits
  calc
    actualBitListRaw τ.length P a b =
        (actualBitListRaw m P a b).take τ.length := by
          exact (actualBitListRaw_take hτ P a b).symm
    _ = w.take τ.length := by rw [hbitsm]
    _ = τ := by
          simp [w, extendBitsTo_take_length]

end BranchFiberNonempty

def rowsAtPrefix
    (R : Finset A) (C : Finset B) (P : Protocol A B Z)
    (w : List Bool) : Finset A :=
  R.filter fun a => ∃ b, b ∈ C ∧ actualBitListRaw w.length P a b = w

def colsAtPrefix
    (R : Finset A) (C : Finset B) (P : Protocol A B Z)
    (w : List Bool) : Finset B :=
  C.filter fun b => ∃ a, a ∈ R ∧ actualBitListRaw w.length P a b = w

structure StopLeafContained
    (G : A -> B -> Bool) (R : Finset A) (C : Finset B)
    (Qr : Protocol A B Bool) (w : List Bool)
    (Rw : Finset A) (Cw : Finset B) : Prop where
  rows_subset :
    ∀ a, a ∈ Rw -> a ∈ rowsAtPrefix R C Qr w
  cols_subset :
    ∀ b, b ∈ Cw -> b ∈ colsAtPrefix R C Qr w
  rows_nonempty : Rw.Nonempty
  cols_nonempty : Cw.Nonempty

namespace StopLeafContained

theorem rows_subset_base
    {G : A -> B -> Bool} {R : Finset A} {C : Finset B}
    {Qr : Protocol A B Bool} {w : List Bool}
    {Rw : Finset A} {Cw : Finset B}
    (h : StopLeafContained G R C Qr w Rw Cw) :
    ∀ a, a ∈ Rw -> a ∈ R := by
  intro a ha
  have hrow := h.rows_subset a ha
  exact (Finset.mem_filter.mp hrow).1

theorem cols_subset_base
    {G : A -> B -> Bool} {R : Finset A} {C : Finset B}
    {Qr : Protocol A B Bool} {w : List Bool}
    {Rw : Finset A} {Cw : Finset B}
    (h : StopLeafContained G R C Qr w Rw Cw) :
    ∀ b, b ∈ Cw -> b ∈ C := by
  intro b hb
  have hcol := h.cols_subset b hb
  exact (Finset.mem_filter.mp hcol).1

end StopLeafContained

theorem D_stopLeaf_le_restrict_cost
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool) (P : Protocol A B Bool)
    (hP : P.Computes G)
    (Rw : Finset A) (Cw : Finset B) :
    D (subgame G Rw Cw) <= (Protocol.restrict Rw Cw P).cost := by
  exact D_subgame_le_restrict_cost Rw Cw P hP

theorem D_stopLeaf_le_protocol_cost
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool) (P : Protocol A B Bool)
    (hP : P.Computes G) (Rw : Finset A) (Cw : Finset B) :
    D (subgame G Rw Cw) <= P.cost := by
  exact le_trans (D_subgame_le_restrict_cost Rw Cw P hP)
    (Protocol.cost_restrict_le Rw Cw P)

def FullStoppingFiberCoverage
    (R : Finset A) (C : Finset B) (P : Protocol A B Z)
    (pat : List ActualBitSide) : Prop :=
  ∀ w : List Bool, w.length = pat.length -> BranchFiberNonempty R C P w

def TerminalHardWitnesses
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool) (R : Finset A) (C : Finset B)
    (Qr : Protocol A B Bool) (pat : List ActualBitSide) (B0 : Nat) : Prop :=
  ∀ w : List Bool, w.length = pat.length ->
    ∃ Rw Cw,
      StopLeafContained G R C Qr w Rw Cw ∧
        B0 <= D (subgame G Rw Cw)

/-- Proposition-valued record of the intended main theorem. -/
def noWaste_firstPatternOn_univ_of_restrict_statement
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool) (P : Protocol A B Bool)
    (R : Finset A) (C : Finset B)
    (pat : List ActualBitSide) (B0 : Nat) : Prop :=
  P.Computes G ->
  P.cost <= pat.length + B0 ->
  FirstPatternOn R C pat (Protocol.restrict R C P) ->
  FullStoppingFiberCoverage R C (Protocol.restrict R C P) pat ->
  TerminalHardWitnesses G R C (Protocol.restrict R C P) pat B0 ->
  FirstPatternOn (Finset.univ : Finset A) (Finset.univ : Finset B) pat P

def noWaste_firstKColBitsOn_univ_of_restrict_statement
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool) (P : Protocol A B Bool)
    (R : Finset A) (C : Finset B)
    (m B0 : Nat) : Prop :=
  P.Computes G ->
  P.cost <= m + B0 ->
  FirstKColBitsOn R C m (Protocol.restrict R C P) ->
  FullStoppingFiberCoverage R C (Protocol.restrict R C P)
    (List.replicate m ActualBitSide.bob) ->
  TerminalHardWitnesses G R C (Protocol.restrict R C P)
    (List.replicate m ActualBitSide.bob) B0 ->
  FirstKColBitsOn (Finset.univ : Finset A) (Finset.univ : Finset B) m P

def noWaste_firstKRowBitsOn_univ_of_restrict_statement
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool) (P : Protocol A B Bool)
    (R : Finset A) (C : Finset B)
    (m B0 : Nat) : Prop :=
  P.Computes G ->
  P.cost <= m + B0 ->
  FirstKRowBitsOn R C m (Protocol.restrict R C P) ->
  FullStoppingFiberCoverage R C (Protocol.restrict R C P)
    (List.replicate m ActualBitSide.alice) ->
  TerminalHardWitnesses G R C (Protocol.restrict R C P)
    (List.replicate m ActualBitSide.alice) B0 ->
  FirstKRowBitsOn (Finset.univ : Finset A) (Finset.univ : Finset B) m P

-- CLAIM-END aux:nowaste-core

-- CLAIM-BEGIN aux:nowaste-main

theorem D_le_cost_of_computes
    {A B : Type*} [Fintype A] [Fintype B]
    {G : A -> B -> Bool} {P : Protocol A B Bool}
    (hP : P.Computes G) :
    D G <= P.cost := by
  have hmem : P.cost ∈ AchievableCosts G := ⟨P, rfl, hP⟩
  calc
    D G = sInf (AchievableCosts G) := rfl
    _ <= P.cost := Nat.sInf_le hmem

theorem actualSideListRaw_eq_of_firstPatternOn
    {A B Z : Type*}
    {R : Finset A} {C : Finset B} {pat : List ActualBitSide}
    {P : Protocol A B Z} {a : A} {b : B}
    (hpat : FirstPatternOn R C pat P)
    (ha : a ∈ R) (hb : b ∈ C) :
    Protocol.actualSideListRaw pat.length P a b = pat := by
  induction pat generalizing R C P with
  | nil =>
      rfl
  | cons side tail ih =>
      cases P with
      | leaf z =>
          exfalso
          rcases hpat with hR | hC
          · rw [hR] at ha
            exact absurd ha (Finset.notMem_empty a)
          · rw [hC] at hb
            exact absurd hb (Finset.notMem_empty b)
      | aNode q l r =>
          cases side with
          | alice =>
              obtain ⟨hl, hr⟩ := hpat
              simp only [Protocol.actualSideListRaw, List.length_cons]
              by_cases hq : q a
              · have ha' : a ∈ R.filter fun x => q x = true := by
                  rw [Finset.mem_filter]
                  exact ⟨ha, hq⟩
                rw [if_pos hq]
                exact congrArg (fun xs => ActualBitSide.alice :: xs)
                  (ih hr ha' hb)
              · have hqf : q a = false := by simp [hq]
                have ha' : a ∈ R.filter fun x => q x = false := by
                  rw [Finset.mem_filter]
                  exact ⟨ha, hqf⟩
                rw [if_neg hq]
                exact congrArg (fun xs => ActualBitSide.alice :: xs)
                  (ih hl ha' hb)
          | bob =>
              exfalso
              rcases hpat with hR | hC
              · rw [hR] at ha
                exact absurd ha (Finset.notMem_empty a)
              · rw [hC] at hb
                exact absurd hb (Finset.notMem_empty b)
      | bNode q l r =>
          cases side with
          | alice =>
              exfalso
              rcases hpat with hR | hC
              · rw [hR] at ha
                exact absurd ha (Finset.notMem_empty a)
              · rw [hC] at hb
                exact absurd hb (Finset.notMem_empty b)
          | bob =>
              obtain ⟨hl, hr⟩ := hpat
              simp only [Protocol.actualSideListRaw, List.length_cons]
              by_cases hq : q b
              · have hb' : b ∈ C.filter fun y => q y = true := by
                  rw [Finset.mem_filter]
                  exact ⟨hb, hq⟩
                rw [if_pos hq]
                exact congrArg (fun xs => ActualBitSide.bob :: xs)
                  (ih hr ha hb')
              · have hqf : q b = false := by simp [hq]
                have hb' : b ∈ C.filter fun y => q y = false := by
                  rw [Finset.mem_filter]
                  exact ⟨hb, hqf⟩
                rw [if_neg hq]
                exact congrArg (fun xs => ActualBitSide.bob :: xs)
                  (ih hl ha hb')

theorem actualPrefixCodeRaw_eq_of_actualBitListRaw_eq
    {A B Z : Type*} {k : Nat} {P : Protocol A B Z}
    {a a' : A} {b b' : B}
    (hbits : actualBitListRaw k P a b = actualBitListRaw k P a' b') :
    Protocol.actualPrefixCodeRaw k P a b =
      Protocol.actualPrefixCodeRaw k P a' b' := by
  induction k generalizing P with
  | zero =>
      rfl
  | succ n ih =>
      cases P with
      | leaf z =>
          rfl
      | aNode q l r =>
          simp only [actualBitListRaw, Protocol.actualPrefixCodeRaw] at hbits ⊢
          by_cases hq : q a
          · by_cases hq' : q a'
            · rw [if_pos hq, if_pos hq']
              simpa [hq, hq'] using congrArg (Protocol.bitCons true)
                (ih (by simpa [hq, hq'] using hbits))
            · simp [hq, hq'] at hbits
          · by_cases hq' : q a'
            · simp [hq, hq'] at hbits
            · rw [if_neg hq, if_neg hq']
              simpa [hq, hq'] using congrArg (Protocol.bitCons false)
                (ih (by simpa [hq, hq'] using hbits))
      | bNode q l r =>
          simp only [actualBitListRaw, Protocol.actualPrefixCodeRaw] at hbits ⊢
          by_cases hq : q b
          · by_cases hq' : q b'
            · rw [if_pos hq, if_pos hq']
              simpa [hq, hq'] using congrArg (Protocol.bitCons true)
                (ih (by simpa [hq, hq'] using hbits))
            · simp [hq, hq'] at hbits
          · by_cases hq' : q b'
            · simp [hq, hq'] at hbits
            · rw [if_neg hq, if_neg hq']
              simpa [hq, hq'] using congrArg (Protocol.bitCons false)
                (ih (by simpa [hq, hq'] using hbits))

theorem actualBitListRaw_eq_of_firstPatternOn_of_row_col_prefix
    {A B Z : Type*}
    {R : Finset A} {C : Finset B}
    {pat : List ActualBitSide} {w : List Bool}
    {P : Protocol A B Z} {a : A} {b : B}
    (hpat : FirstPatternOn R C pat P)
    (ha : a ∈ rowsAtPrefix R C P w)
    (hb : b ∈ colsAtPrefix R C P w)
    (hlen : w.length = pat.length) :
    actualBitListRaw pat.length P a b = w := by
  induction pat generalizing R C P w with
  | nil =>
      have hw : w = [] := List.eq_nil_of_length_eq_zero hlen
      simp [actualBitListRaw, hw]
  | cons side tail ih =>
      cases w with
      | nil =>
          simp at hlen
      | cons bit wt =>
          have hwtlen : wt.length = tail.length := by
            simpa using hlen
          cases P with
          | leaf z =>
              exfalso
              have haR : a ∈ R := (Finset.mem_filter.mp ha).1
              have hbC : b ∈ C := (Finset.mem_filter.mp hb).1
              rcases hpat with hR | hC
              · rw [hR] at haR
                exact absurd haR (Finset.notMem_empty a)
              · rw [hC] at hbC
                exact absurd hbC (Finset.notMem_empty b)
          | aNode q l r =>
              cases side with
              | bob =>
                  exfalso
                  have haR : a ∈ R := (Finset.mem_filter.mp ha).1
                  have hbC : b ∈ C := (Finset.mem_filter.mp hb).1
                  rcases hpat with hR | hC
                  · rw [hR] at haR
                    exact absurd haR (Finset.notMem_empty a)
                  · rw [hC] at hbC
                    exact absurd hbC (Finset.notMem_empty b)
              | alice =>
                  obtain ⟨hl, hr⟩ := hpat
                  have haR : a ∈ R := (Finset.mem_filter.mp ha).1
                  have hbC : b ∈ C := (Finset.mem_filter.mp hb).1
                  rcases (Finset.mem_filter.mp ha).2 with ⟨b1, hb1C, hbits1⟩
                  rcases (Finset.mem_filter.mp hb).2 with ⟨a1, ha1R, hbits2⟩
                  have hbits1' :
                      q a :: actualBitListRaw wt.length
                          (if q a then r else l) a b1 = bit :: wt := by
                    simpa [actualBitListRaw, hlen] using hbits1
                  have hhead1 : q a = bit := (List.cons.inj hbits1').1
                  have htail1 :
                      actualBitListRaw wt.length
                          (if q a then r else l) a b1 = wt :=
                    (List.cons.inj hbits1').2
                  by_cases hqa : q a
                  · have hbit : bit = true := by simpa [hqa] using hhead1.symm
                    have haChild : a ∈ rowsAtPrefix
                        (R.filter fun x => q x = true) C r wt := by
                      rw [rowsAtPrefix, Finset.mem_filter]
                      refine ⟨?_, ?_⟩
                      · rw [Finset.mem_filter]
                        exact ⟨haR, hqa⟩
                      · refine ⟨b1, hb1C, ?_⟩
                        simpa [hqa] using htail1
                    have hbits2' :
                        q a1 :: actualBitListRaw wt.length
                            (if q a1 then r else l) a1 b = bit :: wt := by
                      simpa [actualBitListRaw, hlen] using hbits2
                    have hhead2 : q a1 = bit := (List.cons.inj hbits2').1
                    have htail2 :
                        actualBitListRaw wt.length
                            (if q a1 then r else l) a1 b = wt :=
                      (List.cons.inj hbits2').2
                    have hqa1 : q a1 = true := by rw [hhead2, hbit]
                    have hbChild : b ∈ colsAtPrefix
                        (R.filter fun x => q x = true) C r wt := by
                      rw [colsAtPrefix, Finset.mem_filter]
                      refine ⟨hbC, ?_⟩
                      refine ⟨a1, ?_, ?_⟩
                      · rw [Finset.mem_filter]
                        exact ⟨ha1R, hqa1⟩
                      · simpa [hqa1] using htail2
                    have htail := ih hr haChild hbChild hwtlen
                    simp [actualBitListRaw, hqa, hbit, htail]
                  · have hqaf : q a = false := by simp [hqa]
                    have hbit : bit = false := by simpa [hqaf] using hhead1.symm
                    have haChild : a ∈ rowsAtPrefix
                        (R.filter fun x => q x = false) C l wt := by
                      rw [rowsAtPrefix, Finset.mem_filter]
                      refine ⟨?_, ?_⟩
                      · rw [Finset.mem_filter]
                        exact ⟨haR, hqaf⟩
                      · refine ⟨b1, hb1C, ?_⟩
                        simpa [hqa] using htail1
                    have hbits2' :
                        q a1 :: actualBitListRaw wt.length
                            (if q a1 then r else l) a1 b = bit :: wt := by
                      simpa [actualBitListRaw, hlen] using hbits2
                    have hhead2 : q a1 = bit := (List.cons.inj hbits2').1
                    have htail2 :
                        actualBitListRaw wt.length
                            (if q a1 then r else l) a1 b = wt :=
                      (List.cons.inj hbits2').2
                    have hqa1 : q a1 = false := by rw [hhead2, hbit]
                    have hbChild : b ∈ colsAtPrefix
                        (R.filter fun x => q x = false) C l wt := by
                      rw [colsAtPrefix, Finset.mem_filter]
                      refine ⟨hbC, ?_⟩
                      refine ⟨a1, ?_, ?_⟩
                      · rw [Finset.mem_filter]
                        exact ⟨ha1R, hqa1⟩
                      · simpa [hqa1] using htail2
                    have htail := ih hl haChild hbChild hwtlen
                    simp [actualBitListRaw, hqa, hbit, htail]
          | bNode q l r =>
              cases side with
              | alice =>
                  exfalso
                  have haR : a ∈ R := (Finset.mem_filter.mp ha).1
                  have hbC : b ∈ C := (Finset.mem_filter.mp hb).1
                  rcases hpat with hR | hC
                  · rw [hR] at haR
                    exact absurd haR (Finset.notMem_empty a)
                  · rw [hC] at hbC
                    exact absurd hbC (Finset.notMem_empty b)
              | bob =>
                  obtain ⟨hl, hr⟩ := hpat
                  have haR : a ∈ R := (Finset.mem_filter.mp ha).1
                  have hbC : b ∈ C := (Finset.mem_filter.mp hb).1
                  rcases (Finset.mem_filter.mp ha).2 with ⟨b1, hb1C, hbits1⟩
                  rcases (Finset.mem_filter.mp hb).2 with ⟨a1, ha1R, hbits2⟩
                  have hbits2' :
                      q b :: actualBitListRaw wt.length
                          (if q b then r else l) a1 b = bit :: wt := by
                    simpa [actualBitListRaw, hlen] using hbits2
                  have hhead2 : q b = bit := (List.cons.inj hbits2').1
                  have htail2 :
                      actualBitListRaw wt.length
                          (if q b then r else l) a1 b = wt :=
                    (List.cons.inj hbits2').2
                  by_cases hqb : q b
                  · have hbit : bit = true := by simpa [hqb] using hhead2.symm
                    have hbChild : b ∈ colsAtPrefix R
                        (C.filter fun y => q y = true) r wt := by
                      rw [colsAtPrefix, Finset.mem_filter]
                      refine ⟨?_, ?_⟩
                      · rw [Finset.mem_filter]
                        exact ⟨hbC, hqb⟩
                      · refine ⟨a1, ha1R, ?_⟩
                        simpa [hqb] using htail2
                    have hbits1' :
                        q b1 :: actualBitListRaw wt.length
                            (if q b1 then r else l) a b1 = bit :: wt := by
                      simpa [actualBitListRaw, hlen] using hbits1
                    have hhead1 : q b1 = bit := (List.cons.inj hbits1').1
                    have htail1 :
                        actualBitListRaw wt.length
                            (if q b1 then r else l) a b1 = wt :=
                      (List.cons.inj hbits1').2
                    have hqb1 : q b1 = true := by rw [hhead1, hbit]
                    have haChild : a ∈ rowsAtPrefix R
                        (C.filter fun y => q y = true) r wt := by
                      rw [rowsAtPrefix, Finset.mem_filter]
                      refine ⟨haR, ?_⟩
                      refine ⟨b1, ?_, ?_⟩
                      · rw [Finset.mem_filter]
                        exact ⟨hb1C, hqb1⟩
                      · simpa [hqb1] using htail1
                    have htail := ih hr haChild hbChild hwtlen
                    simp [actualBitListRaw, hqb, hbit, htail]
                  · have hqbf : q b = false := by simp [hqb]
                    have hbit : bit = false := by simpa [hqbf] using hhead2.symm
                    have hbChild : b ∈ colsAtPrefix R
                        (C.filter fun y => q y = false) l wt := by
                      rw [colsAtPrefix, Finset.mem_filter]
                      refine ⟨?_, ?_⟩
                      · rw [Finset.mem_filter]
                        exact ⟨hbC, hqbf⟩
                      · refine ⟨a1, ha1R, ?_⟩
                        simpa [hqb] using htail2
                    have hbits1' :
                        q b1 :: actualBitListRaw wt.length
                            (if q b1 then r else l) a b1 = bit :: wt := by
                      simpa [actualBitListRaw, hlen] using hbits1
                    have hhead1 : q b1 = bit := (List.cons.inj hbits1').1
                    have htail1 :
                        actualBitListRaw wt.length
                            (if q b1 then r else l) a b1 = wt :=
                      (List.cons.inj hbits1').2
                    have hqb1 : q b1 = false := by rw [hhead1, hbit]
                    have haChild : a ∈ rowsAtPrefix R
                        (C.filter fun y => q y = false) l wt := by
                      rw [rowsAtPrefix, Finset.mem_filter]
                      refine ⟨haR, ?_⟩
                      refine ⟨b1, ?_, ?_⟩
                      · rw [Finset.mem_filter]
                        exact ⟨hb1C, hqb1⟩
                      · simpa [hqb1] using htail1
                    have htail := ih hl haChild hbChild hwtlen
                    simp [actualBitListRaw, hqb, hbit, htail]

theorem firstPatternOn_terminal_cost_lower
    {A B : Type*} [Fintype A] [Fintype B]
    {G : A -> B -> Bool} {R : Finset A} {C : Finset B}
    {P : Protocol A B Bool} {pat : List ActualBitSide} {B0 : Nat}
    (hcomp : ∀ a, a ∈ R -> ∀ b, b ∈ C -> P.eval a b = G a b)
    (hpat : FirstPatternOn R C pat P)
    (hterm : TerminalHardWitnesses G R C P pat B0) :
    pat.length + B0 <= P.cost := by
  classical
  let w : List Bool := List.replicate pat.length false
  have hwlen : w.length = pat.length := by simp [w]
  rcases hterm w hwlen with ⟨Rw, Cw, hstop, hB⟩
  obtain ⟨a0, ha0⟩ := hstop.rows_nonempty
  obtain ⟨b0, hb0⟩ := hstop.cols_nonempty
  have ha0R : a0 ∈ R := hstop.rows_subset_base a0 ha0
  have hb0C : b0 ∈ C := hstop.cols_subset_base b0 hb0
  have hbits0 :
      actualBitListRaw pat.length P a0 b0 = w :=
    actualBitListRaw_eq_of_firstPatternOn_of_row_col_prefix hpat
      (hstop.rows_subset a0 ha0) (hstop.cols_subset b0 hb0) hwlen
  let code := Protocol.actualPrefixCodeRaw pat.length P a0 b0
  have hresComp :
      (Protocol.restrictSub Rw Cw
        (Protocol.actualSubtreeAtRaw pat.length P code)).Computes
        (subgame G Rw Cw) := by
    intro a b
    rw [Protocol.eval_restrictSub]
    have habBits :
        actualBitListRaw pat.length P a.val b.val = w :=
      actualBitListRaw_eq_of_firstPatternOn_of_row_col_prefix hpat
        (hstop.rows_subset a.val a.2) (hstop.cols_subset b.val b.2) hwlen
    have hsame :
        actualBitListRaw pat.length P a.val b.val =
          actualBitListRaw pat.length P a0 b0 := by
      rw [habBits, hbits0]
    have hcode :
        Protocol.actualPrefixCodeRaw pat.length P a.val b.val = code := by
      simpa [code] using
        actualPrefixCodeRaw_eq_of_actualBitListRaw_eq (P := P) hsame
    change (Protocol.actualSubtreeAtRaw pat.length P code).eval a.val b.val =
      G a.val b.val
    rw [← hcode]
    rw [Protocol.eval_actualSubtreeAtRaw_eq_of_actualPrefix]
    exact hcomp a.val (hstop.rows_subset_base a.val a.2)
      b.val (hstop.cols_subset_base b.val b.2)
  have hDle :
      D (subgame G Rw Cw) <=
        (Protocol.actualSubtreeAtRaw pat.length P code).cost := by
    have hmem :
        (Protocol.restrictSub Rw Cw
          (Protocol.actualSubtreeAtRaw pat.length P code)).cost ∈
          AchievableCosts (subgame G Rw Cw) :=
      ⟨Protocol.restrictSub Rw Cw
          (Protocol.actualSubtreeAtRaw pat.length P code), rfl, hresComp⟩
    calc
      D (subgame G Rw Cw) =
          sInf (AchievableCosts (subgame G Rw Cw)) := rfl
      _ <= (Protocol.restrictSub Rw Cw
          (Protocol.actualSubtreeAtRaw pat.length P code)).cost :=
          Nat.sInf_le hmem
      _ = (Protocol.actualSubtreeAtRaw pat.length P code).cost := by
          rw [Protocol.cost_restrictSub]
  have hside :
      Protocol.actualSideListRaw pat.length P a0 b0 = pat :=
    actualSideListRaw_eq_of_firstPatternOn hpat ha0R hb0C
  have hcost :=
    Protocol.actualSideListRaw_length_add_cost_actualSubtreeAtRaw_le
      pat.length P a0 b0
  have hcost' :
      pat.length + (Protocol.actualSubtreeAtRaw pat.length P code).cost <=
        P.cost := by
    simpa [code, hside] using hcost
  exact Nat.add_le_add_left (le_trans hB hDle) pat.length |>.trans hcost'

theorem fullStoppingFiberCoverage_tail_false_of_aNode
    {A B Z : Type*} {R : Finset A} {C : Finset B}
    {q : A -> Bool} {l r : Protocol A B Z}
    {tail : List ActualBitSide}
    (hcov : FullStoppingFiberCoverage R C (Protocol.aNode q l r)
      (ActualBitSide.alice :: tail)) :
    FullStoppingFiberCoverage (R.filter fun x => q x = false) C l tail := by
  intro w hw
  have hwfull : (false :: w).length = (ActualBitSide.alice :: tail).length := by
    simp [hw]
  rcases hcov (false :: w) hwfull with ⟨a, ha, b, hb, hbits⟩
  have hbits' :
      q a :: actualBitListRaw w.length (if q a then r else l) a b =
        false :: w := by
    simpa [actualBitListRaw, hw] using hbits
  have hhead : q a = false := (List.cons.inj hbits').1
  have htail :
      actualBitListRaw w.length (if q a then r else l) a b = w :=
    (List.cons.inj hbits').2
  refine ⟨a, ?_, b, hb, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨ha, hhead⟩
  · simpa [hhead] using htail

theorem fullStoppingFiberCoverage_tail_true_of_aNode
    {A B Z : Type*} {R : Finset A} {C : Finset B}
    {q : A -> Bool} {l r : Protocol A B Z}
    {tail : List ActualBitSide}
    (hcov : FullStoppingFiberCoverage R C (Protocol.aNode q l r)
      (ActualBitSide.alice :: tail)) :
    FullStoppingFiberCoverage (R.filter fun x => q x = true) C r tail := by
  intro w hw
  have hwfull : (true :: w).length = (ActualBitSide.alice :: tail).length := by
    simp [hw]
  rcases hcov (true :: w) hwfull with ⟨a, ha, b, hb, hbits⟩
  have hbits' :
      q a :: actualBitListRaw w.length (if q a then r else l) a b =
        true :: w := by
    simpa [actualBitListRaw, hw] using hbits
  have hhead : q a = true := (List.cons.inj hbits').1
  have htail :
      actualBitListRaw w.length (if q a then r else l) a b = w :=
    (List.cons.inj hbits').2
  refine ⟨a, ?_, b, hb, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨ha, hhead⟩
  · simpa [hhead] using htail

theorem fullStoppingFiberCoverage_tail_false_of_bNode
    {A B Z : Type*} {R : Finset A} {C : Finset B}
    {q : B -> Bool} {l r : Protocol A B Z}
    {tail : List ActualBitSide}
    (hcov : FullStoppingFiberCoverage R C (Protocol.bNode q l r)
      (ActualBitSide.bob :: tail)) :
    FullStoppingFiberCoverage R (C.filter fun y => q y = false) l tail := by
  intro w hw
  have hwfull : (false :: w).length = (ActualBitSide.bob :: tail).length := by
    simp [hw]
  rcases hcov (false :: w) hwfull with ⟨a, ha, b, hb, hbits⟩
  have hbits' :
      q b :: actualBitListRaw w.length (if q b then r else l) a b =
        false :: w := by
    simpa [actualBitListRaw, hw] using hbits
  have hhead : q b = false := (List.cons.inj hbits').1
  have htail :
      actualBitListRaw w.length (if q b then r else l) a b = w :=
    (List.cons.inj hbits').2
  refine ⟨a, ha, b, ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨hb, hhead⟩
  · simpa [hhead] using htail

theorem fullStoppingFiberCoverage_tail_true_of_bNode
    {A B Z : Type*} {R : Finset A} {C : Finset B}
    {q : B -> Bool} {l r : Protocol A B Z}
    {tail : List ActualBitSide}
    (hcov : FullStoppingFiberCoverage R C (Protocol.bNode q l r)
      (ActualBitSide.bob :: tail)) :
    FullStoppingFiberCoverage R (C.filter fun y => q y = true) r tail := by
  intro w hw
  have hwfull : (true :: w).length = (ActualBitSide.bob :: tail).length := by
    simp [hw]
  rcases hcov (true :: w) hwfull with ⟨a, ha, b, hb, hbits⟩
  have hbits' :
      q b :: actualBitListRaw w.length (if q b then r else l) a b =
        true :: w := by
    simpa [actualBitListRaw, hw] using hbits
  have hhead : q b = true := (List.cons.inj hbits').1
  have htail :
      actualBitListRaw w.length (if q b then r else l) a b = w :=
    (List.cons.inj hbits').2
  refine ⟨a, ha, b, ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨hb, hhead⟩
  · simpa [hhead] using htail

theorem stopLeafContained_tail_false_of_aNode
    {A B : Type*} {G : A -> B -> Bool}
    {R : Finset A} {C : Finset B} {q : A -> Bool}
    {l r : Protocol A B Bool} {w : List Bool} {Rw : Finset A} {Cw : Finset B}
    (hstop : StopLeafContained G R C (Protocol.aNode q l r) (false :: w) Rw Cw) :
    StopLeafContained G (R.filter fun x => q x = false) C l w Rw Cw where
  rows_subset := by
    intro a ha
    have hrow := hstop.rows_subset a ha
    rw [rowsAtPrefix, Finset.mem_filter] at hrow ⊢
    rcases hrow with ⟨haR, b, hbC, hbits⟩
    have hbits' :
        q a :: actualBitListRaw w.length (if q a then r else l) a b =
          false :: w := by
      simpa [actualBitListRaw] using hbits
    have hhead : q a = false := (List.cons.inj hbits').1
    have htail :
        actualBitListRaw w.length (if q a then r else l) a b = w :=
      (List.cons.inj hbits').2
    refine ⟨?_, b, hbC, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨haR, hhead⟩
    · simpa [hhead] using htail
  cols_subset := by
    intro b hb
    have hcol := hstop.cols_subset b hb
    rw [colsAtPrefix, Finset.mem_filter] at hcol ⊢
    rcases hcol with ⟨hbC, a, haR, hbits⟩
    have hbits' :
        q a :: actualBitListRaw w.length (if q a then r else l) a b =
          false :: w := by
      simpa [actualBitListRaw] using hbits
    have hhead : q a = false := (List.cons.inj hbits').1
    have htail :
        actualBitListRaw w.length (if q a then r else l) a b = w :=
      (List.cons.inj hbits').2
    refine ⟨hbC, a, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨haR, hhead⟩
    · simpa [hhead] using htail
  rows_nonempty := hstop.rows_nonempty
  cols_nonempty := hstop.cols_nonempty

theorem stopLeafContained_tail_true_of_aNode
    {A B : Type*} {G : A -> B -> Bool}
    {R : Finset A} {C : Finset B} {q : A -> Bool}
    {l r : Protocol A B Bool} {w : List Bool} {Rw : Finset A} {Cw : Finset B}
    (hstop : StopLeafContained G R C (Protocol.aNode q l r) (true :: w) Rw Cw) :
    StopLeafContained G (R.filter fun x => q x = true) C r w Rw Cw where
  rows_subset := by
    intro a ha
    have hrow := hstop.rows_subset a ha
    rw [rowsAtPrefix, Finset.mem_filter] at hrow ⊢
    rcases hrow with ⟨haR, b, hbC, hbits⟩
    have hbits' :
        q a :: actualBitListRaw w.length (if q a then r else l) a b =
          true :: w := by
      simpa [actualBitListRaw] using hbits
    have hhead : q a = true := (List.cons.inj hbits').1
    have htail :
        actualBitListRaw w.length (if q a then r else l) a b = w :=
      (List.cons.inj hbits').2
    refine ⟨?_, b, hbC, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨haR, hhead⟩
    · simpa [hhead] using htail
  cols_subset := by
    intro b hb
    have hcol := hstop.cols_subset b hb
    rw [colsAtPrefix, Finset.mem_filter] at hcol ⊢
    rcases hcol with ⟨hbC, a, haR, hbits⟩
    have hbits' :
        q a :: actualBitListRaw w.length (if q a then r else l) a b =
          true :: w := by
      simpa [actualBitListRaw] using hbits
    have hhead : q a = true := (List.cons.inj hbits').1
    have htail :
        actualBitListRaw w.length (if q a then r else l) a b = w :=
      (List.cons.inj hbits').2
    refine ⟨hbC, a, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨haR, hhead⟩
    · simpa [hhead] using htail
  rows_nonempty := hstop.rows_nonempty
  cols_nonempty := hstop.cols_nonempty

theorem stopLeafContained_tail_false_of_bNode
    {A B : Type*} {G : A -> B -> Bool}
    {R : Finset A} {C : Finset B} {q : B -> Bool}
    {l r : Protocol A B Bool} {w : List Bool} {Rw : Finset A} {Cw : Finset B}
    (hstop : StopLeafContained G R C (Protocol.bNode q l r) (false :: w) Rw Cw) :
    StopLeafContained G R (C.filter fun y => q y = false) l w Rw Cw where
  rows_subset := by
    intro a ha
    have hrow := hstop.rows_subset a ha
    rw [rowsAtPrefix, Finset.mem_filter] at hrow ⊢
    rcases hrow with ⟨haR, b, hbC, hbits⟩
    have hbits' :
        q b :: actualBitListRaw w.length (if q b then r else l) a b =
          false :: w := by
      simpa [actualBitListRaw] using hbits
    have hhead : q b = false := (List.cons.inj hbits').1
    have htail :
        actualBitListRaw w.length (if q b then r else l) a b = w :=
      (List.cons.inj hbits').2
    refine ⟨haR, b, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hbC, hhead⟩
    · simpa [hhead] using htail
  cols_subset := by
    intro b hb
    have hcol := hstop.cols_subset b hb
    rw [colsAtPrefix, Finset.mem_filter] at hcol ⊢
    rcases hcol with ⟨hbC, a, haR, hbits⟩
    have hbits' :
        q b :: actualBitListRaw w.length (if q b then r else l) a b =
          false :: w := by
      simpa [actualBitListRaw] using hbits
    have hhead : q b = false := (List.cons.inj hbits').1
    have htail :
        actualBitListRaw w.length (if q b then r else l) a b = w :=
      (List.cons.inj hbits').2
    refine ⟨?_, a, haR, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hbC, hhead⟩
    · simpa [hhead] using htail
  rows_nonempty := hstop.rows_nonempty
  cols_nonempty := hstop.cols_nonempty

theorem stopLeafContained_tail_true_of_bNode
    {A B : Type*} {G : A -> B -> Bool}
    {R : Finset A} {C : Finset B} {q : B -> Bool}
    {l r : Protocol A B Bool} {w : List Bool} {Rw : Finset A} {Cw : Finset B}
    (hstop : StopLeafContained G R C (Protocol.bNode q l r) (true :: w) Rw Cw) :
    StopLeafContained G R (C.filter fun y => q y = true) r w Rw Cw where
  rows_subset := by
    intro a ha
    have hrow := hstop.rows_subset a ha
    rw [rowsAtPrefix, Finset.mem_filter] at hrow ⊢
    rcases hrow with ⟨haR, b, hbC, hbits⟩
    have hbits' :
        q b :: actualBitListRaw w.length (if q b then r else l) a b =
          true :: w := by
      simpa [actualBitListRaw] using hbits
    have hhead : q b = true := (List.cons.inj hbits').1
    have htail :
        actualBitListRaw w.length (if q b then r else l) a b = w :=
      (List.cons.inj hbits').2
    refine ⟨haR, b, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hbC, hhead⟩
    · simpa [hhead] using htail
  cols_subset := by
    intro b hb
    have hcol := hstop.cols_subset b hb
    rw [colsAtPrefix, Finset.mem_filter] at hcol ⊢
    rcases hcol with ⟨hbC, a, haR, hbits⟩
    have hbits' :
        q b :: actualBitListRaw w.length (if q b then r else l) a b =
          true :: w := by
      simpa [actualBitListRaw] using hbits
    have hhead : q b = true := (List.cons.inj hbits').1
    have htail :
        actualBitListRaw w.length (if q b then r else l) a b = w :=
      (List.cons.inj hbits').2
    refine ⟨?_, a, haR, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hbC, hhead⟩
    · simpa [hhead] using htail
  rows_nonempty := hstop.rows_nonempty
  cols_nonempty := hstop.cols_nonempty

theorem terminalHardWitnesses_tail_false_of_aNode
    {A B : Type*} [Fintype A] [Fintype B] {G : A -> B -> Bool}
    {R : Finset A} {C : Finset B} {q : A -> Bool}
    {l r : Protocol A B Bool} {tail : List ActualBitSide} {B0 : Nat}
    (hterm : TerminalHardWitnesses G R C (Protocol.aNode q l r)
      (ActualBitSide.alice :: tail) B0) :
    TerminalHardWitnesses G (R.filter fun x => q x = false) C l tail B0 := by
  intro w hw
  have hwfull : (false :: w).length = (ActualBitSide.alice :: tail).length := by
    simp [hw]
  rcases hterm (false :: w) hwfull with ⟨Rw, Cw, hstop, hB⟩
  exact ⟨Rw, Cw, stopLeafContained_tail_false_of_aNode hstop, hB⟩

theorem terminalHardWitnesses_tail_true_of_aNode
    {A B : Type*} [Fintype A] [Fintype B] {G : A -> B -> Bool}
    {R : Finset A} {C : Finset B} {q : A -> Bool}
    {l r : Protocol A B Bool} {tail : List ActualBitSide} {B0 : Nat}
    (hterm : TerminalHardWitnesses G R C (Protocol.aNode q l r)
      (ActualBitSide.alice :: tail) B0) :
    TerminalHardWitnesses G (R.filter fun x => q x = true) C r tail B0 := by
  intro w hw
  have hwfull : (true :: w).length = (ActualBitSide.alice :: tail).length := by
    simp [hw]
  rcases hterm (true :: w) hwfull with ⟨Rw, Cw, hstop, hB⟩
  exact ⟨Rw, Cw, stopLeafContained_tail_true_of_aNode hstop, hB⟩

theorem terminalHardWitnesses_tail_false_of_bNode
    {A B : Type*} [Fintype A] [Fintype B] {G : A -> B -> Bool}
    {R : Finset A} {C : Finset B} {q : B -> Bool}
    {l r : Protocol A B Bool} {tail : List ActualBitSide} {B0 : Nat}
    (hterm : TerminalHardWitnesses G R C (Protocol.bNode q l r)
      (ActualBitSide.bob :: tail) B0) :
    TerminalHardWitnesses G R (C.filter fun y => q y = false) l tail B0 := by
  intro w hw
  have hwfull : (false :: w).length = (ActualBitSide.bob :: tail).length := by
    simp [hw]
  rcases hterm (false :: w) hwfull with ⟨Rw, Cw, hstop, hB⟩
  exact ⟨Rw, Cw, stopLeafContained_tail_false_of_bNode hstop, hB⟩

theorem terminalHardWitnesses_tail_true_of_bNode
    {A B : Type*} [Fintype A] [Fintype B] {G : A -> B -> Bool}
    {R : Finset A} {C : Finset B} {q : B -> Bool}
    {l r : Protocol A B Bool} {tail : List ActualBitSide} {B0 : Nat}
    (hterm : TerminalHardWitnesses G R C (Protocol.bNode q l r)
      (ActualBitSide.bob :: tail) B0) :
    TerminalHardWitnesses G R (C.filter fun y => q y = true) r tail B0 := by
  intro w hw
  have hwfull : (true :: w).length = (ActualBitSide.bob :: tail).length := by
    simp [hw]
  rcases hterm (true :: w) hwfull with ⟨Rw, Cw, hstop, hB⟩
  exact ⟨Rw, Cw, stopLeafContained_tail_true_of_bNode hstop, hB⟩

theorem noWaste_firstPatternOn_rect_of_restrict
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool) (P : Protocol A B Bool)
    (S : Finset A) (T : Finset B) (R : Finset A) (C : Finset B)
    (pat : List ActualBitSide) (B0 : Nat)
    (hRsub : ∀ a, a ∈ R -> a ∈ S)
    (hCsub : ∀ b, b ∈ C -> b ∈ T)
    (hcomp : ∀ a, a ∈ S -> ∀ b, b ∈ T -> P.eval a b = G a b)
    (hcost : P.cost <= pat.length + B0)
    (hpat : FirstPatternOn R C pat (Protocol.restrict R C P))
    (hcov : FullStoppingFiberCoverage R C (Protocol.restrict R C P) pat)
    (hterm : TerminalHardWitnesses G R C (Protocol.restrict R C P) pat B0) :
    FirstPatternOn S T pat P := by
  induction pat generalizing S T R C P with
  | nil =>
      trivial
  | cons side tail ih =>
      classical
      have hcompRestrict :
          ∀ a, a ∈ R -> ∀ b, b ∈ C ->
            (Protocol.restrict R C P).eval a b = G a b := by
        intro a ha b hb
        rw [Protocol.eval_restrict_of_mem R C P ha hb]
        exact hcomp a (hRsub a ha) b (hCsub b hb)
      have hlow :
          (side :: tail).length + B0 <= (Protocol.restrict R C P).cost :=
        firstPatternOn_terminal_cost_lower hcompRestrict hpat hterm
      cases P with
      | leaf z =>
          exfalso
          simp [Protocol.restrict, Protocol.cost] at hlow
      | aNode q l r =>
          by_cases hconst : ∃ beta, Protocol.IsRowConstantOn R q beta
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
                (if h : ∃ beta, Protocol.IsRowConstantOn R q beta then
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
                refine ⟨?_, ?_⟩
                · have hRsubL :
                      ∀ a, a ∈ R.filter (fun x => q x = false) ->
                        a ∈ S.filter (fun x => q x = false) := by
                    intro a ha
                    rw [Finset.mem_filter] at ha ⊢
                    exact ⟨hRsub a ha.1, ha.2⟩
                  have hcompL :
                      ∀ a, a ∈ S.filter (fun x => q x = false) ->
                        ∀ b, b ∈ T -> l.eval a b = G a b := by
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
                      FullStoppingFiberCoverage
                        (R.filter fun x => q x = false) C
                        (Protocol.restrict (R.filter fun x => q x = false) C l)
                        tail :=
                    fullStoppingFiberCoverage_tail_false_of_aNode hcov'
                  have htermL :
                      TerminalHardWitnesses G
                        (R.filter fun x => q x = false) C
                        (Protocol.restrict (R.filter fun x => q x = false) C l)
                        tail B0 :=
                    terminalHardWitnesses_tail_false_of_aNode hterm'
                  exact ih l (S.filter fun x => q x = false) T
                    (R.filter fun x => q x = false) C
                    hRsubL hCsub hcompL hcostL hpatL hcovL htermL
                · have hRsubR :
                      ∀ a, a ∈ R.filter (fun x => q x = true) ->
                        a ∈ S.filter (fun x => q x = true) := by
                    intro a ha
                    rw [Finset.mem_filter] at ha ⊢
                    exact ⟨hRsub a ha.1, ha.2⟩
                  have hcompR :
                      ∀ a, a ∈ S.filter (fun x => q x = true) ->
                        ∀ b, b ∈ T -> r.eval a b = G a b := by
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
                      FullStoppingFiberCoverage
                        (R.filter fun x => q x = true) C
                        (Protocol.restrict (R.filter fun x => q x = true) C r)
                        tail :=
                    fullStoppingFiberCoverage_tail_true_of_aNode hcov'
                  have htermR :
                      TerminalHardWitnesses G
                        (R.filter fun x => q x = true) C
                        (Protocol.restrict (R.filter fun x => q x = true) C r)
                        tail B0 :=
                    terminalHardWitnesses_tail_true_of_aNode hterm'
                  exact ih r (S.filter fun x => q x = true) T
                    (R.filter fun x => q x = true) C
                    hRsubR hCsub hcompR hcostR hpatR hcovR htermR
            | bob =>
                exfalso
                let w : List Bool := List.replicate (tail.length + 1) false
                have hw : w.length = (ActualBitSide.bob :: tail).length := by
                  simp [w]
                have hfiber := hcov' w hw
                rcases hpat' with hRempty | hCempty
                · obtain ⟨a, ha⟩ := BranchFiberNonempty.rows_nonempty hfiber
                  rw [hRempty] at ha
                  exact absurd ha (Finset.notMem_empty a)
                · obtain ⟨b, hb⟩ := BranchFiberNonempty.cols_nonempty hfiber
                  rw [hCempty] at hb
                  exact absurd hb (Finset.notMem_empty b)
      | bNode q l r =>
          by_cases hconst : ∃ beta, Protocol.IsColConstantOn C q beta
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
                (if h : ∃ beta, Protocol.IsColConstantOn C q beta then
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
                let w : List Bool := List.replicate (tail.length + 1) false
                have hw : w.length = (ActualBitSide.alice :: tail).length := by
                  simp [w]
                have hfiber := hcov' w hw
                rcases hpat' with hRempty | hCempty
                · obtain ⟨a, ha⟩ := BranchFiberNonempty.rows_nonempty hfiber
                  rw [hRempty] at ha
                  exact absurd ha (Finset.notMem_empty a)
                · obtain ⟨b, hb⟩ := BranchFiberNonempty.cols_nonempty hfiber
                  rw [hCempty] at hb
                  exact absurd hb (Finset.notMem_empty b)
            | bob =>
                obtain ⟨hpatL, hpatR⟩ := hpat'
                refine ⟨?_, ?_⟩
                · have hCsubL :
                      ∀ b, b ∈ C.filter (fun y => q y = false) ->
                        b ∈ T.filter (fun y => q y = false) := by
                    intro b hb
                    rw [Finset.mem_filter] at hb ⊢
                    exact ⟨hCsub b hb.1, hb.2⟩
                  have hcompL :
                      ∀ a, a ∈ S ->
                        ∀ b, b ∈ T.filter (fun y => q y = false) ->
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
                      FullStoppingFiberCoverage R
                        (C.filter fun y => q y = false)
                        (Protocol.restrict R (C.filter fun y => q y = false) l)
                        tail :=
                    fullStoppingFiberCoverage_tail_false_of_bNode hcov'
                  have htermL :
                      TerminalHardWitnesses G R
                        (C.filter fun y => q y = false)
                        (Protocol.restrict R (C.filter fun y => q y = false) l)
                        tail B0 :=
                    terminalHardWitnesses_tail_false_of_bNode hterm'
                  exact ih l S (T.filter fun y => q y = false)
                    R (C.filter fun y => q y = false)
                    hRsub hCsubL hcompL hcostL hpatL hcovL htermL
                · have hCsubR :
                      ∀ b, b ∈ C.filter (fun y => q y = true) ->
                        b ∈ T.filter (fun y => q y = true) := by
                    intro b hb
                    rw [Finset.mem_filter] at hb ⊢
                    exact ⟨hCsub b hb.1, hb.2⟩
                  have hcompR :
                      ∀ a, a ∈ S ->
                        ∀ b, b ∈ T.filter (fun y => q y = true) ->
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
                      FullStoppingFiberCoverage R
                        (C.filter fun y => q y = true)
                        (Protocol.restrict R (C.filter fun y => q y = true) r)
                        tail :=
                    fullStoppingFiberCoverage_tail_true_of_bNode hcov'
                  have htermR :
                      TerminalHardWitnesses G R
                        (C.filter fun y => q y = true)
                        (Protocol.restrict R (C.filter fun y => q y = true) r)
                        tail B0 :=
                    terminalHardWitnesses_tail_true_of_bNode hterm'
                  exact ih r S (T.filter fun y => q y = true)
                    R (C.filter fun y => q y = true)
                    hRsub hCsubR hcompR hcostR hpatR hcovR htermR

theorem noWaste_firstPatternOn_univ_of_restrict
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool) (P : Protocol A B Bool)
    (R : Finset A) (C : Finset B)
    (pat : List ActualBitSide) (B0 : Nat) :
    noWaste_firstPatternOn_univ_of_restrict_statement G P R C pat B0 := by
  intro hcomp hcost hpat hcov hterm
  exact noWaste_firstPatternOn_rect_of_restrict G P
    (Finset.univ : Finset A) (Finset.univ : Finset B) R C pat B0
    (by intro a ha; exact Finset.mem_univ a)
    (by intro b hb; exact Finset.mem_univ b)
    (by intro a ha b hb; exact hcomp a b)
    hcost hpat hcov hterm

theorem noWaste_firstKColBitsOn_univ_of_restrict
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool) (P : Protocol A B Bool)
    (R : Finset A) (C : Finset B)
    (m B0 : Nat) :
    noWaste_firstKColBitsOn_univ_of_restrict_statement G P R C m B0 := by
  intro hcomp hcost hfirst hcov hterm
  have hpat :
      FirstPatternOn R C (List.replicate m ActualBitSide.bob)
        (Protocol.restrict R C P) :=
    (firstPattern_replicate_bob_iff R C m (Protocol.restrict R C P)).2 hfirst
  have hamb :
      FirstPatternOn (Finset.univ : Finset A) (Finset.univ : Finset B)
        (List.replicate m ActualBitSide.bob) P :=
    noWaste_firstPatternOn_univ_of_restrict G P R C
      (List.replicate m ActualBitSide.bob) B0
      hcomp (by simpa using hcost) hpat hcov hterm
  exact (firstPattern_replicate_bob_iff
    (Finset.univ : Finset A) (Finset.univ : Finset B) m P).1 hamb

theorem noWaste_firstKRowBitsOn_univ_of_restrict
    {A B : Type*} [Fintype A] [Fintype B]
    (G : A -> B -> Bool) (P : Protocol A B Bool)
    (R : Finset A) (C : Finset B)
    (m B0 : Nat) :
    noWaste_firstKRowBitsOn_univ_of_restrict_statement G P R C m B0 := by
  intro hcomp hcost hfirst hcov hterm
  have hpat :
      FirstPatternOn R C (List.replicate m ActualBitSide.alice)
        (Protocol.restrict R C P) :=
    (firstPattern_replicate_alice_iff R C m (Protocol.restrict R C P)).2 hfirst
  have hamb :
      FirstPatternOn (Finset.univ : Finset A) (Finset.univ : Finset B)
        (List.replicate m ActualBitSide.alice) P :=
    noWaste_firstPatternOn_univ_of_restrict G P R C
      (List.replicate m ActualBitSide.alice) B0
      hcomp (by simpa using hcost) hpat hcov hterm
  exact (firstPattern_replicate_alice_iff
    (Finset.univ : Finset A) (Finset.univ : Finset B) m P).1 hamb

-- CLAIM-END aux:nowaste-main

end Protocol

end NPCC
