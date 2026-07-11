import Mathlib
import NPCC.Defs
import NPCC.Complexity
import NPCC.Robust
import NPCC.RobustAux
import NPCC.Engine
import NPCC.CoordProjection

set_option linter.unusedVariables false

/-! # §3 protocol control (paper lem:no-waste-near-separation,
lem:failure-to-separate-gives-gap) — typed statements.

The paper's
"deterministic protocol communicating exactly `log |Q|` row bits and zero
column bits" is rendered as an ABSTRACT labeling of rows into `L ≤ |Q|`
parts. The paper's proofs use only the part-count bound; consumers
instantiate `lab` with a protocol's leaf map. Consequently the power-of-two
hypothesis on `|Q|` (resp. `q`) is unnecessary, and `R^in ⊆ Q × X` is not
required. -/

namespace NPCC

open Workspace.Types.CommComplexity Workspace.Types.Interlace

/-- The no-waste conclusion (paper `lem:no-waste-near-separation`): every
part `j` has a unique outer block `i*` whose fiber holds at least
`T₀ − (|Q|−1)·T` rows, all other fibers being `< T`. Shared verbatim by
`no_waste_row_partition` (which proves it under the no-two-heavy-blocks
hypothesis) and `failure_to_separate_gives_gap` (which consumes its
negation). Unregistered supporting definition — judged with the two claims
whose statements depend on it. -/
def NoWasteConclusion {ι X : Type*} [DecidableEq ι] {L : ℕ}
    (Q : Finset ι) (Rin : Finset (ι × X)) (lab : ι × X → Fin L)
    (T₀ T : ℕ) : Prop :=
  ∀ j : Fin L, ∃! i, i ∈ Q ∧
    T₀ - (Q.card - 1) * T ≤ (Rin.filter (fun p => lab p = j ∧ p.1 = i)).card ∧
    ∀ i' ∈ Q, i' ≠ i → (Rin.filter (fun p => lab p = j ∧ p.1 = i')).card < T

private lemma row_fiber_card_eq_sum_label {ι X : Type*} [DecidableEq ι]
    {L : ℕ} (Rin : Finset (ι × X)) (lab : ι × X → Fin L) (i : ι) :
    (Rin.filter (fun p => p.1 = i)).card =
      ∑ j : Fin L, (Rin.filter (fun p => lab p = j ∧ p.1 = i)).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Rin.filter (fun p => p.1 = i)) (t := (Finset.univ : Finset (Fin L)))
    (f := lab) (by intro a _; exact Finset.mem_univ (lab a))
  simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using h

private lemma exists_heavy_label_of_fiber {ι X : Type*} [DecidableEq ι]
    {L T₀ T : ℕ} (Rin : Finset (ι × X)) (lab : ι × X → Fin L) {i : ι}
    (hEqi : T₀ ≤ (Rin.filter (fun p => p.1 = i)).card)
    (hLT : L * T < T₀) :
    ∃ j : Fin L, T ≤ (Rin.filter (fun p => lab p = j ∧ p.1 = i)).card := by
  classical
  by_contra hnone
  have hlt : ∀ j : Fin L, (Rin.filter (fun p => lab p = j ∧ p.1 = i)).card < T := by
    intro j
    exact Nat.lt_of_not_ge (by intro hj; exact hnone ⟨j, hj⟩)
  have hsum := row_fiber_card_eq_sum_label Rin lab i
  have htotal_lt : (Rin.filter (fun p => p.1 = i)).card < T₀ := by
    by_cases hL0 : L = 0
    · subst L
      have htotal0 : (Rin.filter (fun p => p.1 = i)).card = 0 := by
        simpa using hsum
      omega
    · have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
      have hne : (Finset.univ : Finset (Fin L)).Nonempty :=
        ⟨⟨0, hLpos⟩, Finset.mem_univ _⟩
      have hsumlt :
          (∑ j : Fin L, (Rin.filter (fun p => lab p = j ∧ p.1 = i)).card)
            < ∑ _j : Fin L, T := by
        exact Finset.sum_lt_sum_of_nonempty hne (by intro j _; exact hlt j)
      have hsumT : (∑ _j : Fin L, T) = L * T := by
        simp [Finset.sum_const]
      omega
  omega

private lemma pair_finset_card_eq_two {q : ℕ} {i₁ i₂ : Fin q} (hne : i₁ ≠ i₂) :
    ({i₁, i₂} : Finset (Fin q)).card = 2 := by
  simp [hne]

private lemma D_projected_subgame_le {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {q r : ℕ}
    {R : Finset (Fin q × X)} {C : Finset (Fin q → Y)}
    {R' : Finset (Fin r × X)} {C' : Finset (Fin r → Y)}
    (emb : Fin r → Fin q)
    (hRows : ∀ a ∈ R', (emb a.1, a.2) ∈ R)
    (hCols : ∀ c' ∈ C', ∃ c ∈ C, ∀ j : Fin r, c' j = c (emb j)) :
    D (subgame (interlaceFun f r) R' C') ≤
      D (subgame (interlaceFun f q) R C) := by
  classical
  let ρ : {a // a ∈ R'} → {a // a ∈ R} :=
    fun a => ⟨(emb a.1.1, a.1.2), hRows a.1 a.2⟩
  let σ : {c // c ∈ C'} → {c // c ∈ C} :=
    fun c => ⟨(Classical.choose (hCols c.1 c.2)),
      (Classical.choose_spec (hCols c.1 c.2)).1⟩
  have hσ : ∀ (c : {c // c ∈ C'}) (j : Fin r), c.1 j = (σ c).1 (emb j) := by
    intro c j
    exact (Classical.choose_spec (hCols c.1 c.2)).2 j
  have heq :
      subgame (interlaceFun f r) R' C' =
        (fun a c => (subgame (interlaceFun f q) R C) (ρ a) (σ c)) := by
    funext a c
    simp only [subgame, interlaceFun]
    exact congrArg (fun y => f a.1.2 y) (hσ c a.1.1)
  rw [heq]
  exact D_mapNodes_le (subgame (interlaceFun f q) R C) ρ σ

-- CLAIM-BEGIN lem:no-waste-near-separation
/-- Paper `lem:no-waste-near-separation` (No-waste row-only partition), in
the abstract-labeling rendering: if `Rin` is `(Q,T₀)`-equipartitioned-≥,
rows are labeled into `L ≤ |Q|` parts, `|Q|·T < T₀`, and no part holds `T`
rows from each of two distinct outer blocks, then every part has a unique
dominant block per `NoWasteConclusion` (fiber ≥ `T₀ − (|Q|−1)T`, all other
fibers `< T`). Power-of-two `|Q|` and `Rin ⊆ Q × X` are dropped (safe
strengthenings; pure counting). -/
theorem no_waste_row_partition {ι X : Type*} [DecidableEq ι]
    (Q : Finset ι) (Rin : Finset (ι × X)) (T₀ T L : ℕ) (hL : L ≤ Q.card)
    (lab : ι × X → Fin L)
    (hEq : IsEquipartitionedGE Rin Q T₀)
    (hT : Q.card * T < T₀)
    (hNoTwo : ∀ j : Fin L, ¬ ∃ i₁ ∈ Q, ∃ i₂ ∈ Q, i₁ ≠ i₂ ∧
        T ≤ (Rin.filter (fun p => lab p = j ∧ p.1 = i₁)).card ∧
        T ≤ (Rin.filter (fun p => lab p = j ∧ p.1 = i₂)).card) :
    NoWasteConclusion Q Rin lab T₀ T :=
-- CLAIM-END lem:no-waste-near-separation
  by
  classical
  unfold NoWasteConclusion
  let count : Fin L → ι → ℕ :=
    fun j i => (Rin.filter (fun p => lab p = j ∧ p.1 = i)).card
  have hLT : L * T < T₀ := by
    exact lt_of_le_of_lt (Nat.mul_le_mul_right T hL) hT
  have hheavy : ∀ s : {i // i ∈ Q}, ∃ j : Fin L, T ≤ count j s.1 := by
    intro s
    exact exists_heavy_label_of_fiber Rin lab (hEq s.1 s.2) hLT
  choose part hpart using hheavy
  have hpart_inj : Function.Injective part := by
    intro a b hab
    by_contra hne
    have hval_ne : a.1 ≠ b.1 := by
      intro h
      exact hne (Subtype.ext h)
    have hb : T ≤ count (part a) b.1 := by
      simpa [count, hab] using hpart b
    exact hNoTwo (part a)
      ⟨a.1, a.2, b.1, b.2, hval_ne, by simpa [count] using hpart a, by simpa [count] using hb⟩
  have hQleL : Q.card ≤ L := by
    have hcard := Fintype.card_le_of_injective part hpart_inj
    simpa [Fintype.card_coe, Fintype.card_fin] using hcard
  have hLeq : L = Q.card := le_antisymm hL hQleL
  have hbij : Function.Bijective part := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hpart_inj, ?_⟩
    simp [Fintype.card_coe, Fintype.card_fin, hLeq]
  intro j
  obtain ⟨s, hsj⟩ := hbij.2 j
  let i : ι := s.1
  have hiQ : i ∈ Q := s.2
  have hiHeavy : T ≤ count j i := by
    simpa [i, count, hsj] using hpart s
  have hother_label_lt : ∀ j' : Fin L, j' ≠ j → count j' i < T := by
    intro j' hjne
    by_contra hnot
    have hge : T ≤ count j' i := Nat.le_of_not_gt hnot
    obtain ⟨s', hs'j⟩ := hbij.2 j'
    have hs'heavy : T ≤ count j' s'.1 := by
      simpa [count, hs'j] using hpart s'
    have hval_ne : i ≠ s'.1 := by
      intro hval
      have hs_eq : s = s' := Subtype.ext (by simpa [i] using hval)
      apply hjne
      calc
        j' = part s' := hs'j.symm
        _ = part s := by rw [← hs_eq]
        _ = j := hsj
    exact hNoTwo j'
      ⟨i, hiQ, s'.1, s'.2, hval_ne, by simpa [count] using hge, by simpa [count] using hs'heavy⟩
  have hlarge : T₀ - (Q.card - 1) * T ≤ count j i := by
    have hsum := row_fiber_card_eq_sum_label Rin lab i
    have hsum_le :
        (Rin.filter (fun p => p.1 = i)).card ≤ count j i + (Q.card - 1) * T := by
      calc
        (Rin.filter (fun p => p.1 = i)).card
            = ∑ k : Fin L, count k i := by
                simpa [count] using hsum
        _ = (∑ k ∈ (Finset.univ : Finset (Fin L)).erase j, count k i) + count j i := by
                exact (Finset.sum_erase_add (Finset.univ : Finset (Fin L))
                  (fun k => count k i) (Finset.mem_univ j)).symm
        _ ≤ ((Finset.univ : Finset (Fin L)).erase j).card * T + count j i := by
                apply Nat.add_le_add_right
                have hle :
                    (∑ k ∈ (Finset.univ : Finset (Fin L)).erase j, count k i)
                      ≤ ((Finset.univ : Finset (Fin L)).erase j).card • T := by
                  apply Finset.sum_le_card_nsmul
                  intro k hk
                  have hkne : k ≠ j := (Finset.mem_erase.mp hk).1
                  exact le_of_lt (hother_label_lt k hkne)
                simpa [nsmul_eq_mul] using hle
        _ = (L - 1) * T + count j i := by
                rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
                  Fintype.card_fin]
        _ = count j i + (Q.card - 1) * T := by
                rw [hLeq]
                omega
    have hT0le : T₀ ≤ count j i + (Q.card - 1) * T := by
      exact le_trans (hEq i hiQ) hsum_le
    omega
  have hothers : ∀ i' ∈ Q, i' ≠ i → count j i' < T := by
    intro i' hi' hne
    by_contra hnot
    exact hNoTwo j
      ⟨i, hiQ, i', hi', hne.symm, by simpa [count] using hiHeavy,
        by simpa [count] using (Nat.le_of_not_gt hnot)⟩
  have hthreshold_ge_T : T ≤ T₀ - (Q.card - 1) * T := by
    have hQpos : 0 < Q.card := by
      have : (j : ℕ) < L := j.2
      omega
    have hmul : Q.card * T = (Q.card - 1) * T + T := by
      calc
        Q.card * T = ((Q.card - 1) + 1) * T := by
          congr 1
          omega
        _ = (Q.card - 1) * T + T := by
          rw [Nat.add_mul, one_mul]
    have hlt' : (Q.card - 1) * T + T < T₀ := by
      simpa [hmul] using hT
    omega
  refine ExistsUnique.intro i ?_ ?_
  · exact ⟨hiQ, by simpa [count] using hlarge, by simpa [count] using hothers⟩
  · intro i' hi'
    by_cases hEqi : i' = i
    · exact hEqi
    · exfalso
      have hge : T ≤ count j i' := le_trans hthreshold_ge_T (by simpa [count] using hi'.2.1)
      have hlt := hothers i' hi'.1 hEqi
      omega

-- CLAIM-BEGIN lem:failure-to-separate-gives-gap
/-- Paper `lem:failure-to-separate-gives-gap`: for `(δ,b)`-robust `f`
(with `1 ≤ b`, `D f ≥ 2` — the standing F1-adjacent guard), a bracket member
`RC ∈ bracketGE X Y q x y` with `(1/2+δ)² ≤ y ≤ 1`, and a row labeling into
`L ≤ q` parts with `q·T < T₀` for the paper's thresholds
`T₀ = ⌈m·x⌉, T = ⌈2^(1−b)·m⌉` (`m = |X|`): if the no-waste conclusion FAILS,
some part `j` — with the FULL column set (zero column bits) — carries a
subgame of complexity `≥ D f + 1`. Abstract-labeling rendering; power-of-two
`q` dropped (safe strengthening). -/
theorem failure_to_separate_gives_gap {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) (hb : 1 ≤ b) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hD : 2 ≤ D f) (q : ℕ) (hq : 1 ≤ q) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy : (1 / 2 + δ) ^ 2 ≤ y) (hy1 : y ≤ 1)
    (RC : Finset (Fin q × X) × Finset (Fin q → Y))
    (hRC : RC ∈ bracketGE X Y q x y)
    {L : ℕ} (hL : L ≤ q) (lab : Fin q × X → Fin L)
    (hqT : q * ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊
        < ⌈(Fintype.card X : ℝ) * x⌉₊)
    (hfail : ¬ NoWasteConclusion (Finset.univ : Finset (Fin q)) RC.1 lab
        ⌈(Fintype.card X : ℝ) * x⌉₊
        ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊) :
    ∃ j : Fin L, D f + 1 ≤
      D (subgame (interlaceFun f q) (RC.1.filter (fun p => lab p = j)) RC.2) :=
-- CLAIM-END lem:failure-to-separate-gives-gap
  by
  classical
  have _guards : 1 ≤ q ∧ 0 < x ∧ x ≤ 1 ∧ y ≤ 1 := ⟨hq, hx0, hx1, hy1⟩
  set T₀ : ℕ := ⌈(Fintype.card X : ℝ) * x⌉₊ with hT₀
  set T : ℕ := ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊ with hT
  have hEq : IsEquipartitionedGE RC.1 (Finset.univ : Finset (Fin q)) T₀ := by
    simpa [T₀] using hRC.1
  have hL' : L ≤ (Finset.univ : Finset (Fin q)).card := by
    simpa [Finset.card_univ, Fintype.card_fin] using hL
  have hqT' : (Finset.univ : Finset (Fin q)).card * T < T₀ := by
    simpa [Finset.card_univ, Fintype.card_fin, T, T₀] using hqT
  have hnotNoTwo :
      ¬ ∀ j : Fin L, ¬ ∃ i₁ ∈ (Finset.univ : Finset (Fin q)), ∃ i₂ ∈ (Finset.univ : Finset (Fin q)),
        i₁ ≠ i₂ ∧
        T ≤ (RC.1.filter (fun p => lab p = j ∧ p.1 = i₁)).card ∧
        T ≤ (RC.1.filter (fun p => lab p = j ∧ p.1 = i₂)).card := by
    intro hNoTwo
    have hNW := no_waste_row_partition
      (Q := (Finset.univ : Finset (Fin q))) (Rin := RC.1) (T₀ := T₀) (T := T)
      (L := L) hL' lab hEq hqT' hNoTwo
    exact hfail (by simpa [T₀, T] using hNW)
  obtain ⟨j, hjnot⟩ := not_forall.mp hnotNoTwo
  have hjheavy :
      ∃ i₁ ∈ (Finset.univ : Finset (Fin q)), ∃ i₂ ∈ (Finset.univ : Finset (Fin q)),
        i₁ ≠ i₂ ∧
        T ≤ (RC.1.filter (fun p => lab p = j ∧ p.1 = i₁)).card ∧
        T ≤ (RC.1.filter (fun p => lab p = j ∧ p.1 = i₂)).card :=
    of_not_not hjnot
  obtain ⟨i₁, hi₁, i₂, hi₂, hi₁₂, hheavy₁, hheavy₂⟩ := hjheavy
  let Rj : Finset (Fin q × X) := RC.1.filter (fun p => lab p = j)
  let Qpair : Finset (Fin q) := {i₁, i₂}
  have hQpair_card : Qpair.card = 2 := by
    simpa [Qpair] using pair_finset_card_eq_two hi₁₂
  let e : Fin 2 ≃ {i // i ∈ Qpair} := (Qpair.orderIsoOfFin hQpair_card).toEquiv
  have hrow : IsEquipartitionedGE Rj Qpair T := by
    intro i hi
    have hi_cases : i = i₁ ∨ i = i₂ := by
      simpa [Qpair] using hi
    rcases hi_cases with rfl | rfl
    · simpa [Rj, Finset.filter_filter, and_comm, and_left_comm, and_assoc] using hheavy₁
    · simpa [Rj, Finset.filter_filter, and_comm, and_left_comm, and_assoc] using hheavy₂
  have hcol :
      ⌈((Fintype.card Y : ℝ) ^ q) * ((1 / 2 + δ) ^ 2)⌉₊ ≤ RC.2.card := by
    rw [Nat.ceil_le]
    calc
      ((Fintype.card Y : ℝ) ^ q) * ((1 / 2 + δ) ^ 2)
          ≤ ((Fintype.card Y : ℝ) ^ q) * y := by
            exact mul_le_mul_of_nonneg_left hy (by positivity)
      _ ≤ (⌈((Fintype.card Y : ℝ) ^ q) * y⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (RC.2.card : ℝ) := by
            exact_mod_cast hRC.2
  have hxT :
      ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ (1 - b))⌉₊ ≤ T := by
    simp [T, mul_comm]
  obtain ⟨RC', hRC', hRows, hCols⟩ :=
    coord_projection (X := X) (Y := Y) (p := q) (r := 2) (hr := by norm_num)
      (Q := Qpair) e (R := Rj) (C := RC.2) (T := T)
      (x := ((2 : ℝ) ^ (1 - b))) (y := ((1 / 2 + δ) ^ 2))
      hrow hcol hxT
  have hFam_member :
      Dfamily (interlaceFun f 2)
          (bracketGE X Y 2 ((2 : ℝ) ^ (1 - b)) ((1 / 2 + δ) ^ 2))
        ≤ D (subgame (interlaceFun f 2) RC'.1 RC'.2) := by
    unfold Dfamily
    exact Nat.sInf_le ⟨RC', hRC', rfl⟩
  have hproj_le :
      D (subgame (interlaceFun f 2) RC'.1 RC'.2) ≤
        D (subgame (interlaceFun f q) Rj RC.2) :=
    D_projected_subgame_le (f := f) (q := q) (r := 2) (R := Rj) (C := RC.2)
      (R' := RC'.1) (C' := RC'.2) (fun a => (e a).val) hRows hCols
  have hamp := two_copy_amplification h hb hδ0 hδ hD
  have hnat : D f + 1 ≤ D (subgame (interlaceFun f q) Rj RC.2) := by
    have hreal :
        ((D f + 1 : ℕ) : ℝ) ≤ (D (subgame (interlaceFun f q) Rj RC.2) : ℝ) := by
      calc
        ((D f + 1 : ℕ) : ℝ) = (D f : ℝ) + 1 := by norm_num
        _ ≤ (Dfamily (interlaceFun f 2)
              (bracketGE X Y 2 ((2 : ℝ) ^ (1 - b)) ((1 / 2 + δ) ^ 2)) : ℝ) := hamp
        _ ≤ (D (subgame (interlaceFun f 2) RC'.1 RC'.2) : ℝ) := by
              exact_mod_cast hFam_member
        _ ≤ (D (subgame (interlaceFun f q) Rj RC.2) : ℝ) := by
              exact_mod_cast hproj_le
    exact_mod_cast hreal
  refine ⟨j, ?_⟩
  simpa [Rj] using hnat

end NPCC

/-! # §3 protocol-prefix layer for `lem:classical-separation-clean`
(`NPCC.classical_separation`).

The rectangle-threaded architecture uses `FirstKRowBitsOn`, fixed-width
`bitCons/bitHead/bitTail` codes, `prefixCodeRaw`, `rowSubtreeAtRaw`, `pullback`,
`prefixLabelFinQ` with junk→0, `prefixFiber`, and `residualProtocolAt`, with:
* `b : ℝ` with the real rpow densities `⌈(card X)·x⌉₊` and
  `⌈2^(1−b)·(card X)⌉₊` exactly as in `failure_to_separate_gives_gap`;
* namespace placement follows the `Protocol.reindex` precedent in
  `NPCC/Complexity.lean` — everything lives inside `namespace NPCC` with the
  artifact `Protocol` opened and dot-named on it;
* the label is specialized to `q := 2^Q` (the code lands in `Fin (2^Q)`
  directly, no `hq` cast witness needed).

Row-onlyness is a rectangle-threaded predicate:
a syntactic "no `bNode` above depth `k`" conclusion is UNPROVABLE — an
unreachable junk subtree may carry Bob nodes / early leaves without changing
`eval` or `cost`. `FirstKRowBitsOn R C k P` forbids Bob nodes and leaves only
on NONEMPTY current rectangles (surviving branches); it is vacuously true on
empty rectangles. This is the paper's actual meaning and is provable. -/

namespace NPCC

open Workspace.Types.CommComplexity Workspace.Types.Protocol Workspace.Types.Interlace

variable {X Y Z : Type*}

/-! ## Semantic protocol restriction by folding constant queries

`Protocol.restrict R C P` is the D5 surgery vehicle: it walks the protocol tree
relative to the current rectangle. If the queried Alice or Bob bit is constant
on that current side of the rectangle, the transform evaluates the bit and
descends to the forced child without adding a node to the compressed protocol.
If the bit is not constant, the node is retained and the current rectangle is
threaded into the two children. The companion `restrictFoldCount` is deliberately
branch-local: it counts exactly the constant queries folded along one evaluated
input branch. -/

def Protocol.IsRowConstantOn (R : Finset X) (a : X → Bool) (beta : Bool) : Prop :=
  ∀ x, x ∈ R → a x = beta

def Protocol.IsColConstantOn (C : Finset Y) (b : Y → Bool) (beta : Bool) : Prop :=
  ∀ y, y ∈ C → b y = beta

/-- Raw evaluated branch depth of a protocol at a concrete input. This is not
the tree cost: `cost` is the maximum depth of the skeleton, while `evalDepth`
is the length of the single branch actually followed by `(x,y)`. -/
def Protocol.evalDepth : Protocol X Y Z → X → Y → ℕ
  | Protocol.leaf _, _, _ => 0
  | Protocol.aNode a l r, x, y =>
      1 + if a x then Protocol.evalDepth r x y else Protocol.evalDepth l x y
  | Protocol.bNode b l r, x, y =>
      1 + if b y then Protocol.evalDepth r x y else Protocol.evalDepth l x y

/-- Semantic restriction/folding of a protocol on a current rectangle. Constant
queries are evaluated and removed; nonconstant queries remain as nodes and the
rectangle is threaded branch-locally into the children. -/
noncomputable def Protocol.restrict (R : Finset X) (C : Finset Y) :
    Protocol X Y Z → Protocol X Y Z
  | Protocol.leaf z => Protocol.leaf z
  | Protocol.aNode a l r =>
      by
      classical
      exact
        if h : ∃ beta, Protocol.IsRowConstantOn R a beta then
          if Classical.choose h then
            Protocol.restrict R C r
          else
            Protocol.restrict R C l
        else
          Protocol.aNode a
            (Protocol.restrict (R.filter fun x => a x = false) C l)
            (Protocol.restrict (R.filter fun x => a x = true) C r)
  | Protocol.bNode b l r =>
      by
      classical
      exact
        if h : ∃ beta, Protocol.IsColConstantOn C b beta then
          if Classical.choose h then
            Protocol.restrict R C r
          else
            Protocol.restrict R C l
        else
          Protocol.bNode b
            (Protocol.restrict R (C.filter fun y => b y = false) l)
            (Protocol.restrict R (C.filter fun y => b y = true) r)

/-- Number of constant queries folded by `Protocol.restrict` along the evaluated
branch for `(x,y)`. This is intentionally branch-local; no global fixed-bit
property of protocols is asserted. -/
noncomputable def Protocol.restrictFoldCount (R : Finset X) (C : Finset Y) :
    Protocol X Y Z → X → Y → ℕ
  | Protocol.leaf _, _, _ => 0
  | Protocol.aNode a l r, x, y =>
      by
      classical
      exact
        if h : ∃ beta, Protocol.IsRowConstantOn R a beta then
          1 + if Classical.choose h then
            Protocol.restrictFoldCount R C r x y
          else
            Protocol.restrictFoldCount R C l x y
        else
          if a x then
            Protocol.restrictFoldCount (R.filter fun x => a x = true) C r x y
          else
            Protocol.restrictFoldCount (R.filter fun x => a x = false) C l x y
  | Protocol.bNode b l r, x, y =>
      by
      classical
      exact
        if h : ∃ beta, Protocol.IsColConstantOn C b beta then
          1 + if Classical.choose h then
            Protocol.restrictFoldCount R C r x y
          else
            Protocol.restrictFoldCount R C l x y
        else
          if b y then
            Protocol.restrictFoldCount R (C.filter fun y => b y = true) r x y
          else
            Protocol.restrictFoldCount R (C.filter fun y => b y = false) l x y

theorem Protocol.evalDepth_le_cost (P : Protocol X Y Z) (x : X) (y : Y) :
    Protocol.evalDepth P x y ≤ P.cost := by
  induction P with
  | leaf z =>
      simp [Protocol.evalDepth, Protocol.cost]
  | aNode a l r ihl ihr =>
      by_cases hax : a x
      · simp [Protocol.evalDepth, Protocol.cost, hax]
        omega
      · simp [Protocol.evalDepth, Protocol.cost, hax]
        omega
  | bNode b l r ihl ihr =>
      by_cases hby : b y
      · simp [Protocol.evalDepth, Protocol.cost, hby]
        omega
      · simp [Protocol.evalDepth, Protocol.cost, hby]
        omega

theorem Protocol.cost_restrict_le (R : Finset X) (C : Finset Y)
    (P : Protocol X Y Z) :
    (Protocol.restrict R C P).cost ≤ P.cost := by
  induction P generalizing R C with
  | leaf z =>
      simp [Protocol.restrict, Protocol.cost]
  | aNode a l r ihl ihr =>
      unfold Protocol.restrict
      by_cases h : ∃ beta, Protocol.IsRowConstantOn R a beta
      · rw [dif_pos h]
        by_cases hb : Classical.choose h = true
        · rw [if_pos hb]
          have := ihr R C
          simp [Protocol.cost]
          omega
        · rw [if_neg hb]
          have := ihl R C
          simp [Protocol.cost]
          omega
      · rw [dif_neg h]
        simp only [Protocol.cost]
        have hl := ihl (R.filter fun x => a x = false) C
        have hr := ihr (R.filter fun x => a x = true) C
        omega
  | bNode b l r ihl ihr =>
      unfold Protocol.restrict
      by_cases h : ∃ beta, Protocol.IsColConstantOn C b beta
      · rw [dif_pos h]
        by_cases hb : Classical.choose h = true
        · rw [if_pos hb]
          have := ihr R C
          simp [Protocol.cost]
          omega
        · rw [if_neg hb]
          have := ihl R C
          simp [Protocol.cost]
          omega
      · rw [dif_neg h]
        simp only [Protocol.cost]
        have hl := ihl R (C.filter fun y => b y = false)
        have hr := ihr R (C.filter fun y => b y = true)
        omega

theorem Protocol.eval_restrict_of_mem (R : Finset X) (C : Finset Y)
    (P : Protocol X Y Z) {x : X} {y : Y} (hx : x ∈ R) (hy : y ∈ C) :
    (Protocol.restrict R C P).eval x y = P.eval x y := by
  induction P generalizing R C x y with
  | leaf z =>
      simp [Protocol.restrict, Protocol.eval]
  | aNode a l r ihl ihr =>
      unfold Protocol.restrict
      by_cases h : ∃ beta, Protocol.IsRowConstantOn R a beta
      · rw [dif_pos h]
        have hconst := Classical.choose_spec h x hx
        by_cases hb : Classical.choose h = true
        · rw [if_pos hb]
          have hax : a x = true := by simpa [hb] using hconst
          rw [Protocol.eval, hax, if_pos rfl]
          exact ihr R C hx hy
        · rw [if_neg hb]
          have hbeta : Classical.choose h = false := by
            cases hchoose : Classical.choose h <;> simp [hchoose] at hb ⊢
          have hax : a x = false := by simpa [hbeta] using hconst
          rw [Protocol.eval, hax, if_neg (by decide)]
          exact ihl R C hx hy
      · rw [dif_neg h]
        by_cases hax : a x
        · simp only [Protocol.eval, hax, if_pos]
          exact ihr (R.filter fun x => a x = true) C
            (by rw [Finset.mem_filter]; exact ⟨hx, hax⟩) hy
        · have haxf : a x = false := by simp [hax]
          simp [Protocol.eval, haxf]
          exact ihl (R.filter fun x => a x = false) C
            (by rw [Finset.mem_filter]; exact ⟨hx, haxf⟩) hy
  | bNode b l r ihl ihr =>
      unfold Protocol.restrict
      by_cases h : ∃ beta, Protocol.IsColConstantOn C b beta
      · rw [dif_pos h]
        have hconst := Classical.choose_spec h y hy
        by_cases hb : Classical.choose h = true
        · rw [if_pos hb]
          have hby : b y = true := by simpa [hb] using hconst
          rw [Protocol.eval, hby, if_pos rfl]
          exact ihr R C hx hy
        · rw [if_neg hb]
          have hbeta : Classical.choose h = false := by
            cases hchoose : Classical.choose h <;> simp [hchoose] at hb ⊢
          have hby : b y = false := by simpa [hbeta] using hconst
          rw [Protocol.eval, hby, if_neg (by decide)]
          exact ihl R C hx hy
      · rw [dif_neg h]
        by_cases hby : b y
        · simp only [Protocol.eval, hby, if_pos]
          exact ihr R (C.filter fun y => b y = true)
            hx (by rw [Finset.mem_filter]; exact ⟨hy, hby⟩)
        · have hbyf : b y = false := by simp [hby]
          simp [Protocol.eval, hbyf]
          exact ihl R (C.filter fun y => b y = false)
            hx (by rw [Finset.mem_filter]; exact ⟨hy, hbyf⟩)

theorem Protocol.evalDepth_restrict_add_foldCount_of_mem
    (R : Finset X) (C : Finset Y) (P : Protocol X Y Z)
    {x : X} {y : Y} (hx : x ∈ R) (hy : y ∈ C) :
    Protocol.evalDepth (Protocol.restrict R C P) x y
      + Protocol.restrictFoldCount R C P x y
        = Protocol.evalDepth P x y := by
  induction P generalizing R C x y with
  | leaf z =>
      simp [Protocol.restrict, Protocol.restrictFoldCount, Protocol.evalDepth]
  | aNode a l r ihl ihr =>
      unfold Protocol.restrict Protocol.restrictFoldCount
      by_cases h : ∃ beta, Protocol.IsRowConstantOn R a beta
      · rw [dif_pos h, dif_pos h]
        have hconst := Classical.choose_spec h x hx
        by_cases hb : Classical.choose h = true
        · rw [if_pos hb, if_pos hb]
          have hax : a x = true := by simpa [hb] using hconst
          rw [Protocol.evalDepth, hax, if_pos rfl]
          have := ihr R C hx hy
          omega
        · rw [if_neg hb, if_neg hb]
          have hbeta : Classical.choose h = false := by
            cases hchoose : Classical.choose h <;> simp [hchoose] at hb ⊢
          have hax : a x = false := by simpa [hbeta] using hconst
          rw [Protocol.evalDepth, hax, if_neg (by decide)]
          have := ihl R C hx hy
          omega
      · rw [dif_neg h, dif_neg h]
        by_cases hax : a x
        · simp only [Protocol.evalDepth, hax, if_pos]
          have hx' : x ∈ R.filter (fun x => a x = true) := by
            rw [Finset.mem_filter]; exact ⟨hx, hax⟩
          have := ihr (R.filter fun x => a x = true) C hx' hy
          omega
        · have haxf : a x = false := by simp [hax]
          simp [Protocol.evalDepth, haxf]
          have hx' : x ∈ R.filter (fun x => a x = false) := by
            rw [Finset.mem_filter]; exact ⟨hx, haxf⟩
          have := ihl (R.filter fun x => a x = false) C hx' hy
          omega
  | bNode b l r ihl ihr =>
      unfold Protocol.restrict Protocol.restrictFoldCount
      by_cases h : ∃ beta, Protocol.IsColConstantOn C b beta
      · rw [dif_pos h, dif_pos h]
        have hconst := Classical.choose_spec h y hy
        by_cases hb : Classical.choose h = true
        · rw [if_pos hb, if_pos hb]
          have hby : b y = true := by simpa [hb] using hconst
          rw [Protocol.evalDepth, hby, if_pos rfl]
          have := ihr R C hx hy
          omega
        · rw [if_neg hb, if_neg hb]
          have hbeta : Classical.choose h = false := by
            cases hchoose : Classical.choose h <;> simp [hchoose] at hb ⊢
          have hby : b y = false := by simpa [hbeta] using hconst
          rw [Protocol.evalDepth, hby, if_neg (by decide)]
          have := ihl R C hx hy
          omega
      · rw [dif_neg h, dif_neg h]
        by_cases hby : b y
        · simp only [Protocol.evalDepth, hby, if_pos]
          have hy' : y ∈ C.filter (fun y => b y = true) := by
            rw [Finset.mem_filter]; exact ⟨hy, hby⟩
          have := ihr R (C.filter fun y => b y = true) hx hy'
          omega
        · have hbyf : b y = false := by simp [hby]
          simp [Protocol.evalDepth, hbyf]
          have hy' : y ∈ C.filter (fun y => b y = false) := by
            rw [Finset.mem_filter]; exact ⟨hy, hbyf⟩
          have := ihl R (C.filter fun y => b y = false) hx hy'
          omega

theorem Protocol.restrictFoldCount_le_evalDepth_of_mem
    (R : Finset X) (C : Finset Y) (P : Protocol X Y Z)
    {x : X} {y : Y} (hx : x ∈ R) (hy : y ∈ C) :
    Protocol.restrictFoldCount R C P x y ≤ Protocol.evalDepth P x y := by
  have h := Protocol.evalDepth_restrict_add_foldCount_of_mem R C P hx hy
  omega

theorem Protocol.evalDepth_restrict_eq_sub_foldCount_of_mem
    (R : Finset X) (C : Finset Y) (P : Protocol X Y Z)
    {x : X} {y : Y} (hx : x ∈ R) (hy : y ∈ C) :
    Protocol.evalDepth (Protocol.restrict R C P) x y
      = Protocol.evalDepth P x y - Protocol.restrictFoldCount R C P x y := by
  have h := Protocol.evalDepth_restrict_add_foldCount_of_mem R C P hx hy
  omega

theorem Protocol.computes_restrictSub_restrict {X Y : Type*}
    {f : X → Y → Bool} (R : Finset X) (C : Finset Y)
    (P : Protocol X Y Bool) (hP : P.Computes f) :
    (Protocol.restrictSub R C (Protocol.restrict R C P)).Computes (subgame f R C) := by
  intro x y
  rw [Protocol.eval_restrictSub]
  rw [Protocol.eval_restrict_of_mem R C P x.2 y.2]
  exact hP x.1 y.1

theorem D_subgame_le_restrict_cost {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} (R : Finset X) (C : Finset Y)
    (P : Protocol X Y Bool) (hP : P.Computes f) :
    D (subgame f R C) ≤ (Protocol.restrict R C P).cost := by
  have hcomp := Protocol.computes_restrictSub_restrict R C P hP
  have hmem :
      (Protocol.restrictSub R C (Protocol.restrict R C P)).cost
        ∈ AchievableCosts (subgame f R C) :=
    ⟨Protocol.restrictSub R C (Protocol.restrict R C P), rfl, hcomp⟩
  calc
    D (subgame f R C) = sInf (AchievableCosts (subgame f R C)) := rfl
    _ ≤ (Protocol.restrictSub R C (Protocol.restrict R C P)).cost := Nat.sInf_le hmem
    _ = (Protocol.restrict R C P).cost := Protocol.cost_restrictSub R C (Protocol.restrict R C P)

/-! ## Rectangle-threaded row-onlyness -/

/-- `Protocol.FirstKRowBitsOn R C k P` is surviving-branch row-onlyness:
the first `k` communicated bits are Alice (row) bits on every SURVIVING branch.
A `leaf` or `bNode` before depth `k` is forbidden only when the current input
rectangle `(R, C)` is nonempty; it is vacuous on dead rectangles
(`R = ∅ ∨ C = ∅`). The Alice case threads the filtered rectangles into the two
children. Unlike a purely syntactic predicate this is stable under arbitrary
dead subtrees. -/
def Protocol.FirstKRowBitsOn :
    Finset X → Finset Y → ℕ → Protocol X Y Z → Prop
  | _, _, 0, _ => True
  | R, C, _ + 1, Protocol.leaf _ => R = ∅ ∨ C = ∅
  | R, C, k + 1, Protocol.aNode a l r =>
      Protocol.FirstKRowBitsOn (R.filter fun x => a x = false) C k l ∧
      Protocol.FirstKRowBitsOn (R.filter fun x => a x = true) C k r
  | R, C, _ + 1, Protocol.bNode _ _ _ => R = ∅ ∨ C = ∅

/-- `FirstKRowBitsOn` holds vacuously on an empty row rectangle. -/
theorem Protocol.firstKRowBitsOn_of_left_empty
    (C : Finset Y) (k : ℕ) (P : Protocol X Y Z) {R : Finset X} (hR : R = ∅) :
    Protocol.FirstKRowBitsOn R C k P := by
  induction k generalizing R P C with
  | zero => trivial
  | succ n ih =>
      cases P with
      | leaf z => exact Or.inl hR
      | aNode a l r =>
          refine ⟨ih _ _ (by rw [hR]; simp), ih _ _ (by rw [hR]; simp)⟩
      | bNode b l r => exact Or.inl hR

/-- `FirstKRowBitsOn` holds vacuously on an empty column rectangle. -/
theorem Protocol.firstKRowBitsOn_of_right_empty
    (R : Finset X) (k : ℕ) (P : Protocol X Y Z) {C : Finset Y} (hC : C = ∅) :
    Protocol.FirstKRowBitsOn R C k P := by
  induction k generalizing R P with
  | zero => trivial
  | succ n ih =>
      cases P with
      | leaf z => exact Or.inr hC
      | aNode a l r => exact ⟨ih _ _, ih _ _⟩
      | bNode b l r => exact Or.inr hC

/-! ## Fixed-width `Fin (2^k)` transcript codes -/

/-- The distinguished zero element of `Fin (2^k)` (`2^k > 0`). -/
def Protocol.zeroPow2 (k : ℕ) : Fin (2 ^ k) :=
  ⟨0, Nat.two_pow_pos k⟩

/-- Fixed-width cons: `false` selects the lower half, `true` the upper half. -/
def Protocol.bitCons {k : ℕ} (b : Bool) (w : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨(if b then 2 ^ k else 0) + w.1, by
    have hw : w.1 < 2 ^ k := w.2
    have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    cases b <;> simp [pow_succ] <;> omega⟩

/-- The high bit of a width-`k+1` code. -/
def Protocol.bitHead {k : ℕ} (w : Fin (2 ^ (k + 1))) : Bool :=
  decide (2 ^ k ≤ w.1)

/-- The low `k` bits of a width-`k+1` code. -/
def Protocol.bitTail {k : ℕ} (w : Fin (2 ^ (k + 1))) : Fin (2 ^ k) :=
  if h : 2 ^ k ≤ w.1 then
    ⟨w.1 - 2 ^ k, by
      have hw : w.1 < 2 ^ (k + 1) := w.2
      have hp : 0 < 2 ^ k := Nat.two_pow_pos k
      simp only [pow_succ] at hw
      omega⟩
  else
    ⟨w.1, by
      have hnot : ¬ 2 ^ k ≤ w.1 := h
      omega⟩

@[simp] theorem Protocol.bitHead_bitCons {k : ℕ} (b : Bool) (w : Fin (2 ^ k)) :
    Protocol.bitHead (Protocol.bitCons b w) = b := by
  have hw : w.1 < 2 ^ k := w.2
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  cases b with
  | false =>
      have : ((Protocol.bitCons false w : Fin (2 ^ (k + 1))) : ℕ) = w.1 := by
        simp [Protocol.bitCons]
      simp only [Protocol.bitHead, this]
      simp only [decide_eq_false_iff_not, not_le]
      exact hw
  | true =>
      have : ((Protocol.bitCons true w : Fin (2 ^ (k + 1))) : ℕ) = 2 ^ k + w.1 := by
        simp [Protocol.bitCons]
      simp only [Protocol.bitHead, this]
      simp only [decide_eq_true_eq]
      omega

@[simp] theorem Protocol.bitTail_bitCons {k : ℕ} (b : Bool) (w : Fin (2 ^ k)) :
    Protocol.bitTail (Protocol.bitCons b w) = w := by
  have hw : w.1 < 2 ^ k := w.2
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  cases b with
  | false =>
      apply Fin.ext
      have hval : ((Protocol.bitCons false w : Fin (2 ^ (k + 1))) : ℕ) = w.1 := by
        simp [Protocol.bitCons]
      simp only [Protocol.bitTail, hval]
      rw [dif_neg (by omega)]
  | true =>
      apply Fin.ext
      have hval : ((Protocol.bitCons true w : Fin (2 ^ (k + 1))) : ℕ) = 2 ^ k + w.1 := by
        simp [Protocol.bitCons]
      simp only [Protocol.bitTail, hval]
      rw [dif_pos (by omega)]
      simp

theorem Protocol.bitCons_injective {k : ℕ} :
    Function.Injective (fun bw : Bool × Fin (2 ^ k) =>
      Protocol.bitCons bw.1 bw.2) := by
  intro ⟨b₁, w₁⟩ ⟨b₂, w₂⟩ hEq
  simp only at hEq
  have hHead : Protocol.bitHead (Protocol.bitCons b₁ w₁)
      = Protocol.bitHead (Protocol.bitCons b₂ w₂) := by rw [hEq]
  have hTail : Protocol.bitTail (Protocol.bitCons b₁ w₁)
      = Protocol.bitTail (Protocol.bitCons b₂ w₂) := by rw [hEq]
  rw [Protocol.bitHead_bitCons, Protocol.bitHead_bitCons] at hHead
  rw [Protocol.bitTail_bitCons, Protocol.bitTail_bitCons] at hTail
  rw [hHead, hTail]

/-- Raw fixed-width row-prefix code. Descends only through Alice nodes; a `leaf`
or `bNode` before depth `k` returns `0` (junk). On surviving branches
`FirstKRowBitsOn` rules the junk cases out. -/
def Protocol.prefixCodeRaw : (k : ℕ) → Protocol X Y Z → X → Fin (2 ^ k)
  | 0, _, _ => Protocol.zeroPow2 0
  | k + 1, Protocol.aNode a l r, x =>
      Protocol.bitCons (a x) (Protocol.prefixCodeRaw k (if a x then r else l) x)
  | k + 1, Protocol.leaf _, _ => Protocol.zeroPow2 (k + 1)
  | k + 1, Protocol.bNode _ _ _, _ => Protocol.zeroPow2 (k + 1)

/-- Raw row-subtree selected by a fixed-width transcript. Descends only through
Alice nodes per the transcript bits; stops at a leaf/Bob node. The cost lemma is
therefore conditional on `FirstKRowBitsOn` + activity. -/
def Protocol.rowSubtreeAtRaw : (k : ℕ) → Protocol X Y Z → Fin (2 ^ k) → Protocol X Y Z
  | 0, P, _ => P
  | k + 1, Protocol.aNode _ l r, w =>
      if Protocol.bitHead w then
        Protocol.rowSubtreeAtRaw k r (Protocol.bitTail w)
      else
        Protocol.rowSubtreeAtRaw k l (Protocol.bitTail w)
  | k + 1, Protocol.leaf z, _ => Protocol.leaf z
  | k + 1, Protocol.bNode b l r, _ => Protocol.bNode b l r

/-! ## Protocol pullback (row/col transport) -/

/-- Pull a protocol back along row and column maps: precompose each node
predicate. Tree shape (hence cost) is preserved. -/
def Protocol.pullback {X' Y' : Type*} (φ : X' → X) (ψ : Y' → Y) :
    Protocol X Y Z → Protocol X' Y' Z
  | Protocol.leaf z => Protocol.leaf z
  | Protocol.aNode a l r =>
      Protocol.aNode (fun x' => a (φ x'))
        (Protocol.pullback φ ψ l) (Protocol.pullback φ ψ r)
  | Protocol.bNode b l r =>
      Protocol.bNode (fun y' => b (ψ y'))
        (Protocol.pullback φ ψ l) (Protocol.pullback φ ψ r)

@[simp] theorem Protocol.pullback_cost {X' Y' : Type*}
    (φ : X' → X) (ψ : Y' → Y) (P : Protocol X Y Z) :
    (Protocol.pullback φ ψ P).cost = P.cost := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr =>
      simp only [Protocol.pullback, Protocol.cost, ihl, ihr]
  | bNode b l r ihl ihr =>
      simp only [Protocol.pullback, Protocol.cost, ihl, ihr]

@[simp] theorem Protocol.pullback_eval {X' Y' : Type*}
    (φ : X' → X) (ψ : Y' → Y) (P : Protocol X Y Z) (x' : X') (y' : Y') :
    (Protocol.pullback φ ψ P).eval x' y' = P.eval (φ x') (ψ y') := by
  induction P generalizing x' y' with
  | leaf z => rfl
  | aNode a l r ihl ihr =>
      simp only [Protocol.pullback, Protocol.eval, ihl, ihr]
  | bNode b l r ihl ihr =>
      simp only [Protocol.pullback, Protocol.eval, ihl, ihr]

/-! ## Prefix label (junk→0) and fibers, specialized to `q = 2^Q` -/

/-- The label handed to `NoWasteConclusion`, specialized to `q = 2^Q`: the code
lands in `Fin (2^Q)` directly (no `hq` cast). Domain is the full ambient row
type `Fin (2^Q) × X`; a genuine row `p ∈ Rin` gets its transcript code, a junk
row `p ∉ Rin` gets the distinguished label `0`. Harmless because every
`NoWasteConclusion` count filters through `Rin` (junk rows are never counted). -/
noncomputable def Protocol.prefixLabelFinQ
    {Q : ℕ}
    (Rin : Finset (Fin (2 ^ Q) × X))
    (P : Protocol {a : Fin (2 ^ Q) × X // a ∈ Rin} Y Z) :
    Fin (2 ^ Q) × X → Fin (2 ^ Q) :=
  fun a => by
    classical
    exact
      if ha : a ∈ Rin then
        Protocol.prefixCodeRaw Q P ⟨a, ha⟩
      else
        Protocol.zeroPow2 Q

/-- The part-`j` fiber under a labeling (label equality is `Fin (2^Q)`-decidable,
so no `DecidableEq X` is needed). -/
def Protocol.prefixFiber
    {Q : ℕ}
    (Rin : Finset (Fin (2 ^ Q) × X))
    (lab : Fin (2 ^ Q) × X → Fin (2 ^ Q))
    (j : Fin (2 ^ Q)) :
    Finset (Fin (2 ^ Q) × X) :=
  Rin.filter fun a => lab a = j

theorem Protocol.prefixFiber_mem_iff
    {Q : ℕ}
    (Rin : Finset (Fin (2 ^ Q) × X))
    (P : Protocol {a : Fin (2 ^ Q) × X // a ∈ Rin} Y Z)
    (j : Fin (2 ^ Q)) (a : Fin (2 ^ Q) × X) :
    a ∈ Protocol.prefixFiber Rin (Protocol.prefixLabelFinQ Rin P) j ↔
      ∃ ha : a ∈ Rin, Protocol.prefixCodeRaw Q P ⟨a, ha⟩ = j := by
  classical
  unfold Protocol.prefixFiber Protocol.prefixLabelFinQ
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨haRin, hlab⟩
    refine ⟨haRin, ?_⟩
    rw [dif_pos haRin] at hlab
    exact hlab
  · rintro ⟨ha, hcode⟩
    refine ⟨ha, ?_⟩
    rw [dif_pos ha]
    exact hcode

/-! ## Residual protocol on the part-`j` fiber (full column set) -/

/-- Residual protocol for the part labelled `j`, keeping the FULL column set.
On inactive (empty fiber or empty column) parts it is an arbitrary leaf (the
subgame is vacuous on one side); on active parts it is the selected raw
row-subtree pulled back onto the fiber subtype. Specialized to `q = 2^Q`. -/
noncomputable def Protocol.residualProtocolAt
    {Q : ℕ}
    (Rin : Finset (Fin (2 ^ Q) × X))
    (C : Finset Y)
    (P : Protocol {a : Fin (2 ^ Q) × X // a ∈ Rin} {c : Y // c ∈ C} Bool)
    (j : Fin (2 ^ Q)) :
    Protocol
      {a : Fin (2 ^ Q) × X // a ∈ Protocol.prefixFiber Rin (Protocol.prefixLabelFinQ Rin P) j}
      {c : Y // c ∈ C}
      Bool :=
  by
    classical
    exact
      if hactive :
          (Protocol.prefixFiber Rin (Protocol.prefixLabelFinQ Rin P) j).Nonempty
            ∧ C.Nonempty then
        Protocol.pullback
          (fun a => ⟨a.1, (Finset.mem_filter.mp a.2).1⟩)
          (fun c => c)
          (Protocol.rowSubtreeAtRaw Q P j)
      else
        Protocol.leaf false

/-! ## Structural cost / eval lemmas for the raw row-subtree

These two structural inductions are conditional on `FirstKRowBitsOn` plus an
active row/column prefix; the
unconditional versions are false (a junk subtree can stop early). Never invoke
`rowSubtreeAtRaw_cost_le_of_active` before row-onlyness is established. -/

/-- CONDITIONAL cost lemma: under `FirstKRowBitsOn R C k P` with a nonempty
active prefix fiber and nonempty columns, descending `k` row bits leaves a
residual of cost `≤ P.cost − k`. -/
theorem Protocol.rowSubtreeAtRaw_cost_le_of_active
    (R : Finset X) (C : Finset Y) (k : ℕ)
    (P : Protocol X Y Z) (w : Fin (2 ^ k))
    (hrow : Protocol.FirstKRowBitsOn R C k P)
    (hR : (R.filter fun x => Protocol.prefixCodeRaw k P x = w).Nonempty)
    (hC : C.Nonempty) :
    (Protocol.rowSubtreeAtRaw k P w).cost ≤ P.cost - k := by
  induction k generalizing R P with
  | zero => simp [Protocol.rowSubtreeAtRaw]
  | succ n ih =>
      cases P with
      | leaf z =>
          -- FirstKRowBitsOn forces R = ∅ ∨ C = ∅, contradicting hR, hC.
          exfalso
          rcases hrow with hRe | hCe
          · obtain ⟨a, ha⟩ := hR
            rw [Finset.mem_filter] at ha
            rw [hRe] at ha
            exact absurd ha.1 (Finset.notMem_empty a)
          · obtain ⟨c, hc⟩ := hC
            rw [hCe] at hc
            exact absurd hc (Finset.notMem_empty c)
      | bNode b l r =>
          exfalso
          rcases hrow with hRe | hCe
          · obtain ⟨a, ha⟩ := hR
            rw [Finset.mem_filter] at ha
            rw [hRe] at ha
            exact absurd ha.1 (Finset.notMem_empty a)
          · obtain ⟨c, hc⟩ := hC
            rw [hCe] at hc
            exact absurd hc (Finset.notMem_empty c)
      | aNode a l r =>
          obtain ⟨hl, hr⟩ := hrow
          have hcost : (Protocol.aNode a l r).cost = 1 + max l.cost r.cost := rfl
          -- The prefix fiber over w splits by the head bit of w.
          obtain ⟨p, hp⟩ := hR
          rw [Finset.mem_filter] at hp
          -- prefixCodeRaw (n+1) (aNode a l r) p = bitCons (a p) (prefixCodeRaw n (…) p)
          have hcode : Protocol.prefixCodeRaw (n + 1) (Protocol.aNode a l r) p
              = Protocol.bitCons (a p)
                  (Protocol.prefixCodeRaw n (if a p then r else l) p) := rfl
          have hpw := hp.2
          rw [hcode] at hpw
          -- head bit of w = a p
          have hhead : Protocol.bitHead w = a p := by
            rw [← hpw, Protocol.bitHead_bitCons]
          have htail : Protocol.bitTail w
              = Protocol.prefixCodeRaw n (if a p then r else l) p := by
            rw [← hpw, Protocol.bitTail_bitCons]
          simp only [Protocol.rowSubtreeAtRaw]
          by_cases hap : a p
          · -- head = true, descend right
            have hheadw : Protocol.bitHead w = true := by rw [hhead, hap]
            rw [hheadw, if_pos (rfl : (true : Bool) = true)]
            have hRne :
                (( R.filter fun x => a x = true).filter
                    fun x => Protocol.prefixCodeRaw n r x = Protocol.bitTail w).Nonempty := by
              refine ⟨p, ?_⟩
              rw [Finset.mem_filter, Finset.mem_filter]
              refine ⟨⟨hp.1, by rw [hap]⟩, ?_⟩
              rw [htail, if_pos hap]
            have := ih (R.filter fun x => a x = true) r (Protocol.bitTail w) hr hRne
            have hchild : r.cost ≤ max l.cost r.cost := le_max_right _ _
            omega
          · -- head = false, descend left
            have hheadw : Protocol.bitHead w = false := by rw [hhead]; simp [hap]
            rw [hheadw, if_neg (by decide : ¬ ((false : Bool) = true))]
            have hRne :
                (( R.filter fun x => a x = false).filter
                    fun x => Protocol.prefixCodeRaw n l x = Protocol.bitTail w).Nonempty := by
              refine ⟨p, ?_⟩
              rw [Finset.mem_filter, Finset.mem_filter]
              refine ⟨⟨hp.1, by simp [hap]⟩, ?_⟩
              rw [htail, if_neg hap]
            have := ih (R.filter fun x => a x = false) l (Protocol.bitTail w) hl hRne
            have hchild : l.cost ≤ max l.cost r.cost := le_max_left _ _
            omega

/-- CONDITIONAL eval lemma: under `FirstKRowBitsOn R C k P`, for a genuine
`(x,y)` in the current rectangle whose transcript code is `w`, the raw
row-subtree agrees with `P` at `(x,y)`. -/
theorem Protocol.eval_rowSubtreeAtRaw_eq_of_prefix
    (R : Finset X) (C : Finset Y) (k : ℕ)
    (P : Protocol X Y Z) (w : Fin (2 ^ k)) {x : X} {y : Y}
    (hrow : Protocol.FirstKRowBitsOn R C k P)
    (hx : x ∈ R) (hy : y ∈ C)
    (hw : Protocol.prefixCodeRaw k P x = w) :
    (Protocol.rowSubtreeAtRaw k P w).eval x y = P.eval x y := by
  induction k generalizing R P with
  | zero => subst hw; simp [Protocol.rowSubtreeAtRaw]
  | succ n ih =>
      cases P with
      | leaf z =>
          exfalso
          rcases hrow with hRe | hCe
          · rw [hRe] at hx; exact absurd hx (Finset.notMem_empty x)
          · rw [hCe] at hy; exact absurd hy (Finset.notMem_empty y)
      | bNode b l r =>
          exfalso
          rcases hrow with hRe | hCe
          · rw [hRe] at hx; exact absurd hx (Finset.notMem_empty x)
          · rw [hCe] at hy; exact absurd hy (Finset.notMem_empty y)
      | aNode a l r =>
          obtain ⟨hl, hr⟩ := hrow
          have hcode : Protocol.prefixCodeRaw (n + 1) (Protocol.aNode a l r) x
              = Protocol.bitCons (a x)
                  (Protocol.prefixCodeRaw n (if a x then r else l) x) := rfl
          rw [hcode] at hw
          have hhead : Protocol.bitHead w = a x := by
            rw [← hw, Protocol.bitHead_bitCons]
          have htail : Protocol.bitTail w
              = Protocol.prefixCodeRaw n (if a x then r else l) x := by
            rw [← hw, Protocol.bitTail_bitCons]
          simp only [Protocol.rowSubtreeAtRaw, Protocol.eval]
          by_cases hax : a x
          · have hheadw : Protocol.bitHead w = true := by rw [hhead, hax]
            rw [hheadw, if_pos (rfl : (true : Bool) = true),
              hax, if_pos (rfl : (true : Bool) = true)]
            have hxR : x ∈ R.filter fun x => a x = true := by
              rw [Finset.mem_filter]; exact ⟨hx, by rw [hax]⟩
            have hcodeR : Protocol.prefixCodeRaw n r x = Protocol.bitTail w := by
              rw [htail, if_pos hax]
            exact ih (R.filter fun x => a x = true) r (Protocol.bitTail w) hr hxR hcodeR
          · have hax' : a x = false := by simp [hax]
            have hheadw : Protocol.bitHead w = false := by rw [hhead, hax']
            rw [hheadw, if_neg (by decide : ¬ ((false : Bool) = true)),
              hax', if_neg (by decide : ¬ ((false : Bool) = true))]
            have hxR : x ∈ R.filter fun x => a x = false := by
              rw [Finset.mem_filter]; exact ⟨hx, hax'⟩
            have hcodeR : Protocol.prefixCodeRaw n l x = Protocol.bitTail w := by
              rw [htail, if_neg hax]
            exact ih (R.filter fun x => a x = false) l (Protocol.bitTail w) hl hxR hcodeR

/-! ## Residual cost / computes and the D bound on the part-`j` fiber -/

/-- The residual protocol on part `j` has cost `≤ P.cost − Q`. Inactive parts
are a leaf (cost `0`); active parts use `pullback_cost` +
`rowSubtreeAtRaw_cost_le_of_active`, converting the ambient fiber witness into a
subtype-row witness via `prefixFiber_mem_iff`. Conditional on row-onlyness. -/
theorem Protocol.residualProtocolAt_cost_le
    {Q : ℕ}
    (Rin : Finset (Fin (2 ^ Q) × X))
    (C : Finset Y)
    (P : Protocol {a : Fin (2 ^ Q) × X // a ∈ Rin} {c : Y // c ∈ C} Bool)
    (j : Fin (2 ^ Q))
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset {a : Fin (2 ^ Q) × X // a ∈ Rin})
        (Finset.univ : Finset {c : Y // c ∈ C})
        Q P) :
    (Protocol.residualProtocolAt Rin C P j).cost ≤ P.cost - Q := by
  classical
  unfold Protocol.residualProtocolAt
  by_cases hactive :
      (Protocol.prefixFiber Rin (Protocol.prefixLabelFinQ Rin P) j).Nonempty
        ∧ C.Nonempty
  · rw [dif_pos hactive]
    rw [Protocol.pullback_cost]
    -- active row/column witnesses in subtype form
    obtain ⟨a₀, ha₀⟩ := hactive.1
    rw [Protocol.prefixFiber_mem_iff] at ha₀
    obtain ⟨ha₀Rin, hcode₀⟩ := ha₀
    have hRne :
        ((Finset.univ : Finset {a : Fin (2 ^ Q) × X // a ∈ Rin}).filter
            fun a => Protocol.prefixCodeRaw Q P a = j).Nonempty := by
      refine ⟨⟨a₀, ha₀Rin⟩, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcode₀⟩
    obtain ⟨c₀, hc₀⟩ := hactive.2
    have hCne : (Finset.univ : Finset {c : Y // c ∈ C}).Nonempty :=
      ⟨⟨c₀, hc₀⟩, Finset.mem_univ _⟩
    exact Protocol.rowSubtreeAtRaw_cost_le_of_active
      (Finset.univ : Finset {a : Fin (2 ^ Q) × X // a ∈ Rin})
      (Finset.univ : Finset {c : Y // c ∈ C}) Q P j hrow hRne hCne
  · rw [dif_neg hactive]
    simp [Protocol.cost]

/-- The residual protocol on part `j` computes exactly the subgame of `G` on the
part-`j` fiber (full column set). Inactive parts are vacuous on one side;
active parts use `pullback_eval` + `eval_rowSubtreeAtRaw_eq_of_prefix` + `hP`. -/
theorem Protocol.residualProtocolAt_computes
    {Q : ℕ}
    (Rin : Finset (Fin (2 ^ Q) × X))
    (C : Finset Y)
    (G : (Fin (2 ^ Q) × X) → Y → Bool)
    (P : Protocol {a : Fin (2 ^ Q) × X // a ∈ Rin} {c : Y // c ∈ C} Bool)
    (j : Fin (2 ^ Q))
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset {a : Fin (2 ^ Q) × X // a ∈ Rin})
        (Finset.univ : Finset {c : Y // c ∈ C})
        Q P)
    (hP : P.Computes (NPCC.subgame G Rin C)) :
    (Protocol.residualProtocolAt Rin C P j).Computes
      (NPCC.subgame G
        (Protocol.prefixFiber Rin (Protocol.prefixLabelFinQ Rin P) j)
        C) := by
  classical
  unfold Protocol.residualProtocolAt
  by_cases hactive :
      (Protocol.prefixFiber Rin (Protocol.prefixLabelFinQ Rin P) j).Nonempty
        ∧ C.Nonempty
  · rw [dif_pos hactive]
    intro a c
    -- unfold the pullback eval
    rw [Protocol.pullback_eval]
    -- a is a fiber row; its ambient membership and code witness
    have hamem := a.2
    rw [Protocol.prefixFiber_mem_iff] at hamem
    obtain ⟨haRin, hcode⟩ := hamem
    -- the row map lands on ⟨a.1, haRin'⟩ where haRin' = (mem_filter …).1
    set a' : {a : Fin (2 ^ Q) × X // a ∈ Rin} :=
      ⟨a.1, (Finset.mem_filter.mp a.2).1⟩ with ha'
    -- the code of a' equals j
    have hcode' : Protocol.prefixCodeRaw Q P a' = j := hcode
    -- eval of the raw row subtree equals eval of P at (a', c)
    have hxR : a' ∈ (Finset.univ : Finset {a : Fin (2 ^ Q) × X // a ∈ Rin}) :=
      Finset.mem_univ _
    have hyC : c ∈ (Finset.univ : Finset {c : Y // c ∈ C}) := Finset.mem_univ _
    have heval :=
      Protocol.eval_rowSubtreeAtRaw_eq_of_prefix
        (Finset.univ : Finset {a : Fin (2 ^ Q) × X // a ∈ Rin})
        (Finset.univ : Finset {c : Y // c ∈ C}) Q P j hrow hxR hyC hcode'
    rw [heval]
    -- now P.eval a' c = subgame G Rin C a' c = G a'.1 c.1 = G a.1 c.1
    rw [hP a' c]
    simp only [NPCC.subgame, ha']
  · rw [dif_neg hactive]
    -- inactive: fiber empty or C empty ⇒ subgame domain vacuous
    intro a c
    exfalso
    rw [not_and_or] at hactive
    rcases hactive with hfib | hCe
    · exact hfib ⟨a.1, a.2⟩
    · exact hCe ⟨c.1, c.2⟩

/-- The D bound: the part-`j` subgame (full columns) has complexity `≤ P.cost − Q`,
from the residual protocol computing it at that cost (`Nat.sInf_le`). -/
theorem D_prefixFiber_le_of_residual
    {Q : ℕ} [Fintype X] [Fintype Y]
    (Rin : Finset (Fin (2 ^ Q) × X))
    (C : Finset Y)
    (G : (Fin (2 ^ Q) × X) → Y → Bool)
    (P : Protocol {a : Fin (2 ^ Q) × X // a ∈ Rin} {c : Y // c ∈ C} Bool)
    (j : Fin (2 ^ Q))
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset {a : Fin (2 ^ Q) × X // a ∈ Rin})
        (Finset.univ : Finset {c : Y // c ∈ C})
        Q P)
    (hP : P.Computes (NPCC.subgame G Rin C)) :
    D (NPCC.subgame G
        (Protocol.prefixFiber Rin (Protocol.prefixLabelFinQ Rin P) j) C)
      ≤ P.cost - Q := by
  have hcomp :=
    Protocol.residualProtocolAt_computes Rin C G P j hrow hP
  have hcost :=
    Protocol.residualProtocolAt_cost_le Rin C P j hrow
  have hmem :
      (Protocol.residualProtocolAt Rin C P j).cost ∈
        AchievableCosts (NPCC.subgame G
          (Protocol.prefixFiber Rin (Protocol.prefixLabelFinQ Rin P) j) C) :=
    ⟨Protocol.residualProtocolAt Rin C P j, rfl, hcomp⟩
  have hle := Nat.sInf_le hmem
  calc
    D (NPCC.subgame G
        (Protocol.prefixFiber Rin (Protocol.prefixLabelFinQ Rin P) j) C)
        = sInf (AchievableCosts (NPCC.subgame G
            (Protocol.prefixFiber Rin (Protocol.prefixLabelFinQ Rin P) j) C)) := by
          rfl
    _ ≤ (Protocol.residualProtocolAt Rin C P j).cost := hle
    _ ≤ P.cost - Q := hcost

/-- Conjunct (b) closer (`noWaste_of_row_prefix_cost_bound`, specialized to
`q = 2^Q`): given row-onlyness `FirstKRowBitsOn`, the cost budget and the gap,
the no-waste conclusion holds. Proof: assume it fails; `failure_to_separate_gives_gap`
(with `L = q`, `lab = prefixLabelFinQ`) yields a part `j` of subgame complexity
`≥ D f + 1`; but `D_prefixFiber_le_of_residual` + `hcost` bound the SAME subgame
by `P.cost − Q ≤ D f`. Contradiction. -/
theorem noWaste_of_row_prefix_cost_bound
    [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) (hb : 1 ≤ b) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hD : 2 ≤ D f)
    (Q : ℕ) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : (1 / 2 + δ) ^ 2 ≤ y) (hy1 : y ≤ 1)
    (hgap : 2 ^ Q * ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊
        < ⌈(Fintype.card X : ℝ) * x⌉₊)
    (RC : Finset (Fin (2 ^ Q) × X) × Finset (Fin (2 ^ Q) → Y))
    (hRC : RC ∈ bracketGE X Y (2 ^ Q) x y)
    (P : Protocol {a // a ∈ RC.1} {c // c ∈ RC.2} Bool)
    (hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset {a // a ∈ RC.1})
        (Finset.univ : Finset {c // c ∈ RC.2})
        Q P)
    (hPc : P.Computes (subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2))
    (hcost : P.cost ≤ D f + Q) :
    NoWasteConclusion
        (Finset.univ : Finset (Fin (2 ^ Q)))
        RC.1
        (Protocol.prefixLabelFinQ RC.1 P)
        ⌈(Fintype.card X : ℝ) * x⌉₊
        ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊ := by
  classical
  by_contra hfail
  have hq1 : 1 ≤ 2 ^ Q := Nat.one_le_two_pow
  -- failure_to_separate_gives_gap with L = q, lab = prefixLabelFinQ
  obtain ⟨j, hj⟩ :=
    failure_to_separate_gives_gap (f := f) (δ := δ) (b := b)
      h hb hδ0 hδ2 hD (2 ^ Q) hq1 hx0 hx1 hy hy1 RC hRC
      (L := 2 ^ Q) (le_refl _) (Protocol.prefixLabelFinQ RC.1 P) hgap hfail
  -- the gap subgame is the prefixFiber subgame (definitionally the same filter)
  have hDbig :
      D f + 1 ≤
        D (subgame (interlaceFun f (2 ^ Q))
            (Protocol.prefixFiber RC.1 (Protocol.prefixLabelFinQ RC.1 P) j) RC.2) := by
    simpa [Protocol.prefixFiber] using hj
  -- residual upper bound on the SAME subgame
  have hDsmall :
      D (subgame (interlaceFun f (2 ^ Q))
          (Protocol.prefixFiber RC.1 (Protocol.prefixLabelFinQ RC.1 P) j) RC.2)
        ≤ P.cost - Q :=
    D_prefixFiber_le_of_residual RC.1 RC.2 (interlaceFun f (2 ^ Q)) P j hrow hPc
  -- P.cost - Q ≤ D f
  have hPQ : P.cost - Q ≤ D f := by omega
  omega

private theorem delta_le_half_of_sep {δ : ℝ}
    (hδ : δ ≤ 1 / Real.sqrt 2 - 1 / 2) :
    δ ≤ 1 / 2 := by
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_ge_one : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hinv : 1 / Real.sqrt 2 ≤ 1 := by
    rw [one_div]
    exact inv_le_one_of_one_le₀ hsqrt_ge_one
  linarith

private theorem sep_y0_le_y {δ y : ℝ}
    (hy : 2 * (1 / 2 + δ) ^ 2 ≤ y) :
    (1 / 2 + δ) ^ 2 ≤ y := by
  nlinarith [sq_nonneg (1 / 2 + δ)]

private lemma D_subgame_le_of_protocol_agrees
    {A B : Type*} [Fintype A] [Fintype B] {G : A → B → Bool}
    (R : Finset A) (C : Finset B) (P : Protocol A B Bool)
    (hP : ∀ a ∈ R, ∀ c ∈ C, P.eval a c = G a c) :
    D (subgame G R C) ≤ P.cost := by
  classical
  have hcomp : (Protocol.restrictSub R C P).Computes (subgame G R C) := by
    intro a c
    rw [Protocol.eval_restrictSub]
    exact hP a.1 a.2 c.1 c.2
  have hmem :
      (Protocol.restrictSub R C P).cost ∈ AchievableCosts (subgame G R C) :=
    ⟨Protocol.restrictSub R C P, rfl, hcomp⟩
  calc
    D (subgame G R C) = sInf (AchievableCosts (subgame G R C)) := rfl
    _ ≤ (Protocol.restrictSub R C P).cost := Nat.sInf_le hmem
    _ = P.cost := Protocol.cost_restrictSub R C P

private lemma D_projected_nested_subgame_le {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {q r : ℕ}
    {RC : Finset (Fin q × X) × Finset (Fin q → Y)}
    {R : Finset {a // a ∈ RC.1}} {C : Finset {c // c ∈ RC.2}}
    {R' : Finset (Fin r × X)} {C' : Finset (Fin r → Y)}
    (emb : Fin r → Fin q)
    (hRows : ∀ a ∈ R', ∃ hmem : (emb a.1, a.2) ∈ RC.1,
      (⟨(emb a.1, a.2), hmem⟩ : {a // a ∈ RC.1}) ∈ R)
    (hCols : ∀ c' ∈ C', ∃ c ∈ C, ∀ j : Fin r, c' j = c.1 (emb j)) :
    D (subgame (interlaceFun f r) R' C') ≤
      D (subgame (subgame (interlaceFun f q) RC.1 RC.2) R C) := by
  classical
  let ρ : {a // a ∈ R'} → {a // a ∈ R} :=
    fun a =>
      let hs := Classical.choose_spec (hRows a.1 a.2)
      ⟨⟨(emb a.1.1, a.1.2), Classical.choose (hRows a.1 a.2)⟩, hs⟩
  let σ : {c // c ∈ C'} → {c // c ∈ C} :=
    fun c =>
      let hs := Classical.choose_spec (hCols c.1 c.2)
      ⟨Classical.choose (hCols c.1 c.2), hs.1⟩
  have hσ : ∀ (c : {c // c ∈ C'}) (j : Fin r),
      c.1 j = (σ c).1.1 (emb j) := by
    intro c j
    exact (Classical.choose_spec (hCols c.1 c.2)).2 j
  have heq :
      subgame (interlaceFun f r) R' C' =
        (fun a c => (subgame (subgame (interlaceFun f q) RC.1 RC.2) R C)
          (ρ a) (σ c)) := by
    funext a c
    simp only [subgame, interlaceFun]
    exact congrArg (fun y => f a.1.2 y) (hσ c a.1.1)
  rw [heq]
  exact D_mapNodes_le (subgame (subgame (interlaceFun f q) RC.1 RC.2) R C) ρ σ

private def ProjectedBranch {X Y : Type*} [Fintype X] [Fintype Y]
    {q : ℕ}
    (RC : Finset (Fin q × X) × Finset (Fin q → Y))
    (R : Finset {a // a ∈ RC.1}) (C : Finset {c // c ∈ RC.2})
    (r : ℕ) (x y : ℝ) : Prop :=
  ∃ RC' : Finset (Fin r × X) × Finset (Fin r → Y),
    RC' ∈ bracketGE X Y r x y ∧
    ∃ emb : Fin r → Fin q,
      (∀ a ∈ RC'.1, ∃ hmem : (emb a.1, a.2) ∈ RC.1,
        (⟨(emb a.1, a.2), hmem⟩ : {a // a ∈ RC.1}) ∈ R) ∧
      (∀ c' ∈ RC'.2, ∃ c ∈ C, ∀ j : Fin r, c' j = c.1 (emb j))

private lemma ProjectedBranch.of_initial {X Y : Type*} [Fintype X] [Fintype Y]
    {Q : ℕ} {x y : ℝ}
    {RC : Finset (Fin (2 ^ Q) × X) × Finset (Fin (2 ^ Q) → Y)}
    (hRC : RC ∈ bracketGE X Y (2 ^ Q) x y) :
    ProjectedBranch RC
      (Finset.univ : Finset {a // a ∈ RC.1})
      (Finset.univ : Finset {c // c ∈ RC.2})
      (2 ^ Q) x y := by
  classical
  refine ⟨RC, hRC, id, ?_, ?_⟩
  · intro a ha
    exact ⟨ha, Finset.mem_univ _⟩
  · intro c hc
    exact ⟨⟨c, hc⟩, Finset.mem_univ _, fun _ => rfl⟩

private lemma ProjectedBranch.lower_bound {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {q r w : ℕ} {x y x₀ y₀ : ℝ}
    {RC : Finset (Fin q × X) × Finset (Fin q → Y)}
    {R : Finset {a // a ∈ RC.1}} {C : Finset {c // c ∈ RC.2}}
    (hbranch : ProjectedBranch RC R C r x y)
    (hfamily :
      D f + w ≤ Dfamily (interlaceFun f r) (bracketGE X Y r x₀ y₀))
    (hx : x₀ ≤ x) (hy : y₀ ≤ y) :
    D f + w ≤
      D (subgame (subgame (interlaceFun f q) RC.1 RC.2) R C) := by
  classical
  obtain ⟨RC', hRC', emb, hRows, hCols⟩ := hbranch
  have hRC₀ : RC' ∈ bracketGE X Y r x₀ y₀ :=
    bracketGE.anti_mono_params r hx hy hRC'
  have hFam_member :
      Dfamily (interlaceFun f r) (bracketGE X Y r x₀ y₀) ≤
        D (subgame (interlaceFun f r) RC'.1 RC'.2) := by
    unfold Dfamily
    exact Nat.sInf_le ⟨RC', hRC₀, rfl⟩
  have hproj :
      D (subgame (interlaceFun f r) RC'.1 RC'.2) ≤
        D (subgame (subgame (interlaceFun f q) RC.1 RC.2) R C) :=
    D_projected_nested_subgame_le (f := f) (q := q) (r := r) (RC := RC)
      (R := R) (C := C) (R' := RC'.1) (C' := RC'.2) emb hRows hCols
  exact le_trans hfamily (le_trans hFam_member hproj)

private lemma exists_bool_filter_large_side {α : Type*} (s : Finset α) (p : α → Bool) :
    ∃ b : Bool, s.card ≤ 2 * (s.filter fun a => p a = b).card := by
  classical
  set st : Finset α := s.filter fun a => p a = true
  set sf : Finset α := s.filter fun a => ¬ p a = true
  have hsplit : st.card + sf.card = s.card := by
    simpa [st, sf] using
      (Finset.card_filter_add_card_filter_not (s := s) (p := fun a => p a = true))
  by_cases hle : sf.card ≤ st.card
  · refine ⟨true, ?_⟩
    have : s.card ≤ 2 * st.card := by omega
    simpa [st] using this
  · refine ⟨false, ?_⟩
    have htf : st.card ≤ sf.card := le_of_not_ge hle
    have : s.card ≤ 2 * sf.card := by omega
    simpa [sf] using this

private lemma ceil_half_le_of_ceil_le_two_mul {A y : ℝ} {n : ℕ}
    (h : ⌈A * y⌉₊ ≤ 2 * n) :
    ⌈A * (y / 2)⌉₊ ≤ n := by
  rw [Nat.ceil_le]
  have hreal : A * y ≤ (2 * n : ℕ) := le_trans (Nat.le_ceil _) (by exact_mod_cast h)
  norm_num at hreal ⊢
  nlinarith

/-! ### The two structural propagation constructions (feed the branch induction).

`projectedBranch_column_half` : a column (Bob) bit halves the columns; the child
keeping the larger half still carries a projected branch at column density `y/2`
(same level, same rows). `projectedBranch_row_split` : the balanced-row-split
argument — under the cost budget an `aNode` at a live rectangle of level `2^(k+1)`
sends each child a projected branch at level `2^k`, half the row density, full
columns. Both are the paper's induction step; extracted so the branch recursion
consumes them. -/

/-- Column-halving. Given a projected branch at level `r` and column density `y`
on `(R, C)`, and a Bob predicate `bp`, the larger-column child (for some
`β : Bool`, columns `C.filter (bp ·.val = β)`) still carries a projected branch
at density `y/2`. -/
private lemma projectedBranch_column_half {X Y : Type*} [Fintype X] [Fintype Y]
    {q r : ℕ} {x y : ℝ}
    {RC : Finset (Fin q × X) × Finset (Fin q → Y)}
    {R : Finset {a // a ∈ RC.1}} {C : Finset {c // c ∈ RC.2}}
    (hbranch : ProjectedBranch RC R C r x y)
    (bp : {c // c ∈ RC.2} → Bool) :
    ∃ β : Bool,
      ProjectedBranch RC R (C.filter fun c => bp c = β) r x (y / 2) := by
  classical
  obtain ⟨RC', hRC', emb, hRows, hCols⟩ := hbranch
  let bp' : (Fin r → Y) → Bool :=
    fun c' => if hmem : c' ∈ RC'.2 then bp (Classical.choose (hCols c' hmem)) else false
  obtain ⟨β, hlarge⟩ := exists_bool_filter_large_side RC'.2 bp'
  refine ⟨β, (RC'.1, RC'.2.filter fun c' => bp' c' = β), ?_, emb, ?_, ?_⟩
  · refine ⟨hRC'.1, ?_⟩
    have hceil :
        ⌈((Fintype.card Y : ℝ) ^ r) * y⌉₊ ≤
          2 * (RC'.2.filter fun c' => bp' c' = β).card := by
      exact le_trans hRC'.2 hlarge
    exact ceil_half_le_of_ceil_le_two_mul
      (A := (Fintype.card Y : ℝ) ^ r) (y := y) hceil
  · intro a ha
    exact hRows a ha
  · intro c' hc'
    rw [Finset.mem_filter] at hc'
    let c : {c // c ∈ RC.2} := Classical.choose (hCols c' hc'.1)
    have hcSpec : c ∈ C ∧ ∀ j : Fin r, c' j = c.1 (emb j) :=
      Classical.choose_spec (hCols c' hc'.1)
    have hbp : bp c = β := by
      have hbp' : bp' c' = β := hc'.2
      change (if hmem : c' ∈ RC'.2 then bp (Classical.choose (hCols c' hmem))
        else false) = β at hbp'
      simpa [c, hc'.1] using hbp'
    exact ⟨c, Finset.mem_filter.mpr ⟨hcSpec.1, hbp⟩, hcSpec.2⟩

private lemma two_rpow_nat_sub_eq_density_half (n : ℕ) (b : ℝ) :
    (2 : ℝ) ^ ((n : ℝ) - b) =
      ((2 : ℝ) ^ n) * (2 : ℝ) ^ (1 - b) / 2 := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hpow1 : (2 : ℝ) ^ (1 - b) = 2 * (2 : ℝ) ^ (-b) := by
    calc
      (2 : ℝ) ^ (1 - b) = (2 : ℝ) ^ (1 + -b) := by ring_nf
      _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-b) := by
        rw [Real.rpow_add h2pos]
      _ = 2 * (2 : ℝ) ^ (-b) := by norm_num
  calc
    (2 : ℝ) ^ ((n : ℝ) - b) = (2 : ℝ) ^ ((n : ℝ) + -b) := by ring_nf
    _ = (2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ (-b) := by
      rw [Real.rpow_add h2pos]
    _ = ((2 : ℝ) ^ n) * (2 : ℝ) ^ (-b) := by
      rw [Real.rpow_natCast]
    _ = ((2 : ℝ) ^ n) * (2 : ℝ) ^ (1 - b) / 2 := by
      rw [hpow1]
      ring

/-- Balanced-row-split. Given a projected branch at level `2^(k+1)` and row
density `x` on `(R, C)`, plus the cost/complexity budget ruling out an
unbalanced split, an Alice predicate `ap` sends each row-filtered child a
projected branch at level `2^k` and density `x/2` (full columns). Packaged as the
pair for the two children. -/
private lemma projectedBranch_row_split {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) (hb : 1 ≤ b) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hD : 2 ≤ D f)
    {Q : ℕ} {k : ℕ} {x y : ℝ}
    {RC : Finset (Fin (2 ^ Q) × X) × Finset (Fin (2 ^ Q) → Y)}
    {R : Finset {a // a ∈ RC.1}} {C : Finset {c // c ∈ RC.2}}
    (hk1 : 1 ≤ k)
    (hbranch : ProjectedBranch RC R C (2 ^ (k + 1)) x y)
    (hxlb : ((2 : ℝ) ^ (k + 1)) * (2 : ℝ) ^ (1 - b) ≤ x) (hx1 : x ≤ 1)
    (hylb : (1 / 2 + δ) ^ 2 ≤ y)
    (hkb : ((k : ℝ) + 1) ≤ b)
    (ap : {a // a ∈ RC.1} → Bool)
    (l r : Protocol {a // a ∈ RC.1} {c // c ∈ RC.2} Bool)
    (hcostL : l.cost ≤ D f + k) (hcostR : r.cost ≤ D f + k)
    (hagreeL : ∀ a ∈ (R.filter fun a => ap a = false), ∀ c ∈ C,
        l.eval a c = subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2 a c)
    (hagreeR : ∀ a ∈ (R.filter fun a => ap a = true), ∀ c ∈ C,
        r.eval a c = subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2 a c) :
    ProjectedBranch RC (R.filter fun a => ap a = false) C (2 ^ k) (x / 2) y ∧
    ProjectedBranch RC (R.filter fun a => ap a = true) C (2 ^ k) (x / 2) y := by
  classical
  have _hx1 : x ≤ 1 := hx1
  obtain ⟨RC', hRC', emb, hRows, hCols⟩ := hbranch
  let T : ℕ := ⌈(Fintype.card X : ℝ) * (x / 2)⌉₊
  let liftRow (a : Fin (2 ^ (k + 1)) × X) (ha : a ∈ RC'.1) :
      {a // a ∈ RC.1} :=
    ⟨(emb a.1, a.2), Classical.choose (hRows a ha)⟩
  let rowBit (a : Fin (2 ^ (k + 1)) × X) : Bool :=
    if ha : a ∈ RC'.1 then ap (liftRow a ha) else false
  let block (j : Fin (2 ^ (k + 1))) (β : Bool) :
      Finset (Fin (2 ^ (k + 1)) × X) :=
    RC'.1.filter fun a => a.1 = j ∧ rowBit a = β
  have hsideChoice : ∀ j : Fin (2 ^ (k + 1)), ∃ β : Bool,
      (RC'.1.filter fun a => a.1 = j).card ≤ 2 * (block j β).card := by
    intro j
    obtain ⟨β, hβ⟩ :=
      exists_bool_filter_large_side (RC'.1.filter fun a => a.1 = j) rowBit
    refine ⟨β, ?_⟩
    simpa [block, Finset.filter_filter, and_left_comm, and_assoc] using hβ
  let side : Fin (2 ^ (k + 1)) → Bool := fun j => Classical.choose (hsideChoice j)
  have hsideSpec : ∀ j : Fin (2 ^ (k + 1)),
      (RC'.1.filter fun a => a.1 = j).card ≤ 2 * (block j (side j)).card :=
    fun j => Classical.choose_spec (hsideChoice j)
  have hblockLarge : ∀ j : Fin (2 ^ (k + 1)), T ≤ (block j (side j)).card := by
    intro j
    have hparent :
        ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ (RC'.1.filter fun a => a.1 = j).card :=
      hRC'.1 j (Finset.mem_univ j)
    have hceil :
        ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ 2 * (block j (side j)).card :=
      le_trans hparent (hsideSpec j)
    simpa [T] using
      ceil_half_le_of_ceil_le_two_mul
        (A := (Fintype.card X : ℝ)) (y := x) (n := (block j (side j)).card) hceil
  let S : Bool → Finset (Fin (2 ^ (k + 1))) :=
    fun β => (Finset.univ : Finset (Fin (2 ^ (k + 1)))).filter fun j => side j = β
  have buildBranch :
      ∀ {r0 : ℕ} (β : Bool) (W : Finset (Fin (2 ^ (k + 1)))),
        W ⊆ S β → W.card = r0 → 0 < r0 →
        ProjectedBranch RC (R.filter fun a => ap a = β) C r0 (x / 2) y := by
    intro r0 β W hWsub hWcard hr0
    let RowsAmb : Finset (Fin (2 ^ (k + 1)) × X) :=
      RC'.1.filter fun a => a.1 ∈ W ∧ rowBit a = β
    have hrowAmb : IsEquipartitionedGE RowsAmb W T := by
      intro j hjW
      have hsidej : side j = β := by
        have hjS := hWsub hjW
        simpa [S] using hjS
      have hblockβ : T ≤ (block j β).card := by
        simpa [hsidej] using hblockLarge j
      refine le_trans hblockβ (Finset.card_le_card ?_)
      intro a ha
      rw [Finset.mem_filter] at ha ⊢
      refine ⟨?_, ha.2.1⟩
      rw [Finset.mem_filter]
      exact ⟨ha.1, ⟨by simpa [ha.2.1] using hjW, ha.2.2⟩⟩
    let e : Fin r0 ≃ {q // q ∈ W} := (W.orderIsoOfFin hWcard).toEquiv
    obtain ⟨M, hM, hRowsM, hColsM⟩ :=
      coord_projection (X := X) (Y := Y) (p := 2 ^ (k + 1)) (r := r0)
        hr0 (Q := W) e (R := RowsAmb) (C := RC'.2) (T := T)
        (x := x / 2) (y := y) hrowAmb hRC'.2 (by simp [T])
    refine ⟨M, hM, fun j => emb ((e j).val), ?_, ?_⟩
    · intro a ha
      have hpa :
          (((e a.1).val, a.2) : Fin (2 ^ (k + 1)) × X) ∈ RowsAmb :=
        hRowsM a ha
      have hpa' := hpa
      rw [Finset.mem_filter] at hpa'
      have hparent :
          (((e a.1).val, a.2) : Fin (2 ^ (k + 1)) × X) ∈ RC'.1 :=
        hpa'.1
      let hmem : (emb ((e a.1).val), a.2) ∈ RC.1 :=
        Classical.choose (hRows (((e a.1).val, a.2) : Fin (2 ^ (k + 1)) × X) hparent)
      have hRmem :
          (⟨(emb ((e a.1).val), a.2), hmem⟩ : {a // a ∈ RC.1}) ∈ R := by
        simpa [hmem] using
          (Classical.choose_spec
            (hRows (((e a.1).val, a.2) : Fin (2 ^ (k + 1)) × X) hparent))
      have hbit : rowBit (((e a.1).val, a.2) : Fin (2 ^ (k + 1)) × X) = β :=
        hpa'.2.2
      have hapβ :
          ap (⟨(emb ((e a.1).val), a.2), hmem⟩ : {a // a ∈ RC.1}) = β := by
        simpa [rowBit, liftRow, hparent, hmem] using hbit
      exact ⟨hmem, Finset.mem_filter.mpr ⟨hRmem, hapβ⟩⟩
    · intro c' hc'
      obtain ⟨c0, hc0, hc0eq⟩ := hColsM c' hc'
      obtain ⟨c, hc, hceq⟩ := hCols c0 hc0
      refine ⟨c, hc, ?_⟩
      intro j
      calc
        c' j = c0 ((e j).val) := hc0eq j
        _ = c.1 (emb ((e j).val)) := hceq ((e j).val)
  have hxDensity :
      (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) - b) ≤ x / 2 := by
    have hdiv :
        ((2 : ℝ) ^ (k + 1)) * (2 : ℝ) ^ (1 - b) / 2 ≤ x / 2 :=
      div_le_div_of_nonneg_right hxlb (by norm_num : (0 : ℝ) ≤ 2)
    calc
      (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) - b)
          = ((2 : ℝ) ^ (k + 1)) * (2 : ℝ) ^ (1 - b) / 2 := by
            simpa using two_rpow_nat_sub_eq_density_half (k + 1) b
      _ ≤ x / 2 := hdiv
  have hfamPlus :
      D f + (k + 1) ≤ Dfamily (interlaceFun f (2 ^ k + 1))
        (bracketGE X Y (2 ^ k + 1) ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) - b))
          ((1 / 2 + δ) ^ 2)) := by
    have hk2 : 2 ≤ k + 1 := by omega
    have hkb' : ((k + 1 : ℕ) : ℝ) ≤ b := by
      simpa [Nat.cast_add, Nat.cast_one] using hkb
    have hkm1 : (k + 1) - 1 = k := by omega
    simpa [hkm1] using plus_one_family h hb hδ0 hδ2 hD (k + 1) hk2 hkb'
  have side_card_le : ∀ β : Bool, (S β).card ≤ 2 ^ k := by
    intro β
    by_contra hle
    have hlarge : 2 ^ k + 1 ≤ (S β).card :=
      Nat.succ_le_of_lt (Nat.lt_of_not_ge hle)
    obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hlarge
    have hbrW :
        ProjectedBranch RC (R.filter fun a => ap a = β) C (2 ^ k + 1) (x / 2) y :=
      buildBranch (r0 := 2 ^ k + 1) β W hWsub hWcard (Nat.succ_pos _)
    have hlow :
        D f + (k + 1) ≤
          D (subgame (subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2)
            (R.filter fun a => ap a = β) C) :=
      ProjectedBranch.lower_bound hbrW hfamPlus hxDensity hylb
    let Pβ : Protocol {a // a ∈ RC.1} {c // c ∈ RC.2} Bool := if β then r else l
    have hcostβ : Pβ.cost ≤ D f + k := by
      cases β <;> simp [Pβ, hcostL, hcostR]
    have hagreeβ :
        ∀ a ∈ (R.filter fun a => ap a = β), ∀ c ∈ C,
          Pβ.eval a c = subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2 a c := by
      cases β
      · simpa [Pβ] using hagreeL
      · simpa [Pβ] using hagreeR
    have hup0 :
        D (subgame (subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2)
          (R.filter fun a => ap a = β) C) ≤ Pβ.cost :=
      D_subgame_le_of_protocol_agrees (R.filter fun a => ap a = β) C Pβ hagreeβ
    have hup :
        D (subgame (subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2)
          (R.filter fun a => ap a = β) C) ≤ D f + k :=
      le_trans hup0 hcostβ
    omega
  have hsumSides : (S false).card + (S true).card = 2 ^ (k + 1) := by
    have hsplit :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (2 ^ (k + 1)))))
        (p := fun j => side j = true)
    have hfalseComp :
        ((Finset.univ : Finset (Fin (2 ^ (k + 1)))).filter
          (fun j => ¬ side j = true)) = S false := by
      ext j
      cases hsj : side j <;> simp [S, hsj]
    have htrueComp :
        ((Finset.univ : Finset (Fin (2 ^ (k + 1)))).filter
          (fun j => side j = true)) = S true := by
      rfl
    rw [htrueComp, hfalseComp] at hsplit
    have hcard :
        (Finset.univ : Finset (Fin (2 ^ (k + 1)))).card = 2 ^ (k + 1) := by
      simp
    omega
  have hpowSplit : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
    rw [pow_succ]
    omega
  have hSfalse : (S false).card = 2 ^ k := by
    have hf := side_card_le false
    have ht := side_card_le true
    omega
  have hStrue : (S true).card = 2 ^ k := by
    have hf := side_card_le false
    have ht := side_card_le true
    omega
  refine ⟨?_, ?_⟩
  · exact buildBranch false (S false) (by intro j hj; exact hj) hSfalse (Nat.two_pow_pos k)
  · exact buildBranch true (S true) (by intro j hj; exact hj) hStrue (Nat.two_pow_pos k)

/-- The branch induction (paper `lem:classical-separation-clean` conclusion (a)),
strengthened form: a projected branch at level `2^k`, agreement of `P'` with the
game on the rectangle, and the cost budget give `FirstKRowBitsOn R C k P'`. -/
private theorem firstKRowBitsOn_of_branch {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) (hb : 1 ≤ b) (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hD : 2 ≤ D f)
    {Q : ℕ}
    {RC : Finset (Fin (2 ^ Q) × X) × Finset (Fin (2 ^ Q) → Y)}
    {y : ℝ} (hylb2 : 2 * (1 / 2 + δ) ^ 2 ≤ y) :
    ∀ (k : ℕ) (x : ℝ)
      (R : Finset {a // a ∈ RC.1}) (C : Finset {c // c ∈ RC.2})
      (P' : Protocol {a // a ∈ RC.1} {c // c ∈ RC.2} Bool),
      ProjectedBranch RC R C (2 ^ k) x y →
      ((2 : ℝ) ^ k) * (2 : ℝ) ^ (1 - b) ≤ x → x ≤ 1 → ((k : ℝ) ≤ b) →
      P'.cost ≤ D f + k →
      (∀ a ∈ R, ∀ c ∈ C,
        P'.eval a c = subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2 a c) →
      Protocol.FirstKRowBitsOn R C k P' := by
  have hylb : (1 / 2 + δ) ^ 2 ≤ y := by nlinarith [sq_nonneg (1 / 2 + δ)]
  -- weak-from-strong density: 2^n·2^(-b) ≤ 2^n·2^(1-b) ≤ x (since 2^(-b) ≤ 2^(1-b))
  have hweak_of_strong : ∀ (n : ℕ) (xx : ℝ),
      ((2 : ℝ) ^ n) * (2 : ℝ) ^ (1 - b) ≤ xx →
      ((2 : ℝ) ^ n) * (2 : ℝ) ^ (-b) ≤ xx := by
    intro n xx hstr
    have hmono : (2 : ℝ) ^ (-b) ≤ (2 : ℝ) ^ (1 - b) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hpow_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
    calc ((2 : ℝ) ^ n) * (2 : ℝ) ^ (-b)
        ≤ ((2 : ℝ) ^ n) * (2 : ℝ) ^ (1 - b) := by
          exact mul_le_mul_of_nonneg_left hmono hpow_nonneg
      _ ≤ xx := hstr
  intro k
  induction k with
  | zero =>
      intro x R C P' _ _ _ _ _ _
      trivial
  | succ k ih =>
      intro x R C P' hbranch hxlb hx1 hkb hcost hagree
      -- If either side of the rectangle is empty, FirstKRowBitsOn is vacuous.
      by_cases hRempty : R = ∅
      · exact Protocol.firstKRowBitsOn_of_left_empty C (k + 1) P' hRempty
      by_cases hCempty : C = ∅
      · exact Protocol.firstKRowBitsOn_of_right_empty R (k + 1) P' hCempty
      have hRne : R.Nonempty := Finset.nonempty_of_ne_empty hRempty
      have hCne : C.Nonempty := Finset.nonempty_of_ne_empty hCempty
      -- numeric: (k+1 : ℝ) ≤ b for power_of_two_lower at w = k+1
      have hk1b : ((k : ℝ) + 1) ≤ b := by exact_mod_cast hkb
      -- The lower bound on this rectangle: D f + (k+1) ≤ D (nested subgame R C).
      have hlow :
          D f + (k + 1) ≤
            D (subgame (subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2) R C) := by
        have hfam :
            D f + (k + 1) ≤ Dfamily (interlaceFun f (2 ^ (k + 1)))
              (bracketGE X Y (2 ^ (k + 1))
                ((2 : ℝ) ^ (k + 1 : ℕ) * (2 : ℝ) ^ (-b)) ((1 / 2 + δ) ^ 2)) :=
          power_of_two_lower h hb hδ0 hδ2 hD (k + 1) (Nat.one_le_iff_ne_zero.mpr (by omega))
            (by exact_mod_cast hk1b)
        have hxk : ((2 : ℝ) ^ (k + 1 : ℕ) * (2 : ℝ) ^ (-b)) ≤ x := by
          have heq : ((2 : ℝ) ^ (k + 1)) = ((2 : ℝ) ^ (k + 1 : ℕ)) := by norm_num
          rw [← heq]; exact hweak_of_strong (k + 1) x hxlb
        exact ProjectedBranch.lower_bound hbranch hfam hxk hylb
      -- Case on P'.
      cases P' with
      | leaf z =>
          exfalso
          -- leaf agrees with the game on R × C ⇒ D(nested) ≤ cost = 0
          have hup :
              D (subgame (subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2) R C)
                ≤ (Protocol.leaf z : Protocol _ _ Bool).cost :=
            D_subgame_le_of_protocol_agrees R C (Protocol.leaf z) hagree
          simp only [Protocol.cost] at hup
          omega
      | bNode bp l r =>
          exfalso
          -- column bit: larger half keeps a projected branch at y/2 ≥ y0
          obtain ⟨β, hbr2⟩ :=
            projectedBranch_column_half hbranch bp
          -- child protocol Pβ and its agreement on (R, C_big)
          set Cbig : Finset {c // c ∈ RC.2} := C.filter fun c => bp c = β with hCbig
          set Pβ : Protocol {a // a ∈ RC.1} {c // c ∈ RC.2} Bool :=
            if β then r else l with hPβ
          have hagreeβ :
              ∀ a ∈ R, ∀ c ∈ Cbig,
                Pβ.eval a c
                  = subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2 a c := by
            intro a ha c hc
            rw [Finset.mem_filter] at hc
            have hbpc : bp c = β := hc.2
            have hval : (Protocol.bNode bp l r).eval a c = Pβ.eval a c := by
              simp only [Protocol.eval, hPβ]
              cases β <;> simp [hbpc]
            rw [← hval]
            exact hagree a ha c hc.1
          have hcostβ : Pβ.cost ≤ D f + k := by
            have hc2 : (Protocol.bNode bp l r).cost = 1 + max l.cost r.cost := rfl
            have : Pβ.cost ≤ max l.cost r.cost := by
              rw [hPβ]; cases β
              · exact le_max_left _ _
              · exact le_max_right _ _
            omega
          -- lower bound on (R, Cbig) at y/2 ≥ y0
          have hyhalf : (1 / 2 + δ) ^ 2 ≤ y / 2 := by linarith [hylb2]
          have hlow2 :
              D f + (k + 1) ≤
                D (subgame (subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2) R Cbig) := by
            have hfam :
                D f + (k + 1) ≤ Dfamily (interlaceFun f (2 ^ (k + 1)))
                  (bracketGE X Y (2 ^ (k + 1))
                    ((2 : ℝ) ^ (k + 1 : ℕ) * (2 : ℝ) ^ (-b)) ((1 / 2 + δ) ^ 2)) :=
              power_of_two_lower h hb hδ0 hδ2 hD (k + 1) (Nat.one_le_iff_ne_zero.mpr (by omega))
                (by exact_mod_cast hk1b)
            have hxk : ((2 : ℝ) ^ (k + 1 : ℕ) * (2 : ℝ) ^ (-b)) ≤ x := by
              have heq : ((2 : ℝ) ^ (k + 1)) = ((2 : ℝ) ^ (k + 1 : ℕ)) := by norm_num
              rw [← heq]; exact hweak_of_strong (k + 1) x hxlb
            exact ProjectedBranch.lower_bound hbr2 hfam hxk hyhalf
          have hup :
              D (subgame (subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2) R Cbig)
                ≤ Pβ.cost :=
            D_subgame_le_of_protocol_agrees R Cbig Pβ hagreeβ
          omega
      | aNode ap l r =>
          -- child costs and per-branch agreement (needed for both k=0 and k≥1)
          have hcostL : l.cost ≤ D f + k := by
            have : (Protocol.aNode ap l r).cost = 1 + max l.cost r.cost := rfl
            have hle : l.cost ≤ max l.cost r.cost := le_max_left _ _
            omega
          have hcostR : r.cost ≤ D f + k := by
            have : (Protocol.aNode ap l r).cost = 1 + max l.cost r.cost := rfl
            have hle : r.cost ≤ max l.cost r.cost := le_max_right _ _
            omega
          have hagreeL :
              ∀ a ∈ (R.filter fun a => ap a = false), ∀ c ∈ C,
                l.eval a c = subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2 a c := by
            intro a ha c hc
            rw [Finset.mem_filter] at ha
            have hval : (Protocol.aNode ap l r).eval a c = l.eval a c := by
              simp [Protocol.eval, ha.2]
            rw [← hval]; exact hagree a ha.1 c hc
          have hagreeR :
              ∀ a ∈ (R.filter fun a => ap a = true), ∀ c ∈ C,
                r.eval a c = subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2 a c := by
            intro a ha c hc
            rw [Finset.mem_filter] at ha
            have hval : (Protocol.aNode ap l r).eval a c = r.eval a c := by
              simp [Protocol.eval, ha.2]
            rw [← hval]; exact hagree a ha.1 c hc
          -- k = 0: both children are at level 0, FirstKRowBitsOn is `True`.
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0
            exact ⟨trivial, trivial⟩
          -- k ≥ 1: balanced row split gives each child a projected branch at 2^k.
          have hk1 : 1 ≤ k := hkpos
          have hxlb2 : ((2 : ℝ) ^ k) * (2 : ℝ) ^ (1 - b) ≤ x / 2 := by
            have hhalf : ((2 : ℝ) ^ (k + 1)) * (2 : ℝ) ^ (1 - b) / 2
                = ((2 : ℝ) ^ k) * (2 : ℝ) ^ (1 - b) := by
              rw [pow_succ]; ring
            rw [← hhalf]; linarith [hxlb]
          have hx1' : x / 2 ≤ 1 := by linarith
          have hkb' : ((k : ℝ) ≤ b) := by
            exact_mod_cast (by linarith [hk1b] : (k : ℝ) ≤ b)
          obtain ⟨hbrF, hbrT⟩ :=
            projectedBranch_row_split h hb hδ0 hδ2 hD hk1 hbranch hxlb hx1 hylb
              (by exact_mod_cast hk1b) ap l r hcostL hcostR hagreeL hagreeR
          refine ⟨?_, ?_⟩
          · exact ih (x / 2) (R.filter fun a => ap a = false) C l hbrF
              hxlb2 hx1' hkb' hcostL hagreeL
          · exact ih (x / 2) (R.filter fun a => ap a = true) C r hbrT
              hxlb2 hx1' hkb' hcostR hagreeR

private theorem classical_separation_row_only
    {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) (hb : 1 ≤ b) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / Real.sqrt 2 - 1 / 2)
    (hD : 2 ≤ D f)
    (Q : ℕ) (hQ : 1 ≤ Q)
    {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : 2 * (1 / 2 + δ) ^ 2 ≤ y) (hy1 : y ≤ 1)
    (hqx : (2 ^ Q : ℝ) * (2 : ℝ) ^ (-b) ≤ x)
    (hgap : 2 ^ Q * ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊
        < ⌈(Fintype.card X : ℝ) * x⌉₊)
    (RC : Finset (Fin (2 ^ Q) × X) × Finset (Fin (2 ^ Q) → Y))
    (hRC : RC ∈ bracketGE X Y (2 ^ Q) x y)
    (P : Protocol {a // a ∈ RC.1} {c // c ∈ RC.2} Bool)
    (hPc : P.Computes (subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2))
    (hcost : P.cost ≤ D f + Q) :
    Protocol.FirstKRowBitsOn
        (Finset.univ : Finset {a // a ∈ RC.1})
        (Finset.univ : Finset {c // c ∈ RC.2})
        Q P := by
  classical
  have hδ2 : δ ≤ 1 / 2 := delta_le_half_of_sep hδ
  have hy0 : (1 / 2 + δ) ^ 2 ≤ y := sep_y0_le_y hy
  -- Degenerate empty case: card X = 0 ⇒ RC.1 = ∅ ⇒ the row set is vacuously row-only.
  by_cases hXcard : Fintype.card X = 0
  · have hXempty : IsEmpty X := Fintype.card_eq_zero_iff.mp hXcard
    have hR1 : RC.1 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      rintro ⟨i, xx⟩ _
      exact hXempty.elim xx
    have hunivempty : (Finset.univ : Finset {a // a ∈ RC.1}) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      rintro ⟨a, ha⟩ _
      rw [hR1] at ha
      exact absurd ha (Finset.notMem_empty a)
    exact Protocol.firstKRowBitsOn_of_left_empty _ Q P hunivempty
  have hXpos : 1 ≤ Fintype.card X := Nat.one_le_iff_ne_zero.mpr hXcard
  -- Strong row-density from hgap (card X ≥ 1, x > 0): 2^Q · 2^(1-b) ≤ x.
  have hxstrong : ((2 : ℝ) ^ Q) * (2 : ℝ) ^ (1 - b) ≤ x := by
    have hmpos : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hXpos
    have hmx0 : (0 : ℝ) ≤ (Fintype.card X : ℝ) * x := by positivity
    have hgapN : 2 ^ Q * ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊ + 1
        ≤ ⌈(Fintype.card X : ℝ) * x⌉₊ := hgap
    have hgapR : ((2 : ℝ) ^ Q) * (⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊ : ℝ) + 1
        ≤ (⌈(Fintype.card X : ℝ) * x⌉₊ : ℝ) := by exact_mod_cast hgapN
    have hlo : ((2 : ℝ) ^ Q) * ((2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ))
        ≤ ((2 : ℝ) ^ Q) * (⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊ : ℝ) :=
      mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by positivity)
    have hup : (⌈(Fintype.card X : ℝ) * x⌉₊ : ℝ) ≤ (Fintype.card X : ℝ) * x + 1 :=
      le_of_lt (Nat.ceil_lt_add_one hmx0)
    have hchain : ((2 : ℝ) ^ Q) * ((2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ))
        ≤ (Fintype.card X : ℝ) * x := by linarith
    have hchain' : (((2 : ℝ) ^ Q) * (2 : ℝ) ^ (1 - b)) * (Fintype.card X : ℝ)
        ≤ x * (Fintype.card X : ℝ) := by nlinarith [hchain]
    have := le_of_mul_le_mul_right hchain' hmpos
    linarith
  -- 2^Q ≤ 2^b, i.e. (Q:ℝ) ≤ b, from hqx and x ≤ 1
  have hQb : (Q : ℝ) ≤ b := by
    have hxle : ((2 : ℝ) ^ Q) * (2 : ℝ) ^ (-b) ≤ 1 := le_trans hqx hx1
    have hcast : ((2 : ℝ) ^ Q) = (2 : ℝ) ^ (Q : ℝ) := by rw [Real.rpow_natCast]
    rw [hcast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hxle
    have h1 : (2 : ℝ) ^ ((Q : ℝ) + (-b)) ≤ (2 : ℝ) ^ (0 : ℝ) := by
      rw [Real.rpow_zero]; exact hxle
    have := (Real.rpow_le_rpow_left_iff (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)).mp h1
    linarith
  -- initial branch at level 2^Q, density x
  have hbranch0 :
      ProjectedBranch RC (Finset.univ : Finset {a // a ∈ RC.1})
        (Finset.univ : Finset {c // c ∈ RC.2}) (2 ^ Q) x y :=
    ProjectedBranch.of_initial hRC
  -- agreement of P with the game on univ × univ
  have hagree0 :
      ∀ a ∈ (Finset.univ : Finset {a // a ∈ RC.1}),
        ∀ c ∈ (Finset.univ : Finset {c // c ∈ RC.2}),
          P.eval a c
            = subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2 a c := by
    intro a _ c _; exact hPc a c
  exact firstKRowBitsOn_of_branch h hb hδ0 hδ2 hD hy Q x
    (Finset.univ) (Finset.univ) P hbranch0 hxstrong hx1 hQb hcost hagree0

/-! ## The claim for `lem:classical-separation-clean` -/

-- CLAIM-BEGIN lem:classical-separation-clean
/-- Paper `lem:classical-separation-clean` (`NPCC.classical_separation`), in a
rectangle-threaded rendering: a syntactic "row-only above depth `Q`"
conclusion is UNPROVABLE (unreachable dead subtrees may hold Bob nodes / early
leaves without changing `eval` or `cost`), so conclusion (a) is the
surviving-branch predicate `FirstKRowBitsOn`: Bob nodes / leaves are forbidden only on
nonempty rectangles. `q = 2^Q` is rendered literally (no `Real.logb`
bit-count); the label lands in `Fin (2^Q)` directly via `prefixLabelFinQ`
(junk rows → block `0`, harmless since every no-waste count filters through
`RC.1`). The δ endpoint `δ ≤ 1/√2 − 1/2` is kept SYMBOLIC; `δ < 1/2` is derived
inside the proof (`1/√2 − 1/2 < 1/2`), not added as a hypothesis. -/
theorem classical_separation {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) (hb : 1 ≤ b) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / Real.sqrt 2 - 1 / 2)
    (hD : 2 ≤ D f)
    (Q : ℕ) (hQ : 1 ≤ Q)
    {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy : 2 * (1 / 2 + δ) ^ 2 ≤ y) (hy1 : y ≤ 1)
    (hqx : (2 ^ Q : ℝ) * (2 : ℝ) ^ (-b) ≤ x)
    (hgap : 2 ^ Q * ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊
        < ⌈(Fintype.card X : ℝ) * x⌉₊)
    (RC : Finset (Fin (2 ^ Q) × X) × Finset (Fin (2 ^ Q) → Y))
    (hRC : RC ∈ bracketGE X Y (2 ^ Q) x y)
    (P : Protocol {a // a ∈ RC.1} {c // c ∈ RC.2} Bool)
    (hPc : P.Computes (subgame (interlaceFun f (2 ^ Q)) RC.1 RC.2))
    (hcost : P.cost ≤ D f + Q) :
    Protocol.FirstKRowBitsOn
        (Finset.univ : Finset {a // a ∈ RC.1})
        (Finset.univ : Finset {c // c ∈ RC.2})
        Q P
    ∧ NoWasteConclusion
        (Finset.univ : Finset (Fin (2 ^ Q)))
        RC.1
        (Protocol.prefixLabelFinQ RC.1 P)
        ⌈(Fintype.card X : ℝ) * x⌉₊
        ⌈(2 : ℝ) ^ (1 - b) * (Fintype.card X : ℝ)⌉₊ :=
-- CLAIM-END lem:classical-separation-clean
  by
  classical
  have hδ2 : δ ≤ 1 / 2 := delta_le_half_of_sep hδ
  have hy0 : (1 / 2 + δ) ^ 2 ≤ y := sep_y0_le_y hy
  have hrow :
      Protocol.FirstKRowBitsOn
        (Finset.univ : Finset {a // a ∈ RC.1})
        (Finset.univ : Finset {c // c ∈ RC.2})
        Q P :=
    classical_separation_row_only (f := f) (δ := δ) (b := b)
      h hb hδ0 hδ hD Q hQ hx0 hx1 hy hy1 hqx hgap RC hRC P hPc hcost
  refine ⟨hrow, ?_⟩
  exact noWaste_of_row_prefix_cost_bound (f := f) (δ := δ) (b := b)
    h hb hδ0 hδ2 hD Q hx0 hx1 hy0 hy1 hgap RC hRC P hrow hPc hcost

end NPCC


/-! ## Actual-branch protocol frontier layer

Generic semantic branch vocabulary promoted from the staged no-waste-lift candidate.
-/

namespace NPCC

open Workspace.Types.Protocol

namespace Protocol

/-- The party whose bit is read at one actual communication step. -/
inductive ActualBitSide where
  | alice
  | bob
deriving DecidableEq, Repr

/-- Fixed-width transcript followed by an actual protocol path, allowing Alice
and Bob nodes to interleave. If the tree ends too early, the remaining code is
the distinguished junk zero. Branch objects below require active paths, so the
junk case cannot witness a live branch. -/
def actualPrefixCodeRaw {A B Z : Type*} :
    (k : Nat) -> Protocol A B Z -> A -> B -> Fin (2 ^ k)
  | 0, _, _, _ => Protocol.zeroPow2 0
  | k + 1, Protocol.leaf _, _, _ => Protocol.zeroPow2 (k + 1)
  | k + 1, Protocol.aNode q l r, a, b =>
      Protocol.bitCons (q a)
        (actualPrefixCodeRaw k (if q a then r else l) a b)
  | k + 1, Protocol.bNode q l r, a, b =>
      Protocol.bitCons (q b)
        (actualPrefixCodeRaw k (if q b then r else l) a b)

/-- The raw subtree selected by an actual fixed-width transcript. -/
def actualSubtreeAtRaw {A B Z : Type*} :
    (k : Nat) -> Protocol A B Z -> Fin (2 ^ k) -> Protocol A B Z
  | 0, P, _ => P
  | k + 1, Protocol.leaf z, _ => Protocol.leaf z
  | k + 1, Protocol.aNode _ l r, w =>
      if Protocol.bitHead w then
        actualSubtreeAtRaw k r (Protocol.bitTail w)
      else
        actualSubtreeAtRaw k l (Protocol.bitTail w)
  | k + 1, Protocol.bNode _ l r, w =>
      if Protocol.bitHead w then
        actualSubtreeAtRaw k r (Protocol.bitTail w)
      else
        actualSubtreeAtRaw k l (Protocol.bitTail w)

/-- Party labels seen along the first `k` actual protocol bits. -/
def actualSideListRaw {A B Z : Type*} :
    (k : Nat) -> Protocol A B Z -> A -> B -> List ActualBitSide
  | 0, _, _, _ => []
  | k + 1, Protocol.leaf _, _, _ => []
  | k + 1, Protocol.aNode q l r, a, b =>
      ActualBitSide.alice ::
        actualSideListRaw k (if q a then r else l) a b
  | k + 1, Protocol.bNode q l r, a, b =>
      ActualBitSide.bob ::
        actualSideListRaw k (if q b then r else l) a b

/-- A semantic branch of `P` after `t` actual bits. The depth parameter is not
phantom: the branch carries its actual transcript, party trace, reachability
clauses, the actual selected subtree restricted to its rectangle, the live
`Protocol.restrict` ledger on that rectangle, and residual correctness for the
subgame of `G`. -/
structure BranchAt {A B : Type*} (P : Protocol A B Bool)
    (G : A -> B -> Bool) (t : Nat) where
  rows : Finset A
  cols : Finset B
  transcript : Fin (2 ^ t)
  sideTrace : List ActualBitSide
  residual : Protocol {a // a ∈ rows} {b // b ∈ cols} Bool
  rows_nonempty : rows.Nonempty
  cols_nonempty : cols.Nonempty
  sideTrace_length : sideTrace.length = t
  sideTrace_eq :
    ∀ (a : A) (ha : a ∈ rows) (b : B) (hb : b ∈ cols),
      Protocol.actualSideListRaw t P a b = sideTrace
  rectangle_transcript :
    ∀ (a : A) (ha : a ∈ rows) (b : B) (hb : b ∈ cols),
      Protocol.actualPrefixCodeRaw t P a b = transcript
  rows_reachable :
    ∀ a : A, a ∈ rows ↔
      ∃ b : B, b ∈ cols ∧
        Protocol.actualPrefixCodeRaw t P a b = transcript
  cols_reachable :
    ∀ b : B, b ∈ cols ↔
      ∃ a : A, a ∈ rows ∧
        Protocol.actualPrefixCodeRaw t P a b = transcript
  residual_eq_actual :
    residual =
      Protocol.restrictSub rows cols
        (Protocol.actualSubtreeAtRaw t P transcript)
  residual_eval_eq :
    ∀ (a : {a // a ∈ rows}) (b : {b // b ∈ cols}),
      residual.eval a b = P.eval a.val b.val
  residual_computes :
    residual.Computes (subgame G rows cols)
  restricted_residual_computes :
    (Protocol.restrictSub rows cols (Protocol.restrict rows cols P)).Computes
      (subgame G rows cols)
  restrict_evalDepth_ledger :
    ∀ (a : A) (ha : a ∈ rows) (b : B) (hb : b ∈ cols),
      Protocol.evalDepth (Protocol.restrict rows cols P) a b
        + Protocol.restrictFoldCount rows cols P a b =
          Protocol.evalDepth P a b
  actualDepth_eq :
    ∀ (a : A) (ha : a ∈ rows) (b : B) (hb : b ∈ cols),
      Protocol.evalDepth P a b =
        t + Protocol.evalDepth residual ⟨a, ha⟩ ⟨b, hb⟩
  cost_after_actualBits :
    t + residual.cost <= P.cost

/-- Genuine refinement of semantic branches. In addition to rectangle
containment, the deeper branch must agree with the shallower transcript on the
same actual inputs, and the deeper residual must be the descendant computation
of the shallower residual on that refined rectangle. -/
structure BranchExtends {A B : Type*} {P : Protocol A B Bool}
    {G : A -> B -> Bool} {t u : Nat}
    (b0 : BranchAt P G t) (b1 : BranchAt P G u) : Prop where
  depth_le : t <= u
  rows_sub : b1.rows ⊆ b0.rows
  cols_sub : b1.cols ⊆ b0.cols
  transcript_compatible :
    ∀ (a : A) (ha : a ∈ b1.rows) (b : B) (hb : b ∈ b1.cols),
      Protocol.actualPrefixCodeRaw t P a b = b0.transcript ∧
        Protocol.actualPrefixCodeRaw u P a b = b1.transcript
  residual_eval_refines :
    ∀ (a : A) (ha : a ∈ b1.rows) (b : B) (hb : b ∈ b1.cols),
      b0.residual.eval ⟨a, rows_sub ha⟩ ⟨b, cols_sub hb⟩ =
        b1.residual.eval ⟨a, ha⟩ ⟨b, hb⟩
  residual_depth_refines :
    ∀ (a : A) (ha : a ∈ b1.rows) (b : B) (hb : b ∈ b1.cols),
      Protocol.evalDepth b0.residual
          ⟨a, rows_sub ha⟩ ⟨b, cols_sub hb⟩ =
        (u - t) + Protocol.evalDepth b1.residual ⟨a, ha⟩ ⟨b, hb⟩

end Protocol

end NPCC

/-! ## Branch constructors from row-prefix frontiers

This block connects the row-prefix frontier used by `FirstKRowBitsOn` to the
promoted semantic `BranchAt` vocabulary.  The public constructor below is
specialized to the all-live rectangle, matching the separated protocols after
their row and column sets have been moved into subtypes.  For arbitrary proper
rectangles, the global `rows_reachable` and `cols_reachable` fields of
`BranchAt` require additional exact-reachability side conditions.
-/

namespace NPCC

open Workspace.Types.Protocol

namespace Protocol

variable {A B Z : Type*}

@[simp] theorem evalDepth_restrictSub {A B Z : Type*}
    (R : Finset A) (C : Finset B) (P : Protocol A B Z)
    (a : {a // a ∈ R}) (b : {b // b ∈ C}) :
    Protocol.evalDepth (Protocol.restrictSub R C P) a b =
      Protocol.evalDepth P a.val b.val := by
  induction P with
  | leaf z => rfl
  | aNode q l r ihl ihr =>
      simp only [Protocol.restrictSub, Protocol.evalDepth]
      by_cases hq : q a.val
      · rw [if_pos hq, if_pos hq, ihr]
      · rw [if_neg hq, if_neg hq, ihl]
  | bNode q l r ihl ihr =>
      simp only [Protocol.restrictSub, Protocol.evalDepth]
      by_cases hq : q b.val
      · rw [if_pos hq, if_pos hq, ihr]
      · rw [if_neg hq, if_neg hq, ihl]

theorem actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
    (R : Finset A) (C : Finset B) (k : Nat)
    (P : Protocol A B Z) {a : A} {b : B}
    (hrow : Protocol.FirstKRowBitsOn R C k P)
    (ha : a ∈ R) (hb : b ∈ C) :
    Protocol.actualPrefixCodeRaw k P a b =
      Protocol.prefixCodeRaw k P a := by
  induction k generalizing R P with
  | zero =>
      rfl
  | succ n ih =>
      cases P with
      | leaf z =>
          exfalso
          rcases hrow with hR | hC
          · rw [hR] at ha
            exact absurd ha (Finset.notMem_empty a)
          · rw [hC] at hb
            exact absurd hb (Finset.notMem_empty b)
      | bNode q l r =>
          exfalso
          rcases hrow with hR | hC
          · rw [hR] at ha
            exact absurd ha (Finset.notMem_empty a)
          · rw [hC] at hb
            exact absurd hb (Finset.notMem_empty b)
      | aNode q l r =>
          obtain ⟨hl, hr⟩ := hrow
          simp only [Protocol.actualPrefixCodeRaw, Protocol.prefixCodeRaw]
          by_cases hq : q a
          · have ha' : a ∈ R.filter fun x => q x = true := by
              rw [Finset.mem_filter]
              exact ⟨ha, hq⟩
            rw [hq]
            simpa using congrArg (Protocol.bitCons true)
              (ih (R.filter fun x => q x = true) r hr ha')
          · have hqf : q a = false := by simp [hq]
            have ha' : a ∈ R.filter fun x => q x = false := by
              rw [Finset.mem_filter]
              exact ⟨ha, hqf⟩
            rw [hqf]
            simpa using congrArg (Protocol.bitCons false)
              (ih (R.filter fun x => q x = false) l hl ha')

theorem actualSideListRaw_eq_replicate_alice_of_firstKRowBitsOn
    (R : Finset A) (C : Finset B) (k : Nat)
    (P : Protocol A B Z) {a : A} {b : B}
    (hrow : Protocol.FirstKRowBitsOn R C k P)
    (ha : a ∈ R) (hb : b ∈ C) :
    Protocol.actualSideListRaw k P a b =
      List.replicate k Protocol.ActualBitSide.alice := by
  induction k generalizing R P with
  | zero =>
      rfl
  | succ n ih =>
      cases P with
      | leaf z =>
          exfalso
          rcases hrow with hR | hC
          · rw [hR] at ha
            exact absurd ha (Finset.notMem_empty a)
          · rw [hC] at hb
            exact absurd hb (Finset.notMem_empty b)
      | bNode q l r =>
          exfalso
          rcases hrow with hR | hC
          · rw [hR] at ha
            exact absurd ha (Finset.notMem_empty a)
          · rw [hC] at hb
            exact absurd hb (Finset.notMem_empty b)
      | aNode q l r =>
          obtain ⟨hl, hr⟩ := hrow
          simp only [Protocol.actualSideListRaw, List.replicate]
          by_cases hq : q a
          · rw [if_pos hq]
            have ha' : a ∈ R.filter fun x => q x = true := by
              rw [Finset.mem_filter]
              exact ⟨ha, hq⟩
            rw [ih (R.filter fun x => q x = true) r hr ha']
          · have hqf : q a = false := by simp [hq]
            rw [if_neg hq]
            have ha' : a ∈ R.filter fun x => q x = false := by
              rw [Finset.mem_filter]
              exact ⟨ha, hqf⟩
            rw [ih (R.filter fun x => q x = false) l hl ha']

theorem actualSubtreeAtRaw_eq_rowSubtreeAtRaw_of_firstKRowBitsOn
    (R : Finset A) (C : Finset B) (k : Nat)
    (P : Protocol A B Z) (w : Fin (2 ^ k))
    (hrow : Protocol.FirstKRowBitsOn R C k P)
    (hR : (R.filter fun a => Protocol.prefixCodeRaw k P a = w).Nonempty)
    (hC : C.Nonempty) :
    Protocol.actualSubtreeAtRaw k P w =
      Protocol.rowSubtreeAtRaw k P w := by
  induction k generalizing R P with
  | zero =>
      rfl
  | succ n ih =>
      cases P with
      | leaf z =>
          exfalso
          rcases hrow with hRe | hCe
          · obtain ⟨a, ha⟩ := hR
            rw [Finset.mem_filter] at ha
            rw [hRe] at ha
            exact absurd ha.1 (Finset.notMem_empty a)
          · obtain ⟨b, hb⟩ := hC
            rw [hCe] at hb
            exact absurd hb (Finset.notMem_empty b)
      | bNode q l r =>
          exfalso
          rcases hrow with hRe | hCe
          · obtain ⟨a, ha⟩ := hR
            rw [Finset.mem_filter] at ha
            rw [hRe] at ha
            exact absurd ha.1 (Finset.notMem_empty a)
          · obtain ⟨b, hb⟩ := hC
            rw [hCe] at hb
            exact absurd hb (Finset.notMem_empty b)
      | aNode q l r =>
          obtain ⟨hl, hr⟩ := hrow
          obtain ⟨a0, ha0⟩ := hR
          rw [Finset.mem_filter] at ha0
          have hcode : Protocol.prefixCodeRaw (n + 1) (Protocol.aNode q l r) a0
              = Protocol.bitCons (q a0)
                  (Protocol.prefixCodeRaw n (if q a0 then r else l) a0) := rfl
          have hw := ha0.2
          rw [hcode] at hw
          have hhead : Protocol.bitHead w = q a0 := by
            rw [← hw, Protocol.bitHead_bitCons]
          have htail : Protocol.bitTail w =
              Protocol.prefixCodeRaw n (if q a0 then r else l) a0 := by
            rw [← hw, Protocol.bitTail_bitCons]
          simp only [Protocol.actualSubtreeAtRaw, Protocol.rowSubtreeAtRaw]
          by_cases hq : q a0
          · have hheadw : Protocol.bitHead w = true := by rw [hhead, hq]
            rw [hheadw, if_pos rfl, if_pos rfl]
            have hR' :
                ((R.filter fun a => q a = true).filter
                    fun a => Protocol.prefixCodeRaw n r a = Protocol.bitTail w).Nonempty := by
              refine ⟨a0, ?_⟩
              rw [Finset.mem_filter, Finset.mem_filter]
              exact ⟨⟨ha0.1, hq⟩, by rw [htail, if_pos hq]⟩
            exact ih (R.filter fun a => q a = true) r (Protocol.bitTail w) hr hR'
          · have hqf : q a0 = false := by simp [hq]
            have hheadw : Protocol.bitHead w = false := by rw [hhead, hqf]
            rw [hheadw, if_neg (by decide), if_neg (by decide)]
            have hR' :
                ((R.filter fun a => q a = false).filter
                    fun a => Protocol.prefixCodeRaw n l a = Protocol.bitTail w).Nonempty := by
              refine ⟨a0, ?_⟩
              rw [Finset.mem_filter, Finset.mem_filter]
              exact ⟨⟨ha0.1, hqf⟩, by rw [htail, if_neg hq]⟩
            exact ih (R.filter fun a => q a = false) l (Protocol.bitTail w) hl hR'

theorem actualSubtreeAtRaw_cost_le_of_firstKRowBitsOn
    (R : Finset A) (C : Finset B) (k : Nat)
    (P : Protocol A B Z) (w : Fin (2 ^ k))
    (hrow : Protocol.FirstKRowBitsOn R C k P)
    (hR : (R.filter fun a => Protocol.prefixCodeRaw k P a = w).Nonempty)
    (hC : C.Nonempty) :
    (Protocol.actualSubtreeAtRaw k P w).cost ≤ P.cost - k := by
  rw [Protocol.actualSubtreeAtRaw_eq_rowSubtreeAtRaw_of_firstKRowBitsOn
    R C k P w hrow hR hC]
  exact Protocol.rowSubtreeAtRaw_cost_le_of_active R C k P w hrow hR hC

theorem evalDepth_eq_add_actualSubtreeAtRaw_of_firstKRowBitsOn
    (R : Finset A) (C : Finset B) (k : Nat)
    (P : Protocol A B Z) (w : Fin (2 ^ k)) {a : A} {b : B}
    (hrow : Protocol.FirstKRowBitsOn R C k P)
    (ha : a ∈ R) (hb : b ∈ C)
    (hw : Protocol.actualPrefixCodeRaw k P a b = w) :
    Protocol.evalDepth P a b =
      k + Protocol.evalDepth (Protocol.actualSubtreeAtRaw k P w) a b := by
  induction k generalizing R P with
  | zero =>
      subst hw
      simp [Protocol.actualSubtreeAtRaw]
  | succ n ih =>
      cases P with
      | leaf z =>
          exfalso
          rcases hrow with hR | hC
          · rw [hR] at ha
            exact absurd ha (Finset.notMem_empty a)
          · rw [hC] at hb
            exact absurd hb (Finset.notMem_empty b)
      | bNode q l r =>
          exfalso
          rcases hrow with hR | hC
          · rw [hR] at ha
            exact absurd ha (Finset.notMem_empty a)
          · rw [hC] at hb
            exact absurd hb (Finset.notMem_empty b)
      | aNode q l r =>
          obtain ⟨hl, hr⟩ := hrow
          simp only [Protocol.actualPrefixCodeRaw] at hw
          have hhead : Protocol.bitHead w = q a := by
            rw [← hw, Protocol.bitHead_bitCons]
          have htail : Protocol.bitTail w =
              Protocol.actualPrefixCodeRaw n (if q a then r else l) a b := by
            rw [← hw, Protocol.bitTail_bitCons]
          simp only [Protocol.evalDepth, Protocol.actualSubtreeAtRaw]
          by_cases hq : q a
          · have hheadw : Protocol.bitHead w = true := by rw [hhead, hq]
            rw [hq, if_pos rfl, hheadw, if_pos rfl]
            have ha' : a ∈ R.filter fun x => q x = true := by
              rw [Finset.mem_filter]
              exact ⟨ha, hq⟩
            have hw' : Protocol.actualPrefixCodeRaw n r a b = Protocol.bitTail w := by
              rw [htail, if_pos hq]
            have hih := ih (R.filter fun x => q x = true) r (Protocol.bitTail w)
              hr ha' hw'
            omega
          · have hqf : q a = false := by simp [hq]
            have hheadw : Protocol.bitHead w = false := by rw [hhead, hqf]
            rw [hqf, if_neg (by decide), hheadw, if_neg (by decide)]
            have ha' : a ∈ R.filter fun x => q x = false := by
              rw [Finset.mem_filter]
              exact ⟨ha, hqf⟩
            have hw' : Protocol.actualPrefixCodeRaw n l a b = Protocol.bitTail w := by
              rw [htail, if_neg hq]
            have hih := ih (R.filter fun x => q x = false) l (Protocol.bitTail w)
              hl ha' hw'
            omega

noncomputable def rowPrefixRows [Fintype A]
    (t : Nat) (P : Protocol A B Bool) (j : Fin (2 ^ t)) : Finset A :=
  (Finset.univ : Finset A).filter fun a => Protocol.prefixCodeRaw t P a = j

-- CLAIM-BEGIN aux:branch-constructors
noncomputable def mkBranchAt_of_rowPrefix [Fintype A] [Fintype B]
    (P : Protocol A B Bool) (G : A → B → Bool) (t : Nat) (j : Fin (2 ^ t))
    (hrow : Protocol.FirstKRowBitsOn
      (Finset.univ : Finset A) (Finset.univ : Finset B) t P)
    (hP : P.Computes G)
    (hrows : (Protocol.rowPrefixRows t P j).Nonempty)
    (hcols : (Finset.univ : Finset B).Nonempty) :
    Protocol.BranchAt P G t where
  rows := Protocol.rowPrefixRows t P j
  cols := (Finset.univ : Finset B)
  transcript := j
  sideTrace := List.replicate t Protocol.ActualBitSide.alice
  residual :=
    Protocol.restrictSub (Protocol.rowPrefixRows t P j)
      (Finset.univ : Finset B)
      (Protocol.actualSubtreeAtRaw t P j)
  rows_nonempty := hrows
  cols_nonempty := hcols
  sideTrace_length := by simp
  sideTrace_eq := by
    intro a ha b hb
    exact Protocol.actualSideListRaw_eq_replicate_alice_of_firstKRowBitsOn
      (Finset.univ : Finset A) (Finset.univ : Finset B) t P hrow
      (Finset.mem_univ a) (Finset.mem_univ b)
  rectangle_transcript := by
    intro a ha b hb
    have hprefix : Protocol.prefixCodeRaw t P a = j := by
      exact (Finset.mem_filter.mp ha).2
    calc
      Protocol.actualPrefixCodeRaw t P a b =
          Protocol.prefixCodeRaw t P a := by
            exact Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
              (Finset.univ : Finset A) (Finset.univ : Finset B) t P hrow
              (Finset.mem_univ a) (Finset.mem_univ b)
      _ = j := hprefix
  rows_reachable := by
    intro a
    constructor
    · intro ha
      obtain ⟨b0, hb0⟩ := hcols
      refine ⟨b0, hb0, ?_⟩
      have hprefix : Protocol.prefixCodeRaw t P a = j := (Finset.mem_filter.mp ha).2
      calc
        Protocol.actualPrefixCodeRaw t P a b0 =
            Protocol.prefixCodeRaw t P a := by
              exact Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
                (Finset.univ : Finset A) (Finset.univ : Finset B) t P hrow
                (Finset.mem_univ a) (Finset.mem_univ b0)
        _ = j := hprefix
    · rintro ⟨b, hb, hcode⟩
      rw [Protocol.rowPrefixRows, Finset.mem_filter]
      refine ⟨Finset.mem_univ a, ?_⟩
      calc
        Protocol.prefixCodeRaw t P a =
            Protocol.actualPrefixCodeRaw t P a b := by
              exact (Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
                (Finset.univ : Finset A) (Finset.univ : Finset B) t P hrow
                (Finset.mem_univ a) (Finset.mem_univ b)).symm
        _ = j := hcode
  cols_reachable := by
    intro b
    constructor
    · intro hb
      obtain ⟨a0, ha0⟩ := hrows
      refine ⟨a0, ha0, ?_⟩
      have hprefix : Protocol.prefixCodeRaw t P a0 = j := (Finset.mem_filter.mp ha0).2
      calc
        Protocol.actualPrefixCodeRaw t P a0 b =
            Protocol.prefixCodeRaw t P a0 := by
              exact Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
                (Finset.univ : Finset A) (Finset.univ : Finset B) t P hrow
                (Finset.mem_univ a0) (Finset.mem_univ b)
        _ = j := hprefix
    · rintro ⟨a, ha, hcode⟩
      exact Finset.mem_univ b
  residual_eq_actual := rfl
  residual_eval_eq := by
    intro a b
    rw [Protocol.eval_restrictSub]
    rw [Protocol.actualSubtreeAtRaw_eq_rowSubtreeAtRaw_of_firstKRowBitsOn
      (Finset.univ : Finset A) (Finset.univ : Finset B) t P j hrow hrows hcols]
    exact Protocol.eval_rowSubtreeAtRaw_eq_of_prefix
      (Finset.univ : Finset A) (Finset.univ : Finset B) t P j hrow
      (Finset.mem_univ a.val) (Finset.mem_univ b.val)
      (by exact (Finset.mem_filter.mp a.2).2)
  residual_computes := by
    intro a b
    rw [Protocol.eval_restrictSub]
    have heval :=
      Protocol.eval_rowSubtreeAtRaw_eq_of_prefix
        (Finset.univ : Finset A) (Finset.univ : Finset B) t P j hrow
        (Finset.mem_univ a.val) (Finset.mem_univ b.val)
        (by
          have hprefix : Protocol.prefixCodeRaw t P a.val = j :=
            (Finset.mem_filter.mp a.2).2
          exact hprefix)
    rw [← Protocol.actualSubtreeAtRaw_eq_rowSubtreeAtRaw_of_firstKRowBitsOn
      (Finset.univ : Finset A) (Finset.univ : Finset B) t P j hrow
      ?_ hcols] at heval
    · rw [heval]
      simpa [NPCC.subgame] using hP a.val b.val
    · exact hrows
  restricted_residual_computes := by
    exact Protocol.computes_restrictSub_restrict
      (Protocol.rowPrefixRows t P j) (Finset.univ : Finset B) P hP
  restrict_evalDepth_ledger := by
    intro a ha b hb
    exact Protocol.evalDepth_restrict_add_foldCount_of_mem
      (Protocol.rowPrefixRows t P j) (Finset.univ : Finset B) P ha hb
  actualDepth_eq := by
    intro a ha b hb
    have hcode : Protocol.actualPrefixCodeRaw t P a b = j := by
      have hprefix : Protocol.prefixCodeRaw t P a = j := (Finset.mem_filter.mp ha).2
      calc
        Protocol.actualPrefixCodeRaw t P a b =
            Protocol.prefixCodeRaw t P a := by
              exact Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
                (Finset.univ : Finset A) (Finset.univ : Finset B) t P hrow
                (Finset.mem_univ a) (Finset.mem_univ b)
        _ = j := hprefix
    rw [Protocol.evalDepth_restrictSub]
    exact Protocol.evalDepth_eq_add_actualSubtreeAtRaw_of_firstKRowBitsOn
      (Finset.univ : Finset A) (Finset.univ : Finset B) t P j hrow
      (Finset.mem_univ a) (Finset.mem_univ b) hcode
  cost_after_actualBits := by
    rw [Protocol.cost_restrictSub]
    have hcost :=
      Protocol.actualSubtreeAtRaw_cost_le_of_firstKRowBitsOn
        (Finset.univ : Finset A) (Finset.univ : Finset B) t P j hrow hrows hcols
    obtain ⟨a0, ha0⟩ := hrows
    obtain ⟨b0, hb0⟩ := hcols
    have hcode : Protocol.actualPrefixCodeRaw t P a0 b0 = j := by
      have hprefix : Protocol.prefixCodeRaw t P a0 = j := (Finset.mem_filter.mp ha0).2
      calc
        Protocol.actualPrefixCodeRaw t P a0 b0 =
            Protocol.prefixCodeRaw t P a0 := by
              exact Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
                (Finset.univ : Finset A) (Finset.univ : Finset B) t P hrow
                (Finset.mem_univ a0) (Finset.mem_univ b0)
        _ = j := hprefix
    have hdepth :=
      Protocol.evalDepth_eq_add_actualSubtreeAtRaw_of_firstKRowBitsOn
        (Finset.univ : Finset A) (Finset.univ : Finset B) t P j hrow
        (Finset.mem_univ a0) (Finset.mem_univ b0) hcode
    have hdepth_le := Protocol.evalDepth_le_cost P a0 b0
    have ht_le : t ≤ P.cost := by omega
    omega
-- CLAIM-END aux:branch-constructors

end Protocol

end NPCC

/-! ## Branch constructors: swap transport

This suffix transports semantic branches through the protocol obtained by
exchanging Alice and Bob.  The transported constructor is the Bob-segment
counterpart of the row-prefix constructor above.
-/

namespace NPCC

open Workspace.Types.Protocol

namespace Protocol

variable {A B Z : Type*}

-- CLAIM-BEGIN aux:branch-constructors-2
/-- Exchange Alice and Bob nodes, leaving the leaf labels and tree shape fixed. -/
def swap : Protocol A B Z -> Protocol B A Z
  | Protocol.leaf z => Protocol.leaf z
  | Protocol.aNode q l r =>
      Protocol.bNode q (Protocol.swap l) (Protocol.swap r)
  | Protocol.bNode q l r =>
      Protocol.aNode q (Protocol.swap l) (Protocol.swap r)

@[simp] theorem swap_swap (P : Protocol A B Z) :
    Protocol.swap (Protocol.swap P) = P := by
  induction P with
  | leaf z => rfl
  | aNode q l r ihl ihr =>
      simp [Protocol.swap, ihl, ihr]
  | bNode q l r ihl ihr =>
      simp [Protocol.swap, ihl, ihr]

@[simp] theorem cost_swap (P : Protocol A B Z) :
    (Protocol.swap P).cost = P.cost := by
  induction P with
  | leaf z => rfl
  | aNode q l r ihl ihr =>
      simp [Protocol.swap, Protocol.cost, ihl, ihr]
  | bNode q l r ihl ihr =>
      simp [Protocol.swap, Protocol.cost, ihl, ihr]

@[simp] theorem eval_swap (P : Protocol A B Z) (b : B) (a : A) :
    (Protocol.swap P).eval b a = P.eval a b := by
  induction P generalizing a b with
  | leaf z => rfl
  | aNode q l r ihl ihr =>
      simp [Protocol.swap, Protocol.eval, ihl, ihr]
  | bNode q l r ihl ihr =>
      simp [Protocol.swap, Protocol.eval, ihl, ihr]

@[simp] theorem evalDepth_swap (P : Protocol A B Z) (b : B) (a : A) :
    Protocol.evalDepth (Protocol.swap P) b a = Protocol.evalDepth P a b := by
  induction P generalizing a b with
  | leaf z => rfl
  | aNode q l r ihl ihr =>
      simp [Protocol.swap, Protocol.evalDepth, ihl, ihr]
  | bNode q l r ihl ihr =>
      simp [Protocol.swap, Protocol.evalDepth, ihl, ihr]

/-- Exchange a party label on an actual transcript. -/
def ActualBitSide.swap : ActualBitSide -> ActualBitSide
  | ActualBitSide.alice => ActualBitSide.bob
  | ActualBitSide.bob => ActualBitSide.alice

@[simp] theorem ActualBitSide.swap_swap (s : ActualBitSide) :
    ActualBitSide.swap (ActualBitSide.swap s) = s := by
  cases s <;> rfl

theorem actualPrefixCodeRaw_swap
    (k : Nat) (P : Protocol A B Z) (a : A) (b : B) :
    Protocol.actualPrefixCodeRaw k (Protocol.swap P) b a =
      Protocol.actualPrefixCodeRaw k P a b := by
  induction k generalizing P with
  | zero => rfl
  | succ n ih =>
      cases P with
      | leaf z =>
          rfl
      | aNode q l r =>
          simp only [Protocol.swap, Protocol.actualPrefixCodeRaw]
          by_cases hq : q a = true
          · rw [if_pos hq, if_pos hq, ih r]
          · rw [if_neg hq, if_neg hq, ih l]
      | bNode q l r =>
          simp only [Protocol.swap, Protocol.actualPrefixCodeRaw]
          by_cases hq : q b = true
          · rw [if_pos hq, if_pos hq, ih r]
          · rw [if_neg hq, if_neg hq, ih l]

theorem actualSubtreeAtRaw_swap
    (k : Nat) (P : Protocol A B Z) (w : Fin (2 ^ k)) :
    Protocol.actualSubtreeAtRaw k (Protocol.swap P) w =
      Protocol.swap (Protocol.actualSubtreeAtRaw k P w) := by
  induction k generalizing P with
  | zero => rfl
  | succ n ih =>
      cases P with
      | leaf z =>
          rfl
      | aNode q l r =>
          simp only [Protocol.swap, Protocol.actualSubtreeAtRaw]
          by_cases h : Protocol.bitHead w
          · simp [h, ih]
          · simp [h, ih]
      | bNode q l r =>
          simp only [Protocol.swap, Protocol.actualSubtreeAtRaw]
          by_cases h : Protocol.bitHead w
          · simp [h, ih]
          · simp [h, ih]

theorem swap_actualSubtreeAtRaw_swap
    (k : Nat) (P : Protocol A B Z) (w : Fin (2 ^ k)) :
    Protocol.swap (Protocol.actualSubtreeAtRaw k (Protocol.swap P) w) =
      Protocol.actualSubtreeAtRaw k P w := by
  have h :=
    (Protocol.actualSubtreeAtRaw_swap (A := B) (B := A) (Z := Z)
      k (Protocol.swap P) w).symm
  simpa [Protocol.swap_swap] using h

theorem actualSideListRaw_swap
    (k : Nat) (P : Protocol A B Z) (a : A) (b : B) :
    Protocol.actualSideListRaw k (Protocol.swap P) b a =
      (Protocol.actualSideListRaw k P a b).map Protocol.ActualBitSide.swap := by
  induction k generalizing P with
  | zero => rfl
  | succ n ih =>
      cases P with
      | leaf z =>
          rfl
      | aNode q l r =>
          simp only [Protocol.swap, Protocol.actualSideListRaw, List.map_cons]
          by_cases hq : q a = true
          · rw [if_pos hq, if_pos hq, ih r]
            rfl
          · rw [if_neg hq, if_neg hq, ih l]
            rfl
      | bNode q l r =>
          simp only [Protocol.swap, Protocol.actualSideListRaw, List.map_cons]
          by_cases hq : q b = true
          · rw [if_pos hq, if_pos hq, ih r]
            rfl
          · rw [if_neg hq, if_neg hq, ih l]
            rfl

theorem actualSideListRaw_swap_back
    (k : Nat) (P : Protocol A B Z) (a : A) (b : B) :
    Protocol.actualSideListRaw k P a b =
      (Protocol.actualSideListRaw k (Protocol.swap P) b a).map
        Protocol.ActualBitSide.swap := by
  rw [Protocol.actualSideListRaw_swap]
  simp [List.map_map, Function.comp_def]

theorem swap_restrictSub
    (R : Finset A) (C : Finset B) (P : Protocol A B Z) :
    Protocol.swap (Protocol.restrictSub R C P) =
      Protocol.restrictSub C R (Protocol.swap P) := by
  induction P with
  | leaf z => rfl
  | aNode q l r ihl ihr =>
      simp [Protocol.swap, Protocol.restrictSub, ihl, ihr]
  | bNode q l r ihl ihr =>
      simp [Protocol.swap, Protocol.restrictSub, ihl, ihr]

/-- Column-onlyness is row-onlyness after swapping the two parties. -/
def FirstKColBitsOn
    (R : Finset A) (C : Finset B) (k : Nat) (P : Protocol A B Z) : Prop :=
  Protocol.FirstKRowBitsOn C R k (Protocol.swap P)

theorem firstKRowBitsOn_swap_iff_firstKColBitsOn
    (R : Finset A) (C : Finset B) (k : Nat) (P : Protocol A B Z) :
    Protocol.FirstKRowBitsOn C R k (Protocol.swap P) ↔
      Protocol.FirstKColBitsOn R C k P := by
  rfl

/-- The columns having a fixed actual Bob-prefix code, implemented by swap. -/
noncomputable def colPrefixCols [Fintype B]
    (t : Nat) (P : Protocol A B Bool) (j : Fin (2 ^ t)) : Finset B :=
  rowPrefixRows t (Protocol.swap P) j

/-- Transport a branch of the swapped protocol back to the original protocol. -/
noncomputable def branchAt_of_swap
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t : Nat}
    (br : Protocol.BranchAt (Protocol.swap P) (fun b a => G a b) t) :
    Protocol.BranchAt P G t where
  rows := br.cols
  cols := br.rows
  transcript := br.transcript
  sideTrace := br.sideTrace.map Protocol.ActualBitSide.swap
  residual := Protocol.swap br.residual
  rows_nonempty := br.cols_nonempty
  cols_nonempty := br.rows_nonempty
  sideTrace_length := by
    simp [br.sideTrace_length]
  sideTrace_eq := by
    intro a ha b hb
    calc
      Protocol.actualSideListRaw t P a b =
          (Protocol.actualSideListRaw t (Protocol.swap P) b a).map
            Protocol.ActualBitSide.swap := by
            exact Protocol.actualSideListRaw_swap_back t P a b
      _ = br.sideTrace.map Protocol.ActualBitSide.swap := by
            rw [br.sideTrace_eq b hb a ha]
  rectangle_transcript := by
    intro a ha b hb
    calc
      Protocol.actualPrefixCodeRaw t P a b =
          Protocol.actualPrefixCodeRaw t (Protocol.swap P) b a := by
            exact (Protocol.actualPrefixCodeRaw_swap t P a b).symm
      _ = br.transcript := br.rectangle_transcript b hb a ha
  rows_reachable := by
    intro a
    constructor
    · intro ha
      obtain ⟨b, hb, hcode⟩ := (br.cols_reachable a).mp ha
      refine ⟨b, hb, ?_⟩
      calc
        Protocol.actualPrefixCodeRaw t P a b =
            Protocol.actualPrefixCodeRaw t (Protocol.swap P) b a := by
              exact (Protocol.actualPrefixCodeRaw_swap t P a b).symm
        _ = br.transcript := hcode
    · rintro ⟨b, hb, hcode⟩
      exact (br.cols_reachable a).mpr
        ⟨b, hb, by
          calc
            Protocol.actualPrefixCodeRaw t (Protocol.swap P) b a =
                Protocol.actualPrefixCodeRaw t P a b := by
                  exact Protocol.actualPrefixCodeRaw_swap t P a b
            _ = br.transcript := hcode⟩
  cols_reachable := by
    intro b
    constructor
    · intro hb
      obtain ⟨a, ha, hcode⟩ := (br.rows_reachable b).mp hb
      refine ⟨a, ha, ?_⟩
      calc
        Protocol.actualPrefixCodeRaw t P a b =
            Protocol.actualPrefixCodeRaw t (Protocol.swap P) b a := by
              exact (Protocol.actualPrefixCodeRaw_swap t P a b).symm
        _ = br.transcript := hcode
    · rintro ⟨a, ha, hcode⟩
      exact (br.rows_reachable b).mpr
        ⟨a, ha, by
          calc
            Protocol.actualPrefixCodeRaw t (Protocol.swap P) b a =
                Protocol.actualPrefixCodeRaw t P a b := by
                  exact Protocol.actualPrefixCodeRaw_swap t P a b
            _ = br.transcript := hcode⟩
  residual_eq_actual := by
    rw [br.residual_eq_actual]
    rw [Protocol.swap_restrictSub]
    rw [Protocol.swap_actualSubtreeAtRaw_swap]
  residual_eval_eq := by
    intro a b
    calc
      (Protocol.swap br.residual).eval a b =
          br.residual.eval b a := by
            exact Protocol.eval_swap br.residual a b
      _ = (Protocol.swap P).eval b.val a.val := br.residual_eval_eq b a
      _ = P.eval a.val b.val := by
            exact Protocol.eval_swap P b.val a.val
  residual_computes := by
    intro a b
    calc
      (Protocol.swap br.residual).eval a b =
          br.residual.eval b a := by
            exact Protocol.eval_swap br.residual a b
      _ = (subgame (fun b a => G a b) br.rows br.cols) b a := by
            exact br.residual_computes b a
      _ = subgame G br.cols br.rows a b := by
            rfl
  restricted_residual_computes := by
    intro a b
    have hres := br.residual_eval_eq b a
    have hcomp := br.residual_computes b a
    rw [Protocol.eval_restrictSub]
    rw [Protocol.eval_restrict_of_mem br.cols br.rows P a.2 b.2]
    calc
      P.eval a.val b.val =
          (Protocol.swap P).eval b.val a.val := by
            exact (Protocol.eval_swap P b.val a.val).symm
      _ = br.residual.eval b a := hres.symm
      _ = subgame G br.cols br.rows a b := by
            simpa using hcomp
  restrict_evalDepth_ledger := by
    intro a ha b hb
    exact Protocol.evalDepth_restrict_add_foldCount_of_mem br.cols br.rows P ha hb
  actualDepth_eq := by
    intro a ha b hb
    have hbr := br.actualDepth_eq b hb a ha
    calc
      Protocol.evalDepth P a b =
          Protocol.evalDepth (Protocol.swap P) b a := by
            exact (Protocol.evalDepth_swap P b a).symm
      _ = t + Protocol.evalDepth br.residual ⟨b, hb⟩ ⟨a, ha⟩ := hbr
      _ = t + Protocol.evalDepth (Protocol.swap br.residual) ⟨a, ha⟩ ⟨b, hb⟩ := by
            rw [Protocol.evalDepth_swap br.residual]
  cost_after_actualBits := by
    simpa [Protocol.cost_swap] using br.cost_after_actualBits

/-- Bob-segment branch constructor obtained by row-prefix construction on swap. -/
noncomputable def mkBranchAt_of_colPrefix [Fintype A] [Fintype B]
    (P : Protocol A B Bool) (G : A -> B -> Bool) (t : Nat) (j : Fin (2 ^ t))
    (hcol : Protocol.FirstKColBitsOn
      (Finset.univ : Finset A) (Finset.univ : Finset B) t P)
    (hP : P.Computes G)
    (hrows : (Finset.univ : Finset A).Nonempty)
    (hcols : (colPrefixCols t P j).Nonempty) :
    Protocol.BranchAt P G t :=
  branchAt_of_swap
    (P := P) (G := G) <|
      mkBranchAt_of_rowPrefix
        (Protocol.swap P) (fun b a => G a b) t j hcol
        (by
          intro b a
          rw [Protocol.eval_swap]
          exact hP a b)
        (by
          simpa [colPrefixCols] using hcols)
        hrows
-- CLAIM-END aux:branch-constructors-2

end Protocol

end NPCC


/-! ## Branch constructor composition and relabelling helpers -/

namespace NPCC

open Workspace.Types.Protocol

namespace Protocol

-- CLAIM-BEGIN aux:branch-constructors-3

/-- Concatenate fixed-width transcript codes, with the earlier code occupying
the high-order bits. This matches `bitCons`, where the next actual bit is
stored in the upper half of the code. -/
def prefixCodeAppend {t1 t2 : Nat}
    (c1 : Fin (2 ^ t1)) (c2 : Fin (2 ^ t2)) : Fin (2 ^ (t1 + t2)) :=
  ⟨c1.1 * 2 ^ t2 + c2.1, by
    have hc1 : c1.1 < 2 ^ t1 := c1.2
    have hc2 : c2.1 < 2 ^ t2 := c2.2
    have hstep : c1.1 * 2 ^ t2 + c2.1 < (c1.1 + 1) * 2 ^ t2 := by
      calc
        c1.1 * 2 ^ t2 + c2.1 < c1.1 * 2 ^ t2 + 2 ^ t2 :=
          Nat.add_lt_add_left hc2 _
        _ = (c1.1 + 1) * 2 ^ t2 := by ring
    have hcap : (c1.1 + 1) * 2 ^ t2 <= 2 ^ t1 * 2 ^ t2 := by
      exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hc1)
    calc
      c1.1 * 2 ^ t2 + c2.1 < (c1.1 + 1) * 2 ^ t2 := hstep
      _ <= 2 ^ t1 * 2 ^ t2 := hcap
      _ = 2 ^ (t1 + t2) := by rw [Nat.pow_add]⟩

@[simp] theorem prefixCodeAppend_val {t1 t2 : Nat}
    (c1 : Fin (2 ^ t1)) (c2 : Fin (2 ^ t2)) :
    (Protocol.prefixCodeAppend c1 c2).1 = c1.1 * 2 ^ t2 + c2.1 :=
  rfl

theorem prefixCodeAppend_zero_left {t2 : Nat} (c2 : Fin (2 ^ t2)) :
    Protocol.prefixCodeAppend (Protocol.zeroPow2 0) c2 =
      Fin.cast (by simp) c2 := by
  apply Fin.ext
  simp [Protocol.prefixCodeAppend, Protocol.zeroPow2]

theorem prefixCodeAppend_left {t1 t2 : Nat}
    (c1 : Fin (2 ^ t1)) (c2 : Fin (2 ^ t2)) :
    (Protocol.prefixCodeAppend c1 c2).1 / 2 ^ t2 = c1.1 := by
  have hp : 0 < 2 ^ t2 := Nat.two_pow_pos t2
  calc
    (Protocol.prefixCodeAppend c1 c2).1 / 2 ^ t2 =
        (2 ^ t2 * c1.1 + c2.1) / 2 ^ t2 := by
          rw [Protocol.prefixCodeAppend_val, Nat.mul_comm]
    _ = c1.1 + c2.1 / 2 ^ t2 := by
          exact Nat.mul_add_div hp c1.1 c2.1
    _ = c1.1 := by
          rw [Nat.div_eq_of_lt c2.2, Nat.add_zero]

theorem prefixCodeAppend_right {t1 t2 : Nat}
    (c1 : Fin (2 ^ t1)) (c2 : Fin (2 ^ t2)) :
    (Protocol.prefixCodeAppend c1 c2).1 % 2 ^ t2 = c2.1 := by
  calc
    (Protocol.prefixCodeAppend c1 c2).1 % 2 ^ t2 =
        (c2.1 + 2 ^ t2 * c1.1) % 2 ^ t2 := by
          rw [Protocol.prefixCodeAppend_val, Nat.mul_comm, Nat.add_comm]
    _ = c2.1 % 2 ^ t2 := by
          exact Nat.add_mul_mod_self_left c2.1 (2 ^ t2) c1.1
    _ = c2.1 := Nat.mod_eq_of_lt c2.2

theorem prefixCodeAppend_inj {t1 t2 : Nat}
    {c1 d1 : Fin (2 ^ t1)} {c2 d2 : Fin (2 ^ t2)} :
    Protocol.prefixCodeAppend c1 c2 = Protocol.prefixCodeAppend d1 d2 <->
      c1 = d1 ∧ c2 = d2 := by
  constructor
  · intro h
    have hleft :
        (Protocol.prefixCodeAppend c1 c2).1 / 2 ^ t2 =
          (Protocol.prefixCodeAppend d1 d2).1 / 2 ^ t2 := by
      rw [h]
    have hright :
        (Protocol.prefixCodeAppend c1 c2).1 % 2 ^ t2 =
          (Protocol.prefixCodeAppend d1 d2).1 % 2 ^ t2 := by
      rw [h]
    constructor
    · apply Fin.ext
      rw [Protocol.prefixCodeAppend_left c1 c2,
        Protocol.prefixCodeAppend_left d1 d2] at hleft
      exact hleft
    · apply Fin.ext
      rw [Protocol.prefixCodeAppend_right c1 c2,
        Protocol.prefixCodeAppend_right d1 d2] at hright
      exact hright
  · rintro ⟨rfl, rfl⟩
    rfl

theorem actualPrefixCodeRaw_restrictSub {A B Z : Type*}
    (R : Finset A) (C : Finset B) (P : Protocol A B Z)
    (k : Nat) (a : {a // a ∈ R}) (b : {b // b ∈ C}) :
    Protocol.actualPrefixCodeRaw k (Protocol.restrictSub R C P) a b =
      Protocol.actualPrefixCodeRaw k P a.1 b.1 := by
  induction k generalizing P with
  | zero =>
      rfl
  | succ n ih =>
      cases P with
      | leaf z =>
          rfl
      | aNode q l r =>
          simp only [Protocol.restrictSub, Protocol.actualPrefixCodeRaw]
          by_cases hq : q a.1
          · rw [if_pos hq, if_pos hq, ih r]
          · rw [if_neg hq, if_neg hq, ih l]
      | bNode q l r =>
          simp only [Protocol.restrictSub, Protocol.actualPrefixCodeRaw]
          by_cases hq : q b.1
          · rw [if_pos hq, if_pos hq, ih r]
          · rw [if_neg hq, if_neg hq, ih l]

theorem actualSideListRaw_restrictSub {A B Z : Type*}
    (R : Finset A) (C : Finset B) (P : Protocol A B Z)
    (k : Nat) (a : {a // a ∈ R}) (b : {b // b ∈ C}) :
    Protocol.actualSideListRaw k (Protocol.restrictSub R C P) a b =
      Protocol.actualSideListRaw k P a.1 b.1 := by
  induction k generalizing P with
  | zero =>
      rfl
  | succ n ih =>
      cases P with
      | leaf z =>
          rfl
      | aNode q l r =>
          simp only [Protocol.restrictSub, Protocol.actualSideListRaw]
          by_cases hq : q a.1
          · rw [if_pos hq, if_pos hq, ih r]
          · rw [if_neg hq, if_neg hq, ih l]
      | bNode q l r =>
          simp only [Protocol.restrictSub, Protocol.actualSideListRaw]
          by_cases hq : q b.1
          · rw [if_pos hq, if_pos hq, ih r]
          · rw [if_neg hq, if_neg hq, ih l]

theorem actualSubtreeAtRaw_restrictSub {A B Z : Type*}
    (R : Finset A) (C : Finset B) (P : Protocol A B Z)
    (k : Nat) (w : Fin (2 ^ k)) :
    Protocol.actualSubtreeAtRaw k (Protocol.restrictSub R C P) w =
      Protocol.restrictSub R C (Protocol.actualSubtreeAtRaw k P w) := by
  induction k generalizing P with
  | zero =>
      rfl
  | succ n ih =>
      cases P with
      | leaf z =>
          rfl
      | aNode q l r =>
          simp only [Protocol.restrictSub, Protocol.actualSubtreeAtRaw]
          by_cases hw : Protocol.bitHead w
          · rw [if_pos hw, if_pos hw, ih r]
          · rw [if_neg hw, if_neg hw, ih l]
      | bNode q l r =>
          simp only [Protocol.restrictSub, Protocol.actualSubtreeAtRaw]
          by_cases hw : Protocol.bitHead w
          · rw [if_pos hw, if_pos hw, ih r]
          · rw [if_neg hw, if_neg hw, ih l]

namespace BranchAt

noncomputable def liftRows {A B : Type*} [DecidableEq A]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1)
    (b2 : Protocol.BranchAt b1.residual (subgame G b1.rows b1.cols) t2) :
    Finset A :=
  b2.rows.map
    ⟨Subtype.val, by
      intro x y h
      exact Subtype.ext h⟩

noncomputable def liftCols {A B : Type*} [DecidableEq B]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1)
    (b2 : Protocol.BranchAt b1.residual (subgame G b1.rows b1.cols) t2) :
    Finset B :=
  b2.cols.map
    ⟨Subtype.val, by
      intro x y h
      exact Subtype.ext h⟩

theorem mem_liftRows {A B : Type*} [DecidableEq A]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1)
    (b2 : Protocol.BranchAt b1.residual (subgame G b1.rows b1.cols) t2)
    (a : A) :
    a ∈ liftRows b1 b2 <->
      ∃ ha : a ∈ b1.rows, (⟨a, ha⟩ : {a // a ∈ b1.rows}) ∈ b2.rows := by
  constructor
  · intro h
    rcases (Finset.mem_map.mp h) with ⟨x, hx, hxval⟩
    refine ⟨by simp [hxval.symm, x.2], ?_⟩
    have hsub : (⟨a, by simp [hxval.symm, x.2]⟩ :
        {a // a ∈ b1.rows}) = x := by
      exact Subtype.ext hxval.symm
    simpa [hsub] using hx
  · rintro ⟨ha, hx⟩
    exact Finset.mem_map.mpr ⟨⟨a, ha⟩, hx, rfl⟩

theorem mem_liftCols {A B : Type*} [DecidableEq B]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1)
    (b2 : Protocol.BranchAt b1.residual (subgame G b1.rows b1.cols) t2)
    (b : B) :
    b ∈ liftCols b1 b2 <->
      ∃ hb : b ∈ b1.cols, (⟨b, hb⟩ : {b // b ∈ b1.cols}) ∈ b2.cols := by
  constructor
  · intro h
    rcases (Finset.mem_map.mp h) with ⟨x, hx, hxval⟩
    refine ⟨by simp [hxval.symm, x.2], ?_⟩
    have hsub : (⟨b, by simp [hxval.symm, x.2]⟩ :
        {b // b ∈ b1.cols}) = x := by
      exact Subtype.ext hxval.symm
    simpa [hsub] using hx
  · rintro ⟨hb, hx⟩
    exact Finset.mem_map.mpr ⟨⟨b, hb⟩, hx, rfl⟩

end BranchAt

noncomputable def dominantIndex {ι X : Type*} [DecidableEq ι]
    {L : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T) (j : Fin L) : ι :=
  Classical.choose (ExistsUnique.exists (hNW j))

theorem dominantIndex_spec {ι X : Type*} [DecidableEq ι]
    {L : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T) (j : Fin L) :
    dominantIndex Q Rin lab hNW j ∈ Q ∧
      T0 - (Q.card - 1) * T <=
        (Rin.filter
          (fun p => lab p = j ∧ p.1 = dominantIndex Q Rin lab hNW j)).card ∧
      ∀ i' ∈ Q, i' ≠ dominantIndex Q Rin lab hNW j ->
        (Rin.filter (fun p => lab p = j ∧ p.1 = i')).card < T := by
  exact Classical.choose_spec (ExistsUnique.exists (hNW j))

theorem dominantIndex_unique {ι X : Type*} [DecidableEq ι]
    {L : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T) (j : Fin L)
    {i : ι}
    (hi : i ∈ Q ∧
      T0 - (Q.card - 1) * T <=
        (Rin.filter (fun p => lab p = j ∧ p.1 = i)).card ∧
      ∀ i' ∈ Q, i' ≠ i ->
        (Rin.filter (fun p => lab p = j ∧ p.1 = i')).card < T) :
    i = dominantIndex Q Rin lab hNW j := by
  exact ExistsUnique.unique (hNW j) hi
    (dominantIndex_spec Q Rin lab hNW j)

noncomputable def alphaOfCode {ι X : Type*} [DecidableEq ι]
    {L t : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T)
    (labelOfCode : Fin (2 ^ t) -> Fin L) (j : Fin (2 ^ t)) : ι :=
  dominantIndex Q Rin lab hNW (labelOfCode j)

theorem alphaOfCode_spec {ι X : Type*} [DecidableEq ι]
    {L t : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T)
    (labelOfCode : Fin (2 ^ t) -> Fin L) (j : Fin (2 ^ t)) :
    alphaOfCode Q Rin lab hNW labelOfCode j ∈ Q ∧
      T0 - (Q.card - 1) * T <=
        (Rin.filter
          (fun p => lab p = labelOfCode j ∧
            p.1 = alphaOfCode Q Rin lab hNW labelOfCode j)).card ∧
      ∀ i' ∈ Q, i' ≠ alphaOfCode Q Rin lab hNW labelOfCode j ->
        (Rin.filter (fun p => lab p = labelOfCode j ∧ p.1 = i')).card < T := by
  exact dominantIndex_spec Q Rin lab hNW (labelOfCode j)

theorem alphaOfCode_eq_of_labelOfCode_eq {ι X : Type*} [DecidableEq ι]
    {L t : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T)
    (labelOfCode : Fin (2 ^ t) -> Fin L) {j1 j2 : Fin (2 ^ t)}
    (h : labelOfCode j1 = labelOfCode j2) :
    alphaOfCode Q Rin lab hNW labelOfCode j1 =
      alphaOfCode Q Rin lab hNW labelOfCode j2 := by
  simp [alphaOfCode, h]

noncomputable def YofCode {ι X : Type*} [Fintype X]
    [DecidableEq ι] [DecidableEq X]
    {L t : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T)
    (labelOfCode : Fin (2 ^ t) -> Fin L) (j : Fin (2 ^ t)) :
    Finset X :=
  let i := alphaOfCode Q Rin lab hNW labelOfCode j
  Finset.univ.filter fun x => (i, x) ∈ Rin ∧ lab (i, x) = labelOfCode j

theorem dominant_fiber_card_eq_YofCode {ι X : Type*} [Fintype X]
    [DecidableEq ι] [DecidableEq X]
    {L t : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T)
    (labelOfCode : Fin (2 ^ t) -> Fin L) (j : Fin (2 ^ t)) :
    (Rin.filter
      (fun p => lab p = labelOfCode j ∧
        p.1 = alphaOfCode Q Rin lab hNW labelOfCode j)).card =
      (YofCode Q Rin lab hNW labelOfCode j).card := by
  classical
  let i := alphaOfCode Q Rin lab hNW labelOfCode j
  let s := Rin.filter (fun p => lab p = labelOfCode j ∧ p.1 = i)
  let u : Finset X :=
    Finset.univ.filter fun x => (i, x) ∈ Rin ∧ lab (i, x) = labelOfCode j
  have hcard : s.card = u.card := by
    refine Finset.card_bij
      (fun p (_hp : p ∈ s) => p.2)
      ?hi ?hinj ?hsurj
    · intro p hp
      rw [Finset.mem_filter]
      rw [Finset.mem_filter] at hp
      refine ⟨Finset.mem_univ p.2, ?_⟩
      rcases hp with ⟨hR, hlab, hfst⟩
      cases p with
      | mk pi px =>
          simp only at hfst hR hlab ⊢
          subst pi
          exact ⟨hR, hlab⟩
    · intro p hp q hq hpq
      rw [Finset.mem_filter] at hp hq
      rcases hp with ⟨_hpR, _hplab, hpfst⟩
      rcases hq with ⟨_hqR, _hqlab, hqfst⟩
      cases p with
      | mk pi px =>
          cases q with
          | mk qi qx =>
              simp only at hpq hpfst hqfst
              subst px
              subst pi
              subst qi
              rfl
    · intro x hx
      rw [Finset.mem_filter] at hx
      rcases hx with ⟨_hxuniv, hxR, hxlab⟩
      refine ⟨(i, x), ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨hxR, hxlab, rfl⟩
  simpa [s, u, YofCode, i] using hcard

theorem YofCode_card_ge {ι X : Type*} [Fintype X]
    [DecidableEq ι] [DecidableEq X]
    {L t : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T)
    (labelOfCode : Fin (2 ^ t) -> Fin L) (j : Fin (2 ^ t)) :
    T0 - (Q.card - 1) * T <=
      (YofCode Q Rin lab hNW labelOfCode j).card := by
  have hspec := alphaOfCode_spec Q Rin lab hNW labelOfCode j
  rw [← dominant_fiber_card_eq_YofCode Q Rin lab hNW labelOfCode j]
  exact hspec.2.1

theorem YofCode_card_ge_of_lowerBound {ι X : Type*} [Fintype X]
    [DecidableEq ι] [DecidableEq X]
    {L t : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T K : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T)
    (labelOfCode : Fin (2 ^ t) -> Fin L) (j : Fin (2 ^ t))
    (hK : K <= T0 - (Q.card - 1) * T) :
    K <= (YofCode Q Rin lab hNW labelOfCode j).card := by
  exact le_trans hK (YofCode_card_ge Q Rin lab hNW labelOfCode j)

def alphaOfCode_surj_on_Q {ι X : Type*} [DecidableEq ι]
    {L t : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T)
    (labelOfCode : Fin (2 ^ t) -> Fin L) : Prop :=
  ∀ i ∈ Q, ∃ j : Fin (2 ^ t), alphaOfCode Q Rin lab hNW labelOfCode j = i

noncomputable def codeOfAlpha {ι X : Type*} [DecidableEq ι]
    {L t : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T)
    (labelOfCode : Fin (2 ^ t) -> Fin L)
    (hsurj : alphaOfCode_surj_on_Q Q Rin lab hNW labelOfCode)
    (i : ι) (hi : i ∈ Q) : Fin (2 ^ t) :=
  Classical.choose (hsurj i hi)

theorem alphaOf_codeOfAlpha {ι X : Type*} [DecidableEq ι]
    {L t : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T)
    (labelOfCode : Fin (2 ^ t) -> Fin L)
    (hsurj : alphaOfCode_surj_on_Q Q Rin lab hNW labelOfCode)
    (i : ι) (hi : i ∈ Q) :
    alphaOfCode Q Rin lab hNW labelOfCode
        (codeOfAlpha Q Rin lab hNW labelOfCode hsurj i hi) = i :=
  Classical.choose_spec (hsurj i hi)

noncomputable def Yalpha {ι X : Type*} [Fintype X]
    [DecidableEq ι] [DecidableEq X]
    {L t : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T)
    (labelOfCode : Fin (2 ^ t) -> Fin L)
    (hsurj : alphaOfCode_surj_on_Q Q Rin lab hNW labelOfCode)
    (i : ι) (hi : i ∈ Q) : Finset X :=
  YofCode Q Rin lab hNW labelOfCode
    (codeOfAlpha Q Rin lab hNW labelOfCode hsurj i hi)

theorem Yalpha_card_ge {ι X : Type*} [Fintype X]
    [DecidableEq ι] [DecidableEq X]
    {L t : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T)
    (labelOfCode : Fin (2 ^ t) -> Fin L)
    (hsurj : alphaOfCode_surj_on_Q Q Rin lab hNW labelOfCode)
    (i : ι) (hi : i ∈ Q) :
    T0 - (Q.card - 1) * T <=
      (Yalpha Q Rin lab hNW labelOfCode hsurj i hi).card := by
  exact YofCode_card_ge Q Rin lab hNW labelOfCode
    (codeOfAlpha Q Rin lab hNW labelOfCode hsurj i hi)

theorem Yalpha_card_ge_of_lowerBound {ι X : Type*} [Fintype X]
    [DecidableEq ι] [DecidableEq X]
    {L t : Nat} (Q : Finset ι) (Rin : Finset (ι × X))
    (lab : ι × X -> Fin L) {T0 T K : Nat}
    (hNW : NoWasteConclusion Q Rin lab T0 T)
    (labelOfCode : Fin (2 ^ t) -> Fin L)
    (hsurj : alphaOfCode_surj_on_Q Q Rin lab hNW labelOfCode)
    (i : ι) (hi : i ∈ Q)
    (hK : K <= T0 - (Q.card - 1) * T) :
    K <= (Yalpha Q Rin lab hNW labelOfCode hsurj i hi).card := by
  exact le_trans hK
    (Yalpha_card_ge Q Rin lab hNW labelOfCode hsurj i hi)

-- CLAIM-END aux:branch-constructors-3

end Protocol

end NPCC

namespace NPCC

open Workspace.Types.Protocol

namespace Protocol

-- CLAIM-BEGIN aux:branch-constructors-4

theorem actualPrefixCodeRaw_append_val {A B Z : Type*}
    (t1 t2 : Nat) (P : Protocol A B Z) (a : A) (b : B) :
    (Protocol.actualPrefixCodeRaw (t1 + t2) P a b).val =
      (Protocol.actualPrefixCodeRaw t1 P a b).val * 2 ^ t2 +
        (Protocol.actualPrefixCodeRaw t2
          (Protocol.actualSubtreeAtRaw t1 P
            (Protocol.actualPrefixCodeRaw t1 P a b)) a b).val := by
  induction t1 generalizing P with
  | zero =>
      rw [Nat.zero_add]
      simp [Protocol.actualPrefixCodeRaw, Protocol.actualSubtreeAtRaw,
        Protocol.zeroPow2]
  | succ n ih =>
      cases P with
      | leaf z =>
          cases t2 with
          | zero =>
              simp [Protocol.actualPrefixCodeRaw, Protocol.zeroPow2]
          | succ m =>
              simp [Protocol.actualPrefixCodeRaw, Protocol.actualSubtreeAtRaw,
                Protocol.zeroPow2]
      | aNode q l r =>
          rw [show n + 1 + t2 = n + t2 + 1 by omega]
          cases hqa : q a
          · have hsub :
                Protocol.actualSubtreeAtRaw (n + 1) (Protocol.aNode q l r)
                    (Protocol.actualPrefixCodeRaw (n + 1)
                      (Protocol.aNode q l r) a b) =
                  Protocol.actualSubtreeAtRaw n l
                    (Protocol.actualPrefixCodeRaw n l a b) := by
              simp [Protocol.actualPrefixCodeRaw, Protocol.actualSubtreeAtRaw,
                hqa]
            rw [hsub]
            simpa [Protocol.actualPrefixCodeRaw, hqa, Protocol.bitCons]
              using ih l
          · have hsub :
                Protocol.actualSubtreeAtRaw (n + 1) (Protocol.aNode q l r)
                    (Protocol.actualPrefixCodeRaw (n + 1)
                      (Protocol.aNode q l r) a b) =
                  Protocol.actualSubtreeAtRaw n r
                    (Protocol.actualPrefixCodeRaw n r a b) := by
              simp [Protocol.actualPrefixCodeRaw, Protocol.actualSubtreeAtRaw,
                hqa]
            rw [hsub]
            calc
              (Protocol.actualPrefixCodeRaw (n + t2 + 1)
                  (Protocol.aNode q l r) a b).val
                  = 2 ^ (n + t2) +
                      (Protocol.actualPrefixCodeRaw (n + t2) r a b).val := by
                    simp [Protocol.actualPrefixCodeRaw, hqa, Protocol.bitCons]
              _ = 2 ^ (n + t2) +
                    ((Protocol.actualPrefixCodeRaw n r a b).val * 2 ^ t2 +
                      (Protocol.actualPrefixCodeRaw t2
                        (Protocol.actualSubtreeAtRaw n r
                          (Protocol.actualPrefixCodeRaw n r a b)) a b).val) := by
                    rw [ih r]
              _ = (2 ^ n + (Protocol.actualPrefixCodeRaw n r a b).val) *
                    2 ^ t2 +
                      (Protocol.actualPrefixCodeRaw t2
                        (Protocol.actualSubtreeAtRaw n r
                          (Protocol.actualPrefixCodeRaw n r a b)) a b).val := by
                    rw [Nat.pow_add]
                    ring
              _ = (Protocol.actualPrefixCodeRaw (n + 1)
                    (Protocol.aNode q l r) a b).val * 2 ^ t2 +
                    (Protocol.actualPrefixCodeRaw t2
                      (Protocol.actualSubtreeAtRaw n r
                        (Protocol.actualPrefixCodeRaw n r a b)) a b).val := by
                    simp [Protocol.actualPrefixCodeRaw, hqa, Protocol.bitCons]
      | bNode q l r =>
          rw [show n + 1 + t2 = n + t2 + 1 by omega]
          cases hqb : q b
          · have hsub :
                Protocol.actualSubtreeAtRaw (n + 1) (Protocol.bNode q l r)
                    (Protocol.actualPrefixCodeRaw (n + 1)
                      (Protocol.bNode q l r) a b) =
                  Protocol.actualSubtreeAtRaw n l
                    (Protocol.actualPrefixCodeRaw n l a b) := by
              simp [Protocol.actualPrefixCodeRaw, Protocol.actualSubtreeAtRaw,
                hqb]
            rw [hsub]
            simpa [Protocol.actualPrefixCodeRaw, hqb, Protocol.bitCons]
              using ih l
          · have hsub :
                Protocol.actualSubtreeAtRaw (n + 1) (Protocol.bNode q l r)
                    (Protocol.actualPrefixCodeRaw (n + 1)
                      (Protocol.bNode q l r) a b) =
                  Protocol.actualSubtreeAtRaw n r
                    (Protocol.actualPrefixCodeRaw n r a b) := by
              simp [Protocol.actualPrefixCodeRaw, Protocol.actualSubtreeAtRaw,
                hqb]
            rw [hsub]
            calc
              (Protocol.actualPrefixCodeRaw (n + t2 + 1)
                  (Protocol.bNode q l r) a b).val
                  = 2 ^ (n + t2) +
                      (Protocol.actualPrefixCodeRaw (n + t2) r a b).val := by
                    simp [Protocol.actualPrefixCodeRaw, hqb, Protocol.bitCons]
              _ = 2 ^ (n + t2) +
                    ((Protocol.actualPrefixCodeRaw n r a b).val * 2 ^ t2 +
                      (Protocol.actualPrefixCodeRaw t2
                        (Protocol.actualSubtreeAtRaw n r
                          (Protocol.actualPrefixCodeRaw n r a b)) a b).val) := by
                    rw [ih r]
              _ = (2 ^ n + (Protocol.actualPrefixCodeRaw n r a b).val) *
                    2 ^ t2 +
                      (Protocol.actualPrefixCodeRaw t2
                        (Protocol.actualSubtreeAtRaw n r
                          (Protocol.actualPrefixCodeRaw n r a b)) a b).val := by
                    rw [Nat.pow_add]
                    ring
              _ = (Protocol.actualPrefixCodeRaw (n + 1)
                    (Protocol.bNode q l r) a b).val * 2 ^ t2 +
                    (Protocol.actualPrefixCodeRaw t2
                      (Protocol.actualSubtreeAtRaw n r
                        (Protocol.actualPrefixCodeRaw n r a b)) a b).val := by
                    simp [Protocol.actualPrefixCodeRaw, hqb, Protocol.bitCons]

theorem actualPrefixCodeRaw_append {A B Z : Type*}
    (t1 t2 : Nat) (P : Protocol A B Z) (a : A) (b : B) :
    Protocol.actualPrefixCodeRaw (t1 + t2) P a b =
      Protocol.prefixCodeAppend
        (Protocol.actualPrefixCodeRaw t1 P a b)
        (Protocol.actualPrefixCodeRaw t2
          (Protocol.actualSubtreeAtRaw t1 P
            (Protocol.actualPrefixCodeRaw t1 P a b)) a b) := by
  apply Fin.ext
  rw [Protocol.actualPrefixCodeRaw_append_val,
    Protocol.prefixCodeAppend_val]

theorem actualSideListRaw_append {A B Z : Type*}
    (t1 t2 : Nat) (P : Protocol A B Z) (a : A) (b : B) :
    Protocol.actualSideListRaw (t1 + t2) P a b =
      Protocol.actualSideListRaw t1 P a b ++
        Protocol.actualSideListRaw t2
          (Protocol.actualSubtreeAtRaw t1 P
            (Protocol.actualPrefixCodeRaw t1 P a b)) a b := by
  induction t1 generalizing P with
  | zero =>
      simp [Protocol.actualSideListRaw, Protocol.actualSubtreeAtRaw]
  | succ n ih =>
      cases P with
      | leaf z =>
          cases t2 with
          | zero =>
              simp [Protocol.actualSideListRaw]
          | succ m =>
              simp [Protocol.actualSideListRaw, Protocol.actualSubtreeAtRaw]
      | aNode q l r =>
          rw [show n + 1 + t2 = n + t2 + 1 by omega]
          cases hqa : q a <;>
            simp [Protocol.actualSideListRaw, Protocol.actualPrefixCodeRaw,
              Protocol.actualSubtreeAtRaw, hqa, ih]
      | bNode q l r =>
          rw [show n + 1 + t2 = n + t2 + 1 by omega]
          cases hqb : q b <;>
            simp [Protocol.actualSideListRaw, Protocol.actualPrefixCodeRaw,
              Protocol.actualSubtreeAtRaw, hqb, ih]

theorem actualSubtreeAtRaw_append_actualPrefix {A B Z : Type*}
    (t1 t2 : Nat) (P : Protocol A B Z) (a : A) (b : B) :
    Protocol.actualSubtreeAtRaw (t1 + t2) P
        (Protocol.actualPrefixCodeRaw (t1 + t2) P a b) =
      Protocol.actualSubtreeAtRaw t2
        (Protocol.actualSubtreeAtRaw t1 P
          (Protocol.actualPrefixCodeRaw t1 P a b))
        (Protocol.actualPrefixCodeRaw t2
          (Protocol.actualSubtreeAtRaw t1 P
            (Protocol.actualPrefixCodeRaw t1 P a b)) a b) := by
  induction t1 generalizing P with
  | zero =>
      rw [Nat.zero_add]
      simp [Protocol.actualSubtreeAtRaw]
  | succ n ih =>
      cases P with
      | leaf z =>
          cases t2 with
          | zero =>
              simp [Protocol.actualSubtreeAtRaw]
          | succ m =>
              simp [Protocol.actualPrefixCodeRaw, Protocol.actualSubtreeAtRaw]
      | aNode q l r =>
          rw [show n + 1 + t2 = n + t2 + 1 by omega]
          cases hqa : q a <;>
            simp [Protocol.actualPrefixCodeRaw, Protocol.actualSubtreeAtRaw,
              hqa, ih]
      | bNode q l r =>
          rw [show n + 1 + t2 = n + t2 + 1 by omega]
          cases hqb : q b <;>
            simp [Protocol.actualPrefixCodeRaw, Protocol.actualSubtreeAtRaw,
              hqb, ih]

theorem eval_actualSubtreeAtRaw_eq_of_actualPrefix {A B Z : Type*}
    (k : Nat) (P : Protocol A B Z) (a : A) (b : B) :
    (Protocol.actualSubtreeAtRaw k P
      (Protocol.actualPrefixCodeRaw k P a b)).eval a b = P.eval a b := by
  induction k generalizing P with
  | zero =>
      simp [Protocol.actualSubtreeAtRaw]
  | succ n ih =>
      cases P with
      | leaf z =>
          simp [Protocol.actualSubtreeAtRaw, Protocol.eval]
      | aNode q l r =>
          cases hqa : q a
          · simp [Protocol.actualPrefixCodeRaw, Protocol.actualSubtreeAtRaw,
              Protocol.eval, hqa, ih l]
          · simp [Protocol.actualPrefixCodeRaw, Protocol.actualSubtreeAtRaw,
              Protocol.eval, hqa, ih r]
      | bNode q l r =>
          cases hqb : q b
          · simp [Protocol.actualPrefixCodeRaw, Protocol.actualSubtreeAtRaw,
              Protocol.eval, hqb, ih l]
          · simp [Protocol.actualPrefixCodeRaw, Protocol.actualSubtreeAtRaw,
              Protocol.eval, hqb, ih r]

theorem evalDepth_eq_actualSideListRaw_length_add {A B Z : Type*}
    (k : Nat) (P : Protocol A B Z) (a : A) (b : B) :
    Protocol.evalDepth P a b =
      (Protocol.actualSideListRaw k P a b).length +
        Protocol.evalDepth
          (Protocol.actualSubtreeAtRaw k P
            (Protocol.actualPrefixCodeRaw k P a b)) a b := by
  induction k generalizing P with
  | zero =>
      simp [Protocol.actualSideListRaw, Protocol.actualSubtreeAtRaw]
  | succ n ih =>
      cases P with
      | leaf z =>
          simp [Protocol.actualSideListRaw, Protocol.actualSubtreeAtRaw,
            Protocol.evalDepth]
      | aNode q l r =>
          cases hqa : q a
          · have hih := ih l
            simp [Protocol.actualSideListRaw, Protocol.actualPrefixCodeRaw,
              Protocol.actualSubtreeAtRaw, Protocol.evalDepth, hqa] at hih ⊢
            omega
          · have hih := ih r
            simp [Protocol.actualSideListRaw, Protocol.actualPrefixCodeRaw,
              Protocol.actualSubtreeAtRaw, Protocol.evalDepth, hqa] at hih ⊢
            omega
      | bNode q l r =>
          cases hqb : q b
          · have hih := ih l
            simp [Protocol.actualSideListRaw, Protocol.actualPrefixCodeRaw,
              Protocol.actualSubtreeAtRaw, Protocol.evalDepth, hqb] at hih ⊢
            omega
          · have hih := ih r
            simp [Protocol.actualSideListRaw, Protocol.actualPrefixCodeRaw,
              Protocol.actualSubtreeAtRaw, Protocol.evalDepth, hqb] at hih ⊢
            omega

theorem actualSideListRaw_length_add_cost_actualSubtreeAtRaw_le {A B Z : Type*}
    (k : Nat) (P : Protocol A B Z) (a : A) (b : B) :
    (Protocol.actualSideListRaw k P a b).length +
        (Protocol.actualSubtreeAtRaw k P
          (Protocol.actualPrefixCodeRaw k P a b)).cost <=
      P.cost := by
  induction k generalizing P with
  | zero =>
      simp [Protocol.actualSideListRaw, Protocol.actualSubtreeAtRaw]
  | succ n ih =>
      cases P with
      | leaf z =>
          simp [Protocol.actualSideListRaw, Protocol.actualSubtreeAtRaw,
            Protocol.cost]
      | aNode q l r =>
          cases hqa : q a
          · have hih := ih l
            simp [Protocol.actualSideListRaw, Protocol.actualPrefixCodeRaw,
              Protocol.actualSubtreeAtRaw, Protocol.cost, hqa] at hih ⊢
            omega
          · have hih := ih r
            simp [Protocol.actualSideListRaw, Protocol.actualPrefixCodeRaw,
              Protocol.actualSubtreeAtRaw, Protocol.cost, hqa] at hih ⊢
            omega
      | bNode q l r =>
          cases hqb : q b
          · have hih := ih l
            simp [Protocol.actualSideListRaw, Protocol.actualPrefixCodeRaw,
              Protocol.actualSubtreeAtRaw, Protocol.cost, hqb] at hih ⊢
            omega
          · have hih := ih r
            simp [Protocol.actualSideListRaw, Protocol.actualPrefixCodeRaw,
              Protocol.actualSubtreeAtRaw, Protocol.cost, hqb] at hih ⊢
            omega

namespace BranchAt

theorem compose_eval_eq_game {A B : Type*} [DecidableEq A] [DecidableEq B]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1)
    (b2 : Protocol.BranchAt b1.residual (subgame G b1.rows b1.cols) t2)
    {a : A} (ha : a ∈ liftRows b1 b2)
    {b : B} (hb : b ∈ liftCols b1 b2) :
    P.eval a b = G a b := by
  obtain ⟨ha1, _ha2⟩ := (mem_liftRows b1 b2 a).1 ha
  obtain ⟨hb1, _hb2⟩ := (mem_liftCols b1 b2 b).1 hb
  have hcomp := b1.residual_computes ⟨a, ha1⟩ ⟨b, hb1⟩
  have heval := b1.residual_eval_eq ⟨a, ha1⟩ ⟨b, hb1⟩
  rw [heval] at hcomp
  simpa [subgame] using hcomp

theorem compose_rectangle_transcript {A B : Type*} [DecidableEq A] [DecidableEq B]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1)
    (b2 : Protocol.BranchAt b1.residual (subgame G b1.rows b1.cols) t2)
    (a : A) (ha : a ∈ liftRows b1 b2)
    (b : B) (hb : b ∈ liftCols b1 b2) :
    Protocol.actualPrefixCodeRaw (t1 + t2) P a b =
      Protocol.prefixCodeAppend b1.transcript b2.transcript := by
  obtain ⟨ha1, ha2⟩ := (mem_liftRows b1 b2 a).1 ha
  obtain ⟨hb1, hb2⟩ := (mem_liftCols b1 b2 b).1 hb
  have hfirst := b1.rectangle_transcript a ha1 b hb1
  have hsecond :
      Protocol.actualPrefixCodeRaw t2
          (Protocol.actualSubtreeAtRaw t1 P
            (Protocol.actualPrefixCodeRaw t1 P a b)) a b =
        b2.transcript := by
    rw [hfirst]
    have hres := b2.rectangle_transcript ⟨a, ha1⟩ ha2 ⟨b, hb1⟩ hb2
    simpa [b1.residual_eq_actual, Protocol.actualPrefixCodeRaw_restrictSub]
      using hres
  calc
    Protocol.actualPrefixCodeRaw (t1 + t2) P a b =
        Protocol.prefixCodeAppend
          (Protocol.actualPrefixCodeRaw t1 P a b)
          (Protocol.actualPrefixCodeRaw t2
            (Protocol.actualSubtreeAtRaw t1 P
              (Protocol.actualPrefixCodeRaw t1 P a b)) a b) := by
          exact Protocol.actualPrefixCodeRaw_append t1 t2 P a b
    _ = Protocol.prefixCodeAppend b1.transcript b2.transcript := by
          have hsecond' :
              Protocol.actualPrefixCodeRaw t2
                  (Protocol.actualSubtreeAtRaw t1 P b1.transcript) a b =
                b2.transcript := by
            simpa [hfirst] using hsecond
          rw [hfirst, hsecond']

theorem compose_sideTrace_eq {A B : Type*} [DecidableEq A] [DecidableEq B]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1)
    (b2 : Protocol.BranchAt b1.residual (subgame G b1.rows b1.cols) t2)
    (a : A) (ha : a ∈ liftRows b1 b2)
    (b : B) (hb : b ∈ liftCols b1 b2) :
    Protocol.actualSideListRaw (t1 + t2) P a b =
      b1.sideTrace ++ b2.sideTrace := by
  obtain ⟨ha1, ha2⟩ := (mem_liftRows b1 b2 a).1 ha
  obtain ⟨hb1, hb2⟩ := (mem_liftCols b1 b2 b).1 hb
  have hfirstCode := b1.rectangle_transcript a ha1 b hb1
  have hfirstSide := b1.sideTrace_eq a ha1 b hb1
  have hsecondSide :
      Protocol.actualSideListRaw t2
          (Protocol.actualSubtreeAtRaw t1 P
            (Protocol.actualPrefixCodeRaw t1 P a b)) a b =
        b2.sideTrace := by
    rw [hfirstCode]
    have hres := b2.sideTrace_eq ⟨a, ha1⟩ ha2 ⟨b, hb1⟩ hb2
    simpa [b1.residual_eq_actual, Protocol.actualSideListRaw_restrictSub]
      using hres
  calc
    Protocol.actualSideListRaw (t1 + t2) P a b =
        Protocol.actualSideListRaw t1 P a b ++
          Protocol.actualSideListRaw t2
            (Protocol.actualSubtreeAtRaw t1 P
              (Protocol.actualPrefixCodeRaw t1 P a b)) a b := by
          exact Protocol.actualSideListRaw_append t1 t2 P a b
    _ = b1.sideTrace ++ b2.sideTrace := by
          rw [hfirstSide, hsecondSide]

theorem compose_rows_reachable {A B : Type*} [DecidableEq A] [DecidableEq B]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1)
    (b2 : Protocol.BranchAt b1.residual (subgame G b1.rows b1.cols) t2)
    (a : A) :
    a ∈ liftRows b1 b2 ↔
      ∃ b : B, b ∈ liftCols b1 b2 ∧
        Protocol.actualPrefixCodeRaw (t1 + t2) P a b =
          Protocol.prefixCodeAppend b1.transcript b2.transcript := by
  constructor
  · intro ha
    obtain ⟨ha1, ha2⟩ := (mem_liftRows b1 b2 a).1 ha
    obtain ⟨b, hb2, hcode2⟩ :=
      (b2.rows_reachable ⟨a, ha1⟩).1 ha2
    have hb : b.val ∈ liftCols b1 b2 :=
      (mem_liftCols b1 b2 b.val).2 ⟨b.2, hb2⟩
    refine ⟨b.val, hb, ?_⟩
    exact compose_rectangle_transcript b1 b2 a ha b.val hb
  · rintro ⟨b, hb, hcode⟩
    obtain ⟨hb1, hb2⟩ := (mem_liftCols b1 b2 b).1 hb
    have happ :
        Protocol.prefixCodeAppend
            (Protocol.actualPrefixCodeRaw t1 P a b)
            (Protocol.actualPrefixCodeRaw t2
              (Protocol.actualSubtreeAtRaw t1 P
                (Protocol.actualPrefixCodeRaw t1 P a b)) a b) =
          Protocol.prefixCodeAppend b1.transcript b2.transcript := by
      rw [← Protocol.actualPrefixCodeRaw_append t1 t2 P a b]
      exact hcode
    have hsplit := (Protocol.prefixCodeAppend_inj).1 happ
    have hfirst : Protocol.actualPrefixCodeRaw t1 P a b = b1.transcript := hsplit.1
    have ha1 : a ∈ b1.rows :=
      (b1.rows_reachable a).2 ⟨b, hb1, hfirst⟩
    have hsecond :
        Protocol.actualPrefixCodeRaw t2 b1.residual
            ⟨a, ha1⟩ ⟨b, hb1⟩ =
          b2.transcript := by
      have htail := hsplit.2
      rw [hfirst] at htail
      simpa [b1.residual_eq_actual, Protocol.actualPrefixCodeRaw_restrictSub]
        using htail
    have ha2 : (⟨a, ha1⟩ : {a // a ∈ b1.rows}) ∈ b2.rows :=
      (b2.rows_reachable ⟨a, ha1⟩).2 ⟨⟨b, hb1⟩, hb2, hsecond⟩
    exact (mem_liftRows b1 b2 a).2 ⟨ha1, ha2⟩

theorem compose_cols_reachable {A B : Type*} [DecidableEq A] [DecidableEq B]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1)
    (b2 : Protocol.BranchAt b1.residual (subgame G b1.rows b1.cols) t2)
    (b : B) :
    b ∈ liftCols b1 b2 ↔
      ∃ a : A, a ∈ liftRows b1 b2 ∧
        Protocol.actualPrefixCodeRaw (t1 + t2) P a b =
          Protocol.prefixCodeAppend b1.transcript b2.transcript := by
  constructor
  · intro hb
    obtain ⟨hb1, hb2⟩ := (mem_liftCols b1 b2 b).1 hb
    obtain ⟨a, ha2, hcode2⟩ :=
      (b2.cols_reachable ⟨b, hb1⟩).1 hb2
    have ha : a.val ∈ liftRows b1 b2 :=
      (mem_liftRows b1 b2 a.val).2 ⟨a.2, ha2⟩
    refine ⟨a.val, ha, ?_⟩
    exact compose_rectangle_transcript b1 b2 a.val ha b hb
  · rintro ⟨a, ha, hcode⟩
    obtain ⟨ha1, ha2⟩ := (mem_liftRows b1 b2 a).1 ha
    have happ :
        Protocol.prefixCodeAppend
            (Protocol.actualPrefixCodeRaw t1 P a b)
            (Protocol.actualPrefixCodeRaw t2
              (Protocol.actualSubtreeAtRaw t1 P
                (Protocol.actualPrefixCodeRaw t1 P a b)) a b) =
          Protocol.prefixCodeAppend b1.transcript b2.transcript := by
      rw [← Protocol.actualPrefixCodeRaw_append t1 t2 P a b]
      exact hcode
    have hsplit := (Protocol.prefixCodeAppend_inj).1 happ
    have hfirst : Protocol.actualPrefixCodeRaw t1 P a b = b1.transcript := hsplit.1
    have hb1 : b ∈ b1.cols :=
      (b1.cols_reachable b).2 ⟨a, ha1, hfirst⟩
    have hsecond :
        Protocol.actualPrefixCodeRaw t2 b1.residual
            ⟨a, ha1⟩ ⟨b, hb1⟩ =
          b2.transcript := by
      have htail := hsplit.2
      rw [hfirst] at htail
      simpa [b1.residual_eq_actual, Protocol.actualPrefixCodeRaw_restrictSub]
        using htail
    have hb2 : (⟨b, hb1⟩ : {b // b ∈ b1.cols}) ∈ b2.cols :=
      (b2.cols_reachable ⟨b, hb1⟩).2 ⟨⟨a, ha1⟩, ha2, hsecond⟩
    exact (mem_liftCols b1 b2 b).2 ⟨hb1, hb2⟩

noncomputable def compose {A B : Type*} [DecidableEq A] [DecidableEq B]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1)
    (b2 : Protocol.BranchAt b1.residual (subgame G b1.rows b1.cols) t2) :
    Protocol.BranchAt P G (t1 + t2) where
  rows := liftRows b1 b2
  cols := liftCols b1 b2
  transcript := Protocol.prefixCodeAppend b1.transcript b2.transcript
  sideTrace := b1.sideTrace ++ b2.sideTrace
  residual :=
    Protocol.restrictSub (liftRows b1 b2) (liftCols b1 b2)
      (Protocol.actualSubtreeAtRaw (t1 + t2) P
        (Protocol.prefixCodeAppend b1.transcript b2.transcript))
  rows_nonempty := by
    obtain ⟨a, ha⟩ := b2.rows_nonempty
    exact ⟨a.val, (mem_liftRows b1 b2 a.val).2 ⟨a.2, ha⟩⟩
  cols_nonempty := by
    obtain ⟨b, hb⟩ := b2.cols_nonempty
    exact ⟨b.val, (mem_liftCols b1 b2 b.val).2 ⟨b.2, hb⟩⟩
  sideTrace_length := by
    rw [List.length_append, b1.sideTrace_length, b2.sideTrace_length]
  sideTrace_eq := by
    intro a ha b hb
    exact compose_sideTrace_eq b1 b2 a ha b hb
  rectangle_transcript := by
    intro a ha b hb
    exact compose_rectangle_transcript b1 b2 a ha b hb
  rows_reachable := by
    intro a
    exact compose_rows_reachable b1 b2 a
  cols_reachable := by
    intro b
    exact compose_cols_reachable b1 b2 b
  residual_eq_actual := rfl
  residual_eval_eq := by
    intro a b
    rw [Protocol.eval_restrictSub]
    have hcode := compose_rectangle_transcript b1 b2 a.val a.2 b.val b.2
    rw [← hcode]
    exact Protocol.eval_actualSubtreeAtRaw_eq_of_actualPrefix (t1 + t2) P a.val b.val
  residual_computes := by
    intro a b
    rw [Protocol.eval_restrictSub]
    have hcode := compose_rectangle_transcript b1 b2 a.val a.2 b.val b.2
    rw [← hcode]
    rw [Protocol.eval_actualSubtreeAtRaw_eq_of_actualPrefix]
    exact compose_eval_eq_game b1 b2 a.2 b.2
  restricted_residual_computes := by
    intro a b
    rw [Protocol.eval_restrictSub]
    rw [Protocol.eval_restrict_of_mem (liftRows b1 b2) (liftCols b1 b2) P a.2 b.2]
    exact compose_eval_eq_game b1 b2 a.2 b.2
  restrict_evalDepth_ledger := by
    intro a ha b hb
    exact Protocol.evalDepth_restrict_add_foldCount_of_mem
      (liftRows b1 b2) (liftCols b1 b2) P ha hb
  actualDepth_eq := by
    intro a ha b hb
    rw [Protocol.evalDepth_restrictSub]
    have hcode := compose_rectangle_transcript b1 b2 a ha b hb
    rw [← hcode]
    have hdepth :=
      Protocol.evalDepth_eq_actualSideListRaw_length_add (t1 + t2) P a b
    have hside := compose_sideTrace_eq b1 b2 a ha b hb
    have hlen :
        (Protocol.actualSideListRaw (t1 + t2) P a b).length = t1 + t2 := by
      rw [hside, List.length_append, b1.sideTrace_length, b2.sideTrace_length]
    rw [hlen] at hdepth
    exact hdepth
  cost_after_actualBits := by
    obtain ⟨a0, ha0⟩ := b2.rows_nonempty
    obtain ⟨b0, hb0⟩ := b2.cols_nonempty
    let a : A := a0.val
    let b : B := b0.val
    have ha : a ∈ liftRows b1 b2 :=
      (mem_liftRows b1 b2 a).2 ⟨a0.2, by simpa [a] using ha0⟩
    have hb : b ∈ liftCols b1 b2 :=
      (mem_liftCols b1 b2 b).2 ⟨b0.2, by simpa [b] using hb0⟩
    rw [Protocol.cost_restrictSub]
    have hcost :=
      Protocol.actualSideListRaw_length_add_cost_actualSubtreeAtRaw_le
        (t1 + t2) P a b
    have hside := compose_sideTrace_eq b1 b2 a ha b hb
    have hcode := compose_rectangle_transcript b1 b2 a ha b hb
    rw [hside, List.length_append, b1.sideTrace_length, b2.sideTrace_length] at hcost
    rw [hcode] at hcost
    exact hcost

theorem branchExtends_compose_left {A B : Type*} [DecidableEq A] [DecidableEq B]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1)
    (b2 : Protocol.BranchAt b1.residual (subgame G b1.rows b1.cols) t2) :
    Protocol.BranchExtends b1 (compose b1 b2) where
  depth_le := by omega
  rows_sub := by
    intro a ha
    exact ((mem_liftRows b1 b2 a).1 ha).1
  cols_sub := by
    intro b hb
    exact ((mem_liftCols b1 b2 b).1 hb).1
  transcript_compatible := by
    intro a ha b hb
    constructor
    · exact b1.rectangle_transcript a (((mem_liftRows b1 b2 a).1 ha).1)
        b (((mem_liftCols b1 b2 b).1 hb).1)
    · exact compose_rectangle_transcript b1 b2 a ha b hb
  residual_eval_refines := by
    intro a ha b hb
    have ha1 := ((mem_liftRows b1 b2 a).1 ha).1
    have hb1 := ((mem_liftCols b1 b2 b).1 hb).1
    calc
      b1.residual.eval ⟨a, ha1⟩ ⟨b, hb1⟩ =
          P.eval a b := b1.residual_eval_eq ⟨a, ha1⟩ ⟨b, hb1⟩
      _ = (compose b1 b2).residual.eval ⟨a, ha⟩ ⟨b, hb⟩ := by
          exact ((compose b1 b2).residual_eval_eq ⟨a, ha⟩ ⟨b, hb⟩).symm
  residual_depth_refines := by
    intro a ha b hb
    have ha1 := ((mem_liftRows b1 b2 a).1 ha).1
    have hb1 := ((mem_liftCols b1 b2 b).1 hb).1
    have h1 := b1.actualDepth_eq a ha1 b hb1
    have h12 := (compose b1 b2).actualDepth_eq a ha b hb
    omega

noncomputable def compose_colPrefix {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t1 t2 : Nat}
    (b1 : Protocol.BranchAt P G t1) (j : Fin (2 ^ t2))
    (hcol : Protocol.FirstKColBitsOn
      (Finset.univ : Finset {a // a ∈ b1.rows})
      (Finset.univ : Finset {b // b ∈ b1.cols}) t2 b1.residual)
    (hcols : (Protocol.colPrefixCols t2 b1.residual j).Nonempty) :
    Protocol.BranchAt P G (t1 + t2) :=
  compose b1 <|
    Protocol.mkBranchAt_of_colPrefix
      b1.residual (subgame G b1.rows b1.cols) t2 j hcol
      b1.residual_computes
      (by
        obtain ⟨a, ha⟩ := b1.rows_nonempty
        exact ⟨⟨a, ha⟩, Finset.mem_univ _⟩)
      hcols

end BranchAt

-- CLAIM-END aux:branch-constructors-4

end Protocol

end NPCC

namespace NPCC

open Workspace.Types.Protocol

namespace Protocol

-- CLAIM-BEGIN aux:branch-constructors-5

theorem actualPrefixCodeRaw_reindex {A B A' B' Z : Type*}
    (eA : A' ≃ A) (eB : B' ≃ B)
    (k : Nat) (P : Protocol A B Z) (a : A') (b : B') :
    Protocol.actualPrefixCodeRaw k (Protocol.reindex eA eB P) a b =
      Protocol.actualPrefixCodeRaw k P (eA a) (eB b) := by
  induction k generalizing P with
  | zero =>
      rfl
  | succ n ih =>
      cases P with
      | leaf z =>
          rfl
      | aNode q l r =>
          simp only [Protocol.reindex, Protocol.actualPrefixCodeRaw]
          by_cases hq : q (eA a)
          · rw [if_pos hq, if_pos hq, ih r]
          · rw [if_neg hq, if_neg hq, ih l]
      | bNode q l r =>
          simp only [Protocol.reindex, Protocol.actualPrefixCodeRaw]
          by_cases hq : q (eB b)
          · rw [if_pos hq, if_pos hq, ih r]
          · rw [if_neg hq, if_neg hq, ih l]

theorem actualSideListRaw_reindex {A B A' B' Z : Type*}
    (eA : A' ≃ A) (eB : B' ≃ B)
    (k : Nat) (P : Protocol A B Z) (a : A') (b : B') :
    Protocol.actualSideListRaw k (Protocol.reindex eA eB P) a b =
      Protocol.actualSideListRaw k P (eA a) (eB b) := by
  induction k generalizing P with
  | zero =>
      rfl
  | succ n ih =>
      cases P with
      | leaf z =>
          rfl
      | aNode q l r =>
          simp only [Protocol.reindex, Protocol.actualSideListRaw]
          by_cases hq : q (eA a)
          · rw [if_pos hq, if_pos hq, ih r]
          · rw [if_neg hq, if_neg hq, ih l]
      | bNode q l r =>
          simp only [Protocol.reindex, Protocol.actualSideListRaw]
          by_cases hq : q (eB b)
          · rw [if_pos hq, if_pos hq, ih r]
          · rw [if_neg hq, if_neg hq, ih l]

theorem actualSubtreeAtRaw_reindex {A B A' B' Z : Type*}
    (eA : A' ≃ A) (eB : B' ≃ B)
    (k : Nat) (P : Protocol A B Z) (w : Fin (2 ^ k)) :
    Protocol.actualSubtreeAtRaw k (Protocol.reindex eA eB P) w =
      Protocol.reindex eA eB (Protocol.actualSubtreeAtRaw k P w) := by
  induction k generalizing P with
  | zero =>
      rfl
  | succ n ih =>
      cases P with
      | leaf z =>
          rfl
      | aNode q l r =>
          simp only [Protocol.reindex, Protocol.actualSubtreeAtRaw]
          by_cases hw : Protocol.bitHead w
          · rw [if_pos hw, if_pos hw, ih r]
          · rw [if_neg hw, if_neg hw, ih l]
      | bNode q l r =>
          simp only [Protocol.reindex, Protocol.actualSubtreeAtRaw]
          by_cases hw : Protocol.bitHead w
          · rw [if_pos hw, if_pos hw, ih r]
          · rw [if_neg hw, if_neg hw, ih l]

@[simp] theorem evalDepth_reindex {A B A' B' Z : Type*}
    (eA : A' ≃ A) (eB : B' ≃ B)
    (P : Protocol A B Z) (a : A') (b : B') :
    Protocol.evalDepth (Protocol.reindex eA eB P) a b =
      Protocol.evalDepth P (eA a) (eB b) := by
  induction P generalizing a b with
  | leaf z =>
      rfl
  | aNode q l r ihl ihr =>
      simp [Protocol.reindex, Protocol.evalDepth, ihl, ihr]
  | bNode q l r ihl ihr =>
      simp [Protocol.reindex, Protocol.evalDepth, ihl, ihr]

theorem mem_map_equiv {A A' : Type*} (e : A' ≃ A) (s : Finset A') (a : A) :
    a ∈ s.map ⟨e, e.injective⟩ ↔ e.symm a ∈ s := by
  constructor
  · intro ha
    rcases Finset.mem_map.mp ha with ⟨x, hxmem, hxval⟩
    have hxeq : x = e.symm a := by
      apply e.injective
      simpa using hxval
    simpa [hxeq] using hxmem
  · intro ha
    exact Finset.mem_map.mpr ⟨e.symm a, ha, by simp⟩

noncomputable def branchAt_of_reindex
    {A B A' B' : Type*} [DecidableEq A] [DecidableEq B]
    [DecidableEq A'] [DecidableEq B']
    (eA : A' ≃ A) (eB : B' ≃ B)
    {P : Protocol A B Bool} {G : A -> B -> Bool} {t : Nat}
    (br : Protocol.BranchAt (Protocol.reindex eA eB P)
      (fun a b => G (eA a) (eB b)) t) :
    Protocol.BranchAt P G t where
  rows := br.rows.map ⟨eA, eA.injective⟩
  cols := br.cols.map ⟨eB, eB.injective⟩
  transcript := br.transcript
  sideTrace := br.sideTrace
  residual :=
    Protocol.restrictSub
      (br.rows.map ⟨eA, eA.injective⟩)
      (br.cols.map ⟨eB, eB.injective⟩)
      (Protocol.actualSubtreeAtRaw t P br.transcript)
  rows_nonempty := by
    obtain ⟨a, ha⟩ := br.rows_nonempty
    exact ⟨eA a, Finset.mem_map.mpr ⟨a, ha, rfl⟩⟩
  cols_nonempty := by
    obtain ⟨b, hb⟩ := br.cols_nonempty
    exact ⟨eB b, Finset.mem_map.mpr ⟨b, hb, rfl⟩⟩
  sideTrace_length := br.sideTrace_length
  sideTrace_eq := by
    intro a ha b hb
    have ha' : eA.symm a ∈ br.rows :=
      (Protocol.mem_map_equiv eA br.rows a).1 ha
    have hb' : eB.symm b ∈ br.cols :=
      (Protocol.mem_map_equiv eB br.cols b).1 hb
    calc
      Protocol.actualSideListRaw t P a b =
          Protocol.actualSideListRaw t P (eA (eA.symm a)) (eB (eB.symm b)) := by
            simp
      _ = Protocol.actualSideListRaw t (Protocol.reindex eA eB P)
            (eA.symm a) (eB.symm b) := by
            rw [Protocol.actualSideListRaw_reindex]
      _ = br.sideTrace := br.sideTrace_eq (eA.symm a) ha' (eB.symm b) hb'
  rectangle_transcript := by
    intro a ha b hb
    have ha' : eA.symm a ∈ br.rows :=
      (Protocol.mem_map_equiv eA br.rows a).1 ha
    have hb' : eB.symm b ∈ br.cols :=
      (Protocol.mem_map_equiv eB br.cols b).1 hb
    calc
      Protocol.actualPrefixCodeRaw t P a b =
          Protocol.actualPrefixCodeRaw t P (eA (eA.symm a)) (eB (eB.symm b)) := by
            simp
      _ = Protocol.actualPrefixCodeRaw t (Protocol.reindex eA eB P)
            (eA.symm a) (eB.symm b) := by
            rw [Protocol.actualPrefixCodeRaw_reindex]
      _ = br.transcript := br.rectangle_transcript (eA.symm a) ha' (eB.symm b) hb'
  rows_reachable := by
    intro a
    constructor
    · intro ha
      have ha' : eA.symm a ∈ br.rows :=
        (Protocol.mem_map_equiv eA br.rows a).1 ha
      obtain ⟨b', hb', hcode⟩ := (br.rows_reachable (eA.symm a)).1 ha'
      refine ⟨eB b', Finset.mem_map.mpr ⟨b', hb', rfl⟩, ?_⟩
      calc
        Protocol.actualPrefixCodeRaw t P a (eB b') =
            Protocol.actualPrefixCodeRaw t P (eA (eA.symm a)) (eB b') := by
              simp
        _ = Protocol.actualPrefixCodeRaw t (Protocol.reindex eA eB P)
              (eA.symm a) b' := by
              rw [Protocol.actualPrefixCodeRaw_reindex]
        _ = br.transcript := hcode
    · rintro ⟨b, hb, hcode⟩
      have hb' : eB.symm b ∈ br.cols :=
        (Protocol.mem_map_equiv eB br.cols b).1 hb
      have hcode' :
          Protocol.actualPrefixCodeRaw t (Protocol.reindex eA eB P)
              (eA.symm a) (eB.symm b) = br.transcript := by
        calc
          Protocol.actualPrefixCodeRaw t (Protocol.reindex eA eB P)
              (eA.symm a) (eB.symm b) =
              Protocol.actualPrefixCodeRaw t P (eA (eA.symm a)) (eB (eB.symm b)) := by
              rw [Protocol.actualPrefixCodeRaw_reindex]
          _ = Protocol.actualPrefixCodeRaw t P a b := by simp
          _ = br.transcript := hcode
      have ha' : eA.symm a ∈ br.rows :=
        (br.rows_reachable (eA.symm a)).2 ⟨eB.symm b, hb', hcode'⟩
      exact (Protocol.mem_map_equiv eA br.rows a).2 ha'
  cols_reachable := by
    intro b
    constructor
    · intro hb
      have hb' : eB.symm b ∈ br.cols :=
        (Protocol.mem_map_equiv eB br.cols b).1 hb
      obtain ⟨a', ha', hcode⟩ := (br.cols_reachable (eB.symm b)).1 hb'
      refine ⟨eA a', Finset.mem_map.mpr ⟨a', ha', rfl⟩, ?_⟩
      calc
        Protocol.actualPrefixCodeRaw t P (eA a') b =
            Protocol.actualPrefixCodeRaw t P (eA a') (eB (eB.symm b)) := by
              simp
        _ = Protocol.actualPrefixCodeRaw t (Protocol.reindex eA eB P)
              a' (eB.symm b) := by
              rw [Protocol.actualPrefixCodeRaw_reindex]
        _ = br.transcript := hcode
    · rintro ⟨a, ha, hcode⟩
      have ha' : eA.symm a ∈ br.rows :=
        (Protocol.mem_map_equiv eA br.rows a).1 ha
      have hcode' :
          Protocol.actualPrefixCodeRaw t (Protocol.reindex eA eB P)
              (eA.symm a) (eB.symm b) = br.transcript := by
        calc
          Protocol.actualPrefixCodeRaw t (Protocol.reindex eA eB P)
              (eA.symm a) (eB.symm b) =
              Protocol.actualPrefixCodeRaw t P (eA (eA.symm a)) (eB (eB.symm b)) := by
              rw [Protocol.actualPrefixCodeRaw_reindex]
          _ = Protocol.actualPrefixCodeRaw t P a b := by simp
          _ = br.transcript := hcode
      have hb' : eB.symm b ∈ br.cols :=
        (br.cols_reachable (eB.symm b)).2 ⟨eA.symm a, ha', hcode'⟩
      exact (Protocol.mem_map_equiv eB br.cols b).2 hb'
  residual_eq_actual := rfl
  residual_eval_eq := by
    intro a b
    rw [Protocol.eval_restrictSub]
    have hcode :
        Protocol.actualPrefixCodeRaw t P a.val b.val = br.transcript := by
      have ha' : eA.symm a.val ∈ br.rows :=
        (Protocol.mem_map_equiv eA br.rows a.val).1 a.2
      have hb' : eB.symm b.val ∈ br.cols :=
        (Protocol.mem_map_equiv eB br.cols b.val).1 b.2
      calc
        Protocol.actualPrefixCodeRaw t P a.val b.val =
            Protocol.actualPrefixCodeRaw t P
              (eA (eA.symm a.val)) (eB (eB.symm b.val)) := by
              simp
        _ = Protocol.actualPrefixCodeRaw t (Protocol.reindex eA eB P)
              (eA.symm a.val) (eB.symm b.val) := by
              rw [Protocol.actualPrefixCodeRaw_reindex]
        _ = br.transcript := br.rectangle_transcript _ ha' _ hb'
    rw [← hcode]
    exact Protocol.eval_actualSubtreeAtRaw_eq_of_actualPrefix t P a.val b.val
  residual_computes := by
    intro a b
    rw [Protocol.eval_restrictSub]
    have hcode :
        Protocol.actualPrefixCodeRaw t P a.val b.val = br.transcript := by
      have ha' : eA.symm a.val ∈ br.rows :=
        (Protocol.mem_map_equiv eA br.rows a.val).1 a.2
      have hb' : eB.symm b.val ∈ br.cols :=
        (Protocol.mem_map_equiv eB br.cols b.val).1 b.2
      calc
        Protocol.actualPrefixCodeRaw t P a.val b.val =
            Protocol.actualPrefixCodeRaw t P
              (eA (eA.symm a.val)) (eB (eB.symm b.val)) := by
              simp
        _ = Protocol.actualPrefixCodeRaw t (Protocol.reindex eA eB P)
              (eA.symm a.val) (eB.symm b.val) := by
              rw [Protocol.actualPrefixCodeRaw_reindex]
        _ = br.transcript := br.rectangle_transcript _ ha' _ hb'
    rw [← hcode]
    rw [Protocol.eval_actualSubtreeAtRaw_eq_of_actualPrefix]
    have ha' : eA.symm a.val ∈ br.rows :=
      (Protocol.mem_map_equiv eA br.rows a.val).1 a.2
    have hb' : eB.symm b.val ∈ br.cols :=
      (Protocol.mem_map_equiv eB br.cols b.val).1 b.2
    have hcomp := br.residual_computes
      ⟨eA.symm a.val, ha'⟩ ⟨eB.symm b.val, hb'⟩
    have heval := br.residual_eval_eq
      ⟨eA.symm a.val, ha'⟩ ⟨eB.symm b.val, hb'⟩
    rw [heval] at hcomp
    simpa [Protocol.eval_reindex, subgame] using hcomp
  restricted_residual_computes := by
    intro a b
    rw [Protocol.eval_restrictSub]
    rw [Protocol.eval_restrict_of_mem
      (br.rows.map ⟨eA, eA.injective⟩)
      (br.cols.map ⟨eB, eB.injective⟩) P a.2 b.2]
    have ha' : eA.symm a.val ∈ br.rows :=
      (Protocol.mem_map_equiv eA br.rows a.val).1 a.2
    have hb' : eB.symm b.val ∈ br.cols :=
      (Protocol.mem_map_equiv eB br.cols b.val).1 b.2
    have hcomp := br.residual_computes
      ⟨eA.symm a.val, ha'⟩ ⟨eB.symm b.val, hb'⟩
    have heval := br.residual_eval_eq
      ⟨eA.symm a.val, ha'⟩ ⟨eB.symm b.val, hb'⟩
    rw [heval] at hcomp
    simpa [Protocol.eval_reindex, subgame] using hcomp
  restrict_evalDepth_ledger := by
    intro a ha b hb
    exact Protocol.evalDepth_restrict_add_foldCount_of_mem
      (br.rows.map ⟨eA, eA.injective⟩)
      (br.cols.map ⟨eB, eB.injective⟩) P ha hb
  actualDepth_eq := by
    intro a ha b hb
    rw [Protocol.evalDepth_restrictSub]
    have hdepth :=
      Protocol.evalDepth_eq_actualSideListRaw_length_add t P a b
    have hside :
        Protocol.actualSideListRaw t P a b = br.sideTrace := by
      have ha' : eA.symm a ∈ br.rows :=
        (Protocol.mem_map_equiv eA br.rows a).1 ha
      have hb' : eB.symm b ∈ br.cols :=
        (Protocol.mem_map_equiv eB br.cols b).1 hb
      calc
        Protocol.actualSideListRaw t P a b =
            Protocol.actualSideListRaw t P (eA (eA.symm a)) (eB (eB.symm b)) := by
              simp
        _ = Protocol.actualSideListRaw t (Protocol.reindex eA eB P)
              (eA.symm a) (eB.symm b) := by
              rw [Protocol.actualSideListRaw_reindex]
        _ = br.sideTrace := br.sideTrace_eq _ ha' _ hb'
    have hcode :
        Protocol.actualPrefixCodeRaw t P a b = br.transcript := by
      have ha' : eA.symm a ∈ br.rows :=
        (Protocol.mem_map_equiv eA br.rows a).1 ha
      have hb' : eB.symm b ∈ br.cols :=
        (Protocol.mem_map_equiv eB br.cols b).1 hb
      calc
        Protocol.actualPrefixCodeRaw t P a b =
            Protocol.actualPrefixCodeRaw t P (eA (eA.symm a)) (eB (eB.symm b)) := by
              simp
        _ = Protocol.actualPrefixCodeRaw t (Protocol.reindex eA eB P)
              (eA.symm a) (eB.symm b) := by
              rw [Protocol.actualPrefixCodeRaw_reindex]
        _ = br.transcript := br.rectangle_transcript _ ha' _ hb'
    have hlen :
        (Protocol.actualSideListRaw t P a b).length = t := by
      rw [hside, br.sideTrace_length]
    rw [hlen] at hdepth
    rw [hcode] at hdepth
    exact hdepth
  cost_after_actualBits := by
    obtain ⟨a0, ha0⟩ := br.rows_nonempty
    obtain ⟨b0, hb0⟩ := br.cols_nonempty
    rw [Protocol.cost_restrictSub]
    have hcost :=
      Protocol.actualSideListRaw_length_add_cost_actualSubtreeAtRaw_le
        t P (eA a0) (eB b0)
    have hside :
        Protocol.actualSideListRaw t P (eA a0) (eB b0) = br.sideTrace := by
      calc
        Protocol.actualSideListRaw t P (eA a0) (eB b0) =
            Protocol.actualSideListRaw t (Protocol.reindex eA eB P) a0 b0 := by
            rw [Protocol.actualSideListRaw_reindex]
        _ = br.sideTrace := br.sideTrace_eq a0 ha0 b0 hb0
    have hcode :
        Protocol.actualPrefixCodeRaw t P (eA a0) (eB b0) = br.transcript := by
      calc
        Protocol.actualPrefixCodeRaw t P (eA a0) (eB b0) =
            Protocol.actualPrefixCodeRaw t (Protocol.reindex eA eB P) a0 b0 := by
            rw [Protocol.actualPrefixCodeRaw_reindex]
        _ = br.transcript := br.rectangle_transcript a0 ha0 b0 hb0
    rw [hside, br.sideTrace_length, hcode] at hcost
    exact hcost

-- CLAIM-END aux:branch-constructors-5

end Protocol

end NPCC
