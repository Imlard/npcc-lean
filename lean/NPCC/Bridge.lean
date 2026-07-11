import Mathlib
import NPCC.Defs
import NPCC.DefsAux
import Workspace.Types.Bracket

/-! # Bridges to the reused interlace library
Set-level transfer between the paper's typed `≥`-form definitions (NPCC) and the
reused library's flattened exact-form machinery (`Workspace.*`). Game-level
communication-value transfer is proved in `NPCC.Twin`. -/

namespace NPCC

open Workspace.Types.Equipartition Workspace.Types.Bracket

/-- Flatten one typed interlace row `(q, i) : Fin p × Fin m` to the artifact's
natural-number index `m * q + i` (block `q` of width `m`). -/
def encRow {p m : ℕ} (a : Fin p × Fin m) : ℕ := m * a.1.1 + a.2.1

lemma encRow_block_iff {p m : ℕ} (a : Fin p × Fin m) (γ : ℕ) :
    (m * γ ≤ encRow a ∧ encRow a < m * (γ + 1)) ↔ (a.1 : ℕ) = γ := by
  have hi : (a.2 : ℕ) < m := a.2.isLt
  have hs1 : m * ((a.1 : ℕ) + 1) = m * (a.1 : ℕ) + m := by ring
  have hs2 : m * (γ + 1) = m * γ + m := by ring
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hi
  unfold encRow
  constructor
  · rintro ⟨h1, h2⟩
    have hq1 : (a.1 : ℕ) < γ + 1 := by
      have h : m * (a.1 : ℕ) < m * (γ + 1) := lt_of_le_of_lt (Nat.le_add_right _ _) h2
      exact Nat.lt_of_mul_lt_mul_left h
    have hq2 : γ < (a.1 : ℕ) + 1 := by
      have h : m * γ < m * ((a.1 : ℕ) + 1) := by
        rw [hs1]
        exact lt_of_le_of_lt h1 (by linarith)
      exact Nat.lt_of_mul_lt_mul_left h
    omega
  · intro h
    rw [← h]
    exact ⟨Nat.le_add_right _ _, by rw [hs1]; linarith⟩

lemma encRow_injective {p m : ℕ} : Function.Injective (encRow (p := p) (m := m)) := by
  intro a b hab
  have hb : m * (b.1 : ℕ) ≤ encRow b ∧ encRow b < m * ((b.1 : ℕ) + 1) :=
    (encRow_block_iff b (b.1 : ℕ)).mpr rfl
  rw [← hab] at hb
  have h1 : (a.1 : ℕ) = (b.1 : ℕ) := (encRow_block_iff a (b.1 : ℕ)).mp hb
  have h2 : (a.2 : ℕ) = (b.2 : ℕ) := by
    have := hab
    unfold encRow at this
    rw [h1] at this
    exact Nat.add_left_cancel this
  exact Prod.ext (Fin.val_injective h1) (Fin.val_injective h2)

/-- `Workspace.Types.Equipartition.IsEquipartitioned` reads its real target only
through `⌈·⌉₊`. -/
lemma isEquipartitioned_congr_ceil {R : Finset ℕ} {m p : ℕ} {T₁ T₂ : ℝ}
    (hc : ⌈T₁⌉₊ = ⌈T₂⌉₊) (h1 : IsEquipartitioned R m T₁ p) :
    IsEquipartitioned R m T₂ p := by
  intro γ hγ
  rw [← hc]
  exact h1 γ hγ

-- CLAIM-BEGIN bridge:equipartition
/-- Bridge (typed → artifact), trim-to-exact direction. If a typed row set
`R : Finset (Fin p × Fin m)` is `(univ, T)`-equipartitioned in the paper's
`≥`-sense (`NPCC.IsEquipartitionedGE`), then some flattened row set
`S ⊆ [0, m·p)` is equipartitioned in the artifact's exact sense
(`Workspace.Types.Equipartition.IsEquipartitioned`: every block `[m·γ, m·(γ+1))`
holds exactly `⌈(T:ℝ)⌉₊ = T` rows): choose a `T`-subset of each fiber and
flatten by `encRow (q,i) = m·q + i`. The converse decode direction is
`bridge_equipartition_ofArtifact`. Typed row sets over general `(ι, X)` reduce
to `(Fin p, Fin m)` via equivalences at use sites. -/
theorem bridge_equipartition {p m T : ℕ} {R : Finset (Fin p × Fin m)}
    (h : IsEquipartitionedGE R (Finset.univ : Finset (Fin p)) T) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (m * p) ∧
      IsEquipartitioned S m (T : ℝ) p :=
-- CLAIM-END bridge:equipartition
  by
  classical
  have hch : ∀ q : Fin p, ∃ t ⊆ R.filter (fun a => a.1 = q), t.card = T :=
    fun q => Finset.exists_subset_card_eq (h q (Finset.mem_univ q))
  choose t hsub hcard using hch
  refine ⟨Finset.univ.biUnion (fun q => (t q).image encRow), ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hj
    obtain ⟨q, a, _, rfl⟩ := hj
    have hia : (a.2 : ℕ) < m := a.2.isLt
    have hqp : (a.1 : ℕ) < p := a.1.isLt
    have h1 : encRow a < m * ((a.1 : ℕ) + 1) := by
      have hs1 : m * ((a.1 : ℕ) + 1) = m * (a.1 : ℕ) + m := by ring
      unfold encRow
      rw [hs1]
      linarith
    have h2 : m * ((a.1 : ℕ) + 1) ≤ m * p := Nat.mul_le_mul_left m hqp
    exact Finset.mem_range.mpr (lt_of_lt_of_le h1 h2)
  · intro γ hγ
    have hfilter :
        (Finset.univ.biUnion (fun q => (t q).image encRow)).filter
          (fun i => m * γ ≤ i ∧ i < m * (γ + 1))
        = (t ⟨γ, hγ⟩).image encRow := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨q, a, hat, rfl⟩, hblock⟩
        have haq : a.1 = q := (Finset.mem_filter.mp (hsub q hat)).2
        have hγa : (a.1 : ℕ) = γ := (encRow_block_iff a γ).mp hblock
        have hqγ : q = (⟨γ, hγ⟩ : Fin p) := by
          apply Fin.ext
          rw [← haq]
          exact hγa
        exact ⟨a, by rw [← hqγ]; exact hat, rfl⟩
      · rintro ⟨a, hat, rfl⟩
        have haq : a.1 = (⟨γ, hγ⟩ : Fin p) :=
          (Finset.mem_filter.mp (hsub _ hat)).2
        have hγa : (a.1 : ℕ) = γ := by rw [haq]
        exact ⟨⟨⟨γ, hγ⟩, a, hat, rfl⟩, (encRow_block_iff a γ).mpr hγa⟩
    rw [hfilter, Finset.card_image_of_injective _ encRow_injective,
      hcard ⟨γ, hγ⟩, Nat.ceil_natCast]

/-- Bridge (artifact → typed), decode direction: a flattened exactly-
equipartitioned set decodes to a typed `≥`-equipartitioned row set at
threshold `⌈T⌉₊`. -/
theorem bridge_equipartition_ofArtifact {p m : ℕ} {S : Finset ℕ} {T : ℝ}
    (h : IsEquipartitioned S m T p) :
    ∃ R : Finset (Fin p × Fin m),
      IsEquipartitionedGE R (Finset.univ : Finset (Fin p)) ⌈T⌉₊ := by
  classical
  refine ⟨Finset.univ.filter (fun a : Fin p × Fin m => encRow a ∈ S), ?_⟩
  intro q _
  have key :
      ((Finset.univ.filter (fun a : Fin p × Fin m => encRow a ∈ S)).filter
        (fun a => a.1 = q)).card
      = (S.filter (fun i => m * (q : ℕ) ≤ i ∧ i < m * ((q : ℕ) + 1))).card := by
    apply Finset.card_bij (fun a _ => encRow a)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      refine Finset.mem_filter.mpr ⟨ha.1, ?_⟩
      exact (encRow_block_iff a (q : ℕ)).mpr (by rw [ha.2])
    · intro a _ b _ hab
      exact encRow_injective hab
    · intro j hj
      obtain ⟨hjS, hblock⟩ := Finset.mem_filter.mp hj
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · exfalso
          have := hblock.2
          rw [h0, Nat.zero_mul] at this
          exact Nat.not_lt_zero _ this
        · exact h0
      have hjlt : j < m * (q : ℕ) + m := by
        have hs : m * ((q : ℕ) + 1) = m * (q : ℕ) + m := by ring
        rw [← hs]
        exact hblock.2
      have hi : j - m * (q : ℕ) < m := by
        rw [tsub_lt_iff_right hblock.1]
        linarith
      refine ⟨(q, ⟨j - m * (q : ℕ), hi⟩), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · show m * (q : ℕ) + (j - m * (q : ℕ)) ∈ S
          rw [Nat.add_sub_cancel' hblock.1]
          exact hjS
        · trivial
      · show m * (q : ℕ) + (j - m * (q : ℕ)) = j
        exact Nat.add_sub_cancel' hblock.1
  rw [key, h (q : ℕ) q.isLt]

-- CLAIM-BEGIN bridge:bracket
/-- Bridge (typed → artifact) for bracket families, set level. A typed member
`RC ∈ bracketGE X Y p x y` yields flattened extraction data `(R, C)` meeting
the artifact bracket's conditions — rows exactly-equipartitioned at the
artifact's real target `(m:ℝ)·x`, columns an exact-size subset of
`range (n^p)` (both column conditions are pure counts, and
`card (Fin p → Y) = n^p`) — and hence, for every `BoolMat` of matching
dimensions, an actual member of `Workspace.Types.Bracket.bracket M p x y`.
This makes the reused bracket machinery available behind the typed definitions;
`NPCC.Twin` proves the corresponding equality of communication values. -/
theorem bridge_bracket {X Y : Type*} [Fintype X] [Fintype Y] {p : ℕ} {x y : ℝ}
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (h : RC ∈ bracketGE X Y p x y) :
    ∃ (R C : Finset ℕ),
      R ⊆ Finset.range (Fintype.card X * p) ∧
      IsEquipartitioned R (Fintype.card X) ((Fintype.card X : ℝ) * x) p ∧
      C ⊆ Finset.range (Fintype.card Y ^ p) ∧
      C.card = ⌈((Fintype.card Y ^ p : ℕ) : ℝ) * y⌉₊ ∧
      ∀ M : Workspace.Types.BoolMat.BoolMat,
        M.m = Fintype.card X → M.n = Fintype.card Y →
        Workspace.Types.Extract.extract
          (Workspace.Types.Interlace.interlace M p) R C
          ∈ Workspace.Types.Bracket.bracket M p x y :=
-- CLAIM-END bridge:bracket
  by
  classical
  obtain ⟨hrow, hcol⟩ := h
  -- COLUMNS: pure counting.
  have hcards : Fintype.card (Fin p → Y) = Fintype.card Y ^ p := by
    rw [Fintype.card_fun, Fintype.card_fin]
  have hKle : ⌈((Fintype.card Y : ℝ) ^ p) * y⌉₊ ≤ Fintype.card Y ^ p := by
    calc ⌈((Fintype.card Y : ℝ) ^ p) * y⌉₊ ≤ RC.2.card := hcol
      _ ≤ Fintype.card (Fin p → Y) := Finset.card_le_univ _
      _ = Fintype.card Y ^ p := hcards
  have hceilC : ⌈((Fintype.card Y ^ p : ℕ) : ℝ) * y⌉₊
      = ⌈((Fintype.card Y : ℝ) ^ p) * y⌉₊ := by
    congr 1
    push_cast
    ring
  obtain ⟨C, hCsub, hCcard⟩ :=
    Finset.exists_subset_card_eq
      (s := Finset.range (Fintype.card Y ^ p))
      (n := ⌈((Fintype.card Y : ℝ) ^ p) * y⌉₊)
      (by rw [Finset.card_range]; exact hKle)
  -- ROWS: case on p; for p ≥ 1 the ceiling fits inside one fiber, so the full
  -- typed row set over (Fin p, Fin m) is GE-equipartitioned and trims.
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · subst hp0
    refine ⟨∅, C, by intro j hj; exact absurd hj (Finset.notMem_empty _), ?_, ?_, ?_, ?_⟩
    · intro γ hγ
      exact absurd hγ (Nat.not_lt_zero _)
    · exact hCsub
    · rw [hCcard, hceilC]
    · intro M hm' hn'
      refine ⟨∅, C, ?_, ?_, ?_, ?_, rfl⟩
      · intro j hj; exact absurd hj (Finset.notMem_empty _)
      · intro γ hγ; exact absurd hγ (Nat.not_lt_zero _)
      · rw [hn']; exact hCsub
      · rw [hn', hCcard, hceilC]
  · have hceil_le : ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ Fintype.card X := by
      have q0 : Fin p := ⟨0, hppos⟩
      have hfib := hrow q0 (Finset.mem_univ q0)
      have hle : (RC.1.filter (fun a => a.1 = q0)).card ≤ Fintype.card X := by
        apply Finset.card_le_card_of_injOn (fun a => a.2)
        · intro a _; exact Finset.mem_univ _
        · intro a ha b hb hab
          have ha1 : a.1 = q0 := (Finset.mem_filter.mp ha).2
          have hb1 : b.1 = q0 := (Finset.mem_filter.mp hb).2
          exact Prod.ext (ha1.trans hb1.symm) hab
      calc ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ (RC.1.filter (fun a => a.1 = q0)).card := hfib
        _ ≤ Fintype.card X := hle
    have huniv : IsEquipartitionedGE
        (Finset.univ : Finset (Fin p × Fin (Fintype.card X)))
        (Finset.univ : Finset (Fin p)) ⌈(Fintype.card X : ℝ) * x⌉₊ :=
      IsEquipartitionedGE.univ _ _ (by rw [Fintype.card_fin]; exact hceil_le)
    obtain ⟨R, hRsub, hRequi⟩ := bridge_equipartition huniv
    have hRequi' : IsEquipartitioned R (Fintype.card X)
        ((Fintype.card X : ℝ) * x) p :=
      isEquipartitioned_congr_ceil (by rw [Nat.ceil_natCast]) hRequi
    refine ⟨R, C, hRsub, hRequi', hCsub, by rw [hCcard, hceilC], ?_⟩
    intro M hm' hn'
    refine ⟨R, C, ?_, ?_, ?_, ?_, rfl⟩
    · rw [hm']; exact hRsub
    · rw [hm']; exact hRequi'
    · rw [hn']; exact hCsub
    · rw [hn', hCcard, hceilC]

end NPCC
