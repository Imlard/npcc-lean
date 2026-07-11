import Mathlib
import NPCC.VBP
import NPCC.Gap
import NPCC.Reduction
import NPCC.PolynomialSize

/-! # Source reduction wrapper: promised `{0,1}` Vector Bin Packing

This file now contains the proved `vbp_np_hard` reduction package, not a
citation axiom. The Lean kernel checks the endpoint-incidence construction,
promise preservation, YES equivalence, and size bounds. Polynomial-time
constructibility and the standard NP-hardness of 4-Colouring remain external
to the kernel statement. -/

namespace NPCC

open Workspace.Types.CommComplexity

/-- An edge-list instance of 4-Colouring: `numVerts` vertices, `numEdges` edges
given by two endpoint maps, with no self-loops. This is the source problem the
paper reduces from (arXiv:2508.05597, Proposition 42: the restricted
`{0,1}`-Vector-Bin-Packing endpoint with capacity `c = 1` and `m = 4` bins is
NP-complete by reduction from 4-Colouring). -/
structure FourColorInstance where
  numVerts : Nat
  numEdges : Nat
  edgeL : Fin numEdges → Fin numVerts
  edgeR : Fin numEdges → Fin numVerts
  edge_ne : ∀ e : Fin numEdges, edgeL e ≠ edgeR e

namespace FourColorInstance

/-- `G` is a YES-instance iff its vertices admit a proper 4-colouring: some
`colour : [numVerts] → [4]` giving distinct colours to the two endpoints of
every edge. -/
def IsYes (G : FourColorInstance) : Prop :=
  ∃ colour : Fin G.numVerts → Fin 4,
    ∀ e : Fin G.numEdges, colour (G.edgeL e) ≠ colour (G.edgeR e)

/-- A combinatorial source-size proxy: vertices plus edges plus one. This is
not a formal bit-level encoding length; relating it to a conventional edge-list
encoding is part of the external complexity-theory wrapper. -/
def sourceSize (G : FourColorInstance) : Nat :=
  G.numVerts + G.numEdges + 1

end FourColorInstance

namespace VBPInstance

/-- The Boolean-matrix footprint `(n+1)(d+1)` of a VBP instance's presentation,
used to state the reduction's monomial size bound. -/
def hardnessMatrixSize (I : VBPInstance) : Nat :=
  (I.n + 1) * (I.d + 1)

end VBPInstance

/-- The endpoint-incidence VBP instance associated to an edge-list
4-colouring instance: one vector per vertex and one coordinate per edge. -/
def toVBP (G : FourColorInstance) : VBPInstance where
  d := G.numEdges
  n := G.numVerts
  v := fun u e => decide (G.edgeL e = u) || decide (G.edgeR e = u)

/-- The endpoint-incidence VBP encoding is feasible exactly when the graph is
4-colourable. -/
theorem toVBP_yes_iff (G : FourColorInstance) :
    G.IsYes ↔ (toVBP G).IsYes := by
  classical
  constructor
  · intro hG
    obtain ⟨colour, hcolour⟩ := hG
    refine ⟨colour, ?_⟩
    intro p α
    apply Finset.card_le_one.mpr
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    obtain ⟨-, hxcol, hxv⟩ := hx
    obtain ⟨-, hycol, hyv⟩ := hy
    have hxedge : (G.edgeL α = x) ∨ (G.edgeR α = x) := by
      simpa [toVBP, Bool.or_eq_true] using hxv
    have hyedge : (G.edgeL α = y) ∨ (G.edgeR α = y) := by
      simpa [toVBP, Bool.or_eq_true] using hyv
    rcases hxedge with hxedge | hxedge <;> rcases hyedge with hyedge | hyedge
    · exact hxedge.symm.trans hyedge
    · exfalso
      exact hcolour α (by
        rw [hxedge, hyedge, hxcol, hycol])
    · exfalso
      exact hcolour α (by
        rw [hyedge, hxedge, hycol, hxcol])
    · exact hxedge.symm.trans hyedge
  · intro hI
    change ∃ σ : Fin G.numVerts → Fin 4, ∀ (p : Fin 4) (α : Fin G.numEdges),
        (Finset.univ.filter
          (fun i => σ i = p ∧
            (decide (G.edgeL α = i) || decide (G.edgeR α = i)) = true)).card ≤ 1 at hI
    obtain ⟨σ, hσ⟩ := hI
    refine ⟨σ, ?_⟩
    intro e hsame
    have hLmem :
        G.edgeL e ∈ Finset.univ.filter
          (fun i => σ i = σ (G.edgeL e) ∧
            (decide (G.edgeL e = i) || decide (G.edgeR e = i)) = true) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, rfl, ?_⟩
      simp
    have hRmem :
        G.edgeR e ∈ Finset.univ.filter
          (fun i => σ i = σ (G.edgeL e) ∧
            (decide (G.edgeL e = i) || decide (G.edgeR e = i)) = true) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hsame.symm, ?_⟩
      simp
    have hend_eq : G.edgeL e = G.edgeR e :=
      Finset.card_le_one.mp (hσ (σ (G.edgeL e)) e)
        (G.edgeL e) hLmem (G.edgeR e) hRmem
    exact G.edge_ne e hend_eq

/-- The endpoint-incidence VBP instance always satisfies the source promise:
each coordinate is hit only by the two endpoint vectors of the corresponding
edge, hence by at most four vectors. -/
theorem toVBP_promise (G : FourColorInstance) : (toVBP G).Promise := by
  classical
  change ∀ α : Fin G.numEdges,
    (Finset.univ.filter
      (fun i : Fin G.numVerts =>
        (decide (G.edgeL α = i) || decide (G.edgeR α = i)) = true)).card ≤ 4
  intro α
  have hsub :
      Finset.univ.filter
        (fun i : Fin G.numVerts =>
          (decide (G.edgeL α = i) || decide (G.edgeR α = i)) = true) ⊆
        ({G.edgeL α, G.edgeR α} : Finset (Fin G.numVerts)) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hendpoint : (G.edgeL α = i) ∨ (G.edgeR α = i) := by
      simpa [Bool.or_eq_true] using hi.2
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact hendpoint.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_le_two (a := G.edgeL α) (b := G.edgeR α)).trans (by norm_num))

/-- The reduction creates one VBP item per graph vertex. -/
theorem toVBP_numItems_bound (G : FourColorInstance) :
    (toVBP G).n ≤ G.sourceSize := by
  simp [toVBP, FourColorInstance.sourceSize]
  omega

/-- The reduction creates one VBP dimension per graph edge. -/
theorem toVBP_numDims_bound (G : FourColorInstance) :
    (toVBP G).d ≤ G.sourceSize := by
  simp [toVBP, FourColorInstance.sourceSize]
  omega

/-- The Boolean matrix footprint of the reduced VBP instance is quadratically
bounded by the source description size. -/
theorem toVBP_matrixSize_bound (G : FourColorInstance) :
    (toVBP G).hardnessMatrixSize ≤ (G.sourceSize) ^ 2 := by
  have hn : G.numVerts + 1 ≤ G.numVerts + G.numEdges + 1 := by
    omega
  have hd : G.numEdges + 1 ≤ G.numVerts + G.numEdges + 1 := by
    omega
  have hmul := Nat.mul_le_mul hn hd
  simpa [toVBP, VBPInstance.hardnessMatrixSize, FourColorInstance.sourceSize, pow_two]
    using hmul

/-- The content of `vbp_np_hard`: a size-bounded correctness map from
edge-list 4-Colouring to the promised `{0,1}`-Vector-Bin-Packing endpoint
(`c = 1`, `m = 4`). It supplies a map `toVBP` such that every produced instance
(i) satisfies the per-coordinate weight promise (each coordinate is `1` in at
most 4 vectors — the paper's "one vector per vertex, one coordinate per edge, so
each coordinate hits exactly its two endpoints" observation, generously
bounded), (ii) is a YES-instance iff the source is 4-colourable, and (iii) has
item count, dimension, and matrix footprint all bounded by fixed monomials in
`sourceSize`. It asserts NOTHING about polynomial runtime, about the class NP,
or about promise-violating VBP inputs — those stay outside the kernel. -/
structure VBP4PromiseHardnessPackage where
  toVBP : FourColorInstance → VBPInstance
  toVBP_promise : ∀ G : FourColorInstance, (toVBP G).Promise
  toVBP_yes_iff : ∀ G : FourColorInstance, G.IsYes ↔ (toVBP G).IsYes
  toVBP_numItems_bound : ∀ G : FourColorInstance, (toVBP G).n ≤ G.sourceSize
  toVBP_numDims_bound : ∀ G : FourColorInstance, (toVBP G).d ≤ G.sourceSize
  toVBP_matrixSize_bound :
    ∀ G : FourColorInstance, (toVBP G).hardnessMatrixSize ≤ (G.sourceSize) ^ 2

-- CLAIM-BEGIN axiom:vbp-np-hard
/-- FORMALIZED reduction package from edge-list 4-Colouring to the promised
`{0,1}`-`d`-Dimension Vector Bin Packing endpoint with capacity `c = 1` and
`m = 4` bins. The package is now a proved Lean definition, no longer a citation
axiom: it uses `toVBP`, proves the promise, proves YES preservation, and proves
the stated item, dimension, and matrix-size bounds. The cited NP-hardness and
polynomial-time constructibility of the map and the known hardness of
4-Colouring remain external.
-/
def vbp_np_hard : VBP4PromiseHardnessPackage := {
  toVBP := toVBP
  toVBP_promise := toVBP_promise
  toVBP_yes_iff := toVBP_yes_iff
  toVBP_numItems_bound := toVBP_numItems_bound
  toVBP_numDims_bound := toVBP_numDims_bound
  toVBP_matrixSize_bound := toVBP_matrixSize_bound
}
-- CLAIM-END axiom:vbp-np-hard

/-- Full-constructor analogue of `ctorScale_le_two_mul_max`. -/
theorem ctorScaleFull_le_two_mul_max (I : VBPInstance)
    (hmax : 1 <= max (preprocess I).d ctorDStarFull) :
    ctorScaleFull I <= 2 * max (preprocess I).d ctorDStarFull := by
  simpa [ctorScaleFull_eq_ceilPowTwo I] using ceilPowTwo_le_two_mul hmax

/-! ## Fixed-degree source-size bound -/

/-- A linear polynomial that dominates the normalized construction scale for
every graph with combinatorial size `s`.  `ctorDStarFull` is one absolute
constant selected once by the large-parameter proof. -/
noncomputable def sourceScalePolynomial (s : Nat) : Nat :=
  10 * (s + ctorDStarFull + 1)

/-- One fixed-degree polynomial dominating both typed carriers of the final
communication matrix. -/
noncomputable def sourceCarrierPolynomial (s : Nat) : Nat :=
  5 * s + 4 + sourceScalePolynomial s ^ fixedStructuralDegree

theorem sourceScalePolynomial_pos (s : Nat) : 0 < sourceScalePolynomial s := by
  unfold sourceScalePolynomial
  positivity

/-- The normalized dimension selected for a graph is linearly bounded by its
combinatorial source size, with absolute coefficients. -/
theorem gapScale_le_sourceScalePolynomial (G : FourColorInstance) :
    ctorScaleFull (vbp_np_hard.toVBP G) <= sourceScalePolynomial G.sourceSize := by
  let I := vbp_np_hard.toVBP G
  have hmax : 1 <= max (preprocess I).d ctorDStarFull := by
    by_contra h
    have hmax0 : max (preprocess I).d ctorDStarFull = 0 := by omega
    have hdCtor : ctorScaleFull I = 1 := by
      simp [ctorScaleFull_eq_ceilPowTwo, hmax0, ceilPowTwo]
    have hcert := CtorScaleCertificateFull I
    omega
  have hscale := ctorScaleFull_le_two_mul_max I hmax
  have hdim : I.d <= G.sourceSize := by
    simpa [I] using vbp_np_hard.toVBP_numDims_bound G
  have hpre : (preprocess I).d <= 5 * G.sourceSize := by
    simp only [preprocess]
    omega
  have hmaxle :
      max (preprocess I).d ctorDStarFull <= 5 * G.sourceSize + ctorDStarFull :=
    max_le (le_trans hpre (Nat.le_add_right _ _)) (Nat.le_add_left _ _)
  calc
    ctorScaleFull (vbp_np_hard.toVBP G) = ctorScaleFull I := by rfl
    _ <= 2 * max (preprocess I).d ctorDStarFull := hscale
    _ <= 2 * (5 * G.sourceSize + ctorDStarFull) := Nat.mul_le_mul_left 2 hmaxle
    _ <= sourceScalePolynomial G.sourceSize := by
      unfold sourceScalePolynomial
      omega

-- CLAIM-BEGIN thm:fixed-degree-size
/-- Fixed-degree output-size theorem for the complete typed reduction.  The
degree `fixedStructuralDegree` and all coefficients are absolute constants,
independent of `G`.  Both Alice's and Bob's carrier cardinalities are bounded
by the same explicit polynomial in `G.sourceSize`. -/
theorem main_output_size_fixed_degree (G : FourColorInstance) :
    Fintype.card
        (R4 (ctorScaleFull (vbp_np_hard.toVBP G))
          (reducedInstanceFull (vbp_np_hard.toVBP G)).n)
      <= sourceCarrierPolynomial G.sourceSize /\
    Fintype.card (C4 (ctorScaleFull (vbp_np_hard.toVBP G)))
      <= sourceCarrierPolynomial G.sourceSize
-- CLAIM-END thm:fixed-degree-size
  := by
  let I := vbp_np_hard.toVBP G
  let dCtor := ctorScaleFull I
  obtain ⟨hpow, hlog, hchk, _, _, _, _, _, _, _⟩ := CtorScaleCertificateFull I
  have hfixed := output_size_fixed_degree hpow hlog hchk
    (n := (reducedInstanceFull I).n)
  have hd : dCtor <= sourceScalePolynomial G.sourceSize := by
    simpa [I, dCtor] using gapScale_le_sourceScalePolynomial G
  have hdpow :
      dCtor ^ fixedStructuralDegree
        <= sourceScalePolynomial G.sourceSize ^ fixedStructuralDegree :=
    Nat.pow_le_pow_left hd fixedStructuralDegree
  have hn : (reducedInstanceFull I).n <= 5 * G.sourceSize + 4 := by
    have hn0 : I.n <= G.sourceSize := by
      simpa [I] using vbp_np_hard.toVBP_numItems_bound G
    simp only [reducedInstanceFull, normalizeInstance, preprocess]
    omega
  change
    Fintype.card (R4 dCtor (reducedInstanceFull I).n)
        <= sourceCarrierPolynomial G.sourceSize /\
      Fintype.card (C4 dCtor) <= sourceCarrierPolynomial G.sourceSize
  constructor
  · calc
      Fintype.card (R4 dCtor (reducedInstanceFull I).n)
          <= (reducedInstanceFull I).n + dCtor ^ fixedStructuralDegree := hfixed.1
      _ <= (5 * G.sourceSize + 4) +
          sourceScalePolynomial G.sourceSize ^ fixedStructuralDegree :=
        Nat.add_le_add hn hdpow
      _ = sourceCarrierPolynomial G.sourceSize := by
        rfl
  · calc
      Fintype.card (C4 dCtor) <= dCtor ^ fixedStructuralDegree := hfixed.2
      _ <= sourceScalePolynomial G.sourceSize ^ fixedStructuralDegree := hdpow
      _ <= sourceCarrierPolynomial G.sourceSize := by
        unfold sourceCarrierPolynomial
        omega

-- CLAIM-BEGIN thm:main-nphard-intro
/-- Paper `thm:main-nphard-intro` (NP-completeness of deterministic communication
complexity), exact kernel content: a choice-based communication-gap construction
from loopless edge-list 4-Colouring to the typed matrix `M₄`. For every instance
`G`, Lean proves the VBP promise, elementary source-size bounds, an explicit scale
bound, explicit row/column carrier bounds, and
`G.IsYes ↔ D(M₄) ≤ B_yes`. Fixed-degree domination is proved by
`main_output_size_fixed_degree`; the final square power-of-two padding, exact
preservation of `D`, and polynomial truth-table bit count are proved in
`NPCC.Public`. It does not prove a serialized source encoding, an executable
balanced-family generator or runtime, NP membership, or source NP-hardness. -/
theorem main_np_hardness :
    ∀ G : FourColorInstance,
      (vbp_np_hard.toVBP G).Promise ∧
      (vbp_np_hard.toVBP G).n ≤ G.sourceSize ∧
      (vbp_np_hard.toVBP G).d ≤ G.sourceSize ∧
      ctorScaleFull (vbp_np_hard.toVBP G)
          ≤ 2 * max (preprocess (vbp_np_hard.toVBP G)).d ctorDStarFull ∧
      ((Fintype.card (R4 (ctorScaleFull (vbp_np_hard.toVBP G))
            (reducedInstanceFull (vbp_np_hard.toVBP G)).n) : ℝ)
          ≤ ((reducedInstanceFull (vbp_np_hard.toVBP G)).n : ℝ)
            + rowPoly (ctorScaleFull (vbp_np_hard.toVBP G))) ∧
      ((Fintype.card (C4 (ctorScaleFull (vbp_np_hard.toVBP G))) : ℝ)
          ≤ colPoly (ctorScaleFull (vbp_np_hard.toVBP G))) ∧
      (G.IsYes ↔
        D (M4 (ctorScaleFull (vbp_np_hard.toVBP G))
              (reducedVectorsFull (vbp_np_hard.toVBP G)))
          ≤ Byes (ctorScaleFull (vbp_np_hard.toVBP G)))
-- CLAIM-END thm:main-nphard-intro
  := by
  intro G
  let I := vbp_np_hard.toVBP G
  let dCtor := ctorScaleFull I
  obtain ⟨hpow, hlog, hchk, hd, hm0, hrowT, hraw, hprime, h35, hrob⟩ :=
    CtorScaleCertificateFull I
  have hscale : dCtor <= 2 * max (preprocess I).d ctorDStarFull := by
    have hmax : 1 <= max (preprocess I).d ctorDStarFull := by
      by_contra hmax
      have hmax0 : max (preprocess I).d ctorDStarFull = 0 := by omega
      have hdCtor : dCtor = 1 := by
        simp [dCtor, ctorScaleFull_eq_ceilPowTwo, hmax0, ceilPowTwo]
      omega
    simpa [dCtor] using ctorScaleFull_le_two_mul_max I hmax
  have hsize :=
    output_size_bounds dCtor (reducedInstanceFull I).n
      (Params.t1_pos dCtor) hchk.t1_le_q1_add_five
      (Params.t2_pos dCtor) hchk.t2_le_q2 hchk.one_le_q1
  have hgap :
      G.IsYes ↔ D (M4 dCtor (reducedVectorsFull I)) <= Byes dCtor := by
    obtain ⟨hYes, hNo⟩ := reduction_gap I
      (by simpa [I] using vbp_np_hard.toVBP_promise G)
    constructor
    · intro hG
      exact hYes ((vbp_np_hard.toVBP_yes_iff G).mp hG)
    · intro hD
      by_contra hnG
      have hNoI : ¬ I.IsYes := by
        intro hI
        exact hnG ((vbp_np_hard.toVBP_yes_iff G).mpr hI)
      exact (not_le.mpr (hNo hNoI)) hD
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [I] using vbp_np_hard.toVBP_promise G
  · simpa [I] using vbp_np_hard.toVBP_numItems_bound G
  · simpa [I] using vbp_np_hard.toVBP_numDims_bound G
  · simpa [I, dCtor] using hscale
  · simpa [I, dCtor] using hsize.1
  · simpa [I, dCtor] using hsize.2
  · simpa [I, dCtor] using hgap

end NPCC
