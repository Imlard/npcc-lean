import NPCC.Wrapper
import NPCC.Padding

/-!
# Public theorem surface

This file gives short names to the objects in the checked gap construction.
It is the recommended entry point for readers who want the mathematical
statement without first unpacking the implementation modules.

The construction is noncomputable because the balanced column families are
selected from the citation axiom
`finite_alphabet_balanced_family_exists`. The theorems below certify the
selected matrix, its communication-complexity gap, and the final square
power-of-two truth-table padding. The carrier and truth-table sizes have an
explicit fixed-degree polynomial bound in the combinatorial source size. The
theorems do not assert an executable polynomial-time reduction.
-/

namespace NPCC

open Workspace.Types.CommComplexity

/-- The promised vector-bin-packing instance produced from a loopless
edge-list instance of 4-Colouring. -/
def sourceVBP (G : FourColorInstance) : VBPInstance :=
  vbp_np_hard.toVBP G

/-- The power-of-two scale selected for the communication matrix. -/
noncomputable def gapScale (G : FourColorInstance) : Nat :=
  ctorScaleFull (sourceVBP G)

/-- Alice's typed input carrier before truth-table padding. -/
abbrev GapRow (G : FourColorInstance) : Type :=
  R4 (gapScale G) (reducedInstanceFull (sourceVBP G)).n

/-- Bob's typed input carrier before truth-table padding. -/
abbrev GapCol (G : FourColorInstance) : Type := C4 (gapScale G)

/-- The communication matrix selected by the checked construction. -/
noncomputable def gapMatrix (G : FourColorInstance) :
    GapRow G -> GapCol G -> Bool :=
  M4 (gapScale G) (reducedVectorsFull (sourceVBP G))

/-- The YES-instance communication budget. -/
noncomputable def gapBudget (G : FourColorInstance) : Nat :=
  Byes (gapScale G)

/-- The exact threshold equivalence proved by the formalization. -/
theorem fourColorable_iff_gapMatrix_cost_le (G : FourColorInstance) :
    G.IsYes ↔ D (gapMatrix G) ≤ gapBudget G := by
  simpa [sourceVBP, gapScale, gapMatrix, gapBudget] using
    (main_np_hardness G).2.2.2.2.2.2

/-- The same gap in its "one more bit" form. Because communication cost is a
natural number, strict failure of the YES budget is equivalent to requiring at
least `gapBudget G + 1` bits. This is a threshold statement: it does not claim
that every NO instance has cost exactly `gapBudget G + 1`. -/
theorem not_fourColorable_iff_gapMatrix_cost_at_least_one_more
    (G : FourColorInstance) :
    (¬ G.IsYes) ↔ gapBudget G + 1 ≤ D (gapMatrix G) := by
  have hgap := fourColorable_iff_gapMatrix_cost_le G
  constructor
  · intro hno
    have hnotle : ¬ D (gapMatrix G) ≤ gapBudget G := by
      intro hcheap
      exact hno (hgap.mpr hcheap)
    omega
  · intro hextra hyes
    have hcheap := hgap.mp hyes
    omega

/-- The exact closed-form carrier bounds used before fixed-degree domination. -/
theorem gapMatrix_carrier_bounds (G : FourColorInstance) :
    ((Fintype.card
          (R4 (gapScale G) (reducedInstanceFull (sourceVBP G)).n) : Real)
        ≤ ((reducedInstanceFull (sourceVBP G)).n : Real) + rowPoly (gapScale G))
    /\
    ((Fintype.card (C4 (gapScale G)) : Real) ≤ colPoly (gapScale G)) := by
  have h := main_np_hardness G
  change
    ((Fintype.card
          (R4 (ctorScaleFull (vbp_np_hard.toVBP G))
            (reducedInstanceFull (vbp_np_hard.toVBP G)).n) : Real)
        ≤ ((reducedInstanceFull (vbp_np_hard.toVBP G)).n : Real)
          + rowPoly (ctorScaleFull (vbp_np_hard.toVBP G)))
      /\
    ((Fintype.card (C4 (ctorScaleFull (vbp_np_hard.toVBP G))) : Real)
        ≤ colPoly (ctorScaleFull (vbp_np_hard.toVBP G)))
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- Both typed carriers are bounded by one explicit fixed-degree polynomial in
the graph's combinatorial source size. -/
theorem gapMatrix_fixed_degree_bounds (G : FourColorInstance) :
    Fintype.card (GapRow G) <= sourceCarrierPolynomial G.sourceSize /\
      Fintype.card (GapCol G) <= sourceCarrierPolynomial G.sourceSize := by
  change
    Fintype.card
        (R4 (ctorScaleFull (vbp_np_hard.toVBP G))
          (reducedInstanceFull (vbp_np_hard.toVBP G)).n)
      <= sourceCarrierPolynomial G.sourceSize /\
    Fintype.card (C4 (ctorScaleFull (vbp_np_hard.toVBP G)))
      <= sourceCarrierPolynomial G.sourceSize
  exact main_output_size_fixed_degree G

/-! ## Conventional square truth-table representation -/

/-- A concrete row witnessing that the reduction's typed matrix is nonempty. -/
noncomputable def gapRowWitness (G : FourColorInstance) : GapRow G := by
  have hcert := CtorScaleCertificateFull (sourceVBP G)
  rcases hcert with ⟨_, _, hchk, _, _, _, _, _, _, _⟩
  have hL2 : 0 < L2 (gapScale G) :=
    L2_pos (gapScale G) hchk.t2_le_q2 hchk.one_le_q1
  exact Sum.inl (⟨0, by norm_num⟩, ⟨0, hL2⟩)

/-- A concrete column witnessing that the reduction's typed matrix is nonempty. -/
noncomputable def gapColWitness (G : FourColorInstance) : GapCol G := by
  have hcert := CtorScaleCertificateFull (sourceVBP G)
  rcases hcert with ⟨_, _, hchk, _, _, _, _, _, _, _⟩
  have hL1 : 0 < L1 (gapScale G) :=
    L1_pos (gapScale G) hchk.t1_le_q1_add_five
  exact
    (⟨0, by norm_num⟩,
      fun _ => (⟨0, Params.q2_pos (gapScale G)⟩, ⟨0, hL1⟩))

/-- The common power-of-two side length of the conventional square truth
table. -/
noncomputable def gapTruthTableSize (G : FourColorInstance) : Nat :=
  squarePadSize (GapRow G) (GapCol G)

/-- The final square Boolean truth table. Extra indices duplicate an existing
row or column; no values on the original matrix are changed. -/
noncomputable def gapTruthTable (G : FourColorInstance) :
    Fin (gapTruthTableSize G) -> Fin (gapTruthTableSize G) -> Bool := by
  letI : Nonempty (GapRow G) := ⟨gapRowWitness G⟩
  letI : Nonempty (GapCol G) := ⟨gapColWitness G⟩
  exact squarePad (gapMatrix G)

/-- The square truth-table padding preserves deterministic communication
complexity exactly. -/
theorem gapTruthTable_cost (G : FourColorInstance) :
    D (gapTruthTable G) = D (gapMatrix G) := by
  letI : Nonempty (GapRow G) := ⟨gapRowWitness G⟩
  letI : Nonempty (GapCol G) := ⟨gapColWitness G⟩
  change D (squarePad (gapMatrix G)) = D (gapMatrix G)
  exact D_squarePad (gapMatrix G)

/-- The final truth table has a power-of-two side length. -/
theorem gapTruthTableSize_eq_two_pow (G : FourColorInstance) :
    ∃ k : Nat, gapTruthTableSize G = 2 ^ k := by
  exact squarePadSize_eq_two_pow (GapRow G) (GapCol G)

/-- Power-of-two rounding increases the larger typed carrier by a factor of at
most two. -/
theorem gapTruthTableSize_le_two_mul_max (G : FourColorInstance) :
    gapTruthTableSize G <=
      2 * max (Fintype.card (GapRow G)) (Fintype.card (GapCol G)) := by
  have hrow : 0 < Fintype.card (GapRow G) :=
    Fintype.card_pos_iff.mpr ⟨gapRowWitness G⟩
  have hmax : 1 <= max (Fintype.card (GapRow G)) (Fintype.card (GapCol G)) := by
    omega
  simpa [gapTruthTableSize, squarePadSize] using ceilPowTwo_le_two_mul hmax

/-- The number of Boolean entries in the final square truth table. -/
noncomputable def gapTruthTableBitCount (G : FourColorInstance) : Nat :=
  gapTruthTableSize G ^ 2

/-- An explicit fixed-degree polynomial bounding the final truth-table bit
count.  Its exponent and coefficients are absolute constants. -/
noncomputable def sourceTruthTablePolynomial (s : Nat) : Nat :=
  4 * sourceCarrierPolynomial s ^ 2

/-- The conventional square truth table has polynomially many bits in the
combinatorial source size, with a single fixed degree. -/
theorem gapTruthTableBitCount_le_fixed_polynomial (G : FourColorInstance) :
    gapTruthTableBitCount G <= sourceTruthTablePolynomial G.sourceSize := by
  have hcarriers := gapMatrix_fixed_degree_bounds G
  have hmax :
      max (Fintype.card (GapRow G)) (Fintype.card (GapCol G))
        <= sourceCarrierPolynomial G.sourceSize :=
    max_le hcarriers.1 hcarriers.2
  have hside :
      gapTruthTableSize G <= 2 * sourceCarrierPolynomial G.sourceSize :=
    le_trans (gapTruthTableSize_le_two_mul_max G) (Nat.mul_le_mul_left 2 hmax)
  have hsquare := Nat.pow_le_pow_left hside 2
  unfold gapTruthTableBitCount sourceTruthTablePolynomial
  nlinarith

-- CLAIM-BEGIN thm:padded-gap
/-- Exact threshold equivalence for the conventional square truth table. -/
theorem fourColorable_iff_gapTruthTable_cost_le (G : FourColorInstance) :
    G.IsYes <-> D (gapTruthTable G) <= gapBudget G := by
  rw [gapTruthTable_cost]
  exact fourColorable_iff_gapMatrix_cost_le G

/-- Exact one-more-bit lower bound for the conventional square truth table. -/
theorem not_fourColorable_iff_gapTruthTable_cost_at_least_one_more
    (G : FourColorInstance) :
    (Not G.IsYes) <-> gapBudget G + 1 <= D (gapTruthTable G) := by
  rw [gapTruthTable_cost]
  exact not_fourColorable_iff_gapMatrix_cost_at_least_one_more G
-- CLAIM-END thm:padded-gap

end NPCC
